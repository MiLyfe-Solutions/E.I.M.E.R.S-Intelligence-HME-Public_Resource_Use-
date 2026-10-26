import V185TrunkScan23Chunk1103

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6537105 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 4]
def baseStart_6537105 : Nat := 118140960795 + 6537105 * 2 ^ 59
def prefixEnd_6537105 : Nat := 4983230072969 + 3 ^ 40 * 6537105 * 2
def baseEnd_6537105 : Nat := 3356676953909751280323907

theorem tailTrace_6537105 : CollatzResearch.WordTrace tailWord_6537105 prefixEnd_6537105 3356676953909751280323907 := by
  unfold tailWord_6537105
  simp only [CollatzResearch.WordTrace]
  refine ⟨238427806982192508494092769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158951871321461672329395179 238427806982192508494092769)
  ·
    refine ⟨178820855236644381370569577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238427806982192508494092769 178820855236644381370569577)
    ·
      refine ⟨134115641427483286027927183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178820855236644381370569577 134115641427483286027927183)
      ·
        refine ⟨201173462141224929041890775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134115641427483286027927183 201173462141224929041890775)
        ·
          refine ⟨301760193211837393562836163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201173462141224929041890775 301760193211837393562836163)
          ·
            refine ⟨452640289817756090344254245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301760193211837393562836163 452640289817756090344254245)
            ·
              refine ⟨84870054340829266939547671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 452640289817756090344254245 84870054340829266939547671)
              ·
                refine ⟨127305081511243900409321507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84870054340829266939547671 127305081511243900409321507)
                ·
                  refine ⟨190957622266865850613982261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127305081511243900409321507 190957622266865850613982261)
                  ·
                    refine ⟨17902277087518673495060837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 190957622266865850613982261 17902277087518673495060837)
                    ·
                      refine ⟨3356676953909751280323907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17902277087518673495060837 3356676953909751280323907)
                      ·
                        rfl

theorem cell23_6537105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_6537105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537105 prefixEnd_6537105 := by exact prefixLift 6537105
  have htrace : WordTrace (prefixWord ++ tailWord_6537105) baseStart_6537105 baseEnd_6537105 := by
    simpa [prefixWord, tailWord_6537105, baseEnd_6537105] using wordTrace_append hprefix tailTrace_6537105
  have hstable : (prefixWord ++ tailWord_6537105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537105).length < 2 ^ (prefixWord ++ tailWord_6537105).sum := by decide
  have hdescent : baseEnd_6537105 < baseStart_6537105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537110 : List Nat := [5, 3, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_6537110 : Nat := 118140960795 + 6537110 * 2 ^ 59
def prefixEnd_6537110 : Nat := 4983230072969 + 3 ^ 40 * 6537110 * 2
def baseEnd_6537110 : Nat := 1118893173771007920253795

theorem tailTrace_6537110 : CollatzResearch.WordTrace tailWord_6537110 prefixEnd_6537110 1118893173771007920253795 := by
  unfold tailWord_6537110
  simp only [CollatzResearch.WordTrace]
  refine ⟨14901749334198399646751549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158951992898116262898683189 14901749334198399646751549)
  ·
    refine ⟨5588156000324399867531831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14901749334198399646751549 5588156000324399867531831)
    ·
      refine ⟨8382234000486599801297747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5588156000324399867531831 8382234000486599801297747)
      ·
        refine ⟨12573351000729899701946621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8382234000486599801297747 12573351000729899701946621)
        ·
          refine ⟨4715006625273712388229983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12573351000729899701946621 4715006625273712388229983)
          ·
            refine ⟨7072509937910568582344975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4715006625273712388229983 7072509937910568582344975)
            ·
              refine ⟨10608764906865852873517463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7072509937910568582344975 10608764906865852873517463)
              ·
                refine ⟨15913147360298779310276195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10608764906865852873517463 15913147360298779310276195)
                ·
                  refine ⟨23869721040448168965414293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15913147360298779310276195 23869721040448168965414293)
                  ·
                    refine ⟨1118893173771007920253795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23869721040448168965414293 1118893173771007920253795)
                    ·
                      rfl

theorem cell23_6537110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_6537110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537110 prefixEnd_6537110 := by exact prefixLift 6537110
  have htrace : WordTrace (prefixWord ++ tailWord_6537110) baseStart_6537110 baseEnd_6537110 := by
    simpa [prefixWord, tailWord_6537110, baseEnd_6537110] using wordTrace_append hprefix tailTrace_6537110
  have hstable : (prefixWord ++ tailWord_6537110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537110).length < 2 ^ (prefixWord ++ tailWord_6537110).sum := by decide
  have hdescent : baseEnd_6537110 < baseStart_6537110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537116 : List Nat := [2, 2, 3, 3, 1, 3, 1, 1, 1, 3, 3]
def baseStart_6537116 : Nat := 118140960795 + 6537116 * 2 ^ 59
def prefixEnd_6537116 : Nat := 4983230072969 + 3 ^ 40 * 6537116 * 2
def baseEnd_6537116 : Nat := 3356682602196950737286357

theorem tailTrace_6537116 : CollatzResearch.WordTrace tailWord_6537116 prefixEnd_6537116 3356682602196950737286357 := by
  unfold tailWord_6537116
  simp only [CollatzResearch.WordTrace]
  refine ⟨119214104092576328686371601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158952138790101771581828801 119214104092576328686371601)
  ·
    refine ⟨89410578069432246514778701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119214104092576328686371601 89410578069432246514778701)
    ·
      refine ⟨33528966776037092443042013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89410578069432246514778701 33528966776037092443042013)
      ·
        refine ⟨12573362541013909666140755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33528966776037092443042013 12573362541013909666140755)
        ·
          refine ⟨18860043811520864499211133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12573362541013909666140755 18860043811520864499211133)
          ·
            refine ⟨7072516429320324187204175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18860043811520864499211133 7072516429320324187204175)
            ·
              refine ⟨10608774643980486280806263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7072516429320324187204175 10608774643980486280806263)
              ·
                refine ⟨15913161965970729421209395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10608774643980486280806263 15913161965970729421209395)
                ·
                  refine ⟨23869742948956094131814093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15913161965970729421209395 23869742948956094131814093)
                  ·
                    refine ⟨8951153605858535299430285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23869742948956094131814093 8951153605858535299430285)
                    ·
                      refine ⟨3356682602196950737286357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8951153605858535299430285 3356682602196950737286357)
                      ·
                        rfl

theorem cell23_6537116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_6537116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537116 prefixEnd_6537116 := by exact prefixLift 6537116
  have htrace : WordTrace (prefixWord ++ tailWord_6537116) baseStart_6537116 baseEnd_6537116 := by
    simpa [prefixWord, tailWord_6537116, baseEnd_6537116] using wordTrace_append hprefix tailTrace_6537116
  have hstable : (prefixWord ++ tailWord_6537116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537116).length < 2 ^ (prefixWord ++ tailWord_6537116).sum := by decide
  have hdescent : baseEnd_6537116 < baseStart_6537116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537125 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 3, 3, 5]
def baseStart_6537125 : Nat := 118140960795 + 6537125 * 2 ^ 59
def prefixEnd_6537125 : Nat := 4983230072969 + 3 ^ 40 * 6537125 * 2
def baseEnd_6537125 : Nat := 3356687223522841202073815

theorem tailTrace_6537125 : CollatzResearch.WordTrace tailWord_6537125 prefixEnd_6537125 3356687223522841202073815 := by
  unfold tailWord_6537125
  simp only [CollatzResearch.WordTrace]
  refine ⟨238428536442120051909820829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158952357628080034606547219 238428536442120051909820829)
  ·
    refine ⟨89410701165795019466182811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238428536442120051909820829 89410701165795019466182811)
    ·
      refine ⟨134116051748692529199274217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89410701165795019466182811 134116051748692529199274217)
      ·
        refine ⟨100587038811519396899455663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134116051748692529199274217 100587038811519396899455663)
        ·
          refine ⟨150880558217279095349183495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100587038811519396899455663 150880558217279095349183495)
          ·
            refine ⟨226320837325918643023775243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150880558217279095349183495 226320837325918643023775243)
            ·
              refine ⟨339481255988877964535662865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226320837325918643023775243 339481255988877964535662865)
              ·
                refine ⟨254610941991658473401747149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339481255988877964535662865 254610941991658473401747149)
                ·
                  refine ⟨95479103246871927525655181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254610941991658473401747149 95479103246871927525655181)
                  ·
                    refine ⟨35804663717576972822120693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95479103246871927525655181 35804663717576972822120693)
                    ·
                      refine ⟨3356687223522841202073815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35804663717576972822120693 3356687223522841202073815)
                      ·
                        rfl

theorem cell23_6537125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_6537125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537125 prefixEnd_6537125 := by exact prefixLift 6537125
  have htrace : WordTrace (prefixWord ++ tailWord_6537125) baseStart_6537125 baseEnd_6537125 := by
    simpa [prefixWord, tailWord_6537125, baseEnd_6537125] using wordTrace_append hprefix tailTrace_6537125
  have hstable : (prefixWord ++ tailWord_6537125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537125).length < 2 ^ (prefixWord ++ tailWord_6537125).sum := by decide
  have hdescent : baseEnd_6537125 < baseStart_6537125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537139 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 6, 2, 2]
def baseStart_6537139 : Nat := 118140960795 + 6537139 * 2 ^ 59
def prefixEnd_6537139 : Nat := 4983230072969 + 3 ^ 40 * 6537139 * 2
def baseEnd_6537139 : Nat := 3356694412252004147298751

theorem tailTrace_6537139 : CollatzResearch.WordTrace tailWord_6537139 prefixEnd_6537139 3356694412252004147298751 := by
  unfold tailWord_6537139
  simp only [CollatzResearch.WordTrace]
  refine ⟨238429047064069332300830471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158952698042712888200553647 238429047064069332300830471)
  ·
    refine ⟨357643570596103998451245707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238429047064069332300830471 357643570596103998451245707)
    ·
      refine ⟨536465355894155997676868561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357643570596103998451245707 536465355894155997676868561)
      ·
        refine ⟨402349016920616998257651421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536465355894155997676868561 402349016920616998257651421)
        ·
          refine ⟨150880881345231374346619283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 402349016920616998257651421 150880881345231374346619283)
          ·
            refine ⟨226321322017847061519928925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150880881345231374346619283 226321322017847061519928925)
            ·
              refine ⟨84870495756692648069973347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226321322017847061519928925 84870495756692648069973347)
              ·
                refine ⟨127305743635038972104960021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84870495756692648069973347 127305743635038972104960021)
                ·
                  refine ⟨5967456732892451817420001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127305743635038972104960021 5967456732892451817420001)
                  ·
                    refine ⟨4475592549669338863065001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5967456732892451817420001 4475592549669338863065001)
                    ·
                      refine ⟨3356694412252004147298751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4475592549669338863065001 3356694412252004147298751)
                      ·
                        rfl

theorem cell23_6537139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 2, 2].length) (baseStart_6537139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537139 prefixEnd_6537139 := by exact prefixLift 6537139
  have htrace : WordTrace (prefixWord ++ tailWord_6537139) baseStart_6537139 baseEnd_6537139 := by
    simpa [prefixWord, tailWord_6537139, baseEnd_6537139] using wordTrace_append hprefix tailTrace_6537139
  have hstable : (prefixWord ++ tailWord_6537139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537139).length < 2 ^ (prefixWord ++ tailWord_6537139).sum := by decide
  have hdescent : baseEnd_6537139 < baseStart_6537139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537162 : List Nat := [3, 1, 2, 1, 2, 1, 5, 1, 7]
def baseStart_6537162 : Nat := 118140960795 + 6537162 * 2 ^ 59
def prefixEnd_6537162 : Nat := 4983230072969 + 3 ^ 40 * 6537162 * 2
def baseEnd_6537162 : Nat := 372967358034117506367905

theorem tailTrace_6537162 : CollatzResearch.WordTrace tailWord_6537162 prefixEnd_6537162 372967358034117506367905 := by
  unfold tailWord_6537162
  simp only [CollatzResearch.WordTrace]
  refine ⟨59607471485746501807229435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158953257295324004819278493 59607471485746501807229435)
  ·
    refine ⟨89411207228619752710844153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59607471485746501807229435 89411207228619752710844153)
    ·
      refine ⟨67058405421464814533133115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89411207228619752710844153 67058405421464814533133115)
      ·
        refine ⟨100587608132197221799699673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67058405421464814533133115 100587608132197221799699673)
        ·
          refine ⟨75440706099147916349774755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100587608132197221799699673 75440706099147916349774755)
          ·
            refine ⟨113161059148721874524662133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75440706099147916349774755 113161059148721874524662133)
            ·
              refine ⟨10608849295192675736687075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113161059148721874524662133 10608849295192675736687075)
              ·
                refine ⟨15913273942789013605030613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10608849295192675736687075 15913273942789013605030613)
                ·
                  refine ⟨372967358034117506367905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15913273942789013605030613 372967358034117506367905)
                  ·
                    rfl

theorem cell23_6537162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 7].length) (baseStart_6537162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537162 prefixEnd_6537162 := by exact prefixLift 6537162
  have htrace : WordTrace (prefixWord ++ tailWord_6537162) baseStart_6537162 baseEnd_6537162 := by
    simpa [prefixWord, tailWord_6537162, baseEnd_6537162] using wordTrace_append hprefix tailTrace_6537162
  have hstable : (prefixWord ++ tailWord_6537162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537162).length < 2 ^ (prefixWord ++ tailWord_6537162).sum := by decide
  have hdescent : baseEnd_6537162 < baseStart_6537162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537173 : List Nat := [1, 3, 2, 3, 2, 2, 1, 3, 2, 2, 2]
def baseStart_6537173 : Nat := 118140960795 + 6537173 * 2 ^ 59
def prefixEnd_6537173 : Nat := 4983230072969 + 3 ^ 40 * 6537173 * 2
def baseEnd_6537173 : Nat := 3356711870594257014273595

theorem tailTrace_6537173 : CollatzResearch.WordTrace tailWord_6537173 prefixEnd_6537173 3356711870594257014273595 := by
  unfold tailWord_6537173
  simp only [CollatzResearch.WordTrace]
  refine ⟨238430287145946156107568173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158953524763964104071712115 238430287145946156107568173)
  ·
    refine ⟨89411357679729808540338065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238430287145946156107568173 89411357679729808540338065)
    ·
      refine ⟨67058518259797356405253549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89411357679729808540338065 67058518259797356405253549)
      ·
        refine ⟨25146944347424008651970081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67058518259797356405253549 25146944347424008651970081)
        ·
          refine ⟨18860208260568006488977561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25146944347424008651970081 18860208260568006488977561)
          ·
            refine ⟨14145156195426004866733171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18860208260568006488977561 14145156195426004866733171)
            ·
              refine ⟨21217734293139007300099757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14145156195426004866733171 21217734293139007300099757)
              ·
                refine ⟨7956650359927127737537409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21217734293139007300099757 7956650359927127737537409)
                ·
                  refine ⟨5967487769945345803153057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7956650359927127737537409 5967487769945345803153057)
                  ·
                    refine ⟨4475615827459009352364793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5967487769945345803153057 4475615827459009352364793)
                    ·
                      refine ⟨3356711870594257014273595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4475615827459009352364793 3356711870594257014273595)
                      ·
                        rfl

theorem cell23_6537173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_6537173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537173 prefixEnd_6537173 := by exact prefixLift 6537173
  have htrace : WordTrace (prefixWord ++ tailWord_6537173) baseStart_6537173 baseEnd_6537173 := by
    simpa [prefixWord, tailWord_6537173, baseEnd_6537173] using wordTrace_append hprefix tailTrace_6537173
  have hstable : (prefixWord ++ tailWord_6537173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537173).length < 2 ^ (prefixWord ++ tailWord_6537173).sum := by decide
  have hdescent : baseEnd_6537173 < baseStart_6537173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537232 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 3]
def baseStart_6537232 : Nat := 118140960795 + 6537232 * 2 ^ 59
def prefixEnd_6537232 : Nat := 4983230072969 + 3 ^ 40 * 6537232 * 2
def baseEnd_6537232 : Nat := 3356742165952872283435823

theorem tailTrace_6537232 : CollatzResearch.WordTrace tailWord_6537232 prefixEnd_6537232 3356742165952872283435823 := by
  unfold tailWord_6537232
  simp only [CollatzResearch.WordTrace]
  refine ⟨119216219526366204591982975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158954959368488272789310633 119216219526366204591982975)
  ·
    refine ⟨178824329289549306887974463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119216219526366204591982975 178824329289549306887974463)
    ·
      refine ⟨268236493934323960331961695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178824329289549306887974463 268236493934323960331961695)
      ·
        refine ⟨402354740901485940497942543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268236493934323960331961695 402354740901485940497942543)
        ·
          refine ⟨603532111352228910746913815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402354740901485940497942543 603532111352228910746913815)
          ·
            refine ⟨905298167028343366120370723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603532111352228910746913815 905298167028343366120370723)
            ·
              refine ⟨1357947250542515049180556085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 905298167028343366120370723 1357947250542515049180556085)
              ·
                refine ⟨127307554738360785860677133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1357947250542515049180556085 127307554738360785860677133)
                ·
                  refine ⟨47740333026885294697753925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127307554738360785860677133 47740333026885294697753925)
                  ·
                    refine ⟨8951312442540992755828861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47740333026885294697753925 8951312442540992755828861)
                    ·
                      refine ⟨3356742165952872283435823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8951312442540992755828861 3356742165952872283435823)
                      ·
                        rfl

theorem cell23_6537232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 3].length) (baseStart_6537232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537232 prefixEnd_6537232 := by exact prefixLift 6537232
  have htrace : WordTrace (prefixWord ++ tailWord_6537232) baseStart_6537232 baseEnd_6537232 := by
    simpa [prefixWord, tailWord_6537232, baseEnd_6537232] using wordTrace_append hprefix tailTrace_6537232
  have hstable : (prefixWord ++ tailWord_6537232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537232).length < 2 ^ (prefixWord ++ tailWord_6537232).sum := by decide
  have hdescent : baseEnd_6537232 < baseStart_6537232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537269 : List Nat := [1, 3, 3, 1, 1, 1, 5, 2, 6]
def baseStart_6537269 : Nat := 118140960795 + 6537269 * 2 ^ 59
def prefixEnd_6537269 : Nat := 4983230072969 + 3 ^ 40 * 6537269 * 2
def baseEnd_6537269 : Nat := 372973462748565404297017

theorem tailTrace_6537269 : CollatzResearch.WordTrace tailWord_6537269 prefixEnd_6537269 372973462748565404297017 := by
  unfold tailWord_6537269
  simp only [CollatzResearch.WordTrace]
  refine ⟨238433788553598364503062861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158955859035732243002041907 238433788553598364503062861)
  ·
    refine ⟨89412670707599386688648573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238433788553598364503062861 89412670707599386688648573)
    ·
      refine ⟨33529751515349770008243215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89412670707599386688648573 33529751515349770008243215)
      ·
        refine ⟨50294627273024655012364823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33529751515349770008243215 50294627273024655012364823)
        ·
          refine ⟨75441940909536982518547235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50294627273024655012364823 75441940909536982518547235)
          ·
            refine ⟨113162911364305473777820853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75441940909536982518547235 113162911364305473777820853)
            ·
              refine ⟨10609022940403638166670705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113162911364305473777820853 10609022940403638166670705)
              ·
                refine ⟨7956767205302728625003029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10609022940403638166670705 7956767205302728625003029)
                ·
                  refine ⟨372973462748565404297017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7956767205302728625003029 372973462748565404297017)
                  ·
                    rfl

theorem cell23_6537269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 6].length) (baseStart_6537269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537269 prefixEnd_6537269 := by exact prefixLift 6537269
  have htrace : WordTrace (prefixWord ++ tailWord_6537269) baseStart_6537269 baseEnd_6537269 := by
    simpa [prefixWord, tailWord_6537269, baseEnd_6537269] using wordTrace_append hprefix tailTrace_6537269
  have hstable : (prefixWord ++ tailWord_6537269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537269).length < 2 ^ (prefixWord ++ tailWord_6537269).sum := by decide
  have hdescent : baseEnd_6537269 < baseStart_6537269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537289 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 3, 5, 2]
def baseStart_6537289 : Nat := 118140960795 + 6537289 * 2 ^ 59
def prefixEnd_6537289 : Nat := 4983230072969 + 3 ^ 40 * 6537289 * 2
def baseEnd_6537289 : Nat := 3356771434350178560423061

theorem tailTrace_6537289 : CollatzResearch.WordTrace tailWord_6537289 prefixEnd_6537289 3356771434350178560423061 := by
  unfold tailWord_6537289
  simp only [CollatzResearch.WordTrace]
  refine ⟨238434518013525907918790921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158956345342350605279193947 238434518013525907918790921)
  ·
    refine ⟨178825888510144430939093191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238434518013525907918790921 178825888510144430939093191)
    ·
      refine ⟨268238832765216646408639787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178825888510144430939093191 268238832765216646408639787)
      ·
        refine ⟨402358249147824969612959681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268238832765216646408639787 402358249147824969612959681)
        ·
          refine ⟨301768686860868727209719761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402358249147824969612959681 301768686860868727209719761)
          ·
            refine ⟨226326515145651545407289821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301768686860868727209719761 226326515145651545407289821)
            ·
              refine ⟨84872443179619329527733683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226326515145651545407289821 84872443179619329527733683)
              ·
                refine ⟨127308664769428994291600525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84872443179619329527733683 127308664769428994291600525)
                ·
                  refine ⟨47740749288535872859350197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127308664769428994291600525 47740749288535872859350197)
                  ·
                    refine ⟨4475695245800238080564081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47740749288535872859350197 4475695245800238080564081)
                    ·
                      refine ⟨3356771434350178560423061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4475695245800238080564081 3356771434350178560423061)
                      ·
                        rfl

theorem cell23_6537289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 5, 2].length) (baseStart_6537289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537289 prefixEnd_6537289 := by exact prefixLift 6537289
  have htrace : WordTrace (prefixWord ++ tailWord_6537289) baseStart_6537289 baseEnd_6537289 := by
    simpa [prefixWord, tailWord_6537289, baseEnd_6537289] using wordTrace_append hprefix tailTrace_6537289
  have hstable : (prefixWord ++ tailWord_6537289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537289).length < 2 ^ (prefixWord ++ tailWord_6537289).sum := by decide
  have hdescent : baseEnd_6537289 < baseStart_6537289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537292 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 2, 1, 7]
def baseStart_6537292 : Nat := 118140960795 + 6537292 * 2 ^ 59
def prefixEnd_6537292 : Nat := 4983230072969 + 3 ^ 40 * 6537292 * 2
def baseEnd_6537292 : Nat := 3356772974792142048685547

theorem tailTrace_6537292 : CollatzResearch.WordTrace tailWord_6537292 prefixEnd_6537292 3356772974792142048685547 := by
  unfold tailWord_6537292
  simp only [CollatzResearch.WordTrace]
  refine ⟨119217313716257519715575065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158956418288343359620766753 119217313716257519715575065)
  ·
    refine ⟨89412985287193139786681299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119217313716257519715575065 89412985287193139786681299)
    ·
      refine ⟨134119477930789709680021949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89412985287193139786681299 134119477930789709680021949)
      ·
        refine ⟨50294804224046141130008231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134119477930789709680021949 50294804224046141130008231)
        ·
          refine ⟨75442206336069211695012347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50294804224046141130008231 75442206336069211695012347)
          ·
            refine ⟨113163309504103817542518521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75442206336069211695012347 113163309504103817542518521)
            ·
              refine ⟨84872482128077863156888891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113163309504103817542518521 84872482128077863156888891)
              ·
                refine ⟨127308723192116794735333337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84872482128077863156888891 127308723192116794735333337)
                ·
                  refine ⟨95481542394087596051500003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127308723192116794735333337 95481542394087596051500003)
                  ·
                    refine ⟨143222313591131394077250005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95481542394087596051500003 143222313591131394077250005)
                    ·
                      refine ⟨3356772974792142048685547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143222313591131394077250005 3356772974792142048685547)
                      ·
                        rfl

theorem cell23_6537292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_6537292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537292 prefixEnd_6537292 := by exact prefixLift 6537292
  have htrace : WordTrace (prefixWord ++ tailWord_6537292) baseStart_6537292 baseEnd_6537292 := by
    simpa [prefixWord, tailWord_6537292, baseEnd_6537292] using wordTrace_append hprefix tailTrace_6537292
  have hstable : (prefixWord ++ tailWord_6537292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537292).length < 2 ^ (prefixWord ++ tailWord_6537292).sum := by decide
  have hdescent : baseEnd_6537292 < baseStart_6537292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537306 : List Nat := [3, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2]
def baseStart_6537306 : Nat := 118140960795 + 6537306 * 2 ^ 59
def prefixEnd_6537306 : Nat := 4983230072969 + 3 ^ 40 * 6537306 * 2
def baseEnd_6537306 : Nat := 3356780163521304993910483

theorem tailTrace_6537306 : CollatzResearch.WordTrace tailWord_6537306 prefixEnd_6537306 3356780163521304993910483 := by
  unfold tailWord_6537306
  simp only [CollatzResearch.WordTrace]
  refine ⟨59608784513616079955539943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158956758702976213214773181 59608784513616079955539943)
  ·
    refine ⟨89413176770424119933309915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59608784513616079955539943 89413176770424119933309915)
    ·
      refine ⟨134119765155636179899964873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89413176770424119933309915 134119765155636179899964873)
      ·
        refine ⟨100589823866727134924973655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134119765155636179899964873 100589823866727134924973655)
        ·
          refine ⟨150884735800090702387460483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100589823866727134924973655 150884735800090702387460483)
          ·
            refine ⟨226327103700136053581190725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150884735800090702387460483 226327103700136053581190725)
            ·
              refine ⟨42436331943775510046473261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226327103700136053581190725 42436331943775510046473261)
              ·
                refine ⟨15913624478915816267427473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42436331943775510046473261 15913624478915816267427473)
                ·
                  refine ⟨11935218359186862200570605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15913624478915816267427473 11935218359186862200570605)
                  ·
                    refine ⟨4475706884695073325213977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11935218359186862200570605 4475706884695073325213977)
                    ·
                      refine ⟨3356780163521304993910483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4475706884695073325213977 3356780163521304993910483)
                      ·
                        rfl

theorem cell23_6537306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_6537306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537306 prefixEnd_6537306 := by exact prefixLift 6537306
  have htrace : WordTrace (prefixWord ++ tailWord_6537306) baseStart_6537306 baseEnd_6537306 := by
    simpa [prefixWord, tailWord_6537306, baseEnd_6537306] using wordTrace_append hprefix tailTrace_6537306
  have hstable : (prefixWord ++ tailWord_6537306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537306).length < 2 ^ (prefixWord ++ tailWord_6537306).sum := by decide
  have hdescent : baseEnd_6537306 < baseStart_6537306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537329 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 4, 4]
def baseStart_6537329 : Nat := 118140960795 + 6537329 * 2 ^ 59
def prefixEnd_6537329 : Nat := 4983230072969 + 3 ^ 40 * 6537329 * 2
def baseEnd_6537329 : Nat := 1118930657858786134640959

theorem tailTrace_6537329 : CollatzResearch.WordTrace tailWord_6537329 prefixEnd_6537329 1118930657858786134640959 := by
  unfold tailWord_6537329
  simp only [CollatzResearch.WordTrace]
  refine ⟨238435976933380994750247041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158957317955587329833498027 238435976933380994750247041)
  ·
    refine ⟨178826982700035746062685281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238435976933380994750247041 178826982700035746062685281)
    ·
      refine ⟨134120237025026809547013961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178826982700035746062685281 134120237025026809547013961)
      ·
        refine ⟨100590177768770107160260471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134120237025026809547013961 100590177768770107160260471)
        ·
          refine ⟨150885266653155160740390707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100590177768770107160260471 150885266653155160740390707)
          ·
            refine ⟨226327899979732741110586061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150885266653155160740390707 226327899979732741110586061)
            ·
              refine ⟨84872962492399777916469773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226327899979732741110586061 84872962492399777916469773)
              ·
                refine ⟨31827360934649916718676165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84872962492399777916469773 31827360934649916718676165)
                ·
                  refine ⟨5967630175246859384751781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31827360934649916718676165 5967630175246859384751781)
                  ·
                    refine ⟨1118930657858786134640959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5967630175246859384751781 1118930657858786134640959)
                    ·
                      rfl

theorem cell23_6537329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 4].length) (baseStart_6537329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537329 prefixEnd_6537329 := by exact prefixLift 6537329
  have htrace : WordTrace (prefixWord ++ tailWord_6537329) baseStart_6537329 baseEnd_6537329 := by
    simpa [prefixWord, tailWord_6537329, baseEnd_6537329] using wordTrace_append hprefix tailTrace_6537329
  have hstable : (prefixWord ++ tailWord_6537329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537329).length < 2 ^ (prefixWord ++ tailWord_6537329).sum := by decide
  have hdescent : baseEnd_6537329 < baseStart_6537329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537349 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 1, 1, 6]
def baseStart_6537349 : Nat := 118140960795 + 6537349 * 2 ^ 59
def prefixEnd_6537349 : Nat := 4983230072969 + 3 ^ 40 * 6537349 * 2
def baseEnd_6537349 : Nat := 3356802243189448325672785

theorem tailTrace_6537349 : CollatzResearch.WordTrace tailWord_6537349 prefixEnd_6537349 3356802243189448325672785 := by
  unfold tailWord_6537349
  simp only [CollatzResearch.WordTrace]
  refine ⟨238436706393308538165975101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158957804262205692110650067 238436706393308538165975101)
  ·
    refine ⟨89413764897490701812240663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238436706393308538165975101 89413764897490701812240663)
    ·
      refine ⟨134120647346236052718360995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89413764897490701812240663 134120647346236052718360995)
      ·
        refine ⟨201180971019354079077541493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134120647346236052718360995 201180971019354079077541493)
        ·
          refine ⟨18860716033064444913519515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201180971019354079077541493 18860716033064444913519515)
          ·
            refine ⟨28291074049596667370279273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18860716033064444913519515 28291074049596667370279273)
            ·
              refine ⟨21218305537197500527709455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28291074049596667370279273 21218305537197500527709455)
              ·
                refine ⟨31827458305796250791564183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21218305537197500527709455 31827458305796250791564183)
                ·
                  refine ⟨47741187458694376187346275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31827458305796250791564183 47741187458694376187346275)
                  ·
                    refine ⟨71611781188041564281019413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47741187458694376187346275 71611781188041564281019413)
                    ·
                      refine ⟨3356802243189448325672785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71611781188041564281019413 3356802243189448325672785)
                      ·
                        rfl

theorem cell23_6537349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_6537349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537349 prefixEnd_6537349 := by exact prefixLift 6537349
  have htrace : WordTrace (prefixWord ++ tailWord_6537349) baseStart_6537349 baseEnd_6537349 := by
    simpa [prefixWord, tailWord_6537349, baseEnd_6537349] using wordTrace_append hprefix tailTrace_6537349
  have hstable : (prefixWord ++ tailWord_6537349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537349).length < 2 ^ (prefixWord ++ tailWord_6537349).sum := by decide
  have hdescent : baseEnd_6537349 < baseStart_6537349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537370 : List Nat := [3, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4]
def baseStart_6537370 : Nat := 118140960795 + 6537370 * 2 ^ 59
def prefixEnd_6537370 : Nat := 4983230072969 + 3 ^ 40 * 6537370 * 2
def baseEnd_6537370 : Nat := 3356813026283192743510189

theorem tailTrace_6537370 : CollatzResearch.WordTrace tailWord_6537370 prefixEnd_6537370 3356813026283192743510189 := by
  unfold tailWord_6537370
  simp only [CollatzResearch.WordTrace]
  refine ⟨59609368081558114688122391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158958314884154972501659709 59609368081558114688122391)
  ·
    refine ⟨89414052122337172032183587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59609368081558114688122391 89414052122337172032183587)
    ·
      refine ⟨134121078183505758048275381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89414052122337172032183587 134121078183505758048275381)
      ·
        refine ⟨12573851079703664817025817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134121078183505758048275381 12573851079703664817025817)
        ·
          refine ⟨9430388309777748612769363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12573851079703664817025817 9430388309777748612769363)
          ·
            refine ⟨14145582464666622919154045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9430388309777748612769363 14145582464666622919154045)
            ·
              refine ⟨5304593424249983594682767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14145582464666622919154045 5304593424249983594682767)
              ·
                refine ⟨7956890136374975392024151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5304593424249983594682767 7956890136374975392024151)
                ·
                  refine ⟨11935335204562463088036227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7956890136374975392024151 11935335204562463088036227)
                  ·
                    refine ⟨17903002806843694632054341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11935335204562463088036227 17903002806843694632054341)
                    ·
                      refine ⟨3356813026283192743510189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17903002806843694632054341 3356813026283192743510189)
                      ·
                        rfl

theorem cell23_6537370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_6537370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537370 prefixEnd_6537370 := by exact prefixLift 6537370
  have htrace : WordTrace (prefixWord ++ tailWord_6537370) baseStart_6537370 baseEnd_6537370 := by
    simpa [prefixWord, tailWord_6537370, baseEnd_6537370] using wordTrace_append hprefix tailTrace_6537370
  have hstable : (prefixWord ++ tailWord_6537370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537370).length < 2 ^ (prefixWord ++ tailWord_6537370).sum := by decide
  have hdescent : baseEnd_6537370 < baseStart_6537370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537393 : List Nat := [1, 2, 2, 5, 3, 1, 1, 8]
def baseStart_6537393 : Nat := 118140960795 + 6537393 * 2 ^ 59
def prefixEnd_6537393 : Nat := 4983230072969 + 3 ^ 40 * 6537393 * 2
def baseEnd_6537393 : Nat := 124326845790305413093429

theorem tailTrace_6537393 : CollatzResearch.WordTrace tailWord_6537393 prefixEnd_6537393 124326845790305413093429 := by
  unfold tailWord_6537393
  simp only [CollatzResearch.WordTrace]
  refine ⟨238438311205149133680576833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158958874136766089120384555 238438311205149133680576833)
  ·
    refine ⟨178828733403861850260432625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238438311205149133680576833 178828733403861850260432625)
    ·
      refine ⟨134121550052896387695324469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178828733403861850260432625 134121550052896387695324469)
      ·
        refine ⟨12573895317459036346436669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134121550052896387695324469 12573895317459036346436669)
        ·
          refine ⟨4715210744047138629913751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12573895317459036346436669 4715210744047138629913751)
          ·
            refine ⟨7072816116070707944870627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4715210744047138629913751 7072816116070707944870627)
            ·
              refine ⟨10609224174106061917305941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7072816116070707944870627 10609224174106061917305941)
              ·
                refine ⟨124326845790305413093429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10609224174106061917305941 124326845790305413093429)
                ·
                  rfl

theorem cell23_6537393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 8].length) (baseStart_6537393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537393 prefixEnd_6537393 := by exact prefixLift 6537393
  have htrace : WordTrace (prefixWord ++ tailWord_6537393) baseStart_6537393 baseEnd_6537393 := by
    simpa [prefixWord, tailWord_6537393, baseEnd_6537393] using wordTrace_append hprefix tailTrace_6537393
  have hstable : (prefixWord ++ tailWord_6537393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537393).length < 2 ^ (prefixWord ++ tailWord_6537393).sum := by decide
  have hdescent : baseEnd_6537393 < baseStart_6537393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537410 : List Nat := [3, 5, 1, 1, 1, 2, 3, 7]
def baseStart_6537410 : Nat := 118140960795 + 6537410 * 2 ^ 59
def prefixEnd_6537410 : Nat := 4983230072969 + 3 ^ 40 * 6537410 * 2
def baseEnd_6537410 : Nat := 124327169092939725444815

theorem tailTrace_6537410 : CollatzResearch.WordTrace tailWord_6537410 prefixEnd_6537410 124327169092939725444815 := by
  unfold tailWord_6537410
  simp only [CollatzResearch.WordTrace]
  refine ⟨59609732811521886395986421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158959287497391697055963789 59609732811521886395986421)
  ·
    refine ⟨5588412451080176849623727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59609732811521886395986421 5588412451080176849623727)
    ·
      refine ⟨8382618676620265274435591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5588412451080176849623727 8382618676620265274435591)
      ·
        refine ⟨12573928014930397911653387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8382618676620265274435591 12573928014930397911653387)
        ·
          refine ⟨18860892022395596867480081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12573928014930397911653387 18860892022395596867480081)
          ·
            refine ⟨14145669016796697650610061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18860892022395596867480081 14145669016796697650610061)
            ·
              refine ⟨5304625881298761618978773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14145669016796697650610061 5304625881298761618978773)
              ·
                refine ⟨124327169092939725444815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5304625881298761618978773 124327169092939725444815)
                ·
                  rfl

theorem cell23_6537410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 7].length) (baseStart_6537410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537410 prefixEnd_6537410 := by exact prefixLift 6537410
  have htrace : WordTrace (prefixWord ++ tailWord_6537410) baseStart_6537410 baseEnd_6537410 := by
    simpa [prefixWord, tailWord_6537410, baseEnd_6537410] using wordTrace_append hprefix tailTrace_6537410
  have hstable : (prefixWord ++ tailWord_6537410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537410).length < 2 ^ (prefixWord ++ tailWord_6537410).sum := by decide
  have hdescent : baseEnd_6537410 < baseStart_6537410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537437 : List Nat := [1, 4, 3, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_6537437 : Nat := 118140960795 + 6537437 * 2 ^ 59
def prefixEnd_6537437 : Nat := 4983230072969 + 3 ^ 40 * 6537437 * 2
def baseEnd_6537437 : Nat := 3356847429487043981372381

theorem tailTrace_6537437 : CollatzResearch.WordTrace tailWord_6537437 prefixEnd_6537437 3356847429487043981372381 := by
  unfold tailWord_6537437
  simp only [CollatzResearch.WordTrace]
  refine ⟨238439916016989729195178565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158959944011326486130119043 238439916016989729195178565)
  ·
    refine ⟨44707484253185574224095981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238439916016989729195178565 44707484253185574224095981)
    ·
      refine ⟨16765306594944590334035993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44707484253185574224095981 16765306594944590334035993)
      ·
        refine ⟨12573979946208442750526995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16765306594944590334035993 12573979946208442750526995)
        ·
          refine ⟨18860969919312664125790493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12573979946208442750526995 18860969919312664125790493)
          ·
            refine ⟨7072863719742249047171435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18860969919312664125790493 7072863719742249047171435)
            ·
              refine ⟨10609295579613373570757153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7072863719742249047171435 10609295579613373570757153)
              ·
                refine ⟨7956971684710030178067865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10609295579613373570757153 7956971684710030178067865)
                ·
                  refine ⟨5967728763532522633550899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7956971684710030178067865 5967728763532522633550899)
                  ·
                    refine ⟨8951593145298783950326349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5967728763532522633550899 8951593145298783950326349)
                    ·
                      refine ⟨3356847429487043981372381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8951593145298783950326349 3356847429487043981372381)
                      ·
                        rfl

theorem cell23_6537437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_6537437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537437 prefixEnd_6537437 := by exact prefixLift 6537437
  have htrace : WordTrace (prefixWord ++ tailWord_6537437) baseStart_6537437 baseEnd_6537437 := by
    simpa [prefixWord, tailWord_6537437, baseEnd_6537437] using wordTrace_append hprefix tailTrace_6537437
  have hstable : (prefixWord ++ tailWord_6537437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537437).length < 2 ^ (prefixWord ++ tailWord_6537437).sum := by decide
  have hdescent : baseEnd_6537437 < baseStart_6537437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537496 : List Nat := [2, 1, 2, 3, 1, 2, 3, 2, 2, 5]
def baseStart_6537496 : Nat := 118140960795 + 6537496 * 2 ^ 59
def prefixEnd_6537496 : Nat := 4983230072969 + 3 ^ 40 * 6537496 * 2
def baseEnd_6537496 : Nat := 1118959241615219750178203

theorem tailTrace_6537496 : CollatzResearch.WordTrace tailWord_6537496 prefixEnd_6537496 1118959241615219750178203 := by
  unfold tailWord_6537496
  simp only [CollatzResearch.WordTrace]
  refine ⟨119221033961887991135788171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158961378615850654847717561 119221033961887991135788171)
  ·
    refine ⟨178831550942831986703682257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119221033961887991135788171 178831550942831986703682257)
    ·
      refine ⟨134123663207123990027761693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178831550942831986703682257 134123663207123990027761693)
      ·
        refine ⟨50296373702671496260410635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134123663207123990027761693 50296373702671496260410635)
        ·
          refine ⟨75444560554007244390615953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50296373702671496260410635 75444560554007244390615953)
          ·
            refine ⟨56583420415505433292961965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75444560554007244390615953 56583420415505433292961965)
            ·
              refine ⟨21218782655814537484860737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56583420415505433292961965 21218782655814537484860737)
              ·
                refine ⟨15914086991860903113645553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21218782655814537484860737 15914086991860903113645553)
                ·
                  refine ⟨11935565243895677335234165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15914086991860903113645553 11935565243895677335234165)
                  ·
                    refine ⟨1118959241615219750178203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11935565243895677335234165 1118959241615219750178203)
                    ·
                      rfl

theorem cell23_6537496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_6537496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537496 prefixEnd_6537496 := by exact prefixLift 6537496
  have htrace : WordTrace (prefixWord ++ tailWord_6537496) baseStart_6537496 baseEnd_6537496 := by
    simpa [prefixWord, tailWord_6537496, baseEnd_6537496] using wordTrace_append hprefix tailTrace_6537496
  have hstable : (prefixWord ++ tailWord_6537496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537496).length < 2 ^ (prefixWord ++ tailWord_6537496).sum := by decide
  have hdescent : baseEnd_6537496 < baseStart_6537496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537506 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_6537506 : Nat := 118140960795 + 6537506 * 2 ^ 59
def prefixEnd_6537506 : Nat := 4983230072969 + 3 ^ 40 * 6537506 * 2
def baseEnd_6537506 : Nat := 3356882859652204211409563

theorem tailTrace_6537506 : CollatzResearch.WordTrace tailWord_6537506 prefixEnd_6537506 3356882859652204211409563 := by
  unfold tailWord_6537506
  simp only [CollatzResearch.WordTrace]
  refine ⟨59610608163434938494860093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158961621769159835986293581 59610608163434938494860093)
  ·
    refine ⟨22353978061288101935572535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59610608163434938494860093 22353978061288101935572535)
    ·
      refine ⟨33530967091932152903358803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22353978061288101935572535 33530967091932152903358803)
      ·
        refine ⟨50296450637898229355038205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33530967091932152903358803 50296450637898229355038205)
        ·
          refine ⟨18861168989211836008139327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50296450637898229355038205 18861168989211836008139327)
          ·
            refine ⟨28291753483817754012208991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18861168989211836008139327 28291753483817754012208991)
            ·
              refine ⟨42437630225726631018313487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28291753483817754012208991 42437630225726631018313487)
              ·
                refine ⟨63656445338589946527470231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42437630225726631018313487 63656445338589946527470231)
                ·
                  refine ⟨95484668007884919791205347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63656445338589946527470231 95484668007884919791205347)
                  ·
                    refine ⟨143227002011827379686808021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95484668007884919791205347 143227002011827379686808021)
                    ·
                      refine ⟨3356882859652204211409563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143227002011827379686808021 3356882859652204211409563)
                      ·
                        rfl

theorem cell23_6537506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_6537506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537506 prefixEnd_6537506 := by exact prefixLift 6537506
  have htrace : WordTrace (prefixWord ++ tailWord_6537506) baseStart_6537506 baseEnd_6537506 := by
    simpa [prefixWord, tailWord_6537506, baseEnd_6537506] using wordTrace_append hprefix tailTrace_6537506
  have hstable : (prefixWord ++ tailWord_6537506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537506).length < 2 ^ (prefixWord ++ tailWord_6537506).sum := by decide
  have hdescent : baseEnd_6537506 < baseStart_6537506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537511 : List Nat := [1, 1, 8, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_6537511 : Nat := 118140960795 + 6537511 * 2 ^ 59
def prefixEnd_6537511 : Nat := 4983230072969 + 3 ^ 40 * 6537511 * 2
def baseEnd_6537511 : Nat := 3356885427055476691847041

theorem tailTrace_6537511 : CollatzResearch.WordTrace tailWord_6537511 prefixEnd_6537511 3356885427055476691847041 := by
  unfold tailWord_6537511
  simp only [CollatzResearch.WordTrace]
  refine ⟨238442615018721639833372387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158961743345814426555581591 238442615018721639833372387)
  ·
    refine ⟨357663922528082459750058581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238442615018721639833372387 357663922528082459750058581)
    ·
      refine ⟨4191374092125966325195999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 357663922528082459750058581 4191374092125966325195999)
      ·
        refine ⟨6287061138188949487793999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4191374092125966325195999 6287061138188949487793999)
        ·
          refine ⟨9430591707283424231690999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6287061138188949487793999 9430591707283424231690999)
          ·
            refine ⟨14145887560925136347536499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9430591707283424231690999 14145887560925136347536499)
            ·
              refine ⟨21218831341387704521304749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14145887560925136347536499 21218831341387704521304749)
              ·
                refine ⟨7957061753020389195489281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21218831341387704521304749 7957061753020389195489281)
                ·
                  refine ⟨5967796314765291896616961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7957061753020389195489281 5967796314765291896616961)
                  ·
                    refine ⟨4475847236073968922462721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5967796314765291896616961 4475847236073968922462721)
                    ·
                      refine ⟨3356885427055476691847041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4475847236073968922462721 3356885427055476691847041)
                      ·
                        rfl

theorem cell23_6537511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_6537511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537511 prefixEnd_6537511 := by exact prefixLift 6537511
  have htrace : WordTrace (prefixWord ++ tailWord_6537511) baseStart_6537511 baseEnd_6537511 := by
    simpa [prefixWord, tailWord_6537511, baseEnd_6537511] using wordTrace_append hprefix tailTrace_6537511
  have hstable : (prefixWord ++ tailWord_6537511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537511).length < 2 ^ (prefixWord ++ tailWord_6537511).sum := by decide
  have hdescent : baseEnd_6537511 < baseStart_6537511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537539 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 10]
def baseStart_6537539 : Nat := 118140960795 + 6537539 * 2 ^ 59
def prefixEnd_6537539 : Nat := 4983230072969 + 3 ^ 40 * 6537539 * 2
def baseEnd_6537539 : Nat := 372988867168200286921879

theorem tailTrace_6537539 : CollatzResearch.WordTrace tailWord_6537539 prefixEnd_6537539 372988867168200286921879 := by
  unfold tailWord_6537539
  simp only [CollatzResearch.WordTrace]
  refine ⟨238443636262620200615391671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158962424175080133743594447 238443636262620200615391671)
  ·
    refine ⟨357665454393930300923087507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238443636262620200615391671 357665454393930300923087507)
    ·
      refine ⟨536498181590895451384631261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357665454393930300923087507 536498181590895451384631261)
      ·
        refine ⟨201186818096585794269236723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 536498181590895451384631261 201186818096585794269236723)
        ·
          refine ⟨301780227144878691403855085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201186818096585794269236723 301780227144878691403855085)
          ·
            refine ⟨113167585179329509276445657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301780227144878691403855085 113167585179329509276445657)
            ·
              refine ⟨84875688884497131957334243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113167585179329509276445657 84875688884497131957334243)
              ·
                refine ⟨127313533326745697936001365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84875688884497131957334243 127313533326745697936001365)
                ·
                  refine ⟨372988867168200286921879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 127313533326745697936001365 372988867168200286921879)
                  ·
                    rfl

theorem cell23_6537539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 10].length) (baseStart_6537539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537539 prefixEnd_6537539 := by exact prefixLift 6537539
  have htrace : WordTrace (prefixWord ++ tailWord_6537539) baseStart_6537539 baseEnd_6537539 := by
    simpa [prefixWord, tailWord_6537539, baseEnd_6537539] using wordTrace_append hprefix tailTrace_6537539
  have hstable : (prefixWord ++ tailWord_6537539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537539).length < 2 ^ (prefixWord ++ tailWord_6537539).sum := by decide
  have hdescent : baseEnd_6537539 < baseStart_6537539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537553 : List Nat := [1, 2, 2, 1, 4, 2, 2, 2, 2, 2, 3]
def baseStart_6537553 : Nat := 118140960795 + 6537553 * 2 ^ 59
def prefixEnd_6537553 : Nat := 4983230072969 + 3 ^ 40 * 6537553 * 2
def baseEnd_6537553 : Nat := 3356906993242965527521847

theorem tailTrace_6537553 : CollatzResearch.WordTrace tailWord_6537553 prefixEnd_6537553 3356906993242965527521847 := by
  unfold tailWord_6537553
  simp only [CollatzResearch.WordTrace]
  refine ⟨238444146884569481006401313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158962764589712987337600875 238444146884569481006401313)
  ·
    refine ⟨178833110163427110754800985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238444146884569481006401313 178833110163427110754800985)
    ·
      refine ⟨134124832622570333066100739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178833110163427110754800985 134124832622570333066100739)
      ·
        refine ⟨201187248933855499599151109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134124832622570333066100739 201187248933855499599151109)
        ·
          refine ⟨37722609175097906174840833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201187248933855499599151109 37722609175097906174840833)
          ·
            refine ⟨28291956881323429631130625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37722609175097906174840833 28291956881323429631130625)
            ·
              refine ⟨21218967660992572223347969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28291956881323429631130625 21218967660992572223347969)
              ·
                refine ⟨15914225745744429167510977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21218967660992572223347969 15914225745744429167510977)
                ·
                  refine ⟨11935669309308321875633233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15914225745744429167510977 11935669309308321875633233)
                  ·
                    refine ⟨8951751981981241406724925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11935669309308321875633233 8951751981981241406724925)
                    ·
                      refine ⟨3356906993242965527521847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8951751981981241406724925 3356906993242965527521847)
                      ·
                        rfl

theorem cell23_6537553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 2, 3].length) (baseStart_6537553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537553 prefixEnd_6537553 := by exact prefixLift 6537553
  have htrace : WordTrace (prefixWord ++ tailWord_6537553) baseStart_6537553 baseEnd_6537553 := by
    simpa [prefixWord, tailWord_6537553, baseEnd_6537553] using wordTrace_append hprefix tailTrace_6537553
  have hstable : (prefixWord ++ tailWord_6537553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537553).length < 2 ^ (prefixWord ++ tailWord_6537553).sum := by decide
  have hdescent : baseEnd_6537553 < baseStart_6537553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537660 : List Nat := [2, 2, 2, 4, 1, 2, 2, 1, 1, 1, 5]
def baseStart_6537660 : Nat := 118140960795 + 6537660 * 2 ^ 59
def prefixEnd_6537660 : Nat := 4983230072969 + 3 ^ 40 * 6537660 * 2
def baseEnd_6537660 : Nat := 3356961935672996608883855

theorem tailTrace_6537660 : CollatzResearch.WordTrace tailWord_6537660 prefixEnd_6537660 3356961935672996608883855 := by
  unfold tailWord_6537660
  simp only [CollatzResearch.WordTrace]
  refine ⟨119224024747590919140273217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158965366330121225520364289 119224024747590919140273217)
  ·
    refine ⟨89418018560693189355204913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119224024747590919140273217 89418018560693189355204913)
    ·
      refine ⟨67063513920519892016403685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89418018560693189355204913 67063513920519892016403685)
      ·
        refine ⟨12574408860097479753075691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67063513920519892016403685 12574408860097479753075691)
        ·
          refine ⟨18861613290146219629613537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12574408860097479753075691 18861613290146219629613537)
          ·
            refine ⟨14146209967609664722210153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18861613290146219629613537 14146209967609664722210153)
            ·
              refine ⟨10609657475707248541657615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14146209967609664722210153 10609657475707248541657615)
              ·
                refine ⟨15914486213560872812486423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10609657475707248541657615 15914486213560872812486423)
                ·
                  refine ⟨23871729320341309218729635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15914486213560872812486423 23871729320341309218729635)
                  ·
                    refine ⟨35807593980511963828094453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23871729320341309218729635 35807593980511963828094453)
                    ·
                      refine ⟨3356961935672996608883855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35807593980511963828094453 3356961935672996608883855)
                      ·
                        rfl

theorem cell23_6537660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_6537660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537660 prefixEnd_6537660 := by exact prefixLift 6537660
  have htrace : WordTrace (prefixWord ++ tailWord_6537660) baseStart_6537660 baseEnd_6537660 := by
    simpa [prefixWord, tailWord_6537660, baseEnd_6537660] using wordTrace_append hprefix tailTrace_6537660
  have hstable : (prefixWord ++ tailWord_6537660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537660).length < 2 ^ (prefixWord ++ tailWord_6537660).sum := by decide
  have hdescent : baseEnd_6537660 < baseStart_6537660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537684 : List Nat := [2, 4, 1, 2, 2, 3, 2, 1, 2, 4]
def baseStart_6537684 : Nat := 118140960795 + 6537684 * 2 ^ 59
def prefixEnd_6537684 : Nat := 4983230072969 + 3 ^ 40 * 6537684 * 2
def baseEnd_6537684 : Nat := 1118991419736234838327915

theorem tailTrace_6537684 : CollatzResearch.WordTrace tailWord_6537684 prefixEnd_6537684 1118991419736234838327915 := by
  unfold tailWord_6537684
  simp only [CollatzResearch.WordTrace]
  refine ⟨119224462423547445189710053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158965949898063260252946737 119224462423547445189710053)
  ·
    refine ⟨22354586704415145973070635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119224462423547445189710053 22354586704415145973070635)
    ·
      refine ⟨33531880056622718959605953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22354586704415145973070635 33531880056622718959605953)
      ·
        refine ⟨25148910042467039219704465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33531880056622718959605953 25148910042467039219704465)
        ·
          refine ⟨18861682531850279414778349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25148910042467039219704465 18861682531850279414778349)
          ·
            refine ⟨7073130949443854780541881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18861682531850279414778349 7073130949443854780541881)
            ·
              refine ⟨5304848212082891085406411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7073130949443854780541881 5304848212082891085406411)
              ·
                refine ⟨7957272318124336628109617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5304848212082891085406411 7957272318124336628109617)
                ·
                  refine ⟨5967954238593252471082213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7957272318124336628109617 5967954238593252471082213)
                  ·
                    refine ⟨1118991419736234838327915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5967954238593252471082213 1118991419736234838327915)
                    ·
                      rfl

theorem cell23_6537684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_6537684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537684 prefixEnd_6537684 := by exact prefixLift 6537684
  have htrace : WordTrace (prefixWord ++ tailWord_6537684) baseStart_6537684 baseEnd_6537684 := by
    simpa [prefixWord, tailWord_6537684, baseEnd_6537684] using wordTrace_append hprefix tailTrace_6537684
  have hstable : (prefixWord ++ tailWord_6537684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537684).length < 2 ^ (prefixWord ++ tailWord_6537684).sum := by decide
  have hdescent : baseEnd_6537684 < baseStart_6537684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537733 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 2, 4, 3]
def baseStart_6537733 : Nat := 118140960795 + 6537733 * 2 ^ 59
def prefixEnd_6537733 : Nat := 4983230072969 + 3 ^ 40 * 6537733 * 2
def baseEnd_6537733 : Nat := 3356999419760774823271019

theorem tailTrace_6537733 : CollatzResearch.WordTrace tailWord_6537733 prefixEnd_6537733 3356999419760774823271019 := by
  unfold tailWord_6537733
  simp only [CollatzResearch.WordTrace]
  refine ⟨238450712023917371747953853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158967141349278247831969235 238450712023917371747953853)
  ·
    refine ⟨89419017008969014405482695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238450712023917371747953853 89419017008969014405482695)
    ·
      refine ⟨134128525513453521608224043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89419017008969014405482695 134128525513453521608224043)
      ·
        refine ⟨201192788270180282412336065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134128525513453521608224043 201192788270180282412336065)
        ·
          refine ⟨150894591202635211809252049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201192788270180282412336065 150894591202635211809252049)
          ·
            refine ⟨113170943401976408856939037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150894591202635211809252049 113170943401976408856939037)
            ·
              refine ⟨42439103775741153321352139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113170943401976408856939037 42439103775741153321352139)
              ·
                refine ⟨63658655663611729982028209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42439103775741153321352139 63658655663611729982028209)
                ·
                  refine ⟨47743991747708797486521157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63658655663611729982028209 47743991747708797486521157)
                  ·
                    refine ⟨8951998452695399528722717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47743991747708797486521157 8951998452695399528722717)
                    ·
                      refine ⟨3356999419760774823271019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8951998452695399528722717 3356999419760774823271019)
                      ·
                        rfl

theorem cell23_6537733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 4, 3].length) (baseStart_6537733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537733 prefixEnd_6537733 := by exact prefixLift 6537733
  have htrace : WordTrace (prefixWord ++ tailWord_6537733) baseStart_6537733 baseEnd_6537733 := by
    simpa [prefixWord, tailWord_6537733, baseEnd_6537733] using wordTrace_append hprefix tailTrace_6537733
  have hstable : (prefixWord ++ tailWord_6537733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537733).length < 2 ^ (prefixWord ++ tailWord_6537733).sum := by decide
  have hdescent : baseEnd_6537733 < baseStart_6537733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537741 : List Nat := [1, 7, 1, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_6537741 : Nat := 118140960795 + 6537741 * 2 ^ 59
def prefixEnd_6537741 : Nat := 4983230072969 + 3 ^ 40 * 6537741 * 2
def baseEnd_6537741 : Nat := 3357003527606010791970983

theorem tailTrace_6537741 : CollatzResearch.WordTrace tailWord_6537741 prefixEnd_6537741 3357003527606010791970983 := by
  unfold tailWord_6537741
  simp only [CollatzResearch.WordTrace]
  refine ⟨238451003807888389114245077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158967335871925592742830051 238451003807888389114245077)
  ·
    refine ⟨5588695401747384119865119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 238451003807888389114245077 5588695401747384119865119)
    ·
      refine ⟨8383043102621076179797679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5588695401747384119865119 8383043102621076179797679)
      ·
        refine ⟨12574564653931614269696519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8383043102621076179797679 12574564653931614269696519)
        ·
          refine ⟨18861846980897421404544779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12574564653931614269696519 18861846980897421404544779)
          ·
            refine ⟨28292770471346132106817169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18861846980897421404544779 28292770471346132106817169)
            ·
              refine ⟨21219577853509599080112877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28292770471346132106817169 21219577853509599080112877)
              ·
                refine ⟨7957341695066099655042329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21219577853509599080112877 7957341695066099655042329)
                ·
                  refine ⟨5968006271299574741281747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7957341695066099655042329 5968006271299574741281747)
                  ·
                    refine ⟨8952009406949362111922621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5968006271299574741281747 8952009406949362111922621)
                    ·
                      refine ⟨3357003527606010791970983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8952009406949362111922621 3357003527606010791970983)
                      ·
                        rfl

theorem cell23_6537741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_6537741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537741 prefixEnd_6537741 := by exact prefixLift 6537741
  have htrace : WordTrace (prefixWord ++ tailWord_6537741) baseStart_6537741 baseEnd_6537741 := by
    simpa [prefixWord, tailWord_6537741, baseEnd_6537741] using wordTrace_append hprefix tailTrace_6537741
  have hstable : (prefixWord ++ tailWord_6537741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537741).length < 2 ^ (prefixWord ++ tailWord_6537741).sum := by decide
  have hdescent : baseEnd_6537741 < baseStart_6537741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537747 : List Nat := [1, 1, 1, 2, 1, 5, 1, 5, 2, 2, 2]
def baseStart_6537747 : Nat := 118140960795 + 6537747 * 2 ^ 59
def prefixEnd_6537747 : Nat := 4983230072969 + 3 ^ 40 * 6537747 * 2
def baseEnd_6537747 : Nat := 3357006608489937768495955

theorem tailTrace_6537747 : CollatzResearch.WordTrace tailWord_6537747 prefixEnd_6537747 3357006608489937768495955 := by
  unfold tailWord_6537747
  simp only [CollatzResearch.WordTrace]
  refine ⟨238451222645866652138963495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158967481763911101425975663 238451222645866652138963495)
  ·
    refine ⟨357676833968799978208445243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238451222645866652138963495 357676833968799978208445243)
    ·
      refine ⟨536515250953199967312667865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357676833968799978208445243 536515250953199967312667865)
      ·
        refine ⟨402386438214899975484500899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536515250953199967312667865 402386438214899975484500899)
        ·
          refine ⟨603579657322349963226751349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402386438214899975484500899 603579657322349963226751349)
          ·
            refine ⟨56585592873970309052507939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 603579657322349963226751349 56585592873970309052507939)
            ·
              refine ⟨84878389310955463578761909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56585592873970309052507939 84878389310955463578761909)
              ·
                refine ⟨7957348997902074710508929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84878389310955463578761909 7957348997902074710508929)
                ·
                  refine ⟨5968011748426556032881697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7957348997902074710508929 5968011748426556032881697)
                  ·
                    refine ⟨4476008811319917024661273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5968011748426556032881697 4476008811319917024661273)
                    ·
                      refine ⟨3357006608489937768495955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4476008811319917024661273 3357006608489937768495955)
                      ·
                        rfl

theorem cell23_6537747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 2, 2].length) (baseStart_6537747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537747 prefixEnd_6537747 := by exact prefixLift 6537747
  have htrace : WordTrace (prefixWord ++ tailWord_6537747) baseStart_6537747 baseEnd_6537747 := by
    simpa [prefixWord, tailWord_6537747, baseEnd_6537747] using wordTrace_append hprefix tailTrace_6537747
  have hstable : (prefixWord ++ tailWord_6537747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537747).length < 2 ^ (prefixWord ++ tailWord_6537747).sum := by decide
  have hdescent : baseEnd_6537747 < baseStart_6537747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537783 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 4, 5]
def baseStart_6537783 : Nat := 118140960795 + 6537783 * 2 ^ 59
def prefixEnd_6537783 : Nat := 4983230072969 + 3 ^ 40 * 6537783 * 2
def baseEnd_6537783 : Nat := 1119008364597833209215263

theorem tailTrace_6537783 : CollatzResearch.WordTrace tailWord_6537783 prefixEnd_6537783 1119008364597833209215263 := by
  unfold tailWord_6537783
  simp only [CollatzResearch.WordTrace]
  refine ⟨238452535673736230287274003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158968357115824153524849335 238452535673736230287274003)
  ·
    refine ⟨357678803510604345430911005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238452535673736230287274003 357678803510604345430911005)
    ·
      refine ⟨134129551316476629536591627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357678803510604345430911005 134129551316476629536591627)
      ·
        refine ⟨201194326974714944304887441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134129551316476629536591627 201194326974714944304887441)
        ·
          refine ⟨150895745231036208228665581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201194326974714944304887441 150895745231036208228665581)
          ·
            refine ⟨56585904461638578085749593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150895745231036208228665581 56585904461638578085749593)
            ·
              refine ⟨42439428346228933564312195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56585904461638578085749593 42439428346228933564312195)
              ·
                refine ⟨63659142519343400346468293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42439428346228933564312195 63659142519343400346468293)
                ·
                  refine ⟨11936089222376887564962805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63659142519343400346468293 11936089222376887564962805)
                  ·
                    refine ⟨1119008364597833209215263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11936089222376887564962805 1119008364597833209215263)
                    ·
                      rfl

theorem cell23_6537783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_6537783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537783 prefixEnd_6537783 := by exact prefixLift 6537783
  have htrace : WordTrace (prefixWord ++ tailWord_6537783) baseStart_6537783 baseEnd_6537783 := by
    simpa [prefixWord, tailWord_6537783, baseEnd_6537783] using wordTrace_append hprefix tailTrace_6537783
  have hstable : (prefixWord ++ tailWord_6537783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537783).length < 2 ^ (prefixWord ++ tailWord_6537783).sum := by decide
  have hdescent : baseEnd_6537783 < baseStart_6537783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537803 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 4]
def baseStart_6537803 : Nat := 118140960795 + 6537803 * 2 ^ 59
def prefixEnd_6537803 : Nat := 4983230072969 + 3 ^ 40 * 6537803 * 2
def baseEnd_6537803 : Nat := 3357035363406589549395697

theorem tailTrace_6537803 : CollatzResearch.WordTrace tailWord_6537803 prefixEnd_6537803 3357035363406589549395697 := by
  unfold tailWord_6537803
  simp only [CollatzResearch.WordTrace]
  refine ⟨238453265133663773703002063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158968843422442515802001375 238453265133663773703002063)
  ·
    refine ⟨357679897700495660554503095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238453265133663773703002063 357679897700495660554503095)
    ·
      refine ⟨536519846550743490831754643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357679897700495660554503095 536519846550743490831754643)
      ·
        refine ⟨804779769826115236247631965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536519846550743490831754643 804779769826115236247631965)
        ·
          refine ⟨301792413684793213592861987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 804779769826115236247631965 301792413684793213592861987)
          ·
            refine ⟨452688620527189820389292981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301792413684793213592861987 452688620527189820389292981)
            ·
              refine ⟨42439558174424045661496217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 452688620527189820389292981 42439558174424045661496217)
              ·
                refine ⟨31829668630818034246122163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42439558174424045661496217 31829668630818034246122163)
                ·
                  refine ⟨47744502946227051369183245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31829668630818034246122163 47744502946227051369183245)
                  ·
                    refine ⟨17904188604835144263443717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47744502946227051369183245 17904188604835144263443717)
                    ·
                      refine ⟨3357035363406589549395697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17904188604835144263443717 3357035363406589549395697)
                      ·
                        rfl

theorem cell23_6537803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 4].length) (baseStart_6537803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537803 prefixEnd_6537803 := by exact prefixLift 6537803
  have htrace : WordTrace (prefixWord ++ tailWord_6537803) baseStart_6537803 baseEnd_6537803 := by
    simpa [prefixWord, tailWord_6537803, baseEnd_6537803] using wordTrace_append hprefix tailTrace_6537803
  have hstable : (prefixWord ++ tailWord_6537803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537803).length < 2 ^ (prefixWord ++ tailWord_6537803).sum := by decide
  have hdescent : baseEnd_6537803 < baseStart_6537803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537837 : List Nat := [1, 5, 1, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_6537837 : Nat := 118140960795 + 6537837 * 2 ^ 59
def prefixEnd_6537837 : Nat := 4983230072969 + 3 ^ 40 * 6537837 * 2
def baseEnd_6537837 : Nat := 3357052821748842416370541

theorem tailTrace_6537837 : CollatzResearch.WordTrace tailWord_6537837 prefixEnd_6537837 3357052821748842416370541 := by
  unfold tailWord_6537837
  simp only [CollatzResearch.WordTrace]
  refine ⟨238454505215540597509739765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158969670143693731673159843 238454505215540597509739765)
  ·
    refine ⟨22355109863956931016538103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 238454505215540597509739765 22355109863956931016538103)
    ·
      refine ⟨33532664795935396524807155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22355109863956931016538103 33532664795935396524807155)
      ·
        refine ⟨50298997193903094787210733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33532664795935396524807155 50298997193903094787210733)
        ·
          refine ⟨18862123947713660545204025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50298997193903094787210733 18862123947713660545204025)
          ·
            refine ⟨14146592960785245408903019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18862123947713660545204025 14146592960785245408903019)
            ·
              refine ⟨21219889441177868113354529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14146592960785245408903019 21219889441177868113354529)
              ·
                refine ⟨15914917080883401085015897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21219889441177868113354529 15914917080883401085015897)
                ·
                  refine ⟨11936187810662550813761923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15914917080883401085015897 11936187810662550813761923)
                  ·
                    refine ⟨17904281715993826220642885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11936187810662550813761923 17904281715993826220642885)
                    ·
                      refine ⟨3357052821748842416370541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17904281715993826220642885 3357052821748842416370541)
                      ·
                        rfl

theorem cell23_6537837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_6537837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537837 prefixEnd_6537837 := by exact prefixLift 6537837
  have htrace : WordTrace (prefixWord ++ tailWord_6537837) baseStart_6537837 baseEnd_6537837 := by
    simpa [prefixWord, tailWord_6537837, baseEnd_6537837] using wordTrace_append hprefix tailTrace_6537837
  have hstable : (prefixWord ++ tailWord_6537837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537837).length < 2 ^ (prefixWord ++ tailWord_6537837).sum := by decide
  have hdescent : baseEnd_6537837 < baseStart_6537837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537847 : List Nat := [1, 1, 3, 1, 1, 3, 2, 6, 1, 4]
def baseStart_6537847 : Nat := 118140960795 + 6537847 * 2 ^ 59
def prefixEnd_6537847 : Nat := 4983230072969 + 3 ^ 40 * 6537847 * 2
def baseEnd_6537847 : Nat := 1119019318851795792415165

theorem tailTrace_6537847 : CollatzResearch.WordTrace tailWord_6537847 prefixEnd_6537847 1119019318851795792415165 := by
  unfold tailWord_6537847
  simp only [CollatzResearch.WordTrace]
  refine ⟨238454869945504369217603795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158969913297002912811735863 238454869945504369217603795)
  ·
    refine ⟨357682304918256553826405693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238454869945504369217603795 357682304918256553826405693)
    ·
      refine ⟨134130864344346207684902135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357682304918256553826405693 134130864344346207684902135)
      ·
        refine ⟨201196296516519311527353203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134130864344346207684902135 201196296516519311527353203)
        ·
          refine ⟨301794444774778967291029805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201196296516519311527353203 301794444774778967291029805)
          ·
            refine ⟨113172916790542112734136177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301794444774778967291029805 113172916790542112734136177)
            ·
              refine ⟨84879687592906584550602133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113172916790542112734136177 84879687592906584550602133)
              ·
                refine ⟨3978735355917496150809475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84879687592906584550602133 3978735355917496150809475)
                ·
                  refine ⟨5968103033876244226214213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3978735355917496150809475 5968103033876244226214213)
                  ·
                    refine ⟨1119019318851795792415165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5968103033876244226214213 1119019318851795792415165)
                    ·
                      rfl

theorem cell23_6537847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 1, 4].length) (baseStart_6537847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537847 prefixEnd_6537847 := by exact prefixLift 6537847
  have htrace : WordTrace (prefixWord ++ tailWord_6537847) baseStart_6537847 baseEnd_6537847 := by
    simpa [prefixWord, tailWord_6537847, baseEnd_6537847] using wordTrace_append hprefix tailTrace_6537847
  have hstable : (prefixWord ++ tailWord_6537847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537847).length < 2 ^ (prefixWord ++ tailWord_6537847).sum := by decide
  have hdescent : baseEnd_6537847 < baseStart_6537847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537874 : List Nat := [3, 2, 3, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_6537874 : Nat := 118140960795 + 6537874 * 2 ^ 59
def prefixEnd_6537874 : Nat := 4983230072969 + 3 ^ 40 * 6537874 * 2
def baseEnd_6537874 : Nat := 3357071820533058771607871

theorem tailTrace_6537874 : CollatzResearch.WordTrace tailWord_6537874 prefixEnd_6537874 3357071820533058771607871 := by
  unfold tailWord_6537874
  simp only [CollatzResearch.WordTrace]
  refine ⟨59613963679101638207209169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158970569810937701885891117 59613963679101638207209169)
  ·
    refine ⟨44710472759326228655406877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59613963679101638207209169 44710472759326228655406877)
    ·
      refine ⟨16766427284747335745777579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44710472759326228655406877 16766427284747335745777579)
      ·
        refine ⟨25149640927121003618666369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16766427284747335745777579 25149640927121003618666369)
        ·
          refine ⟨18862230695340752713999777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25149640927121003618666369 18862230695340752713999777)
          ·
            refine ⟨14146673021505564535499833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18862230695340752713999777 14146673021505564535499833)
            ·
              refine ⟨10610004766129173401624875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14146673021505564535499833 10610004766129173401624875)
              ·
                refine ⟨15915007149193760102437313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10610004766129173401624875 15915007149193760102437313)
                ·
                  refine ⟨11936255361895320076827985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15915007149193760102437313 11936255361895320076827985)
                  ·
                    refine ⟨8952191521421490057620989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11936255361895320076827985 8952191521421490057620989)
                    ·
                      refine ⟨3357071820533058771607871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8952191521421490057620989 3357071820533058771607871)
                      ·
                        rfl

theorem cell23_6537874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_6537874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537874 prefixEnd_6537874 := by exact prefixLift 6537874
  have htrace : WordTrace (prefixWord ++ tailWord_6537874) baseStart_6537874 baseEnd_6537874 := by
    simpa [prefixWord, tailWord_6537874, baseEnd_6537874] using wordTrace_append hprefix tailTrace_6537874
  have hstable : (prefixWord ++ tailWord_6537874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537874).length < 2 ^ (prefixWord ++ tailWord_6537874).sum := by decide
  have hdescent : baseEnd_6537874 < baseStart_6537874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537898 : List Nat := [3, 1, 5, 2, 1, 1, 1, 4, 1, 4]
def baseStart_6537898 : Nat := 118140960795 + 6537898 * 2 ^ 59
def prefixEnd_6537898 : Nat := 4983230072969 + 3 ^ 40 * 6537898 * 2
def baseEnd_6537898 : Nat := 1119028048022922225902587

theorem tailTrace_6537898 : CollatzResearch.WordTrace tailWord_6537898 prefixEnd_6537898 1119028048022922225902587 := by
  unfold tailWord_6537898
  simp only [CollatzResearch.WordTrace]
  refine ⟨59614182517079901231927587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158971153378879736618473565 59614182517079901231927587)
  ·
    refine ⟨89421273775619851847891381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59614182517079901231927587 89421273775619851847891381)
    ·
      refine ⟨8383244416464361110739817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89421273775619851847891381 8383244416464361110739817)
      ·
        refine ⟨6287433312348270833054863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8383244416464361110739817 6287433312348270833054863)
        ·
          refine ⟨9431149968522406249582295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6287433312348270833054863 9431149968522406249582295)
          ·
            refine ⟨14146724952783609374373443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9431149968522406249582295 14146724952783609374373443)
            ·
              refine ⟨21220087429175414061560165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14146724952783609374373443 21220087429175414061560165)
              ·
                refine ⟨3978766392970390136542531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21220087429175414061560165 3978766392970390136542531)
                ·
                  refine ⟨5968149589455585204813797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3978766392970390136542531 5968149589455585204813797)
                  ·
                    refine ⟨1119028048022922225902587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5968149589455585204813797 1119028048022922225902587)
                    ·
                      rfl

theorem cell23_6537898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_6537898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537898 prefixEnd_6537898 := by exact prefixLift 6537898
  have htrace : WordTrace (prefixWord ++ tailWord_6537898) baseStart_6537898 baseEnd_6537898 := by
    simpa [prefixWord, tailWord_6537898, baseEnd_6537898] using wordTrace_append hprefix tailTrace_6537898
  have hstable : (prefixWord ++ tailWord_6537898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537898).length < 2 ^ (prefixWord ++ tailWord_6537898).sum := by decide
  have hdescent : baseEnd_6537898 < baseStart_6537898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537920 : List Nat := [2, 1, 1, 2, 4, 2, 1, 3, 1, 6]
def baseStart_6537920 : Nat := 118140960795 + 6537920 * 2 ^ 59
def prefixEnd_6537920 : Nat := 4983230072969 + 3 ^ 40 * 6537920 * 2
def baseEnd_6537920 : Nat := 1119031813547721863877553

theorem tailTrace_6537920 : CollatzResearch.WordTrace tailWord_6537920 prefixEnd_6537920 1119031813547721863877553 := by
  unfold tailWord_6537920
  simp only [CollatzResearch.WordTrace]
  refine ⟨119228766237119951342505607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158971688316159935123340809 119228766237119951342505607)
  ·
    refine ⟨178843149355679927013758411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119228766237119951342505607 178843149355679927013758411)
    ·
      refine ⟨268264724033519890520637617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178843149355679927013758411 268264724033519890520637617)
      ·
        refine ⟨201198543025139917890478213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268264724033519890520637617 201198543025139917890478213)
        ·
          refine ⟨37724726817213734604464665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201198543025139917890478213 37724726817213734604464665)
          ·
            refine ⟨28293545112910300953348499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37724726817213734604464665 28293545112910300953348499)
            ·
              refine ⟨42440317669365451430022749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28293545112910300953348499 42440317669365451430022749)
              ·
                refine ⟨15915119126012044286258531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42440317669365451430022749 15915119126012044286258531)
                ·
                  refine ⟨23872678689018066429387797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15915119126012044286258531 23872678689018066429387797)
                  ·
                    refine ⟨1119031813547721863877553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23872678689018066429387797 1119031813547721863877553)
                    ·
                      rfl

theorem cell23_6537920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 1, 6].length) (baseStart_6537920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537920 prefixEnd_6537920 := by exact prefixLift 6537920
  have htrace : WordTrace (prefixWord ++ tailWord_6537920) baseStart_6537920 baseEnd_6537920 := by
    simpa [prefixWord, tailWord_6537920, baseEnd_6537920] using wordTrace_append hprefix tailTrace_6537920
  have hstable : (prefixWord ++ tailWord_6537920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537920).length < 2 ^ (prefixWord ++ tailWord_6537920).sum := by decide
  have hdescent : baseEnd_6537920 < baseStart_6537920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537938 : List Nat := [3, 2, 2, 2, 3, 1, 2, 3, 1, 1, 3]
def baseStart_6537938 : Nat := 118140960795 + 6537938 * 2 ^ 59
def prefixEnd_6537938 : Nat := 4983230072969 + 3 ^ 40 * 6537938 * 2
def baseEnd_6537938 : Nat := 3357104683294946521207577

theorem tailTrace_6537938 : CollatzResearch.WordTrace tailWord_6537938 prefixEnd_6537938 3357104683294946521207577 := by
  unfold tailWord_6537938
  simp only [CollatzResearch.WordTrace]
  refine ⟨59614547247043672939791617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158972125992116461172777645 59614547247043672939791617)
  ·
    refine ⟨44710910435282754704843713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59614547247043672939791617 44710910435282754704843713)
    ·
      refine ⟨33533182826462066028632785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44710910435282754704843713 33533182826462066028632785)
      ·
        refine ⟨25149887119846549521474589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33533182826462066028632785 25149887119846549521474589)
        ·
          refine ⟨9431207669942456070552971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25149887119846549521474589 9431207669942456070552971)
          ·
            refine ⟨14146811504913684105829457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9431207669942456070552971 14146811504913684105829457)
            ·
              refine ⟨10610108628685263079372093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14146811504913684105829457 10610108628685263079372093)
              ·
                refine ⟨3978790735756973654764535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10610108628685263079372093 3978790735756973654764535)
                ·
                  refine ⟨5968186103635460482146803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3978790735756973654764535 5968186103635460482146803)
                  ·
                    refine ⟨8952279155453190723220205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5968186103635460482146803 8952279155453190723220205)
                    ·
                      refine ⟨3357104683294946521207577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8952279155453190723220205 3357104683294946521207577)
                      ·
                        rfl

theorem cell23_6537938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_6537938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537938 prefixEnd_6537938 := by exact prefixLift 6537938
  have htrace : WordTrace (prefixWord ++ tailWord_6537938) baseStart_6537938 baseEnd_6537938 := by
    simpa [prefixWord, tailWord_6537938, baseEnd_6537938] using wordTrace_append hprefix tailTrace_6537938
  have hstable : (prefixWord ++ tailWord_6537938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537938).length < 2 ^ (prefixWord ++ tailWord_6537938).sum := by decide
  have hdescent : baseEnd_6537938 < baseStart_6537938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537944 : List Nat := [2, 1, 2, 2, 3, 2, 4, 1, 1, 1, 4]
def baseStart_6537944 : Nat := 118140960795 + 6537944 * 2 ^ 59
def prefixEnd_6537944 : Nat := 4983230072969 + 3 ^ 40 * 6537944 * 2
def baseEnd_6537944 : Nat := 3357107764178873497732549

theorem tailTrace_6537944 : CollatzResearch.WordTrace tailWord_6537944 prefixEnd_6537944 3357107764178873497732549 := by
  unfold tailWord_6537944
  simp only [CollatzResearch.WordTrace]
  refine ⟨119229203913076477391942443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158972271884101969855923257 119229203913076477391942443)
  ·
    refine ⟨178843805869614716087913665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119229203913076477391942443 178843805869614716087913665)
    ·
      refine ⟨134132854402211037065935249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178843805869614716087913665 134132854402211037065935249)
      ·
        refine ⟨100599640801658277799451437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134132854402211037065935249 100599640801658277799451437)
        ·
          refine ⟨37724865300621854174794289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100599640801658277799451437 37724865300621854174794289)
          ·
            refine ⟨28293648975466390631095717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37724865300621854174794289 28293648975466390631095717)
            ·
              refine ⟨5305059182899948243330447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28293648975466390631095717 5305059182899948243330447)
              ·
                refine ⟨7957588774349922364995671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5305059182899948243330447 7957588774349922364995671)
                ·
                  refine ⟨11936383161524883547493507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7957588774349922364995671 11936383161524883547493507)
                  ·
                    refine ⟨17904574742287325321240261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11936383161524883547493507 17904574742287325321240261)
                    ·
                      refine ⟨3357107764178873497732549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17904574742287325321240261 3357107764178873497732549)
                      ·
                        rfl

theorem cell23_6537944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_6537944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537944 prefixEnd_6537944 := by exact prefixLift 6537944
  have htrace : WordTrace (prefixWord ++ tailWord_6537944) baseStart_6537944 baseEnd_6537944 := by
    simpa [prefixWord, tailWord_6537944, baseEnd_6537944] using wordTrace_append hprefix tailTrace_6537944
  have hstable : (prefixWord ++ tailWord_6537944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537944).length < 2 ^ (prefixWord ++ tailWord_6537944).sum := by decide
  have hdescent : baseEnd_6537944 < baseStart_6537944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537961 : List Nat := [1, 2, 1, 1, 1, 2, 6, 4, 1, 2, 2]
def baseStart_6537961 : Nat := 118140960795 + 6537961 * 2 ^ 59
def prefixEnd_6537961 : Nat := 4983230072969 + 3 ^ 40 * 6537961 * 2
def baseEnd_6537961 : Nat := 3357116493349999931219971

theorem tailTrace_6537961 : CollatzResearch.WordTrace tailWord_6537961 prefixEnd_6537961 3357116493349999931219971 := by
  unfold tailWord_6537961
  simp only [CollatzResearch.WordTrace]
  refine ⟨238459027867091366687253737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158972685244727577791502491 238459027867091366687253737)
  ·
    refine ⟨178844270900318525015440303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238459027867091366687253737 178844270900318525015440303)
    ·
      refine ⟨268266406350477787523160455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178844270900318525015440303 268266406350477787523160455)
      ·
        refine ⟨402399609525716681284740683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268266406350477787523160455 402399609525716681284740683)
        ·
          refine ⟨603599414288575021927111025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402399609525716681284740683 603599414288575021927111025)
          ·
            refine ⟨452699560716431266445333269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 603599414288575021927111025 452699560716431266445333269)
            ·
              refine ⟨21220291908582715614624997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 452699560716431266445333269 21220291908582715614624997)
              ·
                refine ⟨3978804732859259177742187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21220291908582715614624997 3978804732859259177742187)
                ·
                  refine ⟨5968207099288888766613281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3978804732859259177742187 5968207099288888766613281)
                  ·
                    refine ⟨4476155324466666574959961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5968207099288888766613281 4476155324466666574959961)
                    ·
                      refine ⟨3357116493349999931219971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4476155324466666574959961 3357116493349999931219971)
                      ·
                        rfl

theorem cell23_6537961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 1, 2, 2].length) (baseStart_6537961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537961 prefixEnd_6537961 := by exact prefixLift 6537961
  have htrace : WordTrace (prefixWord ++ tailWord_6537961) baseStart_6537961 baseEnd_6537961 := by
    simpa [prefixWord, tailWord_6537961, baseEnd_6537961] using wordTrace_append hprefix tailTrace_6537961
  have hstable : (prefixWord ++ tailWord_6537961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537961).length < 2 ^ (prefixWord ++ tailWord_6537961).sum := by decide
  have hdescent : baseEnd_6537961 < baseStart_6537961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538034 : List Nat := [3, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2]
def baseStart_6538034 : Nat := 118140960795 + 6538034 * 2 ^ 59
def prefixEnd_6538034 : Nat := 4983230072969 + 3 ^ 40 * 6538034 * 2
def baseEnd_6538034 : Nat := 3357153977437778145607135

theorem tailTrace_6538034 : CollatzResearch.WordTrace tailWord_6538034 prefixEnd_6538034 3357153977437778145607135 := by
  unfold tailWord_6538034
  simp only [CollatzResearch.WordTrace]
  refine ⟨59615422598956725038665289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158974460263884600103107437 59615422598956725038665289)
  ·
    refine ⟨44711566949217543778998967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59615422598956725038665289 44711566949217543778998967)
    ·
      refine ⟨67067350423826315668498451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44711566949217543778998967 67067350423826315668498451)
      ·
        refine ⟨100601025635739473502747677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67067350423826315668498451 100601025635739473502747677)
        ·
          refine ⟨37725384613402302563530379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100601025635739473502747677 37725384613402302563530379)
          ·
            refine ⟨56588076920103453845295569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37725384613402302563530379 56588076920103453845295569)
            ·
              refine ⟨42441057690077590383971677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56588076920103453845295569 42441057690077590383971677)
              ·
                refine ⟨15915396633779096393989379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42441057690077590383971677 15915396633779096393989379)
                ·
                  refine ⟨23873094950668644590984069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15915396633779096393989379 23873094950668644590984069)
                  ·
                    refine ⟨4476205303250370860809513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23873094950668644590984069 4476205303250370860809513)
                    ·
                      refine ⟨3357153977437778145607135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4476205303250370860809513 3357153977437778145607135)
                      ·
                        rfl

theorem cell23_6538034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_6538034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538034 prefixEnd_6538034 := by exact prefixLift 6538034
  have htrace : WordTrace (prefixWord ++ tailWord_6538034) baseStart_6538034 baseEnd_6538034 := by
    simpa [prefixWord, tailWord_6538034, baseEnd_6538034] using wordTrace_append hprefix tailTrace_6538034
  have hstable : (prefixWord ++ tailWord_6538034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538034).length < 2 ^ (prefixWord ++ tailWord_6538034).sum := by decide
  have hdescent : baseEnd_6538034 < baseStart_6538034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538037 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_6538037 : Nat := 118140960795 + 6538037 * 2 ^ 59
def prefixEnd_6538037 : Nat := 4983230072969 + 3 ^ 40 * 6538037 * 2
def baseEnd_6538037 : Nat := 3357155517879741633869621

theorem tailTrace_6538037 : CollatzResearch.WordTrace tailWord_6538037 prefixEnd_6538037 3357155517879741633869621 := by
  unfold tailWord_6538037
  simp only [CollatzResearch.WordTrace]
  refine ⟨238461799814816031667020365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158974533209877354444680243 238461799814816031667020365)
  ·
    refine ⟨89423174930556011875132637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238461799814816031667020365 89423174930556011875132637)
    ·
      refine ⟨33533690598958504453174739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89423174930556011875132637 33533690598958504453174739)
      ·
        refine ⟨50300535898437756679762109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33533690598958504453174739 50300535898437756679762109)
        ·
          refine ⟨18862700961914158754910791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50300535898437756679762109 18862700961914158754910791)
          ·
            refine ⟨28294051442871238132366187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18862700961914158754910791 28294051442871238132366187)
            ·
              refine ⟨42441077164306857198549281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28294051442871238132366187 42441077164306857198549281)
              ·
                refine ⟨31830807873230142898911961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42441077164306857198549281 31830807873230142898911961)
                ·
                  refine ⟨23873105904922607174183971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31830807873230142898911961 23873105904922607174183971)
                  ·
                    refine ⟨35809658857383910761275957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23873105904922607174183971 35809658857383910761275957)
                    ·
                      refine ⟨3357155517879741633869621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35809658857383910761275957 3357155517879741633869621)
                      ·
                        rfl

theorem cell23_6538037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_6538037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538037 prefixEnd_6538037 := by exact prefixLift 6538037
  have htrace : WordTrace (prefixWord ++ tailWord_6538037) baseStart_6538037 baseEnd_6538037 := by
    simpa [prefixWord, tailWord_6538037, baseEnd_6538037] using wordTrace_append hprefix tailTrace_6538037
  have hstable : (prefixWord ++ tailWord_6538037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538037).length < 2 ^ (prefixWord ++ tailWord_6538037).sum := by decide
  have hdescent : baseEnd_6538037 < baseStart_6538037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538038 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 3, 3, 2]
def baseStart_6538038 : Nat := 118140960795 + 6538038 * 2 ^ 59
def prefixEnd_6538038 : Nat := 4983230072969 + 3 ^ 40 * 6538038 * 2
def baseEnd_6538038 : Nat := 3357156031360396129957117

theorem tailTrace_6538038 : CollatzResearch.WordTrace tailWord_6538038 prefixEnd_6538038 3357156031360396129957117 := by
  unfold tailWord_6538038
  simp only [CollatzResearch.WordTrace]
  refine ⟨14903864767988275552362923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158974557525208272558537845 14903864767988275552362923)
  ·
    refine ⟨22355797151982413328544385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14903864767988275552362923 22355797151982413328544385)
    ·
      refine ⟨16766847863986809996408289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22355797151982413328544385 16766847863986809996408289)
      ·
        refine ⟨12575135897990107497306217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16766847863986809996408289 12575135897990107497306217)
        ·
          refine ⟨9431351923492580622979663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12575135897990107497306217 9431351923492580622979663)
          ·
            refine ⟨14147027885238870934469495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9431351923492580622979663 14147027885238870934469495)
            ·
              refine ⟨21220541827858306401704243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14147027885238870934469495 21220541827858306401704243)
              ·
                refine ⟨31830812741787459602556365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21220541827858306401704243 31830812741787459602556365)
                ·
                  refine ⟨11936554778170297350958637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31830812741787459602556365 11936554778170297350958637)
                  ·
                    refine ⟨4476208041813861506609489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11936554778170297350958637 4476208041813861506609489)
                    ·
                      refine ⟨3357156031360396129957117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4476208041813861506609489 3357156031360396129957117)
                      ·
                        rfl

theorem cell23_6538038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_6538038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538038 prefixEnd_6538038 := by exact prefixLift 6538038
  have htrace : WordTrace (prefixWord ++ tailWord_6538038) baseStart_6538038 baseEnd_6538038 := by
    simpa [prefixWord, tailWord_6538038, baseEnd_6538038] using wordTrace_append hprefix tailTrace_6538038
  have hstable : (prefixWord ++ tailWord_6538038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538038).length < 2 ^ (prefixWord ++ tailWord_6538038).sum := by decide
  have hdescent : baseEnd_6538038 < baseStart_6538038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538040 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 9]
def baseStart_6538040 : Nat := 118140960795 + 6538040 * 2 ^ 59
def prefixEnd_6538040 : Nat := 4983230072969 + 3 ^ 40 * 6538040 * 2
def baseEnd_6538040 : Nat := 373017450924633902459123

theorem tailTrace_6538040 : CollatzResearch.WordTrace tailWord_6538040 prefixEnd_6538040 373017450924633902459123 := by
  unfold tailWord_6538040
  simp only [CollatzResearch.WordTrace]
  refine ⟨119230954616902581589689787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158974606155870108786253049 119230954616902581589689787)
  ·
    refine ⟨178846431925353872384534681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119230954616902581589689787 178846431925353872384534681)
    ·
      refine ⟨134134823944015404288401011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178846431925353872384534681 134134823944015404288401011)
      ·
        refine ⟨201202235916023106432601517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134134823944015404288401011 201202235916023106432601517)
        ·
          refine ⟨75450838468508664912225569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201202235916023106432601517 75450838468508664912225569)
          ·
            refine ⟨56588128851381498684169177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75450838468508664912225569 56588128851381498684169177)
            ·
              refine ⟨42441096638536124013126883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56588128851381498684169177 42441096638536124013126883)
              ·
                refine ⟨63661644957804186019690325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42441096638536124013126883 63661644957804186019690325)
                ·
                  refine ⟨373017450924633902459123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63661644957804186019690325 373017450924633902459123)
                  ·
                    rfl

theorem cell23_6538040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 9].length) (baseStart_6538040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538040 prefixEnd_6538040 := by exact prefixLift 6538040
  have htrace : WordTrace (prefixWord ++ tailWord_6538040) baseStart_6538040 baseEnd_6538040 := by
    simpa [prefixWord, tailWord_6538040, baseEnd_6538040] using wordTrace_append hprefix tailTrace_6538040
  have hstable : (prefixWord ++ tailWord_6538040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538040).length < 2 ^ (prefixWord ++ tailWord_6538040).sum := by decide
  have hdescent : baseEnd_6538040 < baseStart_6538040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538074 : List Nat := [3, 1, 1, 2, 1, 5, 1, 4, 5]
def baseStart_6538074 : Nat := 118140960795 + 6538074 * 2 ^ 59
def prefixEnd_6538074 : Nat := 4983230072969 + 3 ^ 40 * 6538074 * 2
def baseEnd_6538074 : Nat := 373019390740439776567439

theorem tailTrace_6538074 : CollatzResearch.WordTrace tailWord_6538074 prefixEnd_6538074 373019390740439776567439 := by
  unfold tailWord_6538074
  simp only [CollatzResearch.WordTrace]
  refine ⟨59615787328920496746529319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158975432877121324657411517 59615787328920496746529319)
  ·
    refine ⟨89423680993380745119793979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59615787328920496746529319 89423680993380745119793979)
    ·
      refine ⟨134135521490071117679690969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89423680993380745119793979 134135521490071117679690969)
      ·
        refine ⟨100601641117553338259768227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134135521490071117679690969 100601641117553338259768227)
        ·
          refine ⟨150902461676330007389652341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100601641117553338259768227 150902461676330007389652341)
          ·
            refine ⟨14147105782155938192779907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150902461676330007389652341 14147105782155938192779907)
            ·
              refine ⟨21220658673233907289169861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14147105782155938192779907 21220658673233907289169861)
              ·
                refine ⟨3978873501231357616719349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21220658673233907289169861 3978873501231357616719349)
                ·
                  refine ⟨373019390740439776567439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3978873501231357616719349 373019390740439776567439)
                  ·
                    rfl

theorem cell23_6538074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 5].length) (baseStart_6538074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538074 prefixEnd_6538074 := by exact prefixLift 6538074
  have htrace : WordTrace (prefixWord ++ tailWord_6538074) baseStart_6538074 baseEnd_6538074 := by
    simpa [prefixWord, tailWord_6538074, baseEnd_6538074] using wordTrace_append hprefix tailTrace_6538074
  have hstable : (prefixWord ++ tailWord_6538074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538074).length < 2 ^ (prefixWord ++ tailWord_6538074).sum := by decide
  have hdescent : baseEnd_6538074 < baseStart_6538074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538084 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 2, 3, 3]
def baseStart_6538084 : Nat := 118140960795 + 6538084 * 2 ^ 59
def prefixEnd_6538084 : Nat := 4983230072969 + 3 ^ 40 * 6538084 * 2
def baseEnd_6538084 : Nat := 3357179651470502949981905

theorem tailTrace_6538084 : CollatzResearch.WordTrace tailWord_6538084 prefixEnd_6538084 3357179651470502949981905 := by
  unfold tailWord_6538084
  simp only [CollatzResearch.WordTrace]
  refine ⟨119231757022822879346990653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158975676030430505795987537 119231757022822879346990653)
  ·
    refine ⟨44711908883558579755121495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119231757022822879346990653 44711908883558579755121495)
    ·
      refine ⟨67067863325337869632682243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44711908883558579755121495 67067863325337869632682243)
      ·
        refine ⟨100601794988006804449023365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67067863325337869632682243 100601794988006804449023365)
        ·
          refine ⟨18862836560251275834191881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100601794988006804449023365 18862836560251275834191881)
          ·
            refine ⟨14147127420188456875643911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18862836560251275834191881 14147127420188456875643911)
            ·
              refine ⟨21220691130282685313465867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14147127420188456875643911 21220691130282685313465867)
              ·
                refine ⟨31831036695424027970198801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21220691130282685313465867 31831036695424027970198801)
                ·
                  refine ⟨23873277521568020977649101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31831036695424027970198801 23873277521568020977649101)
                  ·
                    refine ⟨8952479070588007866618413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23873277521568020977649101 8952479070588007866618413)
                    ·
                      refine ⟨3357179651470502949981905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8952479070588007866618413 3357179651470502949981905)
                      ·
                        rfl

theorem cell23_6538084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_6538084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538084 prefixEnd_6538084 := by exact prefixLift 6538084
  have htrace : WordTrace (prefixWord ++ tailWord_6538084) baseStart_6538084 baseEnd_6538084 := by
    simpa [prefixWord, tailWord_6538084, baseEnd_6538084] using wordTrace_append hprefix tailTrace_6538084
  have hstable : (prefixWord ++ tailWord_6538084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538084).length < 2 ^ (prefixWord ++ tailWord_6538084).sum := by decide
  have hdescent : baseEnd_6538084 < baseStart_6538084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538124 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 2, 4, 2]
def baseStart_6538124 : Nat := 118140960795 + 6538124 * 2 ^ 59
def prefixEnd_6538124 : Nat := 4983230072969 + 3 ^ 40 * 6538124 * 2
def baseEnd_6538124 : Nat := 3357200190696682793481721

theorem tailTrace_6538124 : CollatzResearch.WordTrace tailWord_6538124 prefixEnd_6538124 3357200190696682793481721 := by
  unfold tailWord_6538124
  simp only [CollatzResearch.WordTrace]
  refine ⟨119232486482750422762718713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158976648643667230350291617 119232486482750422762718713)
  ·
    refine ⟨89424364862062817072039035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119232486482750422762718713 89424364862062817072039035)
    ·
      refine ⟨134136547293094225608058553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89424364862062817072039035 134136547293094225608058553)
      ·
        refine ⟨100602410469820669206043915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134136547293094225608058553 100602410469820669206043915)
        ·
          refine ⟨150903615704731003809065873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100602410469820669206043915 150903615704731003809065873)
          ·
            refine ⟨113177711778548252856799405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150903615704731003809065873 113177711778548252856799405)
            ·
              refine ⟨42441641916955594821299777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113177711778548252856799405 42441641916955594821299777)
              ·
                refine ⟨31831231437716696115974833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42441641916955594821299777 31831231437716696115974833)
                ·
                  refine ⟨23873423578287522086981125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31831231437716696115974833 23873423578287522086981125)
                  ·
                    refine ⟨4476266920928910391308961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23873423578287522086981125 4476266920928910391308961)
                    ·
                      refine ⟨3357200190696682793481721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4476266920928910391308961 3357200190696682793481721)
                      ·
                        rfl

theorem cell23_6538124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_6538124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538124 prefixEnd_6538124 := by exact prefixLift 6538124
  have htrace : WordTrace (prefixWord ++ tailWord_6538124) baseStart_6538124 baseEnd_6538124 := by
    simpa [prefixWord, tailWord_6538124, baseEnd_6538124] using wordTrace_append hprefix tailTrace_6538124
  have hstable : (prefixWord ++ tailWord_6538124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538124).length < 2 ^ (prefixWord ++ tailWord_6538124).sum := by decide
  have hdescent : baseEnd_6538124 < baseStart_6538124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538147 : List Nat := [1, 1, 1, 4, 1, 2, 2, 5, 6]
def baseStart_6538147 : Nat := 118140960795 + 6538147 * 2 ^ 59
def prefixEnd_6538147 : Nat := 4983230072969 + 3 ^ 40 * 6538147 * 2
def baseEnd_6538147 : Nat := 373023555639081800388235

theorem tailTrace_6538147 : CollatzResearch.WordTrace tailWord_6538147 prefixEnd_6538147 373023555639081800388235 := by
  unfold tailWord_6538147
  simp only [CollatzResearch.WordTrace]
  refine ⟨238465811844417520453524695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158977207896278346969016463 238465811844417520453524695)
  ·
    refine ⟨357698717766626280680287043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238465811844417520453524695 357698717766626280680287043)
    ·
      refine ⟨536548076649939421020430565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357698717766626280680287043 536548076649939421020430565)
      ·
        refine ⟨100602764371863641441330731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 536548076649939421020430565 100602764371863641441330731)
        ·
          refine ⟨150904146557795462161996097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100602764371863641441330731 150904146557795462161996097)
          ·
            refine ⟨113178109918346596621497073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150904146557795462161996097 113178109918346596621497073)
            ·
              refine ⟨84883582438759947466122805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113178109918346596621497073 84883582438759947466122805)
              ·
                refine ⟨7957835853633745074949013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84883582438759947466122805 7957835853633745074949013)
                ·
                  refine ⟨373023555639081800388235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7957835853633745074949013 373023555639081800388235)
                  ·
                    rfl

theorem cell23_6538147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 6].length) (baseStart_6538147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538147 prefixEnd_6538147 := by exact prefixLift 6538147
  have htrace : WordTrace (prefixWord ++ tailWord_6538147) baseStart_6538147 baseEnd_6538147 := by
    simpa [prefixWord, tailWord_6538147, baseEnd_6538147] using wordTrace_append hprefix tailTrace_6538147
  have hstable : (prefixWord ++ tailWord_6538147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538147).length < 2 ^ (prefixWord ++ tailWord_6538147).sum := by decide
  have hdescent : baseEnd_6538147 < baseStart_6538147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538168 : List Nat := [2, 1, 2, 1, 2, 6, 1, 3, 1, 4]
def baseStart_6538168 : Nat := 118140960795 + 6538168 * 2 ^ 59
def prefixEnd_6538168 : Nat := 4983230072969 + 3 ^ 40 * 6538168 * 2
def baseEnd_6538168 : Nat := 1119074261281826873777173

theorem tailTrace_6538168 : CollatzResearch.WordTrace tailWord_6538168 prefixEnd_6538168 1119074261281826873777173 := by
  unfold tailWord_6538168
  simp only [CollatzResearch.WordTrace]
  refine ⟨119233288888670720520019579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158977718518227627360026105 119233288888670720520019579)
  ·
    refine ⟨178849933333006080780029369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119233288888670720520019579 178849933333006080780029369)
    ·
      refine ⟨134137449999754560585022027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178849933333006080780029369 134137449999754560585022027)
      ·
        refine ⟨201206174999631840877533041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134137449999754560585022027 201206174999631840877533041)
        ·
          refine ⟨150904631249723880658149781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201206174999631840877533041 150904631249723880658149781)
          ·
            refine ⟨7073654589830806905850771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 150904631249723880658149781 7073654589830806905850771)
            ·
              refine ⟨10610481884746210358776157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7073654589830806905850771 10610481884746210358776157)
              ·
                refine ⟨3978930706779828884541059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10610481884746210358776157 3978930706779828884541059)
                ·
                  refine ⟨5968396060169743326811589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3978930706779828884541059 5968396060169743326811589)
                  ·
                    refine ⟨1119074261281826873777173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5968396060169743326811589 1119074261281826873777173)
                    ·
                      rfl

theorem cell23_6538168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 1, 4].length) (baseStart_6538168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538168 prefixEnd_6538168 := by exact prefixLift 6538168
  have htrace : WordTrace (prefixWord ++ tailWord_6538168) baseStart_6538168 baseEnd_6538168 := by
    simpa [prefixWord, tailWord_6538168, baseEnd_6538168] using wordTrace_append hprefix tailTrace_6538168
  have hstable : (prefixWord ++ tailWord_6538168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538168).length < 2 ^ (prefixWord ++ tailWord_6538168).sum := by decide
  have hdescent : baseEnd_6538168 < baseStart_6538168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538191 : List Nat := [1, 1, 2, 1, 1, 6, 3, 1, 3, 1, 3]
def baseStart_6538191 : Nat := 118140960795 + 6538191 * 2 ^ 59
def prefixEnd_6538191 : Nat := 4983230072969 + 3 ^ 40 * 6538191 * 2
def baseEnd_6538191 : Nat := 3357234593900534031343913

theorem tailTrace_6538191 : CollatzResearch.WordTrace tailWord_6538191 prefixEnd_6538191 3357234593900534031343913 := by
  unfold tailWord_6538191
  simp only [CollatzResearch.WordTrace]
  refine ⟨238467416656258115968126427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158978277770838743978750951 238467416656258115968126427)
  ·
    refine ⟨357701124984387173952189641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238467416656258115968126427 357701124984387173952189641)
    ·
      refine ⟨268275843738290380464142231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357701124984387173952189641 268275843738290380464142231)
      ·
        refine ⟨402413765607435570696213347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268275843738290380464142231 402413765607435570696213347)
        ·
          refine ⟨603620648411153356044320021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402413765607435570696213347 603620648411153356044320021)
          ·
            refine ⟨28294717894272813564577501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 603620648411153356044320021 28294717894272813564577501)
            ·
              refine ⟨10610519210352305086716563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28294717894272813564577501 10610519210352305086716563)
              ·
                refine ⟨15915778815528457630074845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10610519210352305086716563 15915778815528457630074845)
                ·
                  refine ⟨5968417055823171611278067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15915778815528457630074845 5968417055823171611278067)
                  ·
                    refine ⟨8952625583734757416917101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5968417055823171611278067 8952625583734757416917101)
                    ·
                      refine ⟨3357234593900534031343913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8952625583734757416917101 3357234593900534031343913)
                      ·
                        rfl

theorem cell23_6538191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 1, 3].length) (baseStart_6538191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538191 prefixEnd_6538191 := by exact prefixLift 6538191
  have htrace : WordTrace (prefixWord ++ tailWord_6538191) baseStart_6538191 baseEnd_6538191 := by
    simpa [prefixWord, tailWord_6538191, baseEnd_6538191] using wordTrace_append hprefix tailTrace_6538191
  have hstable : (prefixWord ++ tailWord_6538191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538191).length < 2 ^ (prefixWord ++ tailWord_6538191).sum := by decide
  have hdescent : baseEnd_6538191 < baseStart_6538191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538198 : List Nat := [5, 2, 1, 1, 2, 1, 4, 1, 6]
def baseStart_6538198 : Nat := 118140960795 + 6538198 * 2 ^ 59
def prefixEnd_6538198 : Nat := 4983230072969 + 3 ^ 40 * 6538198 * 2
def baseEnd_6538198 : Nat := 373026465362790611550709

theorem tailTrace_6538198 : CollatzResearch.WordTrace tailWord_6538198 prefixEnd_6538198 373026465362790611550709 := by
  unfold tailWord_6538198
  simp only [CollatzResearch.WordTrace]
  refine ⟨14904229497952047260226953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158978447978155170775754165 14904229497952047260226953)
  ·
    refine ⟨11178172123464035445170215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14904229497952047260226953 11178172123464035445170215)
    ·
      refine ⟨16767258185196053167755323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11178172123464035445170215 16767258185196053167755323)
      ·
        refine ⟨25150887277794079751632985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16767258185196053167755323 25150887277794079751632985)
        ·
          refine ⟨18863165458345559813724739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25150887277794079751632985 18863165458345559813724739)
          ·
            refine ⟨28294748187518339720587109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18863165458345559813724739 28294748187518339720587109)
            ·
              refine ⟨5305265285159688697610083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28294748187518339720587109 5305265285159688697610083)
              ·
                refine ⟨7957897927739533046415125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5305265285159688697610083 7957897927739533046415125)
                ·
                  refine ⟨373026465362790611550709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7957897927739533046415125 373026465362790611550709)
                  ·
                    rfl

theorem cell23_6538198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_6538198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538198 prefixEnd_6538198 := by exact prefixLift 6538198
  have htrace : WordTrace (prefixWord ++ tailWord_6538198) baseStart_6538198 baseEnd_6538198 := by
    simpa [prefixWord, tailWord_6538198, baseEnd_6538198] using wordTrace_append hprefix tailTrace_6538198
  have hstable : (prefixWord ++ tailWord_6538198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538198).length < 2 ^ (prefixWord ++ tailWord_6538198).sum := by decide
  have hdescent : baseEnd_6538198 < baseStart_6538198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538218 : List Nat := [3, 1, 3, 1, 2, 3, 2, 1, 2, 3, 2]
def baseStart_6538218 : Nat := 118140960795 + 6538218 * 2 ^ 59
def prefixEnd_6538218 : Nat := 4983230072969 + 3 ^ 40 * 6538218 * 2
def baseEnd_6538218 : Nat := 3357248457878205425706289

theorem tailTrace_6538218 : CollatzResearch.WordTrace tailWord_6538218 prefixEnd_6538218 3357248457878205425706289 := by
  unfold tailWord_6538218
  simp only [CollatzResearch.WordTrace]
  refine ⟨59617100356790074894839827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158978934284773533052906205 59617100356790074894839827)
  ·
    refine ⟨89425650535185112342259741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59617100356790074894839827 89425650535185112342259741)
    ·
      refine ⟨33534618950694417128347403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89425650535185112342259741 33534618950694417128347403)
      ·
        refine ⟨50301928426041625692521105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33534618950694417128347403 50301928426041625692521105)
        ·
          refine ⟨37726446319531219269390829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50301928426041625692521105 37726446319531219269390829)
          ·
            refine ⟨14147417369824207226021561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37726446319531219269390829 14147417369824207226021561)
            ·
              refine ⟨10610563027368155419516171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14147417369824207226021561 10610563027368155419516171)
              ·
                refine ⟨15915844541052233129274257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10610563027368155419516171 15915844541052233129274257)
                ·
                  refine ⟨11936883405789174846955693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15915844541052233129274257 11936883405789174846955693)
                  ·
                    refine ⟨4476331277170940567608385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11936883405789174846955693 4476331277170940567608385)
                    ·
                      refine ⟨3357248457878205425706289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4476331277170940567608385 3357248457878205425706289)
                      ·
                        rfl

theorem cell23_6538218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_6538218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538218 prefixEnd_6538218 := by exact prefixLift 6538218
  have htrace : WordTrace (prefixWord ++ tailWord_6538218) baseStart_6538218 baseEnd_6538218 := by
    simpa [prefixWord, tailWord_6538218, baseEnd_6538218] using wordTrace_append hprefix tailTrace_6538218
  have hstable : (prefixWord ++ tailWord_6538218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538218).length < 2 ^ (prefixWord ++ tailWord_6538218).sum := by decide
  have hdescent : baseEnd_6538218 < baseStart_6538218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538241 : List Nat := [1, 2, 4, 1, 2, 2, 1, 4, 2, 4]
def baseStart_6538241 : Nat := 118140960795 + 6538241 * 2 ^ 59
def prefixEnd_6538241 : Nat := 4983230072969 + 3 ^ 40 * 6538241 * 2
def baseEnd_6538241 : Nat := 1119086755977752945239561

theorem tailTrace_6538241 : CollatzResearch.WordTrace tailWord_6538241 prefixEnd_6538241 1119086755977752945239561 := by
  unfold tailWord_6538241
  simp only [CollatzResearch.WordTrace]
  refine ⟨238469240306076974507446577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158979493537384649671631051 238469240306076974507446577)
  ·
    refine ⟨178851930229557730880584933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238469240306076974507446577 178851930229557730880584933)
    ·
      refine ⟨33534736918042074540109675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178851930229557730880584933 33534736918042074540109675)
      ·
        refine ⟨50302105377063111810164513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33534736918042074540109675 50302105377063111810164513)
        ·
          refine ⟨37726579032797333857623385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50302105377063111810164513 37726579032797333857623385)
          ·
            refine ⟨28294934274598000393217539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37726579032797333857623385 28294934274598000393217539)
            ·
              refine ⟨42442401411897000589826309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28294934274598000393217539 42442401411897000589826309)
              ·
                refine ⟨7957950264730687610592433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42442401411897000589826309 7957950264730687610592433)
                ·
                  refine ⟨5968462698548015707944325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7957950264730687610592433 5968462698548015707944325)
                  ·
                    refine ⟨1119086755977752945239561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5968462698548015707944325 1119086755977752945239561)
                    ·
                      rfl

theorem cell23_6538241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_6538241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538241 prefixEnd_6538241 := by exact prefixLift 6538241
  have htrace : WordTrace (prefixWord ++ tailWord_6538241) baseStart_6538241 baseEnd_6538241 := by
    simpa [prefixWord, tailWord_6538241, baseEnd_6538241] using wordTrace_append hprefix tailTrace_6538241
  have hstable : (prefixWord ++ tailWord_6538241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538241).length < 2 ^ (prefixWord ++ tailWord_6538241).sum := by decide
  have hdescent : baseEnd_6538241 < baseStart_6538241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538254 : List Nat := [4, 1, 1, 2, 2, 2, 3, 8]
def baseStart_6538254 : Nat := 118140960795 + 6538254 * 2 ^ 59
def prefixEnd_6538254 : Nat := 4983230072969 + 3 ^ 40 * 6538254 * 2
def baseEnd_6538254 : Nat := 124343220117843232772449

theorem tailTrace_6538254 : CollatzResearch.WordTrace tailWord_6538254 prefixEnd_6538254 124343220117843232772449 := by
  unfold tailWord_6538254
  simp only [CollatzResearch.WordTrace]
  refine ⟨29808714306878734715958727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158979809636686585151779877 29808714306878734715958727)
  ·
    refine ⟨44713071460318102073938091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29808714306878734715958727 44713071460318102073938091)
    ·
      refine ⟨67069607190477153110907137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44713071460318102073938091 67069607190477153110907137)
      ·
        refine ⟨50302205392857864833180353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67069607190477153110907137 50302205392857864833180353)
        ·
          refine ⟨37726654044643398624885265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50302205392857864833180353 37726654044643398624885265)
          ·
            refine ⟨28294990533482548968663949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37726654044643398624885265 28294990533482548968663949)
            ·
              refine ⟨10610621450055955863248981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28294990533482548968663949 10610621450055955863248981)
              ·
                refine ⟨124343220117843232772449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10610621450055955863248981 124343220117843232772449)
                ·
                  rfl

theorem cell23_6538254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 8].length) (baseStart_6538254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538254 prefixEnd_6538254 := by exact prefixLift 6538254
  have htrace : WordTrace (prefixWord ++ tailWord_6538254) baseStart_6538254 baseEnd_6538254 := by
    simpa [prefixWord, tailWord_6538254, baseEnd_6538254] using wordTrace_append hprefix tailTrace_6538254
  have hstable : (prefixWord ++ tailWord_6538254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538254).length < 2 ^ (prefixWord ++ tailWord_6538254).sum := by decide
  have hdescent : baseEnd_6538254 < baseStart_6538254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538257 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 6]
def baseStart_6538257 : Nat := 118140960795 + 6538257 * 2 ^ 59
def prefixEnd_6538257 : Nat := 4983230072969 + 3 ^ 40 * 6538257 * 2
def baseEnd_6538257 : Nat := 3357268483623730773118609

theorem tailTrace_6538257 : CollatzResearch.WordTrace tailWord_6538257 prefixEnd_6538257 3357268483623730773118609 := by
  unfold tailWord_6538257
  simp only [CollatzResearch.WordTrace]
  refine ⟨238469823874019009240029025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158979882582679339493352683 238469823874019009240029025)
  ·
    refine ⟨178852367905514256930021769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238469823874019009240029025 178852367905514256930021769)
    ·
      refine ⟨134139275929135692697516327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178852367905514256930021769 134139275929135692697516327)
      ·
        refine ⟨201208913893703539046274491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134139275929135692697516327 201208913893703539046274491)
        ·
          refine ⟨301813370840555308569411737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201208913893703539046274491 301813370840555308569411737)
          ·
            refine ⟨226360028130416481427058803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301813370840555308569411737 226360028130416481427058803)
            ·
              refine ⟨339540042195624722140588205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226360028130416481427058803 339540042195624722140588205)
              ·
                refine ⟨127327515823359270802720577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339540042195624722140588205 127327515823359270802720577)
                ·
                  refine ⟨95495636867519453102040433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127327515823359270802720577 95495636867519453102040433)
                  ·
                    refine ⟨71621727650639589826530325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95495636867519453102040433 71621727650639589826530325)
                    ·
                      refine ⟨3357268483623730773118609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71621727650639589826530325 3357268483623730773118609)
                      ·
                        rfl

theorem cell23_6538257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_6538257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538257 prefixEnd_6538257 := by exact prefixLift 6538257
  have htrace : WordTrace (prefixWord ++ tailWord_6538257) baseStart_6538257 baseEnd_6538257 := by
    simpa [prefixWord, tailWord_6538257, baseEnd_6538257] using wordTrace_append hprefix tailTrace_6538257
  have hstable : (prefixWord ++ tailWord_6538257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538257).length < 2 ^ (prefixWord ++ tailWord_6538257).sum := by decide
  have hdescent : baseEnd_6538257 < baseStart_6538257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538261 : List Nat := [1, 3, 2, 1, 4, 2, 2, 1, 1, 2, 4]
def baseStart_6538261 : Nat := 118140960795 + 6538261 * 2 ^ 59
def prefixEnd_6538261 : Nat := 4983230072969 + 3 ^ 40 * 6538261 * 2
def baseEnd_6538261 : Nat := 3357270537546348757468591

theorem tailTrace_6538261 : CollatzResearch.WordTrace tailWord_6538261 prefixEnd_6538261 3357270537546348757468591 := by
  unfold tailWord_6538261
  simp only [CollatzResearch.WordTrace]
  refine ⟨238469969766004517923174637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158979979844003011948783091 238469969766004517923174637)
  ·
    refine ⟨89426238662251694221190489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238469969766004517923174637 89426238662251694221190489)
    ·
      refine ⟨67069678996688770665892867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89426238662251694221190489 67069678996688770665892867)
      ·
        refine ⟨100604518495033155998839301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67069678996688770665892867 100604518495033155998839301)
        ·
          refine ⟨18863347217818716749782369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100604518495033155998839301 18863347217818716749782369)
          ·
            refine ⟨14147510413364037562336777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18863347217818716749782369 14147510413364037562336777)
            ·
              refine ⟨10610632810023028171752583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14147510413364037562336777 10610632810023028171752583)
              ·
                refine ⟨15915949215034542257628875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10610632810023028171752583 15915949215034542257628875)
                ·
                  refine ⟨23873923822551813386443313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15915949215034542257628875 23873923822551813386443313)
                  ·
                    refine ⟨17905442866913860039832485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23873923822551813386443313 17905442866913860039832485)
                    ·
                      refine ⟨3357270537546348757468591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17905442866913860039832485 3357270537546348757468591)
                      ·
                        rfl

theorem cell23_6538261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_6538261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538261 prefixEnd_6538261 := by exact prefixLift 6538261
  have htrace : WordTrace (prefixWord ++ tailWord_6538261) baseStart_6538261 baseEnd_6538261 := by
    simpa [prefixWord, tailWord_6538261, baseEnd_6538261] using wordTrace_append hprefix tailTrace_6538261
  have hstable : (prefixWord ++ tailWord_6538261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538261).length < 2 ^ (prefixWord ++ tailWord_6538261).sum := by decide
  have hdescent : baseEnd_6538261 < baseStart_6538261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538282 : List Nat := [3, 1, 4, 1, 4, 1, 2, 1, 1, 1, 4]
def baseStart_6538282 : Nat := 118140960795 + 6538282 * 2 ^ 59
def prefixEnd_6538282 : Nat := 4983230072969 + 3 ^ 40 * 6538282 * 2
def baseEnd_6538282 : Nat := 3357281320640093175305995

theorem tailTrace_6538282 : CollatzResearch.WordTrace tailWord_6538282 prefixEnd_6538282 3357281320640093175305995 := by
  unfold tailWord_6538282
  simp only [CollatzResearch.WordTrace]
  refine ⟨59617683924732109627422275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158980490465952292339792733 59617683924732109627422275)
  ·
    refine ⟨89426525887098164441133413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59617683924732109627422275 89426525887098164441133413)
    ·
      refine ⟨16767473603830905832712515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89426525887098164441133413 16767473603830905832712515)
      ·
        refine ⟨25151210405746358749068773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16767473603830905832712515 25151210405746358749068773)
        ·
          refine ⟨4715851951077442265450395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25151210405746358749068773 4715851951077442265450395)
          ·
            refine ⟨7073777926616163398175593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4715851951077442265450395 7073777926616163398175593)
            ·
              refine ⟨5305333444962122548631695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7073777926616163398175593 5305333444962122548631695)
              ·
                refine ⟨7958000167443183822947543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5305333444962122548631695 7958000167443183822947543)
                ·
                  refine ⟨11937000251164775734421315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7958000167443183822947543 11937000251164775734421315)
                  ·
                    refine ⟨17905500376747163601631973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11937000251164775734421315 17905500376747163601631973)
                    ·
                      refine ⟨3357281320640093175305995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17905500376747163601631973 3357281320640093175305995)
                      ·
                        rfl

theorem cell23_6538282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_6538282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538282 prefixEnd_6538282 := by exact prefixLift 6538282
  have htrace : WordTrace (prefixWord ++ tailWord_6538282) baseStart_6538282 baseEnd_6538282 := by
    simpa [prefixWord, tailWord_6538282, baseEnd_6538282] using wordTrace_append hprefix tailTrace_6538282
  have hstable : (prefixWord ++ tailWord_6538282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538282).length < 2 ^ (prefixWord ++ tailWord_6538282).sum := by decide
  have hdescent : baseEnd_6538282 < baseStart_6538282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538298 : List Nat := [3, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3]
def baseStart_6538298 : Nat := 118140960795 + 6538298 * 2 ^ 59
def prefixEnd_6538298 : Nat := 4983230072969 + 3 ^ 40 * 6538298 * 2
def baseEnd_6538298 : Nat := 3357289536330565112705921

theorem tailTrace_6538298 : CollatzResearch.WordTrace tailWord_6538298 prefixEnd_6538298 3357289536330565112705921 := by
  unfold tailWord_6538298
  simp only [CollatzResearch.WordTrace]
  refine ⟨59617829816717618310567887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158980879511246982161514365 59617829816717618310567887)
  ·
    refine ⟨89426744725076427465851831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59617829816717618310567887 89426744725076427465851831)
    ·
      refine ⟨134140117087614641198777747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89426744725076427465851831 134140117087614641198777747)
      ·
        refine ⟨201210175631421961798166621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134140117087614641198777747 201210175631421961798166621)
        ·
          refine ⟨75453815861783235674312483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201210175631421961798166621 75453815861783235674312483)
          ·
            refine ⟨113180723792674853511468725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75453815861783235674312483 113180723792674853511468725)
            ·
              refine ⟨10610692855563267516700193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113180723792674853511468725 10610692855563267516700193)
              ·
                refine ⟨7958019641672450637525145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10610692855563267516700193 7958019641672450637525145)
                ·
                  refine ⟨5968514731254337978143859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7958019641672450637525145 5968514731254337978143859)
                  ·
                    refine ⟨8952772096881506967215789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5968514731254337978143859 8952772096881506967215789)
                    ·
                      refine ⟨3357289536330565112705921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8952772096881506967215789 3357289536330565112705921)
                      ·
                        rfl

theorem cell23_6538298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3].length) (baseStart_6538298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538298 prefixEnd_6538298 := by exact prefixLift 6538298
  have htrace : WordTrace (prefixWord ++ tailWord_6538298) baseStart_6538298 baseEnd_6538298 := by
    simpa [prefixWord, tailWord_6538298, baseEnd_6538298] using wordTrace_append hprefix tailTrace_6538298
  have hstable : (prefixWord ++ tailWord_6538298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538298).length < 2 ^ (prefixWord ++ tailWord_6538298).sum := by decide
  have hdescent : baseEnd_6538298 < baseStart_6538298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538314 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 2, 6]
def baseStart_6538314 : Nat := 118140960795 + 6538314 * 2 ^ 59
def prefixEnd_6538314 : Nat := 4983230072969 + 3 ^ 40 * 6538314 * 2
def baseEnd_6538314 : Nat := 1119099250673679016701949

theorem tailTrace_6538314 : CollatzResearch.WordTrace tailWord_6538314 prefixEnd_6538314 1119099250673679016701949 := by
  unfold tailWord_6538314
  simp only [CollatzResearch.WordTrace]
  refine ⟨59617975708703126993713499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158981268556541671983235997 59617975708703126993713499)
  ·
    refine ⟨89426963563054690490570249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59617975708703126993713499 89426963563054690490570249)
    ·
      refine ⟨67070222672291017867927687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89426963563054690490570249 67070222672291017867927687)
      ·
        refine ⟨100605334008436526801891531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67070222672291017867927687 100605334008436526801891531)
        ·
          refine ⟨150908001012654790202837297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100605334008436526801891531 150908001012654790202837297)
          ·
            refine ⟨113181000759491092652127973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150908001012654790202837297 113181000759491092652127973)
            ·
              refine ⟨21221437642404579872273995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113181000759491092652127973 21221437642404579872273995)
              ·
                refine ⟨31832156463606869808410993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21221437642404579872273995 31832156463606869808410993)
                ·
                  refine ⟨23874117347705152356308245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31832156463606869808410993 23874117347705152356308245)
                  ·
                    refine ⟨1119099250673679016701949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23874117347705152356308245 1119099250673679016701949)
                    ·
                      rfl

theorem cell23_6538314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_6538314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538314 prefixEnd_6538314 := by exact prefixLift 6538314
  have htrace : WordTrace (prefixWord ++ tailWord_6538314) baseStart_6538314 baseEnd_6538314 := by
    simpa [prefixWord, tailWord_6538314, baseEnd_6538314] using wordTrace_append hprefix tailTrace_6538314
  have hstable : (prefixWord ++ tailWord_6538314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538314).length < 2 ^ (prefixWord ++ tailWord_6538314).sum := by decide
  have hdescent : baseEnd_6538314 < baseStart_6538314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538354 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_6538354 : Nat := 118140960795 + 6538354 * 2 ^ 59
def prefixEnd_6538354 : Nat := 4983230072969 + 3 ^ 40 * 6538354 * 2
def baseEnd_6538354 : Nat := 3357318291247216893605663

theorem tailTrace_6538354 : CollatzResearch.WordTrace tailWord_6538354 prefixEnd_6538354 3357318291247216893605663 := by
  unfold tailWord_6538354
  simp only [CollatzResearch.WordTrace]
  refine ⟨59618340438666898701577529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158982241169778396537540077 59618340438666898701577529)
  ·
    refine ⟨44713755329000174026183147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59618340438666898701577529 44713755329000174026183147)
    ·
      refine ⟨67070632993500261039274721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44713755329000174026183147 67070632993500261039274721)
      ·
        refine ⟨50302974745125195779456041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67070632993500261039274721 50302974745125195779456041)
        ·
          refine ⟨37727231058843896834592031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50302974745125195779456041 37727231058843896834592031)
          ·
            refine ⟨56590846588265845251888047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37727231058843896834592031 56590846588265845251888047)
            ·
              refine ⟨84886269882398767877832071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56590846588265845251888047 84886269882398767877832071)
              ·
                refine ⟨127329404823598151816748107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84886269882398767877832071 127329404823598151816748107)
                ·
                  refine ⟨190994107235397227725122161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127329404823598151816748107 190994107235397227725122161)
                  ·
                    refine ⟨143245580426547920793841621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 190994107235397227725122161 143245580426547920793841621)
                    ·
                      refine ⟨3357318291247216893605663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143245580426547920793841621 3357318291247216893605663)
                      ·
                        rfl

theorem cell23_6538354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_6538354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538354 prefixEnd_6538354 := by exact prefixLift 6538354
  have htrace : WordTrace (prefixWord ++ tailWord_6538354) baseStart_6538354 baseEnd_6538354 := by
    simpa [prefixWord, tailWord_6538354, baseEnd_6538354] using wordTrace_append hprefix tailTrace_6538354
  have hstable : (prefixWord ++ tailWord_6538354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538354).length < 2 ^ (prefixWord ++ tailWord_6538354).sum := by decide
  have hdescent : baseEnd_6538354 < baseStart_6538354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538372 : List Nat := [2, 3, 2, 1, 2, 2, 4, 1, 2, 2, 2]
def baseStart_6538372 : Nat := 118140960795 + 6538372 * 2 ^ 59
def prefixEnd_6538372 : Nat := 4983230072969 + 3 ^ 40 * 6538372 * 2
def baseEnd_6538372 : Nat := 3357327533898997823180581

theorem tailTrace_6538372 : CollatzResearch.WordTrace tailWord_6538372 prefixEnd_6538372 3357327533898997823180581 := by
  unfold tailWord_6538372
  simp only [CollatzResearch.WordTrace]
  refine ⟨119237009134301191940232685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158982678845734922586976913 119237009134301191940232685)
  ·
    refine ⟨44713878425362946977587257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119237009134301191940232685 44713878425362946977587257)
    ·
      refine ⟨33535408819022210233190443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44713878425362946977587257 33535408819022210233190443)
      ·
        refine ⟨50303113228533315349785665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33535408819022210233190443 50303113228533315349785665)
        ·
          refine ⟨37727334921399986512339249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50303113228533315349785665 37727334921399986512339249)
          ·
            refine ⟨28295501191049989884254437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37727334921399986512339249 28295501191049989884254437)
            ·
              refine ⟨5305406473321873103297707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28295501191049989884254437 5305406473321873103297707)
              ·
                refine ⟨7958109709982809654946561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5305406473321873103297707 7958109709982809654946561)
                ·
                  refine ⟨5968582282487107241209921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7958109709982809654946561 5968582282487107241209921)
                  ·
                    refine ⟨4476436711865330430907441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5968582282487107241209921 4476436711865330430907441)
                    ·
                      refine ⟨3357327533898997823180581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4476436711865330430907441 3357327533898997823180581)
                      ·
                        rfl

theorem cell23_6538372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_6538372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538372 prefixEnd_6538372 := by exact prefixLift 6538372
  have htrace : WordTrace (prefixWord ++ tailWord_6538372) baseStart_6538372 baseEnd_6538372 := by
    simpa [prefixWord, tailWord_6538372, baseEnd_6538372] using wordTrace_append hprefix tailTrace_6538372
  have hstable : (prefixWord ++ tailWord_6538372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538372).length < 2 ^ (prefixWord ++ tailWord_6538372).sum := by decide
  have hdescent : baseEnd_6538372 < baseStart_6538372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538391 : List Nat := [1, 1, 3, 3, 3, 1, 1, 3, 2, 5]
def baseStart_6538391 : Nat := 118140960795 + 6538391 * 2 ^ 59
def prefixEnd_6538391 : Nat := 4983230072969 + 3 ^ 40 * 6538391 * 2
def baseEnd_6538391 : Nat := 1119112430010477749614331

theorem tailTrace_6538391 : CollatzResearch.WordTrace tailWord_6538391 prefixEnd_6538391 1119112430010477749614331 := by
  unfold tailWord_6538391
  simp only [CollatzResearch.WordTrace]
  refine ⟨238474711255533550125407027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158983140837022366750271351 238474711255533550125407027)
  ·
    refine ⟨357712066883300325188110541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238474711255533550125407027 357712066883300325188110541)
    ·
      refine ⟨134142025081237621945541453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357712066883300325188110541 134142025081237621945541453)
      ·
        refine ⟨50303259405464108229578045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134142025081237621945541453 50303259405464108229578045)
        ·
          refine ⟨18863722277049040586091767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50303259405464108229578045 18863722277049040586091767)
          ·
            refine ⟨28295583415573560879137651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18863722277049040586091767 28295583415573560879137651)
            ·
              refine ⟨42443375123360341318706477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28295583415573560879137651 42443375123360341318706477)
              ·
                refine ⟨15916265671260127994514929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42443375123360341318706477 15916265671260127994514929)
                ·
                  refine ⟨11937199253445095995886197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15916265671260127994514929 11937199253445095995886197)
                  ·
                    refine ⟨1119112430010477749614331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11937199253445095995886197 1119112430010477749614331)
                    ·
                      rfl

theorem cell23_6538391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_6538391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538391 prefixEnd_6538391 := by exact prefixLift 6538391
  have htrace : WordTrace (prefixWord ++ tailWord_6538391) baseStart_6538391 baseEnd_6538391 := by
    simpa [prefixWord, tailWord_6538391, baseEnd_6538391] using wordTrace_append hprefix tailTrace_6538391
  have hstable : (prefixWord ++ tailWord_6538391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538391).length < 2 ^ (prefixWord ++ tailWord_6538391).sum := by decide
  have hdescent : baseEnd_6538391 < baseStart_6538391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538422 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_6538422 : Nat := 118140960795 + 6538422 * 2 ^ 59
def prefixEnd_6538422 : Nat := 4983230072969 + 3 ^ 40 * 6538422 * 2
def baseEnd_6538422 : Nat := 3357353207931722627555351

theorem tailTrace_6538422 : CollatzResearch.WordTrace tailWord_6538422 prefixEnd_6538422 3357353207931722627555351 := by
  unfold tailWord_6538422
  simp only [CollatzResearch.WordTrace]
  refine ⟨14904740119901327651236595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158983894612280828279857013 14904740119901327651236595)
  ·
    refine ⟨22357110179851991476854893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14904740119901327651236595 22357110179851991476854893)
    ·
      refine ⟨8383916317444496803820585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22357110179851991476854893 8383916317444496803820585)
      ·
        refine ⟨6287937238083372602865439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8383916317444496803820585 6287937238083372602865439)
        ·
          refine ⟨9431905857125058904298159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6287937238083372602865439 9431905857125058904298159)
          ·
            refine ⟨14147858785687588356447239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9431905857125058904298159 14147858785687588356447239)
            ·
              refine ⟨21221788178531382534670859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14147858785687588356447239 21221788178531382534670859)
              ·
                refine ⟨31832682267797073802006289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21221788178531382534670859 31832682267797073802006289)
                ·
                  refine ⟨23874511700847805351504717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31832682267797073802006289 23874511700847805351504717)
                  ·
                    refine ⟨8952941887817927006814269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23874511700847805351504717 8952941887817927006814269)
                    ·
                      refine ⟨3357353207931722627555351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8952941887817927006814269 3357353207931722627555351)
                      ·
                        rfl

theorem cell23_6538422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_6538422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538422 prefixEnd_6538422 := by exact prefixLift 6538422
  have htrace : WordTrace (prefixWord ++ tailWord_6538422) baseStart_6538422 baseEnd_6538422 := by
    simpa [prefixWord, tailWord_6538422, baseEnd_6538422] using wordTrace_append hprefix tailTrace_6538422
  have hstable : (prefixWord ++ tailWord_6538422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538422).length < 2 ^ (prefixWord ++ tailWord_6538422).sum := by decide
  have hdescent : baseEnd_6538422 < baseStart_6538422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538424 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 4, 1, 6]
def baseStart_6538424 : Nat := 118140960795 + 6538424 * 2 ^ 59
def prefixEnd_6538424 : Nat := 4983230072969 + 3 ^ 40 * 6538424 * 2
def baseEnd_6538424 : Nat := 3357354234893031619730341

theorem tailTrace_6538424 : CollatzResearch.WordTrace tailWord_6538424 prefixEnd_6538424 3357354234893031619730341 := by
  unfold tailWord_6538424
  simp only [CollatzResearch.WordTrace]
  refine ⟨119237957432206998380679163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158983943242942664507572217 119237957432206998380679163)
  ·
    refine ⟨178856936148310497571018745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119237957432206998380679163 178856936148310497571018745)
    ·
      refine ⟨134142702111232873178264059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178856936148310497571018745 134142702111232873178264059)
      ·
        refine ⟨201214053166849309767396089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134142702111232873178264059 201214053166849309767396089)
        ·
          refine ⟨150910539875136982325547067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201214053166849309767396089 150910539875136982325547067)
          ·
            refine ⟨226365809812705473488320601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150910539875136982325547067 226365809812705473488320601)
            ·
              refine ⟨169774357359529105116240451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226365809812705473488320601 169774357359529105116240451)
              ·
                refine ⟨254661536039293657674360677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169774357359529105116240451 254661536039293657674360677)
                ·
                  refine ⟨47749038007367560813942627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 254661536039293657674360677 47749038007367560813942627)
                  ·
                    refine ⟨71623557011051341220913941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47749038007367560813942627 71623557011051341220913941)
                    ·
                      refine ⟨3357354234893031619730341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71623557011051341220913941 3357354234893031619730341)
                      ·
                        rfl

theorem cell23_6538424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_6538424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538424 prefixEnd_6538424 := by exact prefixLift 6538424
  have htrace : WordTrace (prefixWord ++ tailWord_6538424) baseStart_6538424 baseEnd_6538424 := by
    simpa [prefixWord, tailWord_6538424, baseEnd_6538424] using wordTrace_append hprefix tailTrace_6538424
  have hstable : (prefixWord ++ tailWord_6538424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538424).length < 2 ^ (prefixWord ++ tailWord_6538424).sum := by decide
  have hdescent : baseEnd_6538424 < baseStart_6538424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538428 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 1, 6, 2]
def baseStart_6538428 : Nat := 118140960795 + 6538428 * 2 ^ 59
def prefixEnd_6538428 : Nat := 4983230072969 + 3 ^ 40 * 6538428 * 2
def baseEnd_6538428 : Nat := 3357356288815649604080323

theorem tailTrace_6538428 : CollatzResearch.WordTrace tailWord_6538428 prefixEnd_6538428 3357356288815649604080323 := by
  unfold tailWord_6538428
  simp only [CollatzResearch.WordTrace]
  refine ⟨119238030378199752722251969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158984040504266336963002625 119238030378199752722251969)
  ·
    refine ⟨89428522783649814541688977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119238030378199752722251969 89428522783649814541688977)
    ·
      refine ⟨67071392087737360906266733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89428522783649814541688977 67071392087737360906266733)
      ·
        refine ⟨25151772032901510339850025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67071392087737360906266733 25151772032901510339850025)
        ·
          refine ⟨18863829024676132754887519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25151772032901510339850025 18863829024676132754887519)
          ·
            refine ⟨28295743537014199132331279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18863829024676132754887519 28295743537014199132331279)
            ·
              refine ⟨42443615305521298698496919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28295743537014199132331279 42443615305521298698496919)
              ·
                refine ⟨63665422958281948047745379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42443615305521298698496919 63665422958281948047745379)
                ·
                  refine ⟨95498134437422922071618069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63665422958281948047745379 95498134437422922071618069)
                  ·
                    refine ⟨4476475051754199472107097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95498134437422922071618069 4476475051754199472107097)
                    ·
                      refine ⟨3357356288815649604080323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4476475051754199472107097 3357356288815649604080323)
                      ·
                        rfl

theorem cell23_6538428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_6538428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538428 prefixEnd_6538428 := by exact prefixLift 6538428
  have htrace : WordTrace (prefixWord ++ tailWord_6538428) baseStart_6538428 baseEnd_6538428 := by
    simpa [prefixWord, tailWord_6538428, baseEnd_6538428] using wordTrace_append hprefix tailTrace_6538428
  have hstable : (prefixWord ++ tailWord_6538428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538428).length < 2 ^ (prefixWord ++ tailWord_6538428).sum := by decide
  have hdescent : baseEnd_6538428 < baseStart_6538428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538431 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 3]
def baseStart_6538431 : Nat := 118140960795 + 6538431 * 2 ^ 59
def prefixEnd_6538431 : Nat := 4983230072969 + 3 ^ 40 * 6538431 * 2
def baseEnd_6538431 : Nat := 3357357829257613092342809

theorem tailTrace_6538431 : CollatzResearch.WordTrace tailWord_6538431 prefixEnd_6538431 3357357829257613092342809 := by
  unfold tailWord_6538431
  simp only [CollatzResearch.WordTrace]
  refine ⟨238476170175388636956863147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158984113450259091304575431 238476170175388636956863147)
  ·
    refine ⟨357714255263082955435294721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238476170175388636956863147 357714255263082955435294721)
    ·
      refine ⟨268285691447312216576471041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357714255263082955435294721 268285691447312216576471041)
      ·
        refine ⟨201214268585484162432353281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268285691447312216576471041 201214268585484162432353281)
        ·
          refine ⟨150910701439113121824264961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201214268585484162432353281 150910701439113121824264961)
          ·
            refine ⟨113183026079334841368198721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150910701439113121824264961 113183026079334841368198721)
            ·
              refine ⟨84887269559501131026149041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113183026079334841368198721 84887269559501131026149041)
              ·
                refine ⟨63665452169625848269611781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84887269559501131026149041 63665452169625848269611781)
                ·
                  refine ⟨11937272281804846550552209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63665452169625848269611781 11937272281804846550552209)
                  ·
                    refine ⟨8952954211353634912914157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11937272281804846550552209 8952954211353634912914157)
                    ·
                      refine ⟨3357357829257613092342809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8952954211353634912914157 3357357829257613092342809)
                      ·
                        rfl

theorem cell23_6538431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 3].length) (baseStart_6538431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538431 prefixEnd_6538431 := by exact prefixLift 6538431
  have htrace : WordTrace (prefixWord ++ tailWord_6538431) baseStart_6538431 baseEnd_6538431 := by
    simpa [prefixWord, tailWord_6538431, baseEnd_6538431] using wordTrace_append hprefix tailTrace_6538431
  have hstable : (prefixWord ++ tailWord_6538431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538431).length < 2 ^ (prefixWord ++ tailWord_6538431).sum := by decide
  have hdescent : baseEnd_6538431 < baseStart_6538431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538531 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 6]
def baseStart_6538531 : Nat := 118140960795 + 6538531 * 2 ^ 59
def prefixEnd_6538531 : Nat := 4983230072969 + 3 ^ 40 * 6538531 * 2
def baseEnd_6538531 : Nat := 3357409177323062701092349

theorem tailTrace_6538531 : CollatzResearch.WordTrace tailWord_6538531 prefixEnd_6538531 3357409177323062701092349 := by
  unfold tailWord_6538531
  simp only [CollatzResearch.WordTrace]
  refine ⟨238479817475026354035503447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158986544983350902690335631 238479817475026354035503447)
  ·
    refine ⟨357719726212539531053255171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238479817475026354035503447 357719726212539531053255171)
    ·
      refine ⟨536579589318809296579882757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357719726212539531053255171 536579589318809296579882757)
      ·
        refine ⟨100608672997276743108728017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 536579589318809296579882757 100608672997276743108728017)
        ·
          refine ⟨75456504747957557331546013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100608672997276743108728017 75456504747957557331546013)
          ·
            refine ⟨28296189280484083999329755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75456504747957557331546013 28296189280484083999329755)
            ·
              refine ⟨42444283920726125998994633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28296189280484083999329755 42444283920726125998994633)
              ·
                refine ⟨31833212940544594499245975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42444283920726125998994633 31833212940544594499245975)
                ·
                  refine ⟨47749819410816891748868963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31833212940544594499245975 47749819410816891748868963)
                  ·
                    refine ⟨71624729116225337623303445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47749819410816891748868963 71624729116225337623303445)
                    ·
                      refine ⟨3357409177323062701092349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71624729116225337623303445 3357409177323062701092349)
                      ·
                        rfl

theorem cell23_6538531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_6538531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538531 prefixEnd_6538531 := by exact prefixLift 6538531
  have htrace : WordTrace (prefixWord ++ tailWord_6538531) baseStart_6538531 baseEnd_6538531 := by
    simpa [prefixWord, tailWord_6538531, baseEnd_6538531] using wordTrace_append hprefix tailTrace_6538531
  have hstable : (prefixWord ++ tailWord_6538531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538531).length < 2 ^ (prefixWord ++ tailWord_6538531).sum := by decide
  have hdescent : baseEnd_6538531 < baseStart_6538531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538545 : List Nat := [1, 2, 2, 3, 3, 2, 1, 3, 2, 4]
def baseStart_6538545 : Nat := 118140960795 + 6538545 * 2 ^ 59
def prefixEnd_6538545 : Nat := 4983230072969 + 3 ^ 40 * 6538545 * 2
def baseEnd_6538545 : Nat := 1119138788684075215439095

theorem tailTrace_6538545 : CollatzResearch.WordTrace tailWord_6538545 prefixEnd_6538545 1119138788684075215439095 := by
  unfold tailWord_6538545
  simp only [CollatzResearch.WordTrace]
  refine ⟨238480328096975634426513089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158986885397983756284342059 238480328096975634426513089)
  ·
    refine ⟨178860246072731725819884817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238480328096975634426513089 178860246072731725819884817)
    ·
      refine ⟨134145184554548794364913613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178860246072731725819884817 134145184554548794364913613)
      ·
        refine ⟨50304444207955797886842605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134145184554548794364913613 50304444207955797886842605)
        ·
          refine ⟨18864166577983424207565977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50304444207955797886842605 18864166577983424207565977)
          ·
            refine ⟨14148124933487568155674483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18864166577983424207565977 14148124933487568155674483)
            ·
              refine ⟨21222187400231352233511725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14148124933487568155674483 21222187400231352233511725)
              ·
                refine ⟨7958320275086757087566897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21222187400231352233511725 7958320275086757087566897)
                ·
                  refine ⟨5968740206315067815675173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7958320275086757087566897 5968740206315067815675173)
                  ·
                    refine ⟨1119138788684075215439095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5968740206315067815675173 1119138788684075215439095)
                    ·
                      rfl

theorem cell23_6538545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 4].length) (baseStart_6538545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538545 prefixEnd_6538545 := by exact prefixLift 6538545
  have htrace : WordTrace (prefixWord ++ tailWord_6538545) baseStart_6538545 baseEnd_6538545 := by
    simpa [prefixWord, tailWord_6538545, baseEnd_6538545] using wordTrace_append hprefix tailTrace_6538545
  have hstable : (prefixWord ++ tailWord_6538545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538545).length < 2 ^ (prefixWord ++ tailWord_6538545).sum := by decide
  have hdescent : baseEnd_6538545 < baseStart_6538545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538548 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_6538548 : Nat := 118140960795 + 6538548 * 2 ^ 59
def prefixEnd_6538548 : Nat := 4983230072969 + 3 ^ 40 * 6538548 * 2
def baseEnd_6538548 : Nat := 3357417906494189134579771

theorem tailTrace_6538548 : CollatzResearch.WordTrace tailWord_6538548 prefixEnd_6538548 3357417906494189134579771 := by
  unfold tailWord_6538548
  simp only [CollatzResearch.WordTrace]
  refine ⟨119240218757982382969436149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158986958343976510625914865 119240218757982382969436149)
  ·
    refine ⟨11178770508560848403384639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119240218757982382969436149 11178770508560848403384639)
    ·
      refine ⟨16768155762841272605076959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11178770508560848403384639 16768155762841272605076959)
      ·
        refine ⟨25152233644261908907615439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16768155762841272605076959 25152233644261908907615439)
        ·
          refine ⟨37728350466392863361423159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25152233644261908907615439 37728350466392863361423159)
          ·
            refine ⟨56592525699589295042134739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37728350466392863361423159 56592525699589295042134739)
            ·
              refine ⟨84888788549383942563202109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56592525699589295042134739 84888788549383942563202109)
              ·
                refine ⟨31833295706018978461200791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84888788549383942563202109 31833295706018978461200791)
                ·
                  refine ⟨47749943559028467691801187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31833295706018978461200791 47749943559028467691801187)
                  ·
                    refine ⟨71624915338542701537701781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47749943559028467691801187 71624915338542701537701781)
                    ·
                      refine ⟨3357417906494189134579771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71624915338542701537701781 3357417906494189134579771)
                      ·
                        rfl

theorem cell23_6538548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_6538548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538548 prefixEnd_6538548 := by exact prefixLift 6538548
  have htrace : WordTrace (prefixWord ++ tailWord_6538548) baseStart_6538548 baseEnd_6538548 := by
    simpa [prefixWord, tailWord_6538548, baseEnd_6538548] using wordTrace_append hprefix tailTrace_6538548
  have hstable : (prefixWord ++ tailWord_6538548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538548).length < 2 ^ (prefixWord ++ tailWord_6538548).sum := by decide
  have hdescent : baseEnd_6538548 < baseStart_6538548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538566 : List Nat := [6, 1, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_6538566 : Nat := 118140960795 + 6538566 * 2 ^ 59
def prefixEnd_6538566 : Nat := 4983230072969 + 3 ^ 40 * 6538566 * 2
def baseEnd_6538566 : Nat := 1119142383048656688051563

theorem tailTrace_6538566 : CollatzResearch.WordTrace tailWord_6538566 prefixEnd_6538566 1119142383048656688051563 := by
  unfold tailWord_6538566
  simp only [CollatzResearch.WordTrace]
  refine ⟨7452534188434361094157111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 158987396019933036675351701 7452534188434361094157111)
  ·
    refine ⟨11178801282651541641235667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7452534188434361094157111 11178801282651541641235667)
    ·
      refine ⟨16768201923977312461853501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11178801282651541641235667 16768201923977312461853501)
      ·
        refine ⟨6288075721491492173195063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16768201923977312461853501 6288075721491492173195063)
        ·
          refine ⟨9432113582237238259792595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6288075721491492173195063 9432113582237238259792595)
          ·
            refine ⟨14148170373355857389688893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9432113582237238259792595 14148170373355857389688893)
            ·
              refine ⟨5305563890008446521133335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14148170373355857389688893 5305563890008446521133335)
              ·
                refine ⟨7958345835012669781700003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5305563890008446521133335 7958345835012669781700003)
                ·
                  refine ⟨11937518752519004672550005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7958345835012669781700003 11937518752519004672550005)
                  ·
                    refine ⟨1119142383048656688051563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11937518752519004672550005 1119142383048656688051563)
                    ·
                      rfl

theorem cell23_6538566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_6538566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538566 prefixEnd_6538566 := by exact prefixLift 6538566
  have htrace : WordTrace (prefixWord ++ tailWord_6538566) baseStart_6538566 baseEnd_6538566 := by
    simpa [prefixWord, tailWord_6538566, baseEnd_6538566] using wordTrace_append hprefix tailTrace_6538566
  have hstable : (prefixWord ++ tailWord_6538566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538566).length < 2 ^ (prefixWord ++ tailWord_6538566).sum := by decide
  have hdescent : baseEnd_6538566 < baseStart_6538566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538572 : List Nat := [2, 2, 1, 3, 2, 3, 3, 1, 1, 2, 3]
def baseStart_6538572 : Nat := 118140960795 + 6538572 * 2 ^ 59
def prefixEnd_6538572 : Nat := 4983230072969 + 3 ^ 40 * 6538572 * 2
def baseEnd_6538572 : Nat := 3357430230029897040679661

theorem tailTrace_6538572 : CollatzResearch.WordTrace tailWord_6538572 prefixEnd_6538572 3357430230029897040679661 := by
  unfold tailWord_6538572
  simp only [CollatzResearch.WordTrace]
  refine ⟨119240656433938909018872985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158987541911918545358497313 119240656433938909018872985)
  ·
    refine ⟨89430492325454181764154739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119240656433938909018872985 89430492325454181764154739)
    ·
      refine ⟨134145738488181272646232109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89430492325454181764154739 134145738488181272646232109)
      ·
        refine ⟨50304651933067977242337041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134145738488181272646232109 50304651933067977242337041)
        ·
          refine ⟨37728488949800982931752781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50304651933067977242337041 37728488949800982931752781)
          ·
            refine ⟨14148183356175368599407293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37728488949800982931752781 14148183356175368599407293)
            ·
              refine ⟨5305568758565763224777735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14148183356175368599407293 5305568758565763224777735)
              ·
                refine ⟨7958353137848644837166603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5305568758565763224777735 7958353137848644837166603)
                ·
                  refine ⟨11937529706772967255749905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7958353137848644837166603 11937529706772967255749905)
                  ·
                    refine ⟨8953147280079725441812429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11937529706772967255749905 8953147280079725441812429)
                    ·
                      refine ⟨3357430230029897040679661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8953147280079725441812429 3357430230029897040679661)
                      ·
                        rfl

theorem cell23_6538572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_6538572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538572 prefixEnd_6538572 := by exact prefixLift 6538572
  have htrace : WordTrace (prefixWord ++ tailWord_6538572) baseStart_6538572 baseEnd_6538572 := by
    simpa [prefixWord, tailWord_6538572, baseEnd_6538572] using wordTrace_append hprefix tailTrace_6538572
  have hstable : (prefixWord ++ tailWord_6538572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538572).length < 2 ^ (prefixWord ++ tailWord_6538572).sum := by decide
  have hdescent : baseEnd_6538572 < baseStart_6538572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538585 : List Nat := [1, 2, 1, 2, 2, 2, 3, 4, 2, 1, 3]
def baseStart_6538585 : Nat := 118140960795 + 6538585 * 2 ^ 59
def prefixEnd_6538585 : Nat := 4983230072969 + 3 ^ 40 * 6538585 * 2
def baseEnd_6538585 : Nat := 3357436905278405489817101

theorem tailTrace_6538585 : CollatzResearch.WordTrace tailWord_6538585 prefixEnd_6538585 3357436905278405489817101 := by
  unfold tailWord_6538585
  simp only [CollatzResearch.WordTrace]
  refine ⟨238481787016830721257969209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158987858011220480838646139 238481787016830721257969209)
  ·
    refine ⟨178861340262623040943476907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238481787016830721257969209 178861340262623040943476907)
    ·
      refine ⟨268292010393934561415215361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178861340262623040943476907 268292010393934561415215361)
      ·
        refine ⟨201219007795450921061411521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268292010393934561415215361 201219007795450921061411521)
        ·
          refine ⟨150914255846588190796058641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201219007795450921061411521 150914255846588190796058641)
          ·
            refine ⟨113185691884941143097043981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150914255846588190796058641 113185691884941143097043981)
            ·
              refine ⟨42444634456852928661391493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113185691884941143097043981 42444634456852928661391493)
              ·
                refine ⟨7958368960659924124010905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42444634456852928661391493 7958368960659924124010905)
                ·
                  refine ⟨5968776720494943093008179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7958368960659924124010905 5968776720494943093008179)
                  ·
                    refine ⟨8953165080742414639512269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5968776720494943093008179 8953165080742414639512269)
                    ·
                      refine ⟨3357436905278405489817101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8953165080742414639512269 3357436905278405489817101)
                      ·
                        rfl

theorem cell23_6538585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 1, 3].length) (baseStart_6538585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538585 prefixEnd_6538585 := by exact prefixLift 6538585
  have htrace : WordTrace (prefixWord ++ tailWord_6538585) baseStart_6538585 baseEnd_6538585 := by
    simpa [prefixWord, tailWord_6538585, baseEnd_6538585] using wordTrace_append hprefix tailTrace_6538585
  have hstable : (prefixWord ++ tailWord_6538585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538585).length < 2 ^ (prefixWord ++ tailWord_6538585).sum := by decide
  have hdescent : baseEnd_6538585 < baseStart_6538585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538595 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 3, 3, 2]
def baseStart_6538595 : Nat := 118140960795 + 6538595 * 2 ^ 59
def prefixEnd_6538595 : Nat := 4983230072969 + 3 ^ 40 * 6538595 * 2
def baseEnd_6538595 : Nat := 3357442040084950450692055

theorem tailTrace_6538595 : CollatzResearch.WordTrace tailWord_6538595 prefixEnd_6538595 3357442040084950450692055 := by
  unfold tailWord_6538595
  simp only [CollatzResearch.WordTrace]
  refine ⟨238482151746794492965833239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158988101164529661977222159 238482151746794492965833239)
  ·
    refine ⟨357723227620191739448749859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238482151746794492965833239 357723227620191739448749859)
    ·
      refine ⟨536584841430287609173124789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357723227620191739448749859 536584841430287609173124789)
      ·
        refine ⟨50304828884089463359980449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 536584841430287609173124789 50304828884089463359980449)
        ·
          refine ⟨37728621663067097519985337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50304828884089463359980449 37728621663067097519985337)
          ·
            refine ⟨28296466247300323139989003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37728621663067097519985337 28296466247300323139989003)
            ·
              refine ⟨42444699370950484709983505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28296466247300323139989003 42444699370950484709983505)
              ·
                refine ⟨31833524528212863532487629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42444699370950484709983505 31833524528212863532487629)
                ·
                  refine ⟨11937571698079823824682861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31833524528212863532487629 11937571698079823824682861)
                  ·
                    refine ⟨4476589386779933934256073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11937571698079823824682861 4476589386779933934256073)
                    ·
                      refine ⟨3357442040084950450692055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4476589386779933934256073 3357442040084950450692055)
                      ·
                        rfl

theorem cell23_6538595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_6538595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538595 prefixEnd_6538595 := by exact prefixLift 6538595
  have htrace : WordTrace (prefixWord ++ tailWord_6538595) baseStart_6538595 baseEnd_6538595 := by
    simpa [prefixWord, tailWord_6538595, baseEnd_6538595] using wordTrace_append hprefix tailTrace_6538595
  have hstable : (prefixWord ++ tailWord_6538595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538595).length < 2 ^ (prefixWord ++ tailWord_6538595).sum := by decide
  have hdescent : baseEnd_6538595 < baseStart_6538595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538602 : List Nat := [3, 1, 3, 3, 2, 1, 2, 1, 1, 3, 3]
def baseStart_6538602 : Nat := 118140960795 + 6538602 * 2 ^ 59
def prefixEnd_6538602 : Nat := 4983230072969 + 3 ^ 40 * 6538602 * 2
def baseEnd_6538602 : Nat := 3357445634449531923304523

theorem tailTrace_6538602 : CollatzResearch.WordTrace tailWord_6538602 prefixEnd_6538602 3357445634449531923304523 := by
  unfold tailWord_6538602
  simp only [CollatzResearch.WordTrace]
  refine ⟨59620601764442283290334515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158988271371846088774225373 59620601764442283290334515)
  ·
    refine ⟨89430902646663424935501773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59620601764442283290334515 89430902646663424935501773)
    ·
      refine ⟨33536588492498784350813165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89430902646663424935501773 33536588492498784350813165)
      ·
        refine ⟨12576220684687044131554937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33536588492498784350813165 12576220684687044131554937)
        ·
          refine ⟨9432165513515283098666203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12576220684687044131554937 9432165513515283098666203)
          ·
            refine ⟨14148248270272924647999305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9432165513515283098666203 14148248270272924647999305)
            ·
              refine ⟨10611186202704693485999479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14148248270272924647999305 10611186202704693485999479)
              ·
                refine ⟨15916779304057040228999219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10611186202704693485999479 15916779304057040228999219)
                ·
                  refine ⟨23875168956085560343498829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15916779304057040228999219 23875168956085560343498829)
                  ·
                    refine ⟨8953188358532085128812061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23875168956085560343498829 8953188358532085128812061)
                    ·
                      refine ⟨3357445634449531923304523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8953188358532085128812061 3357445634449531923304523)
                      ·
                        rfl

theorem cell23_6538602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_6538602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538602 prefixEnd_6538602 := by exact prefixLift 6538602
  have htrace : WordTrace (prefixWord ++ tailWord_6538602) baseStart_6538602 baseEnd_6538602 := by
    simpa [prefixWord, tailWord_6538602, baseEnd_6538602] using wordTrace_append hprefix tailTrace_6538602
  have hstable : (prefixWord ++ tailWord_6538602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538602).length < 2 ^ (prefixWord ++ tailWord_6538602).sum := by decide
  have hdescent : baseEnd_6538602 < baseStart_6538602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538641 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 7]
def baseStart_6538641 : Nat := 118140960795 + 6538641 * 2 ^ 59
def prefixEnd_6538641 : Nat := 4983230072969 + 3 ^ 40 * 6538641 * 2
def baseEnd_6538641 : Nat := 3357465660195057270716843

theorem tailTrace_6538641 : CollatzResearch.WordTrace tailWord_6538641 prefixEnd_6538641 3357465660195057270716843 := by
  unfold tailWord_6538641
  simp only [CollatzResearch.WordTrace]
  refine ⟨238483829504627842822007777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158989219669751895214671851 238483829504627842822007777)
  ·
    refine ⟨178862872128470882116505833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238483829504627842822007777 178862872128470882116505833)
    ·
      refine ⟨134147154096353161587379375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178862872128470882116505833 134147154096353161587379375)
      ·
        refine ⟨201220731144529742381069063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134147154096353161587379375 201220731144529742381069063)
        ·
          refine ⟨301831096716794613571603595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201220731144529742381069063 301831096716794613571603595)
          ·
            refine ⟨452746645075191920357405393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301831096716794613571603595 452746645075191920357405393)
            ·
              refine ⟨339559983806393940268054045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452746645075191920357405393 339559983806393940268054045)
              ·
                refine ⟨127334993927397727600520267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339559983806393940268054045 127334993927397727600520267)
                ·
                  refine ⟨191002490891096591400780401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127334993927397727600520267 191002490891096591400780401)
                  ·
                    refine ⟨143251868168322443550585301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 191002490891096591400780401 143251868168322443550585301)
                    ·
                      refine ⟨3357465660195057270716843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143251868168322443550585301 3357465660195057270716843)
                      ·
                        rfl

theorem cell23_6538641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_6538641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538641 prefixEnd_6538641 := by exact prefixLift 6538641
  have htrace : WordTrace (prefixWord ++ tailWord_6538641) baseStart_6538641 baseEnd_6538641 := by
    simpa [prefixWord, tailWord_6538641, baseEnd_6538641] using wordTrace_append hprefix tailTrace_6538641
  have hstable : (prefixWord ++ tailWord_6538641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538641).length < 2 ^ (prefixWord ++ tailWord_6538641).sum := by decide
  have hdescent : baseEnd_6538641 < baseStart_6538641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538659 : List Nat := [1, 1, 1, 4, 1, 3, 5, 1, 2, 2, 2]
def baseStart_6538659 : Nat := 118140960795 + 6538659 * 2 ^ 59
def prefixEnd_6538659 : Nat := 4983230072969 + 3 ^ 40 * 6538659 * 2
def baseEnd_6538659 : Nat := 3357474902846838200291761

theorem tailTrace_6538659 : CollatzResearch.WordTrace tailWord_6538659 prefixEnd_6538659 3357474902846838200291761 := by
  unfold tailWord_6538659
  simp only [CollatzResearch.WordTrace]
  refine ⟨238484486018562631896163031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158989657345708421264108687 238484486018562631896163031)
  ·
    refine ⟨357726729027843947844244547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238484486018562631896163031 357726729027843947844244547)
    ·
      refine ⟨536590093541765921766366821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357726729027843947844244547 536590093541765921766366821)
      ·
        refine ⟨100610642539081110331193779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 536590093541765921766366821 100610642539081110331193779)
        ·
          refine ⟨150915963808621665496790669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100610642539081110331193779 150915963808621665496790669)
          ·
            refine ⟨56593486428233124561296501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150915963808621665496790669 56593486428233124561296501)
            ·
              refine ⟨5305639352646855427621547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56593486428233124561296501 5305639352646855427621547)
              ·
                refine ⟨7958459028970283141432321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5305639352646855427621547 7958459028970283141432321)
                ·
                  refine ⟨5968844271727712356074241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7958459028970283141432321 5968844271727712356074241)
                  ·
                    refine ⟨4476633203795784267055681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5968844271727712356074241 4476633203795784267055681)
                    ·
                      refine ⟨3357474902846838200291761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4476633203795784267055681 3357474902846838200291761)
                      ·
                        rfl

theorem cell23_6538659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_6538659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538659 prefixEnd_6538659 := by exact prefixLift 6538659
  have htrace : WordTrace (prefixWord ++ tailWord_6538659) baseStart_6538659 baseEnd_6538659 := by
    simpa [prefixWord, tailWord_6538659, baseEnd_6538659] using wordTrace_append hprefix tailTrace_6538659
  have hstable : (prefixWord ++ tailWord_6538659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538659).length < 2 ^ (prefixWord ++ tailWord_6538659).sum := by decide
  have hdescent : baseEnd_6538659 < baseStart_6538659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538735 : List Nat := [1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 3]
def baseStart_6538735 : Nat := 118140960795 + 6538735 * 2 ^ 59
def prefixEnd_6538735 : Nat := 4983230072969 + 3 ^ 40 * 6538735 * 2
def baseEnd_6538735 : Nat := 3357513927376579902941411

theorem tailTrace_6538735 : CollatzResearch.WordTrace tailWord_6538735 prefixEnd_6538735 3357513927376579902941411 := by
  unfold tailWord_6538735
  simp only [CollatzResearch.WordTrace]
  refine ⟨238487257966287296875929659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158991505310858197917286439 238487257966287296875929659)
  ·
    refine ⟨357730886949430945313894489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238487257966287296875929659 357730886949430945313894489)
    ·
      refine ⟨268298165212073208985420867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357730886949430945313894489 268298165212073208985420867)
      ·
        refine ⟨402447247818109813478131301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268298165212073208985420867 402447247818109813478131301)
        ·
          refine ⟨75458858965895590027149619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 402447247818109813478131301 75458858965895590027149619)
          ·
            refine ⟨113188288448843385040724429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75458858965895590027149619 113188288448843385040724429)
            ·
              refine ⟨42445608168316269390271661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113188288448843385040724429 42445608168316269390271661)
              ·
                refine ⟨15917103063118601021351873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42445608168316269390271661 15917103063118601021351873)
                ·
                  refine ⟨11937827297338950766013905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15917103063118601021351873 11937827297338950766013905)
                  ·
                    refine ⟨8953370473004213074510429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11937827297338950766013905 8953370473004213074510429)
                    ·
                      refine ⟨3357513927376579902941411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8953370473004213074510429 3357513927376579902941411)
                      ·
                        rfl

theorem cell23_6538735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 3].length) (baseStart_6538735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538735 prefixEnd_6538735 := by exact prefixLift 6538735
  have htrace : WordTrace (prefixWord ++ tailWord_6538735) baseStart_6538735 baseEnd_6538735 := by
    simpa [prefixWord, tailWord_6538735, baseEnd_6538735] using wordTrace_append hprefix tailTrace_6538735
  have hstable : (prefixWord ++ tailWord_6538735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538735).length < 2 ^ (prefixWord ++ tailWord_6538735).sum := by decide
  have hdescent : baseEnd_6538735 < baseStart_6538735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538759 : List Nat := [1, 1, 4, 3, 2, 2, 1, 4, 1, 4]
def baseStart_6538759 : Nat := 118140960795 + 6538759 * 2 ^ 59
def prefixEnd_6538759 : Nat := 4983230072969 + 3 ^ 40 * 6538759 * 2
def baseEnd_6538759 : Nat := 1119175416970762603013767

theorem tailTrace_6538759 : CollatzResearch.WordTrace tailWord_6538759 prefixEnd_6538759 1119175416970762603013767 := by
  unfold tailWord_6538759
  simp only [CollatzResearch.WordTrace]
  refine ⟨238488133318200348974803331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158992088878800232649868887 238488133318200348974803331)
  ·
    refine ⟨357732199977300523462204997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238488133318200348974803331 357732199977300523462204997)
    ·
      refine ⟨67074787495743848149163437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 357732199977300523462204997 67074787495743848149163437)
      ·
        refine ⟨25153045310903943055936289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67074787495743848149163437 25153045310903943055936289)
        ·
          refine ⟨18864783983177957291952217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25153045310903943055936289 18864783983177957291952217)
          ·
            refine ⟨14148587987383467968964163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18864783983177957291952217 14148587987383467968964163)
            ·
              refine ⟨21222881981075201953446245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14148587987383467968964163 21222881981075201953446245)
              ·
                refine ⟨3979290371451600366271171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21222881981075201953446245 3979290371451600366271171)
                ·
                  refine ⟨5968935557177400549406757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3979290371451600366271171 5968935557177400549406757)
                  ·
                    refine ⟨1119175416970762603013767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5968935557177400549406757 1119175416970762603013767)
                    ·
                      rfl

theorem cell23_6538759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_6538759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538759 prefixEnd_6538759 := by exact prefixLift 6538759
  have htrace : WordTrace (prefixWord ++ tailWord_6538759) baseStart_6538759 baseEnd_6538759 := by
    simpa [prefixWord, tailWord_6538759, baseEnd_6538759] using wordTrace_append hprefix tailTrace_6538759
  have hstable : (prefixWord ++ tailWord_6538759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538759).length < 2 ^ (prefixWord ++ tailWord_6538759).sum := by decide
  have hdescent : baseEnd_6538759 < baseStart_6538759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538778 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7]
def baseStart_6538778 : Nat := 118140960795 + 6538778 * 2 ^ 59
def prefixEnd_6538778 : Nat := 4983230072969 + 3 ^ 40 * 6538778 * 2
def baseEnd_6538778 : Nat := 3357536007044723234703713

theorem tailTrace_6538778 : CollatzResearch.WordTrace tailWord_6538778 prefixEnd_6538778 3357536007044723234703713 := by
  unfold tailWord_6538778
  simp only [CollatzResearch.WordTrace]
  refine ⟨59622206576282878804936247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158992550870087676813163325 59622206576282878804936247)
  ·
    refine ⟨89433309864424318207404371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59622206576282878804936247 89433309864424318207404371)
    ·
      refine ⟨134149964796636477311106557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89433309864424318207404371 134149964796636477311106557)
      ·
        refine ⟨50306236798738678991664959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134149964796636477311106557 50306236798738678991664959)
        ·
          refine ⟨75459355198108018487497439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50306236798738678991664959 75459355198108018487497439)
          ·
            refine ⟨113189032797162027731246159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75459355198108018487497439 113189032797162027731246159)
            ·
              refine ⟨169783549195743041596869239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113189032797162027731246159 169783549195743041596869239)
              ·
                refine ⟨254675323793614562395303859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169783549195743041596869239 254675323793614562395303859)
                ·
                  refine ⟨382012985690421843592955789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 254675323793614562395303859 382012985690421843592955789)
                  ·
                    refine ⟨143254869633908191347358421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 382012985690421843592955789 143254869633908191347358421)
                    ·
                      refine ⟨3357536007044723234703713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143254869633908191347358421 3357536007044723234703713)
                      ·
                        rfl

theorem cell23_6538778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_6538778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538778 prefixEnd_6538778 := by exact prefixLift 6538778
  have htrace : WordTrace (prefixWord ++ tailWord_6538778) baseStart_6538778 baseEnd_6538778 := by
    simpa [prefixWord, tailWord_6538778, baseEnd_6538778] using wordTrace_append hprefix tailTrace_6538778
  have hstable : (prefixWord ++ tailWord_6538778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538778).length < 2 ^ (prefixWord ++ tailWord_6538778).sum := by decide
  have hdescent : baseEnd_6538778 < baseStart_6538778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538785 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 3, 5]
def baseStart_6538785 : Nat := 118140960795 + 6538785 * 2 ^ 59
def prefixEnd_6538785 : Nat := 4983230072969 + 3 ^ 40 * 6538785 * 2
def baseEnd_6538785 : Nat := 1119179867136434902438727

theorem tailTrace_6538785 : CollatzResearch.WordTrace tailWord_6538785 prefixEnd_6538785 1119179867136434902438727 := by
  unfold tailWord_6538785
  simp only [CollatzResearch.WordTrace]
  refine ⟨238489081616106155415249809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158992721077404103610166539 238489081616106155415249809)
  ·
    refine ⟨178866811212079616561437357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238489081616106155415249809 178866811212079616561437357)
    ·
      refine ⟨67075054204529856210539009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178866811212079616561437357 67075054204529856210539009)
      ·
        refine ⟨50306290653397392157904257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67075054204529856210539009 50306290653397392157904257)
        ·
          refine ⟨37729717990048044118428193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50306290653397392157904257 37729717990048044118428193)
          ·
            refine ⟨28297288492536033088821145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37729717990048044118428193 28297288492536033088821145)
            ·
              refine ⟨21222966369402024816615859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28297288492536033088821145 21222966369402024816615859)
              ·
                refine ⟨31834449554103037224923789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21222966369402024816615859 31834449554103037224923789)
                ·
                  refine ⟨11937918582788638959346421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31834449554103037224923789 11937918582788638959346421)
                  ·
                    refine ⟨1119179867136434902438727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11937918582788638959346421 1119179867136434902438727)
                    ·
                      rfl

theorem cell23_6538785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_6538785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538785 prefixEnd_6538785 := by exact prefixLift 6538785
  have htrace : WordTrace (prefixWord ++ tailWord_6538785) baseStart_6538785 baseEnd_6538785 := by
    simpa [prefixWord, tailWord_6538785, baseEnd_6538785] using wordTrace_append hprefix tailTrace_6538785
  have hstable : (prefixWord ++ tailWord_6538785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538785).length < 2 ^ (prefixWord ++ tailWord_6538785).sum := by decide
  have hdescent : baseEnd_6538785 < baseStart_6538785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538806 : List Nat := [5, 1, 2, 1, 4, 1, 1, 2, 6]
def baseStart_6538806 : Nat := 118140960795 + 6538806 * 2 ^ 59
def prefixEnd_6538806 : Nat := 4983230072969 + 3 ^ 40 * 6538806 * 2
def baseEnd_6538806 : Nat := 373061153833672125017065

theorem tailTrace_6538806 : CollatzResearch.WordTrace tailWord_6538806 prefixEnd_6538806 373061153833672125017065 := by
  unfold tailWord_6538806
  simp only [CollatzResearch.WordTrace]
  refine ⟨14905615471814379750110267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158993231699353384001176181 14905615471814379750110267)
  ·
    refine ⟨22358423207721569625165401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14905615471814379750110267 22358423207721569625165401)
    ·
      refine ⟨16768817405791177218874051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22358423207721569625165401 16768817405791177218874051)
      ·
        refine ⟨25153226108686765828311077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16768817405791177218874051 25153226108686765828311077)
        ·
          refine ⟨4716229895378768592808327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25153226108686765828311077 4716229895378768592808327)
          ·
            refine ⟨7074344843068152889212491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4716229895378768592808327 7074344843068152889212491)
            ·
              refine ⟨10611517264602229333818737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7074344843068152889212491 10611517264602229333818737)
              ·
                refine ⟨7958637948451672000364053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10611517264602229333818737 7958637948451672000364053)
                ·
                  refine ⟨373061153833672125017065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7958637948451672000364053 373061153833672125017065)
                  ·
                    rfl

theorem cell23_6538806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_6538806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538806 prefixEnd_6538806 := by exact prefixLift 6538806
  have htrace : WordTrace (prefixWord ++ tailWord_6538806) baseStart_6538806 baseEnd_6538806 := by
    simpa [prefixWord, tailWord_6538806, baseEnd_6538806] using wordTrace_append hprefix tailTrace_6538806
  have hstable : (prefixWord ++ tailWord_6538806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538806).length < 2 ^ (prefixWord ++ tailWord_6538806).sum := by decide
  have hdescent : baseEnd_6538806 < baseStart_6538806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538825 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 5, 2, 3]
def baseStart_6538825 : Nat := 118140960795 + 6538825 * 2 ^ 59
def prefixEnd_6538825 : Nat := 4983230072969 + 3 ^ 40 * 6538825 * 2
def baseEnd_6538825 : Nat := 3357560140635484550815997

theorem tailTrace_6538825 : CollatzResearch.WordTrace tailWord_6538825 prefixEnd_6538825 3357560140635484550815997 := by
  unfold tailWord_6538825
  simp only [CollatzResearch.WordTrace]
  refine ⟨238490540535961242246705929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158993693690640828164470619 238490540535961242246705929)
  ·
    refine ⟨178867905401970931685029447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238490540535961242246705929 178867905401970931685029447)
    ·
      refine ⟨268301858102956397527544171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178867905401970931685029447 268301858102956397527544171)
      ·
        refine ⟨402452787154434596291316257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268301858102956397527544171 402452787154434596291316257)
        ·
          refine ⟨301839590365825947218487193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402452787154434596291316257 301839590365825947218487193)
          ·
            refine ⟨226379692774369460413865395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301839590365825947218487193 226379692774369460413865395)
            ·
              refine ⟨339569539161554190620798093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226379692774369460413865395 339569539161554190620798093)
              ·
                refine ⟨127338577185582821482799285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339569539161554190620798093 127338577185582821482799285)
                ·
                  refine ⟨11937991611148389514012433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127338577185582821482799285 11937991611148389514012433)
                  ·
                    refine ⟨8953493708361292135509325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11937991611148389514012433 8953493708361292135509325)
                    ·
                      refine ⟨3357560140635484550815997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8953493708361292135509325 3357560140635484550815997)
                      ·
                        rfl

theorem cell23_6538825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 2, 3].length) (baseStart_6538825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538825 prefixEnd_6538825 := by exact prefixLift 6538825
  have htrace : WordTrace (prefixWord ++ tailWord_6538825) baseStart_6538825 baseEnd_6538825 := by
    simpa [prefixWord, tailWord_6538825, baseEnd_6538825] using wordTrace_append hprefix tailTrace_6538825
  have hstable : (prefixWord ++ tailWord_6538825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538825).length < 2 ^ (prefixWord ++ tailWord_6538825).sum := by decide
  have hdescent : baseEnd_6538825 < baseStart_6538825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538839 : List Nat := [1, 1, 3, 2, 2, 3, 2, 2, 3, 2, 2]
def baseStart_6538839 : Nat := 118140960795 + 6538839 * 2 ^ 59
def prefixEnd_6538839 : Nat := 4983230072969 + 3 ^ 40 * 6538839 * 2
def baseEnd_6538839 : Nat := 3357567329364647496040933

theorem tailTrace_6538839 : CollatzResearch.WordTrace tailWord_6538839 prefixEnd_6538839 3357567329364647496040933 := by
  unfold tailWord_6538839
  simp only [CollatzResearch.WordTrace]
  refine ⟨238491051157910522637715571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158994034105273681758477047 238491051157910522637715571)
  ·
    refine ⟨357736576736865783956573357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238491051157910522637715571 357736576736865783956573357)
    ·
      refine ⟨134151216276324668983715009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357736576736865783956573357 134151216276324668983715009)
      ·
        refine ⟨100613412207243501737786257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134151216276324668983715009 100613412207243501737786257)
        ·
          refine ⟨75460059155432626303339693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100613412207243501737786257 75460059155432626303339693)
          ·
            refine ⟨28297522183287234863752385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75460059155432626303339693 28297522183287234863752385)
            ·
              refine ⟨21223141637465426147814289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28297522183287234863752385 21223141637465426147814289)
              ·
                refine ⟨15917356228099069610860717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21223141637465426147814289 15917356228099069610860717)
                ·
                  refine ⟨5969008585537151104072769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15917356228099069610860717 5969008585537151104072769)
                  ·
                    refine ⟨4476756439152863328054577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5969008585537151104072769 4476756439152863328054577)
                    ·
                      refine ⟨3357567329364647496040933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4476756439152863328054577 3357567329364647496040933)
                      ·
                        rfl

theorem cell23_6538839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_6538839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538839 prefixEnd_6538839 := by exact prefixLift 6538839
  have htrace : WordTrace (prefixWord ++ tailWord_6538839) baseStart_6538839 baseEnd_6538839 := by
    simpa [prefixWord, tailWord_6538839, baseEnd_6538839] using wordTrace_append hprefix tailTrace_6538839
  have hstable : (prefixWord ++ tailWord_6538839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538839).length < 2 ^ (prefixWord ++ tailWord_6538839).sum := by decide
  have hdescent : baseEnd_6538839 < baseStart_6538839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538862 : List Nat := [4, 1, 2, 2, 3, 2, 9]
def baseStart_6538862 : Nat := 118140960795 + 6538862 * 2 ^ 59
def prefixEnd_6538862 : Nat := 4983230072969 + 3 ^ 40 * 6538862 * 2
def baseEnd_6538862 : Nat := 41451594313823467975967

theorem tailTrace_6538862 : CollatzResearch.WordTrace tailWord_6538862 prefixEnd_6538862 41451594313823467975967 := by
  unfold tailWord_6538862
  simp only [CollatzResearch.WordTrace]
  refine ⟨29811486254603399695725355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158994593357884798377201893 29811486254603399695725355)
  ·
    refine ⟨44717229381905099543588033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29811486254603399695725355 44717229381905099543588033)
    ·
      refine ⟨33537922036428824657691025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44717229381905099543588033 33537922036428824657691025)
      ·
        refine ⟨25153441527321618493268269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33537922036428824657691025 25153441527321618493268269)
        ·
          refine ⟨9432540572745606934975601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25153441527321618493268269 9432540572745606934975601)
          ·
            refine ⟨7074405429559205201231701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9432540572745606934975601 7074405429559205201231701)
            ·
              refine ⟨41451594313823467975967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7074405429559205201231701 41451594313823467975967)
              ·
                rfl

theorem cell23_6538862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 9].length) (baseStart_6538862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538862 prefixEnd_6538862 := by exact prefixLift 6538862
  have htrace : WordTrace (prefixWord ++ tailWord_6538862) baseStart_6538862 baseEnd_6538862 := by
    simpa [prefixWord, tailWord_6538862, baseEnd_6538862] using wordTrace_append hprefix tailTrace_6538862
  have hstable : (prefixWord ++ tailWord_6538862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538862).length < 2 ^ (prefixWord ++ tailWord_6538862).sum := by decide
  have hdescent : baseEnd_6538862 < baseStart_6538862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538873 : List Nat := [1, 2, 1, 3, 3, 1, 5, 2, 1, 2, 2]
def baseStart_6538873 : Nat := 118140960795 + 6538873 * 2 ^ 59
def prefixEnd_6538873 : Nat := 4983230072969 + 3 ^ 40 * 6538873 * 2
def baseEnd_6538873 : Nat := 3357584787706900363015777

theorem tailTrace_6538873 : CollatzResearch.WordTrace tailWord_6538873 prefixEnd_6538873 3357584787706900363015777 := by
  unfold tailWord_6538873
  simp only [CollatzResearch.WordTrace]
  refine ⟨238492291239787346444453273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158994860826524897629635515 238492291239787346444453273)
  ·
    refine ⟨178869218429840509833339955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238492291239787346444453273 178869218429840509833339955)
    ·
      refine ⟨268303827644760764750009933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178869218429840509833339955 268303827644760764750009933)
      ·
        refine ⟨100613935366785286781253725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268303827644760764750009933 100613935366785286781253725)
        ·
          refine ⟨37730225762544482542970147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100613935366785286781253725 37730225762544482542970147)
          ·
            refine ⟨56595338643816723814455221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37730225762544482542970147 56595338643816723814455221)
            ·
              refine ⟨5305812997857817857605177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56595338643816723814455221 5305812997857817857605177)
              ·
                refine ⟨3979359748393363393203883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5305812997857817857605177 3979359748393363393203883)
                ·
                  refine ⟨5969039622590045089805825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3979359748393363393203883 5969039622590045089805825)
                  ·
                    refine ⟨4476779716942533817354369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5969039622590045089805825 4476779716942533817354369)
                    ·
                      refine ⟨3357584787706900363015777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4476779716942533817354369 3357584787706900363015777)
                      ·
                        rfl

theorem cell23_6538873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 1, 2, 2].length) (baseStart_6538873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538873 prefixEnd_6538873 := by exact prefixLift 6538873
  have htrace : WordTrace (prefixWord ++ tailWord_6538873) baseStart_6538873 baseEnd_6538873 := by
    simpa [prefixWord, tailWord_6538873, baseEnd_6538873] using wordTrace_append hprefix tailTrace_6538873
  have hstable : (prefixWord ++ tailWord_6538873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538873).length < 2 ^ (prefixWord ++ tailWord_6538873).sum := by decide
  have hdescent : baseEnd_6538873 < baseStart_6538873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538915 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 5]
def baseStart_6538915 : Nat := 118140960795 + 6538915 * 2 ^ 59
def prefixEnd_6538915 : Nat := 4983230072969 + 3 ^ 40 * 6538915 * 2
def baseEnd_6538915 : Nat := 3357606353894389198690583

theorem tailTrace_6538915 : CollatzResearch.WordTrace tailWord_6538915 prefixEnd_6538915 3357606353894389198690583 := by
  unfold tailWord_6538915
  simp only [CollatzResearch.WordTrace]
  refine ⟨238493823105635187617482199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158995882070423458411654799 238493823105635187617482199)
  ·
    refine ⟨357740734658452781426223299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238493823105635187617482199 357740734658452781426223299)
    ·
      refine ⟨536611101987679172139334949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357740734658452781426223299 536611101987679172139334949)
      ·
        refine ⟨100614581622689844776125303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 536611101987679172139334949 100614581622689844776125303)
        ·
          refine ⟨150921872434034767164187955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100614581622689844776125303 150921872434034767164187955)
          ·
            refine ⟨226382808651052150746281933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150921872434034767164187955 226382808651052150746281933)
            ·
              refine ⟨84893553244144556529855725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226382808651052150746281933 84893553244144556529855725)
              ·
                refine ⟨31835082466554208698695897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84893553244144556529855725 31835082466554208698695897)
                ·
                  refine ⟨23876311849915656524021923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31835082466554208698695897 23876311849915656524021923)
                  ·
                    refine ⟨35814467774873484786032885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23876311849915656524021923 35814467774873484786032885)
                    ·
                      refine ⟨3357606353894389198690583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35814467774873484786032885 3357606353894389198690583)
                      ·
                        rfl

theorem cell23_6538915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_6538915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538915 prefixEnd_6538915 := by exact prefixLift 6538915
  have htrace : WordTrace (prefixWord ++ tailWord_6538915) baseStart_6538915 baseEnd_6538915 := by
    simpa [prefixWord, tailWord_6538915, baseEnd_6538915] using wordTrace_append hprefix tailTrace_6538915
  have hstable : (prefixWord ++ tailWord_6538915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538915).length < 2 ^ (prefixWord ++ tailWord_6538915).sum := by decide
  have hdescent : baseEnd_6538915 < baseStart_6538915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538942 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_6538942 : Nat := 118140960795 + 6538942 * 2 ^ 59
def prefixEnd_6538942 : Nat := 4983230072969 + 3 ^ 40 * 6538942 * 2
def baseEnd_6538942 : Nat := 3357620217872060593052959

theorem tailTrace_6538942 : CollatzResearch.WordTrace tailWord_6538942 prefixEnd_6538942 3357620217872060593052959 := by
  unfold tailWord_6538942
  simp only [CollatzResearch.WordTrace]
  refine ⟨29811850984567171403589385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158996538584358247485810053 29811850984567171403589385)
  ·
    refine ⟨22358888238425378552692039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29811850984567171403589385 22358888238425378552692039)
    ·
      refine ⟨33538332357638067829038059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22358888238425378552692039 33538332357638067829038059)
      ·
        refine ⟨50307498536457101743557089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33538332357638067829038059 50307498536457101743557089)
        ·
          refine ⟨37730623902342826307667817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50307498536457101743557089 37730623902342826307667817)
          ·
            refine ⟨28297967926757119730750863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37730623902342826307667817 28297967926757119730750863)
            ·
              refine ⟨42446951890135679596126295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28297967926757119730750863 42446951890135679596126295)
              ·
                refine ⟨63670427835203519394189443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42446951890135679596126295 63670427835203519394189443)
                ·
                  refine ⟨95505641752805279091284165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63670427835203519394189443 95505641752805279091284165)
                  ·
                    refine ⟨17907307828650989829615781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95505641752805279091284165 17907307828650989829615781)
                    ·
                      refine ⟨3357620217872060593052959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17907307828650989829615781 3357620217872060593052959)
                      ·
                        rfl

theorem cell23_6538942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_6538942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538942 prefixEnd_6538942 := by exact prefixLift 6538942
  have htrace : WordTrace (prefixWord ++ tailWord_6538942) baseStart_6538942 baseEnd_6538942 := by
    simpa [prefixWord, tailWord_6538942, baseEnd_6538942] using wordTrace_append hprefix tailTrace_6538942
  have hstable : (prefixWord ++ tailWord_6538942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538942).length < 2 ^ (prefixWord ++ tailWord_6538942).sum := by decide
  have hdescent : baseEnd_6538942 < baseStart_6538942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6538969 : List Nat := [1, 2, 1, 2, 3, 4, 2, 3, 5]
def baseStart_6538969 : Nat := 118140960795 + 6538969 * 2 ^ 59
def prefixEnd_6538969 : Nat := 4983230072969 + 3 ^ 40 * 6538969 * 2
def baseEnd_6538969 : Nat := 373070453538859109712815

theorem tailTrace_6538969 : CollatzResearch.WordTrace tailWord_6538969 prefixEnd_6538969 373070453538859109712815 := by
  unfold tailWord_6538969
  simp only [CollatzResearch.WordTrace]
  refine ⟨238495792647439554839947961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158997195098293036559965307 238495792647439554839947961)
  ·
    refine ⟨178871844485579666129960971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238495792647439554839947961 178871844485579666129960971)
    ·
      refine ⟨268307766728369499194941457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178871844485579666129960971 268307766728369499194941457)
      ·
        refine ⟨201230825046277124396206093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268307766728369499194941457 201230825046277124396206093)
        ·
          refine ⟨75461559392353921648577285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201230825046277124396206093 75461559392353921648577285)
          ·
            refine ⟨14149042386066360309108241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75461559392353921648577285 14149042386066360309108241)
            ·
              refine ⟨10611781789549770231831181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14149042386066360309108241 10611781789549770231831181)
              ·
                refine ⟨3979418171081163836936693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10611781789549770231831181 3979418171081163836936693)
                ·
                  refine ⟨373070453538859109712815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3979418171081163836936693 373070453538859109712815)
                  ·
                    rfl

theorem cell23_6538969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 5].length) (baseStart_6538969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6538969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6538969 prefixEnd_6538969 := by exact prefixLift 6538969
  have htrace : WordTrace (prefixWord ++ tailWord_6538969) baseStart_6538969 baseEnd_6538969 := by
    simpa [prefixWord, tailWord_6538969, baseEnd_6538969] using wordTrace_append hprefix tailTrace_6538969
  have hstable : (prefixWord ++ tailWord_6538969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6538969).length < 2 ^ (prefixWord ++ tailWord_6538969).sum := by decide
  have hdescent : baseEnd_6538969 < baseStart_6538969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6538969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539039 : List Nat := [1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 3]
def baseStart_6539039 : Nat := 118140960795 + 6539039 * 2 ^ 59
def prefixEnd_6539039 : Nat := 4983230072969 + 3 ^ 40 * 6539039 * 2
def baseEnd_6539039 : Nat := 3357670025495546713540013

theorem tailTrace_6539039 : CollatzResearch.WordTrace tailWord_6539039 prefixEnd_6539039 3357670025495546713540013 := by
  unfold tailWord_6539039
  simp only [CollatzResearch.WordTrace]
  refine ⟨238498345757185956794996171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158998897171457304529997447 238498345757185956794996171)
  ·
    refine ⟨357747518635778935192494257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238498345757185956794996171 357747518635778935192494257)
    ·
      refine ⟨268310638976834201394370693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357747518635778935192494257 268310638976834201394370693)
      ·
        refine ⟨50308244808156412761444505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 268310638976834201394370693 50308244808156412761444505)
        ·
          refine ⟨37731183606117309571083379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50308244808156412761444505 37731183606117309571083379)
          ·
            refine ⟨56596775409175964356625069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37731183606117309571083379 56596775409175964356625069)
            ·
              refine ⟨21223790778440986633734401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56596775409175964356625069 21223790778440986633734401)
              ·
                refine ⟨15917843083830739975300801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21223790778440986633734401 15917843083830739975300801)
                ·
                  refine ⟨11938382312873054981475601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15917843083830739975300801 11938382312873054981475601)
                  ·
                    refine ⟨8953786734654791236106701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11938382312873054981475601 8953786734654791236106701)
                    ·
                      refine ⟨3357670025495546713540013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8953786734654791236106701 3357670025495546713540013)
                      ·
                        rfl

theorem cell23_6539039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_6539039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539039 prefixEnd_6539039 := by exact prefixLift 6539039
  have htrace : WordTrace (prefixWord ++ tailWord_6539039) baseStart_6539039 baseEnd_6539039 := by
    simpa [prefixWord, tailWord_6539039, baseEnd_6539039] using wordTrace_append hprefix tailTrace_6539039
  have hstable : (prefixWord ++ tailWord_6539039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539039).length < 2 ^ (prefixWord ++ tailWord_6539039).sum := by decide
  have hdescent : baseEnd_6539039 < baseStart_6539039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539042 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 8]
def baseStart_6539042 : Nat := 118140960795 + 6539042 * 2 ^ 59
def prefixEnd_6539042 : Nat := 4983230072969 + 3 ^ 40 * 6539042 * 2
def baseEnd_6539042 : Nat := 373074618437501133533611

theorem tailTrace_6539042 : CollatzResearch.WordTrace tailWord_6539042 prefixEnd_6539042 373074618437501133533611 := by
  unfold tailWord_6539042
  simp only [CollatzResearch.WordTrace]
  refine ⟨59624613794043772076838845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158998970117450058871570253 59624613794043772076838845)
  ·
    refine ⟨22359230172766414528814567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59624613794043772076838845 22359230172766414528814567)
    ·
      refine ⟨33538845259149621793221851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22359230172766414528814567 33538845259149621793221851)
      ·
        refine ⟨50308267888724432689832777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33538845259149621793221851 50308267888724432689832777)
        ·
          refine ⟨37731200916543324517374583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50308267888724432689832777 37731200916543324517374583)
          ·
            refine ⟨56596801374814986776061875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37731200916543324517374583 56596801374814986776061875)
            ·
              refine ⟨84895202062222480164092813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56596801374814986776061875 84895202062222480164092813)
              ·
                refine ⟨31835700773333430061534805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84895202062222480164092813 31835700773333430061534805)
                ·
                  refine ⟨373074618437501133533611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31835700773333430061534805 373074618437501133533611)
                  ·
                    rfl

theorem cell23_6539042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_6539042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539042 prefixEnd_6539042 := by exact prefixLift 6539042
  have htrace : WordTrace (prefixWord ++ tailWord_6539042) baseStart_6539042 baseEnd_6539042 := by
    simpa [prefixWord, tailWord_6539042, baseEnd_6539042] using wordTrace_append hprefix tailTrace_6539042
  have hstable : (prefixWord ++ tailWord_6539042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539042).length < 2 ^ (prefixWord ++ tailWord_6539042).sum := by decide
  have hdescent : baseEnd_6539042 < baseStart_6539042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539059 : List Nat := [1, 1, 1, 2, 7, 1, 1, 3, 6]
def baseStart_6539059 : Nat := 118140960795 + 6539059 * 2 ^ 59
def prefixEnd_6539059 : Nat := 4983230072969 + 3 ^ 40 * 6539059 * 2
def baseEnd_6539059 : Nat := 373075588345404070587769

theorem tailTrace_6539059 : CollatzResearch.WordTrace tailWord_6539059 prefixEnd_6539059 373075588345404070587769 := by
  unfold tailWord_6539059
  simp only [CollatzResearch.WordTrace]
  refine ⟨238499075217113500210724231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158999383478075666807149487 238499075217113500210724231)
  ·
    refine ⟨357748612825670250316086347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238499075217113500210724231 357748612825670250316086347)
    ·
      refine ⟨536622919238505375474129521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357748612825670250316086347 536622919238505375474129521)
      ·
        refine ⟨402467189428879031605597141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536622919238505375474129521 402467189428879031605597141)
        ·
          refine ⟨9432824752239352303256183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 402467189428879031605597141 9432824752239352303256183)
          ·
            refine ⟨14149237128359028454884275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9432824752239352303256183 14149237128359028454884275)
            ·
              refine ⟨21223855692538542682326413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14149237128359028454884275 21223855692538542682326413)
              ·
                refine ⟨7958945884701953505872405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21223855692538542682326413 7958945884701953505872405)
                ·
                  refine ⟨373075588345404070587769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7958945884701953505872405 373075588345404070587769)
                  ·
                    rfl

theorem cell23_6539059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 6].length) (baseStart_6539059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539059 prefixEnd_6539059 := by exact prefixLift 6539059
  have htrace : WordTrace (prefixWord ++ tailWord_6539059) baseStart_6539059 baseEnd_6539059 := by
    simpa [prefixWord, tailWord_6539059, baseEnd_6539059] using wordTrace_append hprefix tailTrace_6539059
  have hstable : (prefixWord ++ tailWord_6539059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539059).length < 2 ^ (prefixWord ++ tailWord_6539059).sum := by decide
  have hdescent : baseEnd_6539059 < baseStart_6539059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539079 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 1, 5, 2]
def baseStart_6539079 : Nat := 118140960795 + 6539079 * 2 ^ 59
def prefixEnd_6539079 : Nat := 4983230072969 + 3 ^ 40 * 6539079 * 2
def baseEnd_6539079 : Nat := 3357690564721726557039829

theorem tailTrace_6539079 : CollatzResearch.WordTrace tailWord_6539079 prefixEnd_6539079 3357690564721726557039829 := by
  unfold tailWord_6539079
  simp only [CollatzResearch.WordTrace]
  refine ⟨238499804677041043626452291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158999869784694029084301527 238499804677041043626452291)
  ·
    refine ⟨357749707015561565439678437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238499804677041043626452291 357749707015561565439678437)
    ·
      refine ⟨67078070065417793519939707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 357749707015561565439678437 67078070065417793519939707)
      ·
        refine ⟨100617105098126690279909561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67078070065417793519939707 100617105098126690279909561)
        ·
          refine ⟨75462828823595017709932171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100617105098126690279909561 75462828823595017709932171)
          ·
            refine ⟨113194243235392526564898257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75462828823595017709932171 113194243235392526564898257)
            ·
              refine ⟨84895682426544394923673693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113194243235392526564898257 84895682426544394923673693)
              ·
                refine ⟨31835880909954148096377635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84895682426544394923673693 31835880909954148096377635)
                ·
                  refine ⟨47753821364931222144566453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31835880909954148096377635 47753821364931222144566453)
                  ·
                    refine ⟨4476920752962302076053105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47753821364931222144566453 4476920752962302076053105)
                    ·
                      refine ⟨3357690564721726557039829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4476920752962302076053105 3357690564721726557039829)
                      ·
                        rfl

theorem cell23_6539079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_6539079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539079 prefixEnd_6539079 := by exact prefixLift 6539079
  have htrace : WordTrace (prefixWord ++ tailWord_6539079) baseStart_6539079 baseEnd_6539079 := by
    simpa [prefixWord, tailWord_6539079, baseEnd_6539079] using wordTrace_append hprefix tailTrace_6539079
  have hstable : (prefixWord ++ tailWord_6539079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539079).length < 2 ^ (prefixWord ++ tailWord_6539079).sum := by decide
  have hdescent : baseEnd_6539079 < baseStart_6539079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539103 : List Nat := [1, 1, 2, 3, 1, 5, 1, 4, 1, 1, 3]
def baseStart_6539103 : Nat := 118140960795 + 6539103 * 2 ^ 59
def prefixEnd_6539103 : Nat := 4983230072969 + 3 ^ 40 * 6539103 * 2
def baseEnd_6539103 : Nat := 3357702888257434463139719

theorem tailTrace_6539103 : CollatzResearch.WordTrace tailWord_6539103 prefixEnd_6539103 3357702888257434463139719 := by
  unfold tailWord_6539103
  simp only [CollatzResearch.WordTrace]
  refine ⟨238500680028954095725325963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159000453352636063816883975 238500680028954095725325963)
  ·
    refine ⟨357751020043431143587988945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238500680028954095725325963 357751020043431143587988945)
    ·
      refine ⟨268313265032573357690991709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357751020043431143587988945 268313265032573357690991709)
      ·
        refine ⟨100617474387215009134121891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268313265032573357690991709 100617474387215009134121891)
        ·
          refine ⟨150926211580822513701182837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100617474387215009134121891 150926211580822513701182837)
          ·
            refine ⟨14149332335702110659485891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150926211580822513701182837 14149332335702110659485891)
            ·
              refine ⟨21223998503553165989228837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14149332335702110659485891 21223998503553165989228837)
              ·
                refine ⟨3979499719416218622980407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21223998503553165989228837 3979499719416218622980407)
                ·
                  refine ⟨5969249579124327934470611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3979499719416218622980407 5969249579124327934470611)
                  ·
                    refine ⟨8953874368686491901705917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5969249579124327934470611 8953874368686491901705917)
                    ·
                      refine ⟨3357702888257434463139719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8953874368686491901705917 3357702888257434463139719)
                      ·
                        rfl

theorem cell23_6539103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 1, 1, 3].length) (baseStart_6539103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539103 prefixEnd_6539103 := by exact prefixLift 6539103
  have htrace : WordTrace (prefixWord ++ tailWord_6539103) baseStart_6539103 baseEnd_6539103 := by
    simpa [prefixWord, tailWord_6539103, baseEnd_6539103] using wordTrace_append hprefix tailTrace_6539103
  have hstable : (prefixWord ++ tailWord_6539103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539103).length < 2 ^ (prefixWord ++ tailWord_6539103).sum := by decide
  have hdescent : baseEnd_6539103 < baseStart_6539103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539109 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 2, 6, 2]
def baseStart_6539109 : Nat := 118140960795 + 6539109 * 2 ^ 59
def prefixEnd_6539109 : Nat := 4983230072969 + 3 ^ 40 * 6539109 * 2
def baseEnd_6539109 : Nat := 3357705969141361439664691

theorem tailTrace_6539109 : CollatzResearch.WordTrace tailWord_6539109 prefixEnd_6539109 3357705969141361439664691 := by
  unfold tailWord_6539109
  simp only [CollatzResearch.WordTrace]
  refine ⟨238500898866932358750044381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159000599244621572500029587 238500898866932358750044381)
  ·
    refine ⟨89437837075099634531266643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238500898866932358750044381 89437837075099634531266643)
    ·
      refine ⟨134156755612649451796899965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89437837075099634531266643 134156755612649451796899965)
      ·
        refine ⟨50308783354743544423837487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134156755612649451796899965 50308783354743544423837487)
        ·
          refine ⟨75463175032115316635756231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50308783354743544423837487 75463175032115316635756231)
          ·
            refine ⟨113194762548172974953634347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75463175032115316635756231 113194762548172974953634347)
            ·
              refine ⟨169792143822259462430451521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113194762548172974953634347 169792143822259462430451521)
              ·
                refine ⟨127344107866694596822838641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169792143822259462430451521 127344107866694596822838641)
                ·
                  refine ⟨95508080900020947617128981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127344107866694596822838641 95508080900020947617128981)
                  ·
                    refine ⟨4476941292188481919552921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95508080900020947617128981 4476941292188481919552921)
                    ·
                      refine ⟨3357705969141361439664691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4476941292188481919552921 3357705969141361439664691)
                      ·
                        rfl

theorem cell23_6539109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_6539109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539109 prefixEnd_6539109 := by exact prefixLift 6539109
  have htrace : WordTrace (prefixWord ++ tailWord_6539109) baseStart_6539109 baseEnd_6539109 := by
    simpa [prefixWord, tailWord_6539109, baseEnd_6539109] using wordTrace_append hprefix tailTrace_6539109
  have hstable : (prefixWord ++ tailWord_6539109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539109).length < 2 ^ (prefixWord ++ tailWord_6539109).sum := by decide
  have hdescent : baseEnd_6539109 < baseStart_6539109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539129 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 3, 2, 3]
def baseStart_6539129 : Nat := 118140960795 + 6539129 * 2 ^ 59
def prefixEnd_6539129 : Nat := 4983230072969 + 3 ^ 40 * 6539129 * 2
def baseEnd_6539129 : Nat := 3357716238754451361414599

theorem tailTrace_6539129 : CollatzResearch.WordTrace tailWord_6539129 prefixEnd_6539129 3357716238754451361414599 := by
  unfold tailWord_6539129
  simp only [CollatzResearch.WordTrace]
  refine ⟨238501628326859902165772441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159001085551239934777181627 238501628326859902165772441)
  ·
    refine ⟨178876221245144926624329331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238501628326859902165772441 178876221245144926624329331)
    ·
      refine ⟨268314331867717389936493997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178876221245144926624329331 268314331867717389936493997)
      ·
        refine ⟨100617874450394021226185249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268314331867717389936493997 100617874450394021226185249)
        ·
          refine ⟨75463405837795515919638937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100617874450394021226185249 75463405837795515919638937)
          ·
            refine ⟨56597554378346636939729203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75463405837795515919638937 56597554378346636939729203)
            ·
              refine ⟨84896331567519955409593805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56597554378346636939729203 84896331567519955409593805)
              ·
                refine ⟨31836124337819983278597677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84896331567519955409593805 31836124337819983278597677)
                ·
                  refine ⟨11938546626682493729474129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31836124337819983278597677 11938546626682493729474129)
                  ·
                    refine ⟨8953909970011870297105597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11938546626682493729474129 8953909970011870297105597)
                    ·
                      refine ⟨3357716238754451361414599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8953909970011870297105597 3357716238754451361414599)
                      ·
                        rfl

theorem cell23_6539129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_6539129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539129 prefixEnd_6539129 := by exact prefixLift 6539129
  have htrace : WordTrace (prefixWord ++ tailWord_6539129) baseStart_6539129 baseEnd_6539129 := by
    simpa [prefixWord, tailWord_6539129, baseEnd_6539129] using wordTrace_append hprefix tailTrace_6539129
  have hstable : (prefixWord ++ tailWord_6539129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539129).length < 2 ^ (prefixWord ++ tailWord_6539129).sum := by decide
  have hdescent : baseEnd_6539129 < baseStart_6539129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539137 : List Nat := [1, 2, 4, 4, 1, 1, 2, 3, 1, 1, 3]
def baseStart_6539137 : Nat := 118140960795 + 6539137 * 2 ^ 59
def prefixEnd_6539137 : Nat := 4983230072969 + 3 ^ 40 * 6539137 * 2
def baseEnd_6539137 : Nat := 3357720346599687330114563

theorem tailTrace_6539137 : CollatzResearch.WordTrace tailWord_6539137 prefixEnd_6539137 3357720346599687330114563 := by
  unfold tailWord_6539137
  simp only [CollatzResearch.WordTrace]
  refine ⟨238501920110830919532063665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159001280073887279688042443 238501920110830919532063665)
  ·
    refine ⟨178876440083123189649047749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238501920110830919532063665 178876440083123189649047749)
    ·
      refine ⟨33539332515585598059196453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178876440083123189649047749 33539332515585598059196453)
      ·
        refine ⟨6288624846672299636099335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33539332515585598059196453 6288624846672299636099335)
        ·
          refine ⟨9432937270008449454149003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6288624846672299636099335 9432937270008449454149003)
          ·
            refine ⟨14149405905012674181223505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9432937270008449454149003 14149405905012674181223505)
            ·
              refine ⟨10612054428759505635917629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14149405905012674181223505 10612054428759505635917629)
              ·
                refine ⟨3979520410784814613469111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10612054428759505635917629 3979520410784814613469111)
                ·
                  refine ⟨5969280616177221920203667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3979520410784814613469111 5969280616177221920203667)
                  ·
                    refine ⟨8953920924265832880305501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5969280616177221920203667 8953920924265832880305501)
                    ·
                      refine ⟨3357720346599687330114563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8953920924265832880305501 3357720346599687330114563)
                      ·
                        rfl

theorem cell23_6539137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_6539137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539137 prefixEnd_6539137 := by exact prefixLift 6539137
  have htrace : WordTrace (prefixWord ++ tailWord_6539137) baseStart_6539137 baseEnd_6539137 := by
    simpa [prefixWord, tailWord_6539137, baseEnd_6539137] using wordTrace_append hprefix tailTrace_6539137
  have hstable : (prefixWord ++ tailWord_6539137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539137).length < 2 ^ (prefixWord ++ tailWord_6539137).sum := by decide
  have hdescent : baseEnd_6539137 < baseStart_6539137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539139 : List Nat := [1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 4]
def baseStart_6539139 : Nat := 118140960795 + 6539139 * 2 ^ 59
def prefixEnd_6539139 : Nat := 4983230072969 + 3 ^ 40 * 6539139 * 2
def baseEnd_6539139 : Nat := 3357721373560996322289553

theorem tailTrace_6539139 : CollatzResearch.WordTrace tailWord_6539139 prefixEnd_6539139 3357721373560996322289553 := by
  unfold tailWord_6539139
  simp only [CollatzResearch.WordTrace]
  refine ⟨238501993056823673873636471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159001328704549115915757647 238501993056823673873636471)
  ·
    refine ⟨357752989585235510810454707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238501993056823673873636471 357752989585235510810454707)
    ·
      refine ⟨536629484377853266215682061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357752989585235510810454707 536629484377853266215682061)
      ·
        refine ⟨201236056641694974830880773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 536629484377853266215682061 201236056641694974830880773)
        ·
          refine ⟨37731760620317807780790145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201236056641694974830880773 37731760620317807780790145)
          ·
            refine ⟨28298820465238355835592609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37731760620317807780790145 28298820465238355835592609)
            ·
              refine ⟨21224115348928766876694457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28298820465238355835592609 21224115348928766876694457)
              ·
                refine ⟨15918086511696575157520843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21224115348928766876694457 15918086511696575157520843)
                ·
                  refine ⟨23877129767544862736281265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15918086511696575157520843 23877129767544862736281265)
                  ·
                    refine ⟨17907847325658647052210949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23877129767544862736281265 17907847325658647052210949)
                    ·
                      refine ⟨3357721373560996322289553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17907847325658647052210949 3357721373560996322289553)
                      ·
                        rfl

theorem cell23_6539139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_6539139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539139 prefixEnd_6539139 := by exact prefixLift 6539139
  have htrace : WordTrace (prefixWord ++ tailWord_6539139) baseStart_6539139 baseEnd_6539139 := by
    simpa [prefixWord, tailWord_6539139, baseEnd_6539139] using wordTrace_append hprefix tailTrace_6539139
  have hstable : (prefixWord ++ tailWord_6539139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539139).length < 2 ^ (prefixWord ++ tailWord_6539139).sum := by decide
  have hdescent : baseEnd_6539139 < baseStart_6539139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539170 : List Nat := [3, 3, 1, 2, 3, 1, 3, 1, 2, 4]
def baseStart_6539170 : Nat := 118140960795 + 6539170 * 2 ^ 59
def prefixEnd_6539170 : Nat := 4983230072969 + 3 ^ 40 * 6539170 * 2
def baseEnd_6539170 : Nat := 1119245763820428567000637

theorem tailTrace_6539170 : CollatzResearch.WordTrace tailWord_6539170 prefixEnd_6539170 1119245763820428567000637 := by
  unfold tailWord_6539170
  simp only [CollatzResearch.WordTrace]
  refine ⟨59625780929927841542003741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159002082479807577445343309 59625780929927841542003741)
  ·
    refine ⟨22359667848722940578251403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59625780929927841542003741 22359667848722940578251403)
    ·
      refine ⟨33539501773084410867377105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22359667848722940578251403 33539501773084410867377105)
      ·
        refine ⟨25154626329813308150532829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33539501773084410867377105 25154626329813308150532829)
        ·
          refine ⟨9432984873679990556449811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25154626329813308150532829 9432984873679990556449811)
          ·
            refine ⟨14149477310519985834674717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9432984873679990556449811 14149477310519985834674717)
            ·
              refine ⟨5306053991444994688003019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14149477310519985834674717 5306053991444994688003019)
              ·
                refine ⟨7959080987167492032004529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5306053991444994688003019 7959080987167492032004529)
                ·
                  refine ⟨5969310740375619024003397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7959080987167492032004529 5969310740375619024003397)
                  ·
                    refine ⟨1119245763820428567000637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5969310740375619024003397 1119245763820428567000637)
                    ·
                      rfl

theorem cell23_6539170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_6539170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539170 prefixEnd_6539170 := by exact prefixLift 6539170
  have htrace : WordTrace (prefixWord ++ tailWord_6539170) baseStart_6539170 baseEnd_6539170 := by
    simpa [prefixWord, tailWord_6539170, baseEnd_6539170] using wordTrace_append hprefix tailTrace_6539170
  have hstable : (prefixWord ++ tailWord_6539170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539170).length < 2 ^ (prefixWord ++ tailWord_6539170).sum := by decide
  have hdescent : baseEnd_6539170 < baseStart_6539170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539186 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2]
def baseStart_6539186 : Nat := 118140960795 + 6539186 * 2 ^ 59
def prefixEnd_6539186 : Nat := 4983230072969 + 3 ^ 40 * 6539186 * 2
def baseEnd_6539186 : Nat := 3357745507151757638401837

theorem tailTrace_6539186 : CollatzResearch.WordTrace tailWord_6539186 prefixEnd_6539186 3357745507151757638401837 := by
  unfold tailWord_6539186
  simp only [CollatzResearch.WordTrace]
  refine ⟨59625926821913350225149353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159002471525102267267064941 59625926821913350225149353)
  ·
    refine ⟨44719445116435012668862015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59625926821913350225149353 44719445116435012668862015)
    ·
      refine ⟨67079167674652519003293023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44719445116435012668862015 67079167674652519003293023)
      ·
        refine ⟨100618751511978778504939535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67079167674652519003293023 100618751511978778504939535)
        ·
          refine ⟨150928127267968167757409303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100618751511978778504939535 150928127267968167757409303)
          ·
            refine ⟨226392190901952251636113955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150928127267968167757409303 226392190901952251636113955)
            ·
              refine ⟨339588286352928377454170933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226392190901952251636113955 339588286352928377454170933)
              ·
                refine ⟨31836401845587035386328525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 339588286352928377454170933 31836401845587035386328525)
                ·
                  refine ⟨11938650692095138269873197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31836401845587035386328525 11938650692095138269873197)
                  ·
                    refine ⟨4476994009535676851202449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11938650692095138269873197 4476994009535676851202449)
                    ·
                      refine ⟨3357745507151757638401837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4476994009535676851202449 3357745507151757638401837)
                      ·
                        rfl

theorem cell23_6539186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_6539186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539186 prefixEnd_6539186 := by exact prefixLift 6539186
  have htrace : WordTrace (prefixWord ++ tailWord_6539186) baseStart_6539186 baseEnd_6539186 := by
    simpa [prefixWord, tailWord_6539186, baseEnd_6539186] using wordTrace_append hprefix tailTrace_6539186
  have hstable : (prefixWord ++ tailWord_6539186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539186).length < 2 ^ (prefixWord ++ tailWord_6539186).sum := by decide
  have hdescent : baseEnd_6539186 < baseStart_6539186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539189 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_6539189 : Nat := 118140960795 + 6539189 * 2 ^ 59
def prefixEnd_6539189 : Nat := 4983230072969 + 3 ^ 40 * 6539189 * 2
def baseEnd_6539189 : Nat := 3357747047593721126664323

theorem tailTrace_6539189 : CollatzResearch.WordTrace tailWord_6539189 prefixEnd_6539189 3357747047593721126664323 := by
  unfold tailWord_6539189
  simp only [CollatzResearch.WordTrace]
  refine ⟨238503816706642532412956621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159002544471095021608637747 238503816706642532412956621)
  ·
    refine ⟨89438931264990949654858733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238503816706642532412956621 89438931264990949654858733)
    ·
      refine ⟨33539599224371606120572025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89438931264990949654858733 33539599224371606120572025)
      ·
        refine ⟨25154699418278704590429019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33539599224371606120572025 25154699418278704590429019)
        ·
          refine ⟨37732049127418056885643529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25154699418278704590429019 37732049127418056885643529)
          ·
            refine ⟨28299036845563542664232647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37732049127418056885643529 28299036845563542664232647)
            ·
              refine ⟨42448555268345313996348971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28299036845563542664232647 42448555268345313996348971)
              ·
                refine ⟨63672832902517970994523457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42448555268345313996348971 63672832902517970994523457)
                ·
                  refine ⟨47754624676888478245892593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63672832902517970994523457 47754624676888478245892593)
                  ·
                    refine ⟨35815968507666358684419445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47754624676888478245892593 35815968507666358684419445)
                    ·
                      refine ⟨3357747047593721126664323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35815968507666358684419445 3357747047593721126664323)
                      ·
                        rfl

theorem cell23_6539189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_6539189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539189 prefixEnd_6539189 := by exact prefixLift 6539189
  have htrace : WordTrace (prefixWord ++ tailWord_6539189) baseStart_6539189 baseEnd_6539189 := by
    simpa [prefixWord, tailWord_6539189, baseEnd_6539189] using wordTrace_append hprefix tailTrace_6539189
  have hstable : (prefixWord ++ tailWord_6539189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539189).length < 2 ^ (prefixWord ++ tailWord_6539189).sum := by decide
  have hdescent : baseEnd_6539189 < baseStart_6539189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539276 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 1, 7, 2]
def baseStart_6539276 : Nat := 118140960795 + 6539276 * 2 ^ 59
def prefixEnd_6539276 : Nat := 4983230072969 + 3 ^ 40 * 6539276 * 2
def baseEnd_6539276 : Nat := 3357791720410662286276423

theorem tailTrace_6539276 : CollatzResearch.WordTrace tailWord_6539276 prefixEnd_6539276 3357791720410662286276423 := by
  unfold tailWord_6539276
  simp only [CollatzResearch.WordTrace]
  refine ⟨119253494928663673135686841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159004659904884897514249121 119253494928663673135686841)
  ·
    refine ⟨89440121196497754851765131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119253494928663673135686841 89440121196497754851765131)
    ·
      refine ⟨134160181794746632277647697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89440121196497754851765131 134160181794746632277647697)
      ·
        refine ⟨100620136346059974208235773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134160181794746632277647697 100620136346059974208235773)
        ·
          refine ⟨37732551129772490328088415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100620136346059974208235773 37732551129772490328088415)
          ·
            refine ⟨56598826694658735492132623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37732551129772490328088415 56598826694658735492132623)
            ·
              refine ⟨84898240041988103238198935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56598826694658735492132623 84898240041988103238198935)
              ·
                refine ⟨127347360062982154857298403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84898240041988103238198935 127347360062982154857298403)
                ·
                  refine ⟨191021040094473232285947605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127347360062982154857298403 191021040094473232285947605)
                  ·
                    refine ⟨4477055627214216381701897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 191021040094473232285947605 4477055627214216381701897)
                    ·
                      refine ⟨3357791720410662286276423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4477055627214216381701897 3357791720410662286276423)
                      ·
                        rfl

theorem cell23_6539276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_6539276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539276 prefixEnd_6539276 := by exact prefixLift 6539276
  have htrace : WordTrace (prefixWord ++ tailWord_6539276) baseStart_6539276 baseEnd_6539276 := by
    simpa [prefixWord, tailWord_6539276, baseEnd_6539276] using wordTrace_append hprefix tailTrace_6539276
  have hstable : (prefixWord ++ tailWord_6539276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539276).length < 2 ^ (prefixWord ++ tailWord_6539276).sum := by decide
  have hdescent : baseEnd_6539276 < baseStart_6539276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539289 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 1, 3, 4]
def baseStart_6539289 : Nat := 118140960795 + 6539289 * 2 ^ 59
def prefixEnd_6539289 : Nat := 4983230072969 + 3 ^ 40 * 6539289 * 2
def baseEnd_6539289 : Nat := 3357798395659170735413863

theorem tailTrace_6539289 : CollatzResearch.WordTrace tailWord_6539289 prefixEnd_6539289 3357798395659170735413863 := by
  unfold tailWord_6539289
  simp only [CollatzResearch.WordTrace]
  refine ⟨238507464006280249491596921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159004976004186832994397947 238507464006280249491596921)
  ·
    refine ⟨178880598004710187118697691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238507464006280249491596921 178880598004710187118697691)
    ·
      refine ⟨268320897007065280678046537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178880598004710187118697691 268320897007065280678046537)
      ·
        refine ⟨201240672755298960508534903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268320897007065280678046537 201240672755298960508534903)
        ·
          refine ⟨301861009132948440762802355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201240672755298960508534903 301861009132948440762802355)
          ·
            refine ⟨452791513699422661144203533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301861009132948440762802355 452791513699422661144203533)
            ·
              refine ⟨169796817637283497929076325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 452791513699422661144203533 169796817637283497929076325)
              ·
                refine ⟨31836903306990655861701811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169796817637283497929076325 31836903306990655861701811)
                ·
                  refine ⟨47755354960485983792552717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31836903306990655861701811 47755354960485983792552717)
                  ·
                    refine ⟨17908258110182243922207269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47755354960485983792552717 17908258110182243922207269)
                    ·
                      refine ⟨3357798395659170735413863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17908258110182243922207269 3357798395659170735413863)
                      ·
                        rfl

theorem cell23_6539289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_6539289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539289 prefixEnd_6539289 := by exact prefixLift 6539289
  have htrace : WordTrace (prefixWord ++ tailWord_6539289) baseStart_6539289 baseEnd_6539289 := by
    simpa [prefixWord, tailWord_6539289, baseEnd_6539289] using wordTrace_append hprefix tailTrace_6539289
  have hstable : (prefixWord ++ tailWord_6539289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539289).length < 2 ^ (prefixWord ++ tailWord_6539289).sum := by decide
  have hdescent : baseEnd_6539289 < baseStart_6539289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539303 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 1, 7]
def baseStart_6539303 : Nat := 118140960795 + 6539303 * 2 ^ 59
def prefixEnd_6539303 : Nat := 4983230072969 + 3 ^ 40 * 6539303 * 2
def baseEnd_6539303 : Nat := 1119268528129444560212933

theorem tailTrace_6539303 : CollatzResearch.WordTrace tailWord_6539303 prefixEnd_6539303 1119268528129444560212933 := by
  unfold tailWord_6539303
  simp only [CollatzResearch.WordTrace]
  refine ⟨238507974628229529882606563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159005316418819686588404375 238507974628229529882606563)
  ·
    refine ⟨357761961942344294823909845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238507974628229529882606563 357761961942344294823909845)
    ·
      refine ⟨8385045983023694409935387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 357761961942344294823909845 8385045983023694409935387)
      ·
        refine ⟨12577568974535541614903081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8385045983023694409935387 12577568974535541614903081)
        ·
          refine ⟨9433176730901656211177311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12577568974535541614903081 9433176730901656211177311)
          ·
            refine ⟨14149765096352484316765967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9433176730901656211177311 14149765096352484316765967)
            ·
              refine ⟨21224647644528726475148951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14149765096352484316765967 21224647644528726475148951)
              ·
                refine ⟨31836971466793089712723427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21224647644528726475148951 31836971466793089712723427)
                ·
                  refine ⟨47755457200189634569085141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31836971466793089712723427 47755457200189634569085141)
                  ·
                    refine ⟨1119268528129444560212933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47755457200189634569085141 1119268528129444560212933)
                    ·
                      rfl

theorem cell23_6539303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_6539303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539303 prefixEnd_6539303 := by exact prefixLift 6539303
  have htrace : WordTrace (prefixWord ++ tailWord_6539303) baseStart_6539303 baseEnd_6539303 := by
    simpa [prefixWord, tailWord_6539303, baseEnd_6539303] using wordTrace_append hprefix tailTrace_6539303
  have hstable : (prefixWord ++ tailWord_6539303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539303).length < 2 ^ (prefixWord ++ tailWord_6539303).sum := by decide
  have hdescent : baseEnd_6539303 < baseStart_6539303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539319 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 6]
def baseStart_6539319 : Nat := 118140960795 + 6539319 * 2 ^ 59
def prefixEnd_6539319 : Nat := 4983230072969 + 3 ^ 40 * 6539319 * 2
def baseEnd_6539319 : Nat := 3357813800078805618038725

theorem tailTrace_6539319 : CollatzResearch.WordTrace tailWord_6539319 prefixEnd_6539319 3357813800078805618038725 := by
  unfold tailWord_6539319
  simp only [CollatzResearch.WordTrace]
  refine ⟨238508558196171564615189011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159005705464114376410126007 238508558196171564615189011)
  ·
    refine ⟨357762837294257346922783517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238508558196171564615189011 357762837294257346922783517)
    ·
      refine ⟨134161063985346505096043819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357762837294257346922783517 134161063985346505096043819)
      ·
        refine ⟨201241595978019757644065729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134161063985346505096043819 201241595978019757644065729)
        ·
          refine ⟨150931196983514818233049297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201241595978019757644065729 150931196983514818233049297)
          ·
            refine ⟨113198397737636113674786973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150931196983514818233049297 113198397737636113674786973)
            ·
              refine ⟨42449399151613542628045115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113198397737636113674786973 42449399151613542628045115)
              ·
                refine ⟨63674098727420313942067673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42449399151613542628045115 63674098727420313942067673)
                ·
                  refine ⟨47755574045565235456550755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63674098727420313942067673 47755574045565235456550755)
                  ·
                    refine ⟨71633361068347853184826133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47755574045565235456550755 71633361068347853184826133)
                    ·
                      refine ⟨3357813800078805618038725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71633361068347853184826133 3357813800078805618038725)
                      ·
                        rfl

theorem cell23_6539319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_6539319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539319 prefixEnd_6539319 := by exact prefixLift 6539319
  have htrace : WordTrace (prefixWord ++ tailWord_6539319) baseStart_6539319 baseEnd_6539319 := by
    simpa [prefixWord, tailWord_6539319, baseEnd_6539319] using wordTrace_append hprefix tailTrace_6539319
  have hstable : (prefixWord ++ tailWord_6539319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539319).length < 2 ^ (prefixWord ++ tailWord_6539319).sum := by decide
  have hdescent : baseEnd_6539319 < baseStart_6539319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539383 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 4, 3, 2]
def baseStart_6539383 : Nat := 118140960795 + 6539383 * 2 ^ 59
def prefixEnd_6539383 : Nat := 4983230072969 + 3 ^ 40 * 6539383 * 2
def baseEnd_6539383 : Nat := 3357846662840693367638431

theorem tailTrace_6539383 : CollatzResearch.WordTrace tailWord_6539383 prefixEnd_6539383 3357846662840693367638431 := by
  unfold tailWord_6539383
  simp only [CollatzResearch.WordTrace]
  refine ⟨238510892467939703545518803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159007261645293135697012535 238510892467939703545518803)
  ·
    refine ⟨357766338701909555318278205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238510892467939703545518803 357766338701909555318278205)
    ·
      refine ⟨134162377013216083244354327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357766338701909555318278205 134162377013216083244354327)
      ·
        refine ⟨201243565519824124866531491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134162377013216083244354327 201243565519824124866531491)
        ·
          refine ⟨301865348279736187299797237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201243565519824124866531491 301865348279736187299797237)
          ·
            refine ⟨28299876401225267559355991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 301865348279736187299797237 28299876401225267559355991)
            ·
              refine ⟨42449814601837901339033987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28299876401225267559355991 42449814601837901339033987)
              ·
                refine ⟨63674721902756852008550981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42449814601837901339033987 63674721902756852008550981)
                ·
                  refine ⟨11939010356766909751603309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63674721902756852008550981 11939010356766909751603309)
                  ·
                    refine ⟨4477128883787591156851241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11939010356766909751603309 4477128883787591156851241)
                    ·
                      refine ⟨3357846662840693367638431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4477128883787591156851241 3357846662840693367638431)
                      ·
                        rfl

theorem cell23_6539383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 3, 2].length) (baseStart_6539383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539383 prefixEnd_6539383 := by exact prefixLift 6539383
  have htrace : WordTrace (prefixWord ++ tailWord_6539383) baseStart_6539383 baseEnd_6539383 := by
    simpa [prefixWord, tailWord_6539383, baseEnd_6539383] using wordTrace_append hprefix tailTrace_6539383
  have hstable : (prefixWord ++ tailWord_6539383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539383).length < 2 ^ (prefixWord ++ tailWord_6539383).sum := by decide
  have hdescent : baseEnd_6539383 < baseStart_6539383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539419 : List Nat := [1, 1, 1, 1, 1, 1, 2, 15]
def baseStart_6539419 : Nat := 118140960795 + 6539419 * 2 ^ 59
def prefixEnd_6539419 : Nat := 4983230072969 + 3 ^ 40 * 6539419 * 2
def baseEnd_6539419 : Nat := 124365375857194638029195

theorem tailTrace_6539419 : CollatzResearch.WordTrace tailWord_6539419 prefixEnd_6539419 124365375857194638029195 := by
  unfold tailWord_6539419
  simp only [CollatzResearch.WordTrace]
  refine ⟨238512205495809281693829311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159008136997206187795886207 238512205495809281693829311)
  ·
    refine ⟨357768308243713922540743967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238512205495809281693829311 357768308243713922540743967)
    ·
      refine ⟨536652462365570883811115951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357768308243713922540743967 536652462365570883811115951)
      ·
        refine ⟨804978693548356325716673927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536652462365570883811115951 804978693548356325716673927)
        ·
          refine ⟨1207468040322534488575010891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804978693548356325716673927 1207468040322534488575010891)
          ·
            refine ⟨1811202060483801732862516337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207468040322534488575010891 1811202060483801732862516337)
            ·
              refine ⟨1358401545362851299646887253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1811202060483801732862516337 1358401545362851299646887253)
              ·
                refine ⟨124365375857194638029195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 15 1358401545362851299646887253 124365375857194638029195)
                ·
                  rfl

theorem cell23_6539419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 15].length) (baseStart_6539419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539419 prefixEnd_6539419 := by exact prefixLift 6539419
  have htrace : WordTrace (prefixWord ++ tailWord_6539419) baseStart_6539419 baseEnd_6539419 := by
    simpa [prefixWord, tailWord_6539419, baseEnd_6539419] using wordTrace_append hprefix tailTrace_6539419
  have hstable : (prefixWord ++ tailWord_6539419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539419).length < 2 ^ (prefixWord ++ tailWord_6539419).sum := by decide
  have hdescent : baseEnd_6539419 < baseStart_6539419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539423 : List Nat := [1, 1, 2, 6, 1, 2, 1, 2, 1, 6]
def baseStart_6539423 : Nat := 118140960795 + 6539423 * 2 ^ 59
def prefixEnd_6539423 : Nat := 4983230072969 + 3 ^ 40 * 6539423 * 2
def baseEnd_6539423 : Nat := 1119289067355624403712749

theorem tailTrace_6539423 : CollatzResearch.WordTrace tailWord_6539423 prefixEnd_6539423 1119289067355624403712749 := by
  unfold tailWord_6539423
  simp only [CollatzResearch.WordTrace]
  refine ⟨238512351387794790376974923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159008234258529860251316615 238512351387794790376974923)
  ·
    refine ⟨357768527081692185565462385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238512351387794790376974923 357768527081692185565462385)
    ·
      refine ⟨268326395311269139174096789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357768527081692185565462385 268326395311269139174096789)
      ·
        refine ⟨12577799780215740898785787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 268326395311269139174096789 12577799780215740898785787)
        ·
          refine ⟨18866699670323611348178681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12577799780215740898785787 18866699670323611348178681)
          ·
            refine ⟨14150024752742708511134011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18866699670323611348178681 14150024752742708511134011)
            ·
              refine ⟨21225037129114062766701017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14150024752742708511134011 21225037129114062766701017)
              ·
                refine ⟨15918777846835547075025763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21225037129114062766701017 15918777846835547075025763)
                ·
                  refine ⟨23878166770253320612538645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15918777846835547075025763 23878166770253320612538645)
                  ·
                    refine ⟨1119289067355624403712749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23878166770253320612538645 1119289067355624403712749)
                    ·
                      rfl

theorem cell23_6539423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 6].length) (baseStart_6539423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539423 prefixEnd_6539423 := by exact prefixLift 6539423
  have htrace : WordTrace (prefixWord ++ tailWord_6539423) baseStart_6539423 baseEnd_6539423 := by
    simpa [prefixWord, tailWord_6539423, baseEnd_6539423] using wordTrace_append hprefix tailTrace_6539423
  have hstable : (prefixWord ++ tailWord_6539423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539423).length < 2 ^ (prefixWord ++ tailWord_6539423).sum := by decide
  have hdescent : baseEnd_6539423 < baseStart_6539423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539441 : List Nat := [1, 2, 2, 5, 2, 2, 2, 2, 1, 1, 3]
def baseStart_6539441 : Nat := 118140960795 + 6539441 * 2 ^ 59
def prefixEnd_6539441 : Nat := 4983230072969 + 3 ^ 40 * 6539441 * 2
def baseEnd_6539441 : Nat := 3357876444718654140713165

theorem tailTrace_6539441 : CollatzResearch.WordTrace tailWord_6539441 prefixEnd_6539441 3357876444718654140713165 := by
  unfold tailWord_6539441
  simp only [CollatzResearch.WordTrace]
  refine ⟨238513007901729579451130177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159008671934486386300753451 238513007901729579451130177)
  ·
    refine ⟨178884755926297184588347633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238513007901729579451130177 178884755926297184588347633)
    ·
      refine ⟨134163566944722888441260725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178884755926297184588347633 134163566944722888441260725)
      ·
        refine ⟨12577834401067770791368193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134163566944722888441260725 12577834401067770791368193)
        ·
          refine ⟨9433375800800828093526145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12577834401067770791368193 9433375800800828093526145)
          ·
            refine ⟨7075031850600621070144609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9433375800800828093526145 7075031850600621070144609)
            ·
              refine ⟨5306273887950465802608457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7075031850600621070144609 5306273887950465802608457)
              ·
                refine ⟨3979705415962849351956343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5306273887950465802608457 3979705415962849351956343)
                ·
                  refine ⟨5969558123944274027934515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3979705415962849351956343 5969558123944274027934515)
                  ·
                    refine ⟨8954337185916411041901773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5969558123944274027934515 8954337185916411041901773)
                    ·
                      refine ⟨3357876444718654140713165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8954337185916411041901773 3357876444718654140713165)
                      ·
                        rfl

theorem cell23_6539441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_6539441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539441 prefixEnd_6539441 := by exact prefixLift 6539441
  have htrace : WordTrace (prefixWord ++ tailWord_6539441) baseStart_6539441 baseEnd_6539441 := by
    simpa [prefixWord, tailWord_6539441, baseEnd_6539441] using wordTrace_append hprefix tailTrace_6539441
  have hstable : (prefixWord ++ tailWord_6539441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539441).length < 2 ^ (prefixWord ++ tailWord_6539441).sum := by decide
  have hdescent : baseEnd_6539441 < baseStart_6539441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539460 : List Nat := [2, 3, 3, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_6539460 : Nat := 118140960795 + 6539460 * 2 ^ 59
def prefixEnd_6539460 : Nat := 4983230072969 + 3 ^ 40 * 6539460 * 2
def baseEnd_6539460 : Nat := 3357886200851089566375577

theorem tailTrace_6539460 : CollatzResearch.WordTrace tailWord_6539460 prefixEnd_6539460 3357886200851089566375577 := by
  unfold tailWord_6539460
  simp only [CollatzResearch.WordTrace]
  refine ⟨119256850444330372848035917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159009133925773830464047889 119256850444330372848035917)
  ·
    refine ⟨44721318916623889818013469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119256850444330372848035917 44721318916623889818013469)
    ·
      refine ⟨16770494593733958681755051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44721318916623889818013469 16770494593733958681755051)
      ·
        refine ⟨25155741890600938022632577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16770494593733958681755051 25155741890600938022632577)
        ·
          refine ⟨18866806417950703516974433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25155741890600938022632577 18866806417950703516974433)
          ·
            refine ⟨14150104813463027637730825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18866806417950703516974433 14150104813463027637730825)
            ·
              refine ⟨10612578610097270728298119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14150104813463027637730825 10612578610097270728298119)
              ·
                refine ⟨15918867915145906092447179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10612578610097270728298119 15918867915145906092447179)
                ·
                  refine ⟨23878301872718859138670769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15918867915145906092447179 23878301872718859138670769)
                  ·
                    refine ⟨17908726404539144354003077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23878301872718859138670769 17908726404539144354003077)
                    ·
                      refine ⟨3357886200851089566375577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17908726404539144354003077 3357886200851089566375577)
                      ·
                        rfl

theorem cell23_6539460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_6539460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539460 prefixEnd_6539460 := by exact prefixLift 6539460
  have htrace : WordTrace (prefixWord ++ tailWord_6539460) baseStart_6539460 baseEnd_6539460 := by
    simpa [prefixWord, tailWord_6539460, baseEnd_6539460] using wordTrace_append hprefix tailTrace_6539460
  have hstable : (prefixWord ++ tailWord_6539460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539460).length < 2 ^ (prefixWord ++ tailWord_6539460).sum := by decide
  have hdescent : baseEnd_6539460 < baseStart_6539460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539463 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 8, 1, 3]
def baseStart_6539463 : Nat := 118140960795 + 6539463 * 2 ^ 59
def prefixEnd_6539463 : Nat := 4983230072969 + 3 ^ 40 * 6539463 * 2
def baseEnd_6539463 : Nat := 3357887741293053054638063

theorem tailTrace_6539463 : CollatzResearch.WordTrace tailWord_6539463 prefixEnd_6539463 3357887741293053054638063 := by
  unfold tailWord_6539463
  simp only [CollatzResearch.WordTrace]
  refine ⟨238513810307649877208431043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159009206871766584805620695 238513810307649877208431043)
  ·
    refine ⟨357770715461474815812646565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238513810307649877208431043 357770715461474815812646565)
    ·
      refine ⟨67082009149026527964871231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 357770715461474815812646565 67082009149026527964871231)
      ·
        refine ⟨100623013723539791947306847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67082009149026527964871231 100623013723539791947306847)
        ·
          refine ⟨150934520585309687920960271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100623013723539791947306847 150934520585309687920960271)
          ·
            refine ⟨226401780877964531881440407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150934520585309687920960271 226401780877964531881440407)
            ·
              refine ⟨339602671316946797822160611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226401780877964531881440407 339602671316946797822160611)
              ·
                refine ⟨509404006975420196733240917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339602671316946797822160611 509404006975420196733240917)
                ·
                  refine ⟨5969578206743205430467667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 509404006975420196733240917 5969578206743205430467667)
                  ·
                    refine ⟨8954367310114808145701501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5969578206743205430467667 8954367310114808145701501)
                    ·
                      refine ⟨3357887741293053054638063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8954367310114808145701501 3357887741293053054638063)
                      ·
                        rfl

theorem cell23_6539463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_6539463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539463 prefixEnd_6539463 := by exact prefixLift 6539463
  have htrace : WordTrace (prefixWord ++ tailWord_6539463) baseStart_6539463 baseEnd_6539463 := by
    simpa [prefixWord, tailWord_6539463, baseEnd_6539463] using wordTrace_append hprefix tailTrace_6539463
  have hstable : (prefixWord ++ tailWord_6539463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539463).length < 2 ^ (prefixWord ++ tailWord_6539463).sum := by decide
  have hdescent : baseEnd_6539463 < baseStart_6539463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539466 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 2, 7]
def baseStart_6539466 : Nat := 118140960795 + 6539466 * 2 ^ 59
def prefixEnd_6539466 : Nat := 4983230072969 + 3 ^ 40 * 6539466 * 2
def baseEnd_6539466 : Nat := 1119296427245005514300183

theorem tailTrace_6539466 : CollatzResearch.WordTrace tailWord_6539466 prefixEnd_6539466 1119296427245005514300183 := by
  unfold tailWord_6539466
  simp only [CollatzResearch.WordTrace]
  refine ⟨59628479931659752180197563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159009279817759339147193501 59628479931659752180197563)
  ·
    refine ⟨89442719897489628270296345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59628479931659752180197563 89442719897489628270296345)
    ·
      refine ⟨67082039923117221202722259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89442719897489628270296345 67082039923117221202722259)
      ·
        refine ⟨100623059884675831804083389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67082039923117221202722259 100623059884675831804083389)
        ·
          refine ⟨37733647456753436926531271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100623059884675831804083389 37733647456753436926531271)
          ·
            refine ⟨56600471185130155389796907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37733647456753436926531271 56600471185130155389796907)
            ·
              refine ⟨84900706777695233084695361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56600471185130155389796907 84900706777695233084695361)
              ·
                refine ⟨63675530083271424813521521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84900706777695233084695361 63675530083271424813521521)
                ·
                  refine ⟨47756647562453568610141141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63675530083271424813521521 47756647562453568610141141)
                  ·
                    refine ⟨1119296427245005514300183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47756647562453568610141141 1119296427245005514300183)
                    ·
                      rfl

theorem cell23_6539466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_6539466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539466 prefixEnd_6539466 := by exact prefixLift 6539466
  have htrace : WordTrace (prefixWord ++ tailWord_6539466) baseStart_6539466 baseEnd_6539466 := by
    simpa [prefixWord, tailWord_6539466, baseEnd_6539466] using wordTrace_append hprefix tailTrace_6539466
  have hstable : (prefixWord ++ tailWord_6539466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539466).length < 2 ^ (prefixWord ++ tailWord_6539466).sum := by decide
  have hdescent : baseEnd_6539466 < baseStart_6539466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539484 : List Nat := [2, 2, 5, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_6539484 : Nat := 118140960795 + 6539484 * 2 ^ 59
def prefixEnd_6539484 : Nat := 4983230072969 + 3 ^ 40 * 6539484 * 2
def baseEnd_6539484 : Nat := 3357898524386797472475467

theorem tailTrace_6539484 : CollatzResearch.WordTrace tailWord_6539484 prefixEnd_6539484 3357898524386797472475467 := by
  unfold tailWord_6539484
  simp only [CollatzResearch.WordTrace]
  refine ⟨119257288120286898897472753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159009717493715865196630337 119257288120286898897472753)
  ·
    refine ⟨89442966090215174173104565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119257288120286898897472753 89442966090215174173104565)
    ·
      refine ⟨8385278070957672578728553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89442966090215174173104565 8385278070957672578728553)
      ·
        refine ⟨6288958553218254434046415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8385278070957672578728553 6288958553218254434046415)
        ·
          refine ⟨9433437829827381651069623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6288958553218254434046415 9433437829827381651069623)
          ·
            refine ⟨14150156744741072476604435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9433437829827381651069623 14150156744741072476604435)
            ·
              refine ⟨21225235117111608714906653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14150156744741072476604435 21225235117111608714906653)
              ·
                refine ⟨7959463168916853268089995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21225235117111608714906653 7959463168916853268089995)
                ·
                  refine ⟨11939194753375279902134993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7959463168916853268089995 11939194753375279902134993)
                  ·
                    refine ⟨8954396065031459926601245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11939194753375279902134993 8954396065031459926601245)
                    ·
                      refine ⟨3357898524386797472475467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8954396065031459926601245 3357898524386797472475467)
                      ·
                        rfl

theorem cell23_6539484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_6539484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539484 prefixEnd_6539484 := by exact prefixLift 6539484
  have htrace : WordTrace (prefixWord ++ tailWord_6539484) baseStart_6539484 baseEnd_6539484 := by
    simpa [prefixWord, tailWord_6539484, baseEnd_6539484] using wordTrace_append hprefix tailTrace_6539484
  have hstable : (prefixWord ++ tailWord_6539484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539484).length < 2 ^ (prefixWord ++ tailWord_6539484).sum := by decide
  have hdescent : baseEnd_6539484 < baseStart_6539484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539520 : List Nat := [2, 1, 1, 2, 1, 1, 7, 1, 1, 4, 2]
def baseStart_6539520 : Nat := 118140960795 + 6539520 * 2 ^ 59
def prefixEnd_6539520 : Nat := 4983230072969 + 3 ^ 40 * 6539520 * 2
def baseEnd_6539520 : Nat := 3357917009690359331625301

theorem tailTrace_6539520 : CollatzResearch.WordTrace tailWord_6539520 prefixEnd_6539520 3357917009690359331625301 := by
  unfold tailWord_6539520
  simp only [CollatzResearch.WordTrace]
  refine ⟨119257944634221687971628007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159010592845628917295504009 119257944634221687971628007)
  ·
    refine ⟨178886916951332531957442011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119257944634221687971628007 178886916951332531957442011)
    ·
      refine ⟨268330375426998797936163017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178886916951332531957442011 268330375426998797936163017)
      ·
        refine ⟨201247781570249098452122263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268330375426998797936163017 201247781570249098452122263)
        ·
          refine ⟨301871672355373647678183395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201247781570249098452122263 301871672355373647678183395)
          ·
            refine ⟨452807508533060471517275093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301871672355373647678183395 452807508533060471517275093)
            ·
              refine ⟨10612675981243604801186135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 452807508533060471517275093 10612675981243604801186135)
              ·
                refine ⟨15919013971865407201779203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10612675981243604801186135 15919013971865407201779203)
                ·
                  refine ⟨23878520957798110802668805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15919013971865407201779203 23878520957798110802668805)
                  ·
                    refine ⟨4477222679587145775500401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23878520957798110802668805 4477222679587145775500401)
                    ·
                      refine ⟨3357917009690359331625301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4477222679587145775500401 3357917009690359331625301)
                      ·
                        rfl

theorem cell23_6539520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 1, 4, 2].length) (baseStart_6539520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539520 prefixEnd_6539520 := by exact prefixLift 6539520
  have htrace : WordTrace (prefixWord ++ tailWord_6539520) baseStart_6539520 baseEnd_6539520 := by
    simpa [prefixWord, tailWord_6539520, baseEnd_6539520] using wordTrace_append hprefix tailTrace_6539520
  have hstable : (prefixWord ++ tailWord_6539520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539520).length < 2 ^ (prefixWord ++ tailWord_6539520).sum := by decide
  have hdescent : baseEnd_6539520 < baseStart_6539520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539524 : List Nat := [2, 3, 2, 2, 3, 1, 2, 2, 1, 3, 2]
def baseStart_6539524 : Nat := 118140960795 + 6539524 * 2 ^ 59
def prefixEnd_6539524 : Nat := 4983230072969 + 3 ^ 40 * 6539524 * 2
def baseEnd_6539524 : Nat := 3357919063612977315975283

theorem tailTrace_6539524 : CollatzResearch.WordTrace tailWord_6539524 prefixEnd_6539524 3357919063612977315975283 := by
  unfold tailWord_6539524
  simp only [CollatzResearch.WordTrace]
  refine ⟨119258017580214442313200813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159010690106952589750934417 119258017580214442313200813)
  ·
    refine ⟨44721756592580415867450305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119258017580214442313200813 44721756592580415867450305)
    ·
      refine ⟨33541317444435311900587729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44721756592580415867450305 33541317444435311900587729)
      ·
        refine ⟨25155988083326483925440797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33541317444435311900587729 25155988083326483925440797)
        ·
          refine ⟨9433495531247431472040299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25155988083326483925440797 9433495531247431472040299)
          ·
            refine ⟨14150243296871147208060449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9433495531247431472040299 14150243296871147208060449)
            ·
              refine ⟨10612682472653360406045337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14150243296871147208060449 10612682472653360406045337)
              ·
                refine ⟨7959511854490020304534003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10612682472653360406045337 7959511854490020304534003)
                ·
                  refine ⟨11939267781735030456801005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7959511854490020304534003 11939267781735030456801005)
                  ·
                    refine ⟨4477225418150636421300377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11939267781735030456801005 4477225418150636421300377)
                    ·
                      refine ⟨3357919063612977315975283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4477225418150636421300377 3357919063612977315975283)
                      ·
                        rfl

theorem cell23_6539524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_6539524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539524 prefixEnd_6539524 := by exact prefixLift 6539524
  have htrace : WordTrace (prefixWord ++ tailWord_6539524) baseStart_6539524 baseEnd_6539524 := by
    simpa [prefixWord, tailWord_6539524, baseEnd_6539524] using wordTrace_append hprefix tailTrace_6539524
  have hstable : (prefixWord ++ tailWord_6539524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539524).length < 2 ^ (prefixWord ++ tailWord_6539524).sum := by decide
  have hdescent : baseEnd_6539524 < baseStart_6539524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539553 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 4, 3, 3]
def baseStart_6539553 : Nat := 118140960795 + 6539553 * 2 ^ 59
def prefixEnd_6539553 : Nat := 4983230072969 + 3 ^ 40 * 6539553 * 2
def baseEnd_6539553 : Nat := 3357933954551957702512649

theorem tailTrace_6539553 : CollatzResearch.WordTrace tailWord_6539553 prefixEnd_6539553 3357933954551957702512649 := by
  unfold tailWord_6539553
  simp only [CollatzResearch.WordTrace]
  refine ⟨238517092877323822579207313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159011395251549215052804875 238517092877323822579207313)
  ·
    refine ⟨178887819657992866934405485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238517092877323822579207313 178887819657992866934405485)
    ·
      refine ⟨67082932371747325100402057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178887819657992866934405485 67082932371747325100402057)
      ·
        refine ⟨50312199278810493825301543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67082932371747325100402057 50312199278810493825301543)
        ·
          refine ⟨75468298918215740737952315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50312199278810493825301543 75468298918215740737952315)
          ·
            refine ⟨113202448377323611106928473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75468298918215740737952315 113202448377323611106928473)
            ·
              refine ⟨84901836282992708330196355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113202448377323611106928473 84901836282992708330196355)
              ·
                refine ⟨127352754424489062495294533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84901836282992708330196355 127352754424489062495294533)
                ·
                  refine ⟨23878641454591699217867725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127352754424489062495294533 23878641454591699217867725)
                  ·
                    refine ⟨8954490545471887206700397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23878641454591699217867725 8954490545471887206700397)
                    ·
                      refine ⟨3357933954551957702512649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8954490545471887206700397 3357933954551957702512649)
                      ·
                        rfl

theorem cell23_6539553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_6539553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539553 prefixEnd_6539553 := by exact prefixLift 6539553
  have htrace : WordTrace (prefixWord ++ tailWord_6539553) baseStart_6539553 baseEnd_6539553 := by
    simpa [prefixWord, tailWord_6539553, baseEnd_6539553] using wordTrace_append hprefix tailTrace_6539553
  have hstable : (prefixWord ++ tailWord_6539553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539553).length < 2 ^ (prefixWord ++ tailWord_6539553).sum := by decide
  have hdescent : baseEnd_6539553 < baseStart_6539553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539573 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 4, 5]
def baseStart_6539573 : Nat := 118140960795 + 6539573 * 2 ^ 59
def prefixEnd_6539573 : Nat := 4983230072969 + 3 ^ 40 * 6539573 * 2
def baseEnd_6539573 : Nat := 1119314741388349208087519

theorem tailTrace_6539573 : CollatzResearch.WordTrace tailWord_6539573 prefixEnd_6539573 1119314741388349208087519 := by
  unfold tailWord_6539573
  simp only [CollatzResearch.WordTrace]
  refine ⟨238517822337251365994935373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159011881558167577329956915 238517822337251365994935373)
  ·
    refine ⟨89444183376469262248100765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238517822337251365994935373 89444183376469262248100765)
    ·
      refine ⟨33541568766175973343037787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89444183376469262248100765 33541568766175973343037787)
      ·
        refine ⟨50312353149263960014556681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33541568766175973343037787 50312353149263960014556681)
        ·
          refine ⟨37734264861947970010917511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50312353149263960014556681 37734264861947970010917511)
          ·
            refine ⟨56601397292921955016376267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37734264861947970010917511 56601397292921955016376267)
            ·
              refine ⟨84902095939382932524564401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56601397292921955016376267 84902095939382932524564401)
              ·
                refine ⟨63676571954537199393423301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84902095939382932524564401 63676571954537199393423301)
                ·
                  refine ⟨11939357241475724886266869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63676571954537199393423301 11939357241475724886266869)
                  ·
                    refine ⟨1119314741388349208087519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11939357241475724886266869 1119314741388349208087519)
                    ·
                      rfl

theorem cell23_6539573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_6539573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539573 prefixEnd_6539573 := by exact prefixLift 6539573
  have htrace : WordTrace (prefixWord ++ tailWord_6539573) baseStart_6539573 baseEnd_6539573 := by
    simpa [prefixWord, tailWord_6539573, baseEnd_6539573] using wordTrace_append hprefix tailTrace_6539573
  have hstable : (prefixWord ++ tailWord_6539573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539573).length < 2 ^ (prefixWord ++ tailWord_6539573).sum := by decide
  have hdescent : baseEnd_6539573 < baseStart_6539573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539603 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 7, 4]
def baseStart_6539603 : Nat := 118140960795 + 6539603 * 2 ^ 59
def prefixEnd_6539603 : Nat := 4983230072969 + 3 ^ 40 * 6539603 * 2
def baseEnd_6539603 : Nat := 1119319876194894168962473

theorem tailTrace_6539603 : CollatzResearch.WordTrace tailWord_6539603 prefixEnd_6539603 1119319876194894168962473 := by
  unfold tailWord_6539603
  simp only [CollatzResearch.WordTrace]
  refine ⟨238518916527142681118527463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159012611018095120745684975 238518916527142681118527463)
  ·
    refine ⟨357778374790714021677791195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238518916527142681118527463 357778374790714021677791195)
    ·
      refine ⟨536667562186071032516686793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357778374790714021677791195 536667562186071032516686793)
      ·
        refine ⟨402500671639553274387515095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536667562186071032516686793 402500671639553274387515095)
        ·
          refine ⟨603751007459329911581272643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402500671639553274387515095 603751007459329911581272643)
          ·
            refine ⟨905626511188994867371908965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603751007459329911581272643 905626511188994867371908965)
            ·
              refine ⟨169804970847936537632232931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 905626511188994867371908965 169804970847936537632232931)
              ·
                refine ⟨254707456271904806448349397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169804970847936537632232931 254707456271904806448349397)
                ·
                  refine ⟨5969706006372768901133189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 254707456271904806448349397 5969706006372768901133189)
                  ·
                    refine ⟨1119319876194894168962473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5969706006372768901133189 1119319876194894168962473)
                    ·
                      rfl

theorem cell23_6539603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 4].length) (baseStart_6539603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539603 prefixEnd_6539603 := by exact prefixLift 6539603
  have htrace : WordTrace (prefixWord ++ tailWord_6539603) baseStart_6539603 baseEnd_6539603 := by
    simpa [prefixWord, tailWord_6539603, baseEnd_6539603] using wordTrace_append hprefix tailTrace_6539603
  have hstable : (prefixWord ++ tailWord_6539603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539603).length < 2 ^ (prefixWord ++ tailWord_6539603).sum := by decide
  have hdescent : baseEnd_6539603 < baseStart_6539603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539610 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2]
def baseStart_6539610 : Nat := 118140960795 + 6539610 * 2 ^ 59
def prefixEnd_6539610 : Nat := 4983230072969 + 3 ^ 40 * 6539610 * 2
def baseEnd_6539610 : Nat := 3357963222949263979499887

theorem tailTrace_6539610 : CollatzResearch.WordTrace tailWord_6539610 prefixEnd_6539610 3357963222949263979499887 := by
  unfold tailWord_6539610
  simp only [CollatzResearch.WordTrace]
  refine ⟨59629792959529330328508071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159012781225411547542688189 59629792959529330328508071)
  ·
    refine ⟨89444689439293995492762107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59629792959529330328508071 89444689439293995492762107)
    ·
      refine ⟨134167034158940993239143161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89444689439293995492762107 134167034158940993239143161)
      ·
        refine ⟨100625275619205744929357371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134167034158940993239143161 100625275619205744929357371)
        ·
          refine ⟨150937913428808617394036057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100625275619205744929357371 150937913428808617394036057)
          ·
            refine ⟨113203435071606463045527043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150937913428808617394036057 113203435071606463045527043)
            ·
              refine ⟨169805152607409694568290565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113203435071606463045527043 169805152607409694568290565)
              ·
                refine ⟨31838466113889317731554481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169805152607409694568290565 31838466113889317731554481)
                ·
                  refine ⟨23878849585416988298665861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31838466113889317731554481 23878849585416988298665861)
                  ·
                    refine ⟨4477284297265685305999849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23878849585416988298665861 4477284297265685305999849)
                    ·
                      refine ⟨3357963222949263979499887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4477284297265685305999849 3357963222949263979499887)
                      ·
                        rfl

theorem cell23_6539610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_6539610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539610 prefixEnd_6539610 := by exact prefixLift 6539610
  have htrace : WordTrace (prefixWord ++ tailWord_6539610) baseStart_6539610 baseEnd_6539610 := by
    simpa [prefixWord, tailWord_6539610, baseEnd_6539610] using wordTrace_append hprefix tailTrace_6539610
  have hstable : (prefixWord ++ tailWord_6539610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539610).length < 2 ^ (prefixWord ++ tailWord_6539610).sum := by decide
  have hdescent : baseEnd_6539610 < baseStart_6539610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539620 : List Nat := [2, 3, 1, 1, 3, 1, 2, 3, 3, 4]
def baseStart_6539620 : Nat := 118140960795 + 6539620 * 2 ^ 59
def prefixEnd_6539620 : Nat := 4983230072969 + 3 ^ 40 * 6539620 * 2
def baseEnd_6539620 : Nat := 1119322785918602980124947

theorem tailTrace_6539620 : CollatzResearch.WordTrace tailWord_6539620 prefixEnd_6539620 1119322785918602980124947 := by
  unfold tailWord_6539620
  simp only [CollatzResearch.WordTrace]
  refine ⟨119259768284040546510948157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159013024378720728681264209 119259768284040546510948157)
  ·
    refine ⟨44722413106515204941605559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119259768284040546510948157 44722413106515204941605559)
    ·
      refine ⟨67083619659772807412408339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44722413106515204941605559 67083619659772807412408339)
      ·
        refine ⟨100625429489659211118612509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67083619659772807412408339 100625429489659211118612509)
        ·
          refine ⟨37734536058622204169479691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100625429489659211118612509 37734536058622204169479691)
          ·
            refine ⟨56601804087933306254219537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37734536058622204169479691 56601804087933306254219537)
            ·
              refine ⟨42451353065949979690664653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56601804087933306254219537 42451353065949979690664653)
              ·
                refine ⟨15919257399731242383999245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42451353065949979690664653 15919257399731242383999245)
                ·
                  refine ⟨5969721524899215893999717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15919257399731242383999245 5969721524899215893999717)
                  ·
                    refine ⟨1119322785918602980124947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5969721524899215893999717 1119322785918602980124947)
                    ·
                      rfl

theorem cell23_6539620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_6539620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539620 prefixEnd_6539620 := by exact prefixLift 6539620
  have htrace : WordTrace (prefixWord ++ tailWord_6539620) baseStart_6539620 baseEnd_6539620 := by
    simpa [prefixWord, tailWord_6539620, baseEnd_6539620] using wordTrace_append hprefix tailTrace_6539620
  have hstable : (prefixWord ++ tailWord_6539620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539620).length < 2 ^ (prefixWord ++ tailWord_6539620).sum := by decide
  have hdescent : baseEnd_6539620 < baseStart_6539620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539637 : List Nat := [1, 3, 4, 1, 2, 2, 1, 2, 3, 4]
def baseStart_6539637 : Nat := 118140960795 + 6539637 * 2 ^ 59
def prefixEnd_6539637 : Nat := 4983230072969 + 3 ^ 40 * 6539637 * 2
def baseEnd_6539637 : Nat := 1119325695642311791287421

theorem tailTrace_6539637 : CollatzResearch.WordTrace tailWord_6539637 prefixEnd_6539637 1119325695642311791287421 := by
  unfold tailWord_6539637
  simp only [CollatzResearch.WordTrace]
  refine ⟨238520156609019504925265165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159013437739346336616843443 238520156609019504925265165)
  ·
    refine ⟨89445058728382314346974437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238520156609019504925265165 89445058728382314346974437)
    ·
      refine ⟨16770948511571683940057707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89445058728382314346974437 16770948511571683940057707)
      ·
        refine ⟨25156422767357525910086561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16770948511571683940057707 25156422767357525910086561)
        ·
          refine ⟨18867317075518144432564921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25156422767357525910086561 18867317075518144432564921)
          ·
            refine ⟨14150487806638608324423691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18867317075518144432564921 14150487806638608324423691)
            ·
              refine ⟨21225731709957912486635537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14150487806638608324423691 21225731709957912486635537)
              ·
                refine ⟨15919298782468434364976653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21225731709957912486635537 15919298782468434364976653)
                ·
                  refine ⟨5969737043425662886866245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15919298782468434364976653 5969737043425662886866245)
                  ·
                    refine ⟨1119325695642311791287421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5969737043425662886866245 1119325695642311791287421)
                    ·
                      rfl

theorem cell23_6539637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_6539637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539637 prefixEnd_6539637 := by exact prefixLift 6539637
  have htrace : WordTrace (prefixWord ++ tailWord_6539637) baseStart_6539637 baseEnd_6539637 := by
    simpa [prefixWord, tailWord_6539637, baseEnd_6539637] using wordTrace_append hprefix tailTrace_6539637
  have hstable : (prefixWord ++ tailWord_6539637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539637).length < 2 ^ (prefixWord ++ tailWord_6539637).sum := by decide
  have hdescent : baseEnd_6539637 < baseStart_6539637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539687 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 1, 5, 2]
def baseStart_6539687 : Nat := 118140960795 + 6539687 * 2 ^ 59
def prefixEnd_6539687 : Nat := 4983230072969 + 3 ^ 40 * 6539687 * 2
def baseEnd_6539687 : Nat := 3358002760959660178237033

theorem tailTrace_6539687 : CollatzResearch.WordTrace tailWord_6539687 prefixEnd_6539687 3358002760959660178237033 := by
  unfold tailWord_6539687
  simp only [CollatzResearch.WordTrace]
  refine ⟨238521980258838363464585315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159014653505892242309723543 238521980258838363464585315)
  ·
    refine ⟨357782970388257545196877973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238521980258838363464585315 357782970388257545196877973)
    ·
      refine ⟨16771076736949572431103655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 357782970388257545196877973 16771076736949572431103655)
      ·
        refine ⟨25156615105424358646655483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16771076736949572431103655 25156615105424358646655483)
        ·
          refine ⟨37734922658136537969983225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25156615105424358646655483 37734922658136537969983225)
          ·
            refine ⟨28301191993602403477487419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37734922658136537969983225 28301191993602403477487419)
            ·
              refine ⟨42451787990403605216231129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28301191993602403477487419 42451787990403605216231129)
              ·
                refine ⟨31838840992802703912173347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42451787990403605216231129 31838840992802703912173347)
                ·
                  refine ⟨47758261489204055868260021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31838840992802703912173347 47758261489204055868260021)
                  ·
                    refine ⟨4477337014612880237649377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47758261489204055868260021 4477337014612880237649377)
                    ·
                      refine ⟨3358002760959660178237033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4477337014612880237649377 3358002760959660178237033)
                      ·
                        rfl

theorem cell23_6539687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_6539687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539687 prefixEnd_6539687 := by exact prefixLift 6539687
  have htrace : WordTrace (prefixWord ++ tailWord_6539687) baseStart_6539687 baseEnd_6539687 := by
    simpa [prefixWord, tailWord_6539687, baseEnd_6539687] using wordTrace_append hprefix tailTrace_6539687
  have hstable : (prefixWord ++ tailWord_6539687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539687).length < 2 ^ (prefixWord ++ tailWord_6539687).sum := by decide
  have hdescent : baseEnd_6539687 < baseStart_6539687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539697 : List Nat := [1, 2, 2, 4, 1, 3, 2, 2, 1, 5]
def baseStart_6539697 : Nat := 118140960795 + 6539697 * 2 ^ 59
def prefixEnd_6539697 : Nat := 4983230072969 + 3 ^ 40 * 6539697 * 2
def baseEnd_6539697 : Nat := 1119335965255401713037329

theorem tailTrace_6539697 : CollatzResearch.WordTrace tailWord_6539697 prefixEnd_6539697 1119335965255401713037329 := by
  unfold tailWord_6539697
  simp only [CollatzResearch.WordTrace]
  refine ⟨238522344988802135172449345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159014896659201423448299563 238522344988802135172449345)
  ·
    refine ⟨178891758741601601379337009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238522344988802135172449345 178891758741601601379337009)
    ·
      refine ⟨134168819056201201034502757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178891758741601601379337009 134168819056201201034502757)
      ·
        refine ⟨25156653573037725193969267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134168819056201201034502757 25156653573037725193969267)
        ·
          refine ⟨37734980359556587790953901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25156653573037725193969267 37734980359556587790953901)
          ·
            refine ⟨14150617634833720421607713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37734980359556587790953901 14150617634833720421607713)
            ·
              refine ⟨10612963226125290316205785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14150617634833720421607713 10612963226125290316205785)
              ·
                refine ⟨7959722419593967737154339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10612963226125290316205785 7959722419593967737154339)
                ·
                  refine ⟨11939583629390951605731509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7959722419593967737154339 11939583629390951605731509)
                  ·
                    refine ⟨1119335965255401713037329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11939583629390951605731509 1119335965255401713037329)
                    ·
                      rfl

theorem cell23_6539697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 5].length) (baseStart_6539697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539697 prefixEnd_6539697 := by exact prefixLift 6539697
  have htrace : WordTrace (prefixWord ++ tailWord_6539697) baseStart_6539697 baseEnd_6539697 := by
    simpa [prefixWord, tailWord_6539697, baseEnd_6539697] using wordTrace_append hprefix tailTrace_6539697
  have hstable : (prefixWord ++ tailWord_6539697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539697).length < 2 ^ (prefixWord ++ tailWord_6539697).sum := by decide
  have hdescent : baseEnd_6539697 < baseStart_6539697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539710 : List Nat := [4, 2, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_6539710 : Nat := 118140960795 + 6539710 * 2 ^ 59
def prefixEnd_6539710 : Nat := 4983230072969 + 3 ^ 40 * 6539710 * 2
def baseEnd_6539710 : Nat := 1119338190338237862749809

theorem tailTrace_6539710 : CollatzResearch.WordTrace tailWord_6539710 prefixEnd_6539710 1119338190338237862749809 := by
  unfold tailWord_6539710
  simp only [CollatzResearch.WordTrace]
  refine ⟨29815352392219379799084073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159015212758503358928448389 29815352392219379799084073)
  ·
    refine ⟨22361514294164534849313055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29815352392219379799084073 22361514294164534849313055)
    ·
      refine ⟨33542271441246802273969583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22361514294164534849313055 33542271441246802273969583)
      ·
        refine ⟨50313407161870203410954375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33542271441246802273969583 50313407161870203410954375)
        ·
          refine ⟨75470110742805305116431563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50313407161870203410954375 75470110742805305116431563)
          ·
            refine ⟨113205166114207957674647345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75470110742805305116431563 113205166114207957674647345)
            ·
              refine ⟨84903874585655968255985509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113205166114207957674647345 84903874585655968255985509)
              ·
                refine ⟨15919476484810494047997283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84903874585655968255985509 15919476484810494047997283)
                ·
                  refine ⟨23879214727215741071995925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15919476484810494047997283 23879214727215741071995925)
                  ·
                    refine ⟨1119338190338237862749809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23879214727215741071995925 1119338190338237862749809)
                    ·
                      rfl

theorem cell23_6539710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_6539710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539710 prefixEnd_6539710 := by exact prefixLift 6539710
  have htrace : WordTrace (prefixWord ++ tailWord_6539710) baseStart_6539710 baseEnd_6539710 := by
    simpa [prefixWord, tailWord_6539710, baseEnd_6539710] using wordTrace_append hprefix tailTrace_6539710
  have hstable : (prefixWord ++ tailWord_6539710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539710).length < 2 ^ (prefixWord ++ tailWord_6539710).sum := by decide
  have hdescent : baseEnd_6539710 < baseStart_6539710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539720 : List Nat := [2, 1, 3, 1, 3, 2, 1, 3, 1, 1, 5]
def baseStart_6539720 : Nat := 118140960795 + 6539720 * 2 ^ 59
def prefixEnd_6539720 : Nat := 4983230072969 + 3 ^ 40 * 6539720 * 2
def baseEnd_6539720 : Nat := 3358019705821258549124381

theorem tailTrace_6539720 : CollatzResearch.WordTrace tailWord_6539720 prefixEnd_6539720 3358019705821258549124381 := by
  unfold tailWord_6539720
  simp only [CollatzResearch.WordTrace]
  refine ⟨119261591933859405050268307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159015455911812540067024409 119261591933859405050268307)
  ·
    refine ⟨178892387900789107575402461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119261591933859405050268307 178892387900789107575402461)
    ·
      refine ⟨67084645462795915340775923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178892387900789107575402461 67084645462795915340775923)
      ·
        refine ⟨100626968194193873011163885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67084645462795915340775923 100626968194193873011163885)
        ·
          refine ⟨37735113072822702379186457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100626968194193873011163885 37735113072822702379186457)
          ·
            refine ⟨28301334804617026784389843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37735113072822702379186457 28301334804617026784389843)
            ·
              refine ⟨42452002206925540176584765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28301334804617026784389843 42452002206925540176584765)
              ·
                refine ⟨15919500827597077566219287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42452002206925540176584765 15919500827597077566219287)
                ·
                  refine ⟨23879251241395616349328931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15919500827597077566219287 23879251241395616349328931)
                  ·
                    refine ⟨35818876862093424523993397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23879251241395616349328931 35818876862093424523993397)
                    ·
                      refine ⟨3358019705821258549124381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35818876862093424523993397 3358019705821258549124381)
                      ·
                        rfl

theorem cell23_6539720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_6539720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539720 prefixEnd_6539720 := by exact prefixLift 6539720
  have htrace : WordTrace (prefixWord ++ tailWord_6539720) baseStart_6539720 baseEnd_6539720 := by
    simpa [prefixWord, tailWord_6539720, baseEnd_6539720] using wordTrace_append hprefix tailTrace_6539720
  have hstable : (prefixWord ++ tailWord_6539720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539720).length < 2 ^ (prefixWord ++ tailWord_6539720).sum := by decide
  have hdescent : baseEnd_6539720 < baseStart_6539720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539753 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 4, 7]
def baseStart_6539753 : Nat := 118140960795 + 6539753 * 2 ^ 59
def prefixEnd_6539753 : Nat := 4983230072969 + 3 ^ 40 * 6539753 * 2
def baseEnd_6539753 : Nat := 1119345550227618973337243

theorem tailTrace_6539753 : CollatzResearch.WordTrace tailWord_6539753 prefixEnd_6539753 1119345550227618973337243 := by
  unfold tailWord_6539753
  simp only [CollatzResearch.WordTrace]
  refine ⟨238524387476599256736487913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159016258317732837824325275 238524387476599256736487913)
  ·
    refine ⟨178893290607449442552365935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238524387476599256736487913 178893290607449442552365935)
    ·
      refine ⟨268339935911174163828548903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178893290607449442552365935 268339935911174163828548903)
      ·
        refine ⟨402509903866761245742823355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268339935911174163828548903 402509903866761245742823355)
        ·
          refine ⟨603764855800141868614235033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402509903866761245742823355 603764855800141868614235033)
          ·
            refine ⟨452823641850106401460676275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 603764855800141868614235033 452823641850106401460676275)
            ·
              refine ⟨679235462775159602191014413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452823641850106401460676275 679235462775159602191014413)
              ·
                refine ⟨254713298540684850821630405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 679235462775159602191014413 254713298540684850821630405)
                ·
                  refine ⟨47758743476378409529055701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 254713298540684850821630405 47758743476378409529055701)
                  ·
                    refine ⟨1119345550227618973337243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47758743476378409529055701 1119345550227618973337243)
                    ·
                      rfl

theorem cell23_6539753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 7].length) (baseStart_6539753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539753 prefixEnd_6539753 := by exact prefixLift 6539753
  have htrace : WordTrace (prefixWord ++ tailWord_6539753) baseStart_6539753 baseEnd_6539753 := by
    simpa [prefixWord, tailWord_6539753, baseEnd_6539753] using wordTrace_append hprefix tailTrace_6539753
  have hstable : (prefixWord ++ tailWord_6539753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539753).length < 2 ^ (prefixWord ++ tailWord_6539753).sum := by decide
  have hdescent : baseEnd_6539753 < baseStart_6539753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539754 : List Nat := [3, 1, 3, 1, 3, 1, 3, 2, 1, 2, 3]
def baseStart_6539754 : Nat := 118140960795 + 6539754 * 2 ^ 59
def prefixEnd_6539754 : Nat := 4983230072969 + 3 ^ 40 * 6539754 * 2
def baseEnd_6539754 : Nat := 3358037164163511416099225

theorem tailTrace_6539754 : CollatzResearch.WordTrace tailWord_6539754 prefixEnd_6539754 3358037164163511416099225 := by
  unfold tailWord_6539754
  simp only [CollatzResearch.WordTrace]
  refine ⟨59631105987398908476818579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159016282633063755938182877 59631105987398908476818579)
  ·
    refine ⟨89446658981098362715227869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59631105987398908476818579 89446658981098362715227869)
    ·
      refine ⟨33542497117911886018210451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89446658981098362715227869 33542497117911886018210451)
      ·
        refine ⟨50313745676867829027315677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33542497117911886018210451 50313745676867829027315677)
        ·
          refine ⟨18867654628825435885243379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50313745676867829027315677 18867654628825435885243379)
          ·
            refine ⟨28301481943238153827865069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18867654628825435885243379 28301481943238153827865069)
            ·
              refine ⟨10613055728714307685449401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28301481943238153827865069 10613055728714307685449401)
              ·
                refine ⟨7959791796535730764087051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10613055728714307685449401 7959791796535730764087051)
                ·
                  refine ⟨11939687694803596146130577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7959791796535730764087051 11939687694803596146130577)
                  ·
                    refine ⟨8954765771102697109597933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11939687694803596146130577 8954765771102697109597933)
                    ·
                      refine ⟨3358037164163511416099225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8954765771102697109597933 3358037164163511416099225)
                      ·
                        rfl

theorem cell23_6539754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_6539754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539754 prefixEnd_6539754 := by exact prefixLift 6539754
  have htrace : WordTrace (prefixWord ++ tailWord_6539754) baseStart_6539754 baseEnd_6539754 := by
    simpa [prefixWord, tailWord_6539754, baseEnd_6539754] using wordTrace_append hprefix tailTrace_6539754
  have hstable : (prefixWord ++ tailWord_6539754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539754).length < 2 ^ (prefixWord ++ tailWord_6539754).sum := by decide
  have hdescent : baseEnd_6539754 < baseStart_6539754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539800 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 1, 8]
def baseStart_6539800 : Nat := 118140960795 + 6539800 * 2 ^ 59
def prefixEnd_6539800 : Nat := 4983230072969 + 3 ^ 40 * 6539800 * 2
def baseEnd_6539800 : Nat := 1119353594757872745374671

theorem tailTrace_6539800 : CollatzResearch.WordTrace tailWord_6539800 prefixEnd_6539800 1119353594757872745374671 := by
  unfold tailWord_6539800
  simp only [CollatzResearch.WordTrace]
  refine ⟨119263050853714491881724427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159017401138285989175632569 119263050853714491881724427)
  ·
    refine ⟨178894576280571737822586641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119263050853714491881724427 178894576280571737822586641)
    ·
      refine ⟨134170932210428803366939981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178894576280571737822586641 134170932210428803366939981)
      ·
        refine ⟨50314099578910801262602493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134170932210428803366939981 50314099578910801262602493)
        ·
          refine ⟨18867787342091550473475935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50314099578910801262602493 18867787342091550473475935)
          ·
            refine ⟨28301681013137325710213903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18867787342091550473475935 28301681013137325710213903)
            ·
              refine ⟨42452521519705988565320855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28301681013137325710213903 42452521519705988565320855)
              ·
                refine ⟨63678782279558982847981283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42452521519705988565320855 63678782279558982847981283)
                ·
                  refine ⟨95518173419338474271971925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63678782279558982847981283 95518173419338474271971925)
                  ·
                    refine ⟨1119353594757872745374671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95518173419338474271971925 1119353594757872745374671)
                    ·
                      rfl

theorem cell23_6539800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_6539800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539800 prefixEnd_6539800 := by exact prefixLift 6539800
  have htrace : WordTrace (prefixWord ++ tailWord_6539800) baseStart_6539800 baseEnd_6539800 := by
    simpa [prefixWord, tailWord_6539800, baseEnd_6539800] using wordTrace_append hprefix tailTrace_6539800
  have hstable : (prefixWord ++ tailWord_6539800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539800).length < 2 ^ (prefixWord ++ tailWord_6539800).sum := by decide
  have hdescent : baseEnd_6539800 < baseStart_6539800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539837 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 2, 2, 4]
def baseStart_6539837 : Nat := 118140960795 + 6539837 * 2 ^ 59
def prefixEnd_6539837 : Nat := 4983230072969 + 3 ^ 40 * 6539837 * 2
def baseEnd_6539837 : Nat := 3358079783057834591361343

theorem tailTrace_6539837 : CollatzResearch.WordTrace tailWord_6539837 prefixEnd_6539837 3358079783057834591361343 := by
  unfold tailWord_6539837
  simp only [CollatzResearch.WordTrace]
  refine ⟨238527451208294939082545765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159018300805529959388363843 238527451208294939082545765)
  ·
    refine ⟨44723897101555301077977331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238527451208294939082545765 44723897101555301077977331)
    ·
      refine ⟨67085845652332951616965997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44723897101555301077977331 67085845652332951616965997)
      ·
        refine ⟨25157192119624856856362249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67085845652332951616965997 25157192119624856856362249)
        ·
          refine ⟨18867894089718642642271687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25157192119624856856362249 18867894089718642642271687)
          ·
            refine ⟨28301841134577963963407531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18867894089718642642271687 28301841134577963963407531)
            ·
              refine ⟨42452761701866945945111297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28301841134577963963407531 42452761701866945945111297)
              ·
                refine ⟨31839571276400209458833473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42452761701866945945111297 31839571276400209458833473)
                ·
                  refine ⟨23879678457300157094125105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31839571276400209458833473 23879678457300157094125105)
                  ·
                    refine ⟨17909758842975117820593829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23879678457300157094125105 17909758842975117820593829)
                    ·
                      refine ⟨3358079783057834591361343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17909758842975117820593829 3358079783057834591361343)
                      ·
                        rfl

theorem cell23_6539837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_6539837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539837 prefixEnd_6539837 := by exact prefixLift 6539837
  have htrace : WordTrace (prefixWord ++ tailWord_6539837) baseStart_6539837 baseEnd_6539837 := by
    simpa [prefixWord, tailWord_6539837, baseEnd_6539837] using wordTrace_append hprefix tailTrace_6539837
  have hstable : (prefixWord ++ tailWord_6539837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539837).length < 2 ^ (prefixWord ++ tailWord_6539837).sum := by decide
  have hdescent : baseEnd_6539837 < baseStart_6539837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539841 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 4, 2, 2]
def baseStart_6539841 : Nat := 118140960795 + 6539841 * 2 ^ 59
def prefixEnd_6539841 : Nat := 4983230072969 + 3 ^ 40 * 6539841 * 2
def baseEnd_6539841 : Nat := 3358081836980452575711325

theorem tailTrace_6539841 : CollatzResearch.WordTrace tailWord_6539841 prefixEnd_6539841 3358081836980452575711325 := by
  unfold tailWord_6539841
  simp only [CollatzResearch.WordTrace]
  refine ⟨238527597100280447765691377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159018398066853631843794251 238527597100280447765691377)
  ·
    refine ⟨178895697825210335824268533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238527597100280447765691377 178895697825210335824268533)
    ·
      refine ⟨16771471671113468983525175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178895697825210335824268533 16771471671113468983525175)
      ·
        refine ⟨25157207506670203475287763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16771471671113468983525175 25157207506670203475287763)
        ·
          refine ⟨37735811260005305212931645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25157207506670203475287763 37735811260005305212931645)
          ·
            refine ⟨14150929222501989454849367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37735811260005305212931645 14150929222501989454849367)
            ·
              refine ⟨21226393833752984182274051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14150929222501989454849367 21226393833752984182274051)
              ·
                refine ⟨31839590750629476273411077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21226393833752984182274051 31839590750629476273411077)
                ·
                  refine ⟨5969923265743026801264577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31839590750629476273411077 5969923265743026801264577)
                  ·
                    refine ⟨4477442449307270100948433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5969923265743026801264577 4477442449307270100948433)
                    ·
                      refine ⟨3358081836980452575711325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4477442449307270100948433 3358081836980452575711325)
                      ·
                        rfl

theorem cell23_6539841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_6539841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539841 prefixEnd_6539841 := by exact prefixLift 6539841
  have htrace : WordTrace (prefixWord ++ tailWord_6539841) baseStart_6539841 baseEnd_6539841 := by
    simpa [prefixWord, tailWord_6539841, baseEnd_6539841] using wordTrace_append hprefix tailTrace_6539841
  have hstable : (prefixWord ++ tailWord_6539841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539841).length < 2 ^ (prefixWord ++ tailWord_6539841).sum := by decide
  have hdescent : baseEnd_6539841 < baseStart_6539841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539847 : List Nat := [1, 1, 4, 1, 4, 2, 2, 1, 7]
def baseStart_6539847 : Nat := 118140960795 + 6539847 * 2 ^ 59
def prefixEnd_6539847 : Nat := 4983230072969 + 3 ^ 40 * 6539847 * 2
def baseEnd_6539847 : Nat := 373120546429375505804033

theorem tailTrace_6539847 : CollatzResearch.WordTrace tailWord_6539847 prefixEnd_6539847 373120546429375505804033 := by
  unfold tailWord_6539847
  simp only [CollatzResearch.WordTrace]
  refine ⟨238527815938258710790409795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159018543958839140526939863 238527815938258710790409795)
  ·
    refine ⟨357791723907388066185614693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238527815938258710790409795 357791723907388066185614693)
    ·
      refine ⟨67085948232635262409802755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 357791723907388066185614693 67085948232635262409802755)
      ·
        refine ⟨100628922348952893614704133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67085948232635262409802755 100628922348952893614704133)
        ·
          refine ⟨18867922940428667552757025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100628922348952893614704133 18867922940428667552757025)
          ·
            refine ⟨14150942205321500664567769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18867922940428667552757025 14150942205321500664567769)
            ·
              refine ⟨10613206653991125498425827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14150942205321500664567769 10613206653991125498425827)
              ·
                refine ⟨15919809980986688247638741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10613206653991125498425827 15919809980986688247638741)
                ·
                  refine ⟨373120546429375505804033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15919809980986688247638741 373120546429375505804033)
                  ·
                    rfl

theorem cell23_6539847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 7].length) (baseStart_6539847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539847 prefixEnd_6539847 := by exact prefixLift 6539847
  have htrace : WordTrace (prefixWord ++ tailWord_6539847) baseStart_6539847 baseEnd_6539847 := by
    simpa [prefixWord, tailWord_6539847, baseEnd_6539847] using wordTrace_append hprefix tailTrace_6539847
  have hstable : (prefixWord ++ tailWord_6539847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539847).length < 2 ^ (prefixWord ++ tailWord_6539847).sum := by decide
  have hdescent : baseEnd_6539847 < baseStart_6539847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539857 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 2, 3, 3]
def baseStart_6539857 : Nat := 118140960795 + 6539857 * 2 ^ 59
def prefixEnd_6539857 : Nat := 4983230072969 + 3 ^ 40 * 6539857 * 2
def baseEnd_6539857 : Nat := 3358090052670924513111251

theorem tailTrace_6539857 : CollatzResearch.WordTrace tailWord_6539857 prefixEnd_6539857 3358090052670924513111251 := by
  unfold tailWord_6539857
  simp only [CollatzResearch.WordTrace]
  refine ⟨238528180668222482498273825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159018787112148321665515883 238528180668222482498273825)
  ·
    refine ⟨178896135501166861873705369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238528180668222482498273825 178896135501166861873705369)
    ·
      refine ⟨134172101625875146405279027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178896135501166861873705369 134172101625875146405279027)
      ·
        refine ⟨201258152438812719607918541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134172101625875146405279027 201258152438812719607918541)
        ·
          refine ⟨75471807164554769852969453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201258152438812719607918541 75471807164554769852969453)
          ·
            refine ⟨28301927686708038694863545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75471807164554769852969453 28301927686708038694863545)
            ·
              refine ⟨21226445765031029021147659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28301927686708038694863545 21226445765031029021147659)
              ·
                refine ⟨31839668647546543531721489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21226445765031029021147659 31839668647546543531721489)
                ·
                  refine ⟨23879751485659907648791117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31839668647546543531721489 23879751485659907648791117)
                  ·
                    refine ⟨8954906807122465368296669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23879751485659907648791117 8954906807122465368296669)
                    ·
                      refine ⟨3358090052670924513111251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8954906807122465368296669 3358090052670924513111251)
                      ·
                        rfl

theorem cell23_6539857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 3, 3].length) (baseStart_6539857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539857 prefixEnd_6539857 := by exact prefixLift 6539857
  have htrace : WordTrace (prefixWord ++ tailWord_6539857) baseStart_6539857 baseEnd_6539857 := by
    simpa [prefixWord, tailWord_6539857, baseEnd_6539857] using wordTrace_append hprefix tailTrace_6539857
  have hstable : (prefixWord ++ tailWord_6539857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539857).length < 2 ^ (prefixWord ++ tailWord_6539857).sum := by decide
  have hdescent : baseEnd_6539857 < baseStart_6539857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539858 : List Nat := [3, 2, 2, 1, 2, 1, 5, 1, 2, 2, 2]
def baseStart_6539858 : Nat := 118140960795 + 6539858 * 2 ^ 59
def prefixEnd_6539858 : Nat := 4983230072969 + 3 ^ 40 * 6539858 * 2
def baseEnd_6539858 : Nat := 3358090566151579009198747

theorem tailTrace_6539858 : CollatzResearch.WordTrace tailWord_6539858 prefixEnd_6539858 3358090566151579009198747 := by
  unfold tailWord_6539858
  simp only [CollatzResearch.WordTrace]
  refine ⟨59632054285304714917265057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159018811427479239779373485 59632054285304714917265057)
  ·
    refine ⟨44724040713978536187948793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59632054285304714917265057 44724040713978536187948793)
    ·
      refine ⟨33543030535483902140961595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44724040713978536187948793 33543030535483902140961595)
      ·
        refine ⟨50314545803225853211442393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33543030535483902140961595 50314545803225853211442393)
        ·
          refine ⟨37735909352419389908581795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50314545803225853211442393 37735909352419389908581795)
          ·
            refine ⟨56603864028629084862872693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37735909352419389908581795 56603864028629084862872693)
            ·
              refine ⟨5306612252683976705894315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56603864028629084862872693 5306612252683976705894315)
              ·
                refine ⟨7959918379025965058841473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5306612252683976705894315 7959918379025965058841473)
                ·
                  refine ⟨5969938784269473794131105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7959918379025965058841473 5969938784269473794131105)
                  ·
                    refine ⟨4477454088202105345598329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5969938784269473794131105 4477454088202105345598329)
                    ·
                      refine ⟨3358090566151579009198747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4477454088202105345598329 3358090566151579009198747)
                      ·
                        rfl

theorem cell23_6539858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_6539858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539858 prefixEnd_6539858 := by exact prefixLift 6539858
  have htrace : WordTrace (prefixWord ++ tailWord_6539858) baseStart_6539858 baseEnd_6539858 := by
    simpa [prefixWord, tailWord_6539858, baseEnd_6539858] using wordTrace_append hprefix tailTrace_6539858
  have hstable : (prefixWord ++ tailWord_6539858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539858).length < 2 ^ (prefixWord ++ tailWord_6539858).sum := by decide
  have hdescent : baseEnd_6539858 < baseStart_6539858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539897 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 4, 1, 4]
def baseStart_6539897 : Nat := 118140960795 + 6539897 * 2 ^ 59
def prefixEnd_6539897 : Nat := 4983230072969 + 3 ^ 40 * 6539897 * 2
def baseEnd_6539897 : Nat := 3358110591897104356611067

theorem tailTrace_6539897 : CollatzResearch.WordTrace tailWord_6539897 prefixEnd_6539897 3358110591897104356611067 := by
  unfold tailWord_6539897
  simp only [CollatzResearch.WordTrace]
  refine ⟨238529639588077569329729945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159019759725385046219819963 238529639588077569329729945)
  ·
    refine ⟨178897229691058176997297459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238529639588077569329729945 178897229691058176997297459)
    ·
      refine ⟨268345844536587265495946189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178897229691058176997297459 268345844536587265495946189)
      ·
        refine ⟨100629691701220224560979821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268345844536587265495946189 100629691701220224560979821)
        ·
          refine ⟨37736134387957584210367433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100629691701220224560979821 37736134387957584210367433)
          ·
            refine ⟨28302100790968188157775575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37736134387957584210367433 28302100790968188157775575)
            ·
              refine ⟨42453151186452282236663363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28302100790968188157775575 42453151186452282236663363)
              ·
                refine ⟨63679726779678423354995045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42453151186452282236663363 63679726779678423354995045)
                ·
                  refine ⟨11939948771189704379061571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63679726779678423354995045 11939948771189704379061571)
                  ·
                    refine ⟨17909923156784556568592357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11939948771189704379061571 17909923156784556568592357)
                    ·
                      refine ⟨3358110591897104356611067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17909923156784556568592357 3358110591897104356611067)
                      ·
                        rfl

theorem cell23_6539897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_6539897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539897 prefixEnd_6539897 := by exact prefixLift 6539897
  have htrace : WordTrace (prefixWord ++ tailWord_6539897) baseStart_6539897 baseEnd_6539897 := by
    simpa [prefixWord, tailWord_6539897, baseEnd_6539897] using wordTrace_append hprefix tailTrace_6539897
  have hstable : (prefixWord ++ tailWord_6539897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539897).length < 2 ^ (prefixWord ++ tailWord_6539897).sum := by decide
  have hdescent : baseEnd_6539897 < baseStart_6539897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539967 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 3, 5]
def baseStart_6539967 : Nat := 118140960795 + 6539967 * 2 ^ 59
def prefixEnd_6539967 : Nat := 4983230072969 + 3 ^ 40 * 6539967 * 2
def baseEnd_6539967 : Nat := 1119382178514306360911915

theorem tailTrace_6539967 : CollatzResearch.WordTrace tailWord_6539967 prefixEnd_6539967 1119382178514306360911915 := by
  unfold tailWord_6539967
  simp only [CollatzResearch.WordTrace]
  refine ⟨238532192697823971284778155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159021461798549314189852103 238532192697823971284778155)
  ·
    refine ⟨357798289046735956927167233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238532192697823971284778155 357798289046735956927167233)
    ·
      refine ⟨268348716785051967695375425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357798289046735956927167233 268348716785051967695375425)
      ·
        refine ⟨201261537588788975771531569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268348716785051967695375425 201261537588788975771531569)
        ·
          refine ⟨150946153191591731828648677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201261537588788975771531569 150946153191591731828648677)
          ·
            refine ⟨28302403723423449717871627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150946153191591731828648677 28302403723423449717871627)
            ·
              refine ⟨42453605585135174576807441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28302403723423449717871627 42453605585135174576807441)
              ·
                refine ⟨31840204188851380932605581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42453605585135174576807441 31840204188851380932605581)
                ·
                  refine ⟨11940076570819267849727093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31840204188851380932605581 11940076570819267849727093)
                  ·
                    refine ⟨1119382178514306360911915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11940076570819267849727093 1119382178514306360911915)
                    ·
                      rfl

theorem cell23_6539967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 5].length) (baseStart_6539967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539967 prefixEnd_6539967 := by exact prefixLift 6539967
  have htrace : WordTrace (prefixWord ++ tailWord_6539967) baseStart_6539967 baseEnd_6539967 := by
    simpa [prefixWord, tailWord_6539967, baseEnd_6539967] using wordTrace_append hprefix tailTrace_6539967
  have hstable : (prefixWord ++ tailWord_6539967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539967).length < 2 ^ (prefixWord ++ tailWord_6539967).sum := by decide
  have hdescent : baseEnd_6539967 < baseStart_6539967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6539991 : List Nat := [1, 1, 3, 2, 1, 4, 3, 1, 2, 3, 2]
def baseStart_6539991 : Nat := 118140960795 + 6539991 * 2 ^ 59
def prefixEnd_6539991 : Nat := 4983230072969 + 3 ^ 40 * 6539991 * 2
def baseEnd_6539991 : Nat := 3358158859078626988835635

theorem tailTrace_6539991 : CollatzResearch.WordTrace tailWord_6539991 prefixEnd_6539991 3358158859078626988835635 := by
  unfold tailWord_6539991
  simp only [CollatzResearch.WordTrace]
  refine ⟨238533068049737023383651827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159022045366491348922434551 238533068049737023383651827)
  ·
    refine ⟨357799602074605535075477741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238533068049737023383651827 357799602074605535075477741)
    ·
      refine ⟨134174850777977075653304153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357799602074605535075477741 134174850777977075653304153)
      ·
        refine ⟨100631138083482806739978115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134174850777977075653304153 100631138083482806739978115)
        ·
          refine ⟨150946707125224210109967173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100631138083482806739978115 150946707125224210109967173)
          ·
            refine ⟨28302507585979539395618845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150946707125224210109967173 28302507585979539395618845)
            ·
              refine ⟨10613440344742327273357067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28302507585979539395618845 10613440344742327273357067)
              ·
                refine ⟨15920160517113490910035601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10613440344742327273357067 15920160517113490910035601)
                ·
                  refine ⟨11940120387835118182526701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15920160517113490910035601 11940120387835118182526701)
                  ·
                    refine ⟨4477545145438169318447513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11940120387835118182526701 4477545145438169318447513)
                    ·
                      refine ⟨3358158859078626988835635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4477545145438169318447513 3358158859078626988835635)
                      ·
                        rfl

theorem cell23_6539991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_6539991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6539991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6539991 prefixEnd_6539991 := by exact prefixLift 6539991
  have htrace : WordTrace (prefixWord ++ tailWord_6539991) baseStart_6539991 baseEnd_6539991 := by
    simpa [prefixWord, tailWord_6539991, baseEnd_6539991] using wordTrace_append hprefix tailTrace_6539991
  have hstable : (prefixWord ++ tailWord_6539991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6539991).length < 2 ^ (prefixWord ++ tailWord_6539991).sum := by decide
  have hdescent : baseEnd_6539991 < baseStart_6539991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6539991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540001 : List Nat := [1, 2, 3, 1, 4, 1, 4, 1, 1, 5]
def baseStart_6540001 : Nat := 118140960795 + 6540001 * 2 ^ 59
def prefixEnd_6540001 : Nat := 4983230072969 + 3 ^ 40 * 6540001 * 2
def baseEnd_6540001 : Nat := 1119387997961723983236863

theorem tailTrace_6540001 : CollatzResearch.WordTrace tailWord_6540001 prefixEnd_6540001 1119387997961723983236863 := by
  unfold tailWord_6540001
  simp only [CollatzResearch.WordTrace]
  refine ⟨238533432779700795091515857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159022288519800530061010571 238533432779700795091515857)
  ·
    refine ⟨178900074584775596318636893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238533432779700795091515857 178900074584775596318636893)
    ·
      refine ⟨67087527969290848619488835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178900074584775596318636893 67087527969290848619488835)
      ·
        refine ⟨100631291953936272929233253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67087527969290848619488835 100631291953936272929233253)
        ·
          refine ⟨18868367241363051174231235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100631291953936272929233253 18868367241363051174231235)
          ·
            refine ⟨28302550862044576761346853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18868367241363051174231235 28302550862044576761346853)
            ·
              refine ⟨5306728286633358142752535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28302550862044576761346853 5306728286633358142752535)
              ·
                refine ⟨7960092429950037214128803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5306728286633358142752535 7960092429950037214128803)
                ·
                  refine ⟨11940138644925055821193205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7960092429950037214128803 11940138644925055821193205)
                  ·
                    refine ⟨1119387997961723983236863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11940138644925055821193205 1119387997961723983236863)
                    ·
                      rfl

theorem cell23_6540001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_6540001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540001 prefixEnd_6540001 := by exact prefixLift 6540001
  have htrace : WordTrace (prefixWord ++ tailWord_6540001) baseStart_6540001 baseEnd_6540001 := by
    simpa [prefixWord, tailWord_6540001, baseEnd_6540001] using wordTrace_append hprefix tailTrace_6540001
  have hstable : (prefixWord ++ tailWord_6540001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540001).length < 2 ^ (prefixWord ++ tailWord_6540001).sum := by decide
  have hdescent : baseEnd_6540001 < baseStart_6540001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540017 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 6]
def baseStart_6540017 : Nat := 118140960795 + 6540017 * 2 ^ 59
def prefixEnd_6540017 : Nat := 4983230072969 + 3 ^ 40 * 6540017 * 2
def baseEnd_6540017 : Nat := 3358172209575643887110515

theorem tailTrace_6540017 : CollatzResearch.WordTrace tailWord_6540017 prefixEnd_6540017 3358172209575643887110515 := by
  unfold tailWord_6540017
  simp only [CollatzResearch.WordTrace]
  refine ⟨238534016347642829824098305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159022677565095219882732203 238534016347642829824098305)
  ·
    refine ⟨178900512260732122368073729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238534016347642829824098305 178900512260732122368073729)
    ·
      refine ⟨134175384195549091776055297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178900512260732122368073729 134175384195549091776055297)
      ·
        refine ⟨100631538146661818832041473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134175384195549091776055297 100631538146661818832041473)
        ·
          refine ⟨75473653609996364124031105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100631538146661818832041473 75473653609996364124031105)
          ·
            refine ⟨56605240207497273093023329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75473653609996364124031105 56605240207497273093023329)
            ·
              refine ⟨42453930155622954819767497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56605240207497273093023329 42453930155622954819767497)
              ·
                refine ⟨31840447616717216114825623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42453930155622954819767497 31840447616717216114825623)
                ·
                  refine ⟨47760671425075824172238435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31840447616717216114825623 47760671425075824172238435)
                  ·
                    refine ⟨71641007137613736258357653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47760671425075824172238435 71641007137613736258357653)
                    ·
                      refine ⟨3358172209575643887110515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71641007137613736258357653 3358172209575643887110515)
                      ·
                        rfl

theorem cell23_6540017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_6540017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540017 prefixEnd_6540017 := by exact prefixLift 6540017
  have htrace : WordTrace (prefixWord ++ tailWord_6540017) baseStart_6540017 baseEnd_6540017 := by
    simpa [prefixWord, tailWord_6540017, baseEnd_6540017] using wordTrace_append hprefix tailTrace_6540017
  have hstable : (prefixWord ++ tailWord_6540017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540017).length < 2 ^ (prefixWord ++ tailWord_6540017).sum := by decide
  have hdescent : baseEnd_6540017 < baseStart_6540017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540061 : List Nat := [1, 4, 2, 4, 1, 2, 9]
def baseStart_6540061 : Nat := 118140960795 + 6540061 * 2 ^ 59
def prefixEnd_6540061 : Nat := 4983230072969 + 3 ^ 40 * 6540061 * 2
def baseEnd_6540061 : Nat := 41459195095363477962473

theorem tailTrace_6540061 : CollatzResearch.WordTrace tailWord_6540061 prefixEnd_6540061 41459195095363477962473 := by
  unfold tailWord_6540061
  simp only [CollatzResearch.WordTrace]
  refine ⟨238535621159483425338700037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159023747439655616892466691 238535621159483425338700037)
  ·
    refine ⟨44725428967403142251006257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238535621159483425338700037 44725428967403142251006257)
    ·
      refine ⟨33544071725552356688254693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44725428967403142251006257 33544071725552356688254693)
      ·
        refine ⟨6289513448541066879047755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33544071725552356688254693 6289513448541066879047755)
        ·
          refine ⟨9434270172811600318571633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6289513448541066879047755 9434270172811600318571633)
          ·
            refine ⟨7075702629608700238928725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9434270172811600318571633 7075702629608700238928725)
            ·
              refine ⟨41459195095363477962473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7075702629608700238928725 41459195095363477962473)
              ·
                rfl

theorem cell23_6540061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 9].length) (baseStart_6540061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540061 prefixEnd_6540061 := by exact prefixLift 6540061
  have htrace : WordTrace (prefixWord ++ tailWord_6540061) baseStart_6540061 baseEnd_6540061 := by
    simpa [prefixWord, tailWord_6540061, baseEnd_6540061] using wordTrace_append hprefix tailTrace_6540061
  have hstable : (prefixWord ++ tailWord_6540061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540061).length < 2 ^ (prefixWord ++ tailWord_6540061).sum := by decide
  have hdescent : baseEnd_6540061 < baseStart_6540061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540067 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 5]
def baseStart_6540067 : Nat := 118140960795 + 6540067 * 2 ^ 59
def prefixEnd_6540067 : Nat := 4983230072969 + 3 ^ 40 * 6540067 * 2
def baseEnd_6540067 : Nat := 3358197883608368691485285

theorem tailTrace_6540067 : CollatzResearch.WordTrace tailWord_6540067 prefixEnd_6540067 3358197883608368691485285 := by
  unfold tailWord_6540067
  simp only [CollatzResearch.WordTrace]
  refine ⟨238535839997461688363418455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159023893331641125575612303 238535839997461688363418455)
  ·
    refine ⟨357803759996192532545127683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238535839997461688363418455 357803759996192532545127683)
    ·
      refine ⟨536705639994288798817691525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357803759996192532545127683 536705639994288798817691525)
      ·
        refine ⟨100632307498929149778317161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 536705639994288798817691525 100632307498929149778317161)
        ·
          refine ⟨75474230624196862333737871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100632307498929149778317161 75474230624196862333737871)
          ·
            refine ⟨113211345936295293500606807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75474230624196862333737871 113211345936295293500606807)
            ·
              refine ⟨169817018904442940250910211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113211345936295293500606807 169817018904442940250910211)
              ·
                refine ⟨254725528356664410376365317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169817018904442940250910211 254725528356664410376365317)
                ·
                  refine ⟨47761036566874576945568497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 254725528356664410376365317 47761036566874576945568497)
                  ·
                    refine ⟨35820777425155932709176373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47761036566874576945568497 35820777425155932709176373)
                    ·
                      refine ⟨3358197883608368691485285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35820777425155932709176373 3358197883608368691485285)
                      ·
                        rfl

theorem cell23_6540067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_6540067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540067 prefixEnd_6540067 := by exact prefixLift 6540067
  have htrace : WordTrace (prefixWord ++ tailWord_6540067) baseStart_6540067 baseEnd_6540067 := by
    simpa [prefixWord, tailWord_6540067, baseEnd_6540067] using wordTrace_append hprefix tailTrace_6540067
  have hstable : (prefixWord ++ tailWord_6540067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540067).length < 2 ^ (prefixWord ++ tailWord_6540067).sum := by decide
  have hdescent : baseEnd_6540067 < baseStart_6540067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540072 : List Nat := [2, 1, 5, 1, 1, 1, 5, 2, 1, 2, 2]
def baseStart_6540072 : Nat := 118140960795 + 6540072 * 2 ^ 59
def prefixEnd_6540072 : Nat := 4983230072969 + 3 ^ 40 * 6540072 * 2
def baseEnd_6540072 : Nat := 3358200451011641171922763

theorem tailTrace_6540072 : CollatzResearch.WordTrace tailWord_6540072 prefixEnd_6540072 3358200451011641171922763 := by
  unfold tailWord_6540072
  simp only [CollatzResearch.WordTrace]
  refine ⟨119268011181221787108675235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159024014908295716144900313 119268011181221787108675235)
  ·
    refine ⟨178902016771832680663012853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119268011181221787108675235 178902016771832680663012853)
    ·
      refine ⟨16772064072359313812157455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178902016771832680663012853 16772064072359313812157455)
      ·
        refine ⟨25158096108538970718236183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16772064072359313812157455 25158096108538970718236183)
        ·
          refine ⟨37737144162808456077354275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25158096108538970718236183 37737144162808456077354275)
          ·
            refine ⟨56605716244212684116031413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37737144162808456077354275 56605716244212684116031413)
            ·
              refine ⟨5306785897894939135877945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56605716244212684116031413 5306785897894939135877945)
              ·
                refine ⟨3980089423421204351908459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5306785897894939135877945 3980089423421204351908459)
                ·
                  refine ⟨5970134135131806527862689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3980089423421204351908459 5970134135131806527862689)
                  ·
                    refine ⟨4477600601348854895897017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5970134135131806527862689 4477600601348854895897017)
                    ·
                      refine ⟨3358200451011641171922763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4477600601348854895897017 3358200451011641171922763)
                      ·
                        rfl

theorem cell23_6540072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_6540072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540072 prefixEnd_6540072 := by exact prefixLift 6540072
  have htrace : WordTrace (prefixWord ++ tailWord_6540072) baseStart_6540072 baseEnd_6540072 := by
    simpa [prefixWord, tailWord_6540072, baseEnd_6540072] using wordTrace_append hprefix tailTrace_6540072
  have hstable : (prefixWord ++ tailWord_6540072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540072).length < 2 ^ (prefixWord ++ tailWord_6540072).sum := by decide
  have hdescent : baseEnd_6540072 < baseStart_6540072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540081 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 3, 3, 2]
def baseStart_6540081 : Nat := 118140960795 + 6540081 * 2 ^ 59
def prefixEnd_6540081 : Nat := 4983230072969 + 3 ^ 40 * 6540081 * 2
def baseEnd_6540081 : Nat := 3358205072337531636710221

theorem tailTrace_6540081 : CollatzResearch.WordTrace tailWord_6540081 prefixEnd_6540081 3358205072337531636710221 := by
  unfold tailWord_6540081
  simp only [CollatzResearch.WordTrace]
  refine ⟨238536350619410968754428097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159024233746273979169618731 238536350619410968754428097)
  ·
    refine ⟨178902262964558226565821073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238536350619410968754428097 178902262964558226565821073)
    ·
      refine ⟨134176697223418669924365805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178902262964558226565821073 134176697223418669924365805)
      ·
        refine ⟨50316261458782001221637177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134176697223418669924365805 50316261458782001221637177)
        ·
          refine ⟨37737196094086500916227883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50316261458782001221637177 37737196094086500916227883)
          ·
            refine ⟨56605794141129751374341825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37737196094086500916227883 56605794141129751374341825)
            ·
              refine ⟨42454345605847313530756369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56605794141129751374341825 42454345605847313530756369)
              ·
                refine ⟨31840759204385485148067277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42454345605847313530756369 31840759204385485148067277)
                ·
                  refine ⟨11940284701644556930525229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31840759204385485148067277 11940284701644556930525229)
                  ·
                    refine ⟨4477606763116708848946961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11940284701644556930525229 4477606763116708848946961)
                    ·
                      refine ⟨3358205072337531636710221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4477606763116708848946961 3358205072337531636710221)
                      ·
                        rfl

theorem cell23_6540081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_6540081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540081 prefixEnd_6540081 := by exact prefixLift 6540081
  have htrace : WordTrace (prefixWord ++ tailWord_6540081) baseStart_6540081 baseEnd_6540081 := by
    simpa [prefixWord, tailWord_6540081, baseEnd_6540081] using wordTrace_append hprefix tailTrace_6540081
  have hstable : (prefixWord ++ tailWord_6540081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540081).length < 2 ^ (prefixWord ++ tailWord_6540081).sum := by decide
  have hdescent : baseEnd_6540081 < baseStart_6540081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540087 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 1, 8]
def baseStart_6540087 : Nat := 118140960795 + 6540087 * 2 ^ 59
def prefixEnd_6540087 : Nat := 4983230072969 + 3 ^ 40 * 6540087 * 2
def baseEnd_6540087 : Nat := 1119402717740486204411731

theorem tailTrace_6540087 : CollatzResearch.WordTrace tailWord_6540087 prefixEnd_6540087 1119402717740486204411731 := by
  unfold tailWord_6540087
  simp only [CollatzResearch.WordTrace]
  refine ⟨238536569457389231779146515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159024379638259487852764343 238536569457389231779146515)
  ·
    refine ⟨357804854186083847668719773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238536569457389231779146515 357804854186083847668719773)
    ·
      refine ⟨134176820319781442875769915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357804854186083847668719773 134176820319781442875769915)
      ·
        refine ⟨201265230479672164313654873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134176820319781442875769915 201265230479672164313654873)
        ·
          refine ⟨150948922859754123235241155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201265230479672164313654873 150948922859754123235241155)
          ·
            refine ⟨226423384289631184852861733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150948922859754123235241155 226423384289631184852861733)
            ·
              refine ⟨42454384554305847159911575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226423384289631184852861733 42454384554305847159911575)
              ·
                refine ⟨63681576831458770739867363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42454384554305847159911575 63681576831458770739867363)
                ·
                  refine ⟨95522365247188156109801045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63681576831458770739867363 95522365247188156109801045)
                  ·
                    refine ⟨1119402717740486204411731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95522365247188156109801045 1119402717740486204411731)
                    ·
                      rfl

theorem cell23_6540087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_6540087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540087 prefixEnd_6540087 := by exact prefixLift 6540087
  have htrace : WordTrace (prefixWord ++ tailWord_6540087) baseStart_6540087 baseEnd_6540087 := by
    simpa [prefixWord, tailWord_6540087, baseEnd_6540087] using wordTrace_append hprefix tailTrace_6540087
  have hstable : (prefixWord ++ tailWord_6540087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540087).length < 2 ^ (prefixWord ++ tailWord_6540087).sum := by decide
  have hdescent : baseEnd_6540087 < baseStart_6540087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540114 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_6540114 : Nat := 118140960795 + 6540114 * 2 ^ 59
def prefixEnd_6540114 : Nat := 4983230072969 + 3 ^ 40 * 6540114 * 2
def baseEnd_6540114 : Nat := 3358222017199130007597569

theorem tailTrace_6540114 : CollatzResearch.WordTrace tailWord_6540114 prefixEnd_6540114 3358222017199130007597569 := by
  unfold tailWord_6540114
  simp only [CollatzResearch.WordTrace]
  refine ⟨59634388557072853847594849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159025036152194276926919597 59634388557072853847594849)
  ·
    refine ⟨44725791417804640385696137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59634388557072853847594849 44725791417804640385696137)
    ·
      refine ⟨33544343563353480289272103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44725791417804640385696137 33544343563353480289272103)
      ·
        refine ⟨50316515345030220433908155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33544343563353480289272103 50316515345030220433908155)
        ·
          refine ⟨75474773017545330650862233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50316515345030220433908155 75474773017545330650862233)
          ·
            refine ⟨56606079763158997988146675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75474773017545330650862233 56606079763158997988146675)
            ·
              refine ⟨84909119644738496982220013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56606079763158997988146675 84909119644738496982220013)
              ·
                refine ⟨31840919866776936368332505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84909119644738496982220013 31840919866776936368332505)
                ·
                  refine ⟨23880689900082702276249379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31840919866776936368332505 23880689900082702276249379)
                  ·
                    refine ⟨35821034850124053414374069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23880689900082702276249379 35821034850124053414374069)
                    ·
                      refine ⟨3358222017199130007597569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35821034850124053414374069 3358222017199130007597569)
                      ·
                        rfl

theorem cell23_6540114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_6540114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540114 prefixEnd_6540114 := by exact prefixLift 6540114
  have htrace : WordTrace (prefixWord ++ tailWord_6540114) baseStart_6540114 baseEnd_6540114 := by
    simpa [prefixWord, tailWord_6540114, baseEnd_6540114] using wordTrace_append hprefix tailTrace_6540114
  have hstable : (prefixWord ++ tailWord_6540114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540114).length < 2 ^ (prefixWord ++ tailWord_6540114).sum := by decide
  have hdescent : baseEnd_6540114 < baseStart_6540114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540137 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 8]
def baseStart_6540137 : Nat := 118140960795 + 6540137 * 2 ^ 59
def prefixEnd_6540137 : Nat := 4983230072969 + 3 ^ 40 * 6540137 * 2
def baseEnd_6540137 : Nat := 3358233827254183417609963

theorem tailTrace_6540137 : CollatzResearch.WordTrace tailWord_6540137 prefixEnd_6540137 3358233827254183417609963 := by
  unfold tailWord_6540137
  simp only [CollatzResearch.WordTrace]
  refine ⟨238538393107208090318466665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159025595404805393545644443 238538393107208090318466665)
  ·
    refine ⟨178903794830406067738849999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238538393107208090318466665 178903794830406067738849999)
    ·
      refine ⟨268355692245609101608274999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178903794830406067738849999 268355692245609101608274999)
      ·
        refine ⟨402533538368413652412412499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268355692245609101608274999 402533538368413652412412499)
        ·
          refine ⟨603800307552620478618618749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402533538368413652412412499 603800307552620478618618749)
          ·
            refine ⟨226425115332232679481982031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 603800307552620478618618749 226425115332232679481982031)
            ·
              refine ⟨339637672998349019222973047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226425115332232679481982031 339637672998349019222973047)
              ·
                refine ⟨509456509497523528834459571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339637672998349019222973047 509456509497523528834459571)
                ·
                  refine ⟨764184764246285293251689357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 509456509497523528834459571 764184764246285293251689357)
                  ·
                    refine ⟨286569286592356984969383509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 764184764246285293251689357 286569286592356984969383509)
                    ·
                      refine ⟨3358233827254183417609963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 286569286592356984969383509 3358233827254183417609963)
                      ·
                        rfl

theorem cell23_6540137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_6540137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540137 prefixEnd_6540137 := by exact prefixLift 6540137
  have htrace : WordTrace (prefixWord ++ tailWord_6540137) baseStart_6540137 baseEnd_6540137 := by
    simpa [prefixWord, tailWord_6540137, baseEnd_6540137] using wordTrace_append hprefix tailTrace_6540137
  have hstable : (prefixWord ++ tailWord_6540137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540137).length < 2 ^ (prefixWord ++ tailWord_6540137).sum := by decide
  have hdescent : baseEnd_6540137 < baseStart_6540137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540144 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 3]
def baseStart_6540144 : Nat := 118140960795 + 6540144 * 2 ^ 59
def prefixEnd_6540144 : Nat := 4983230072969 + 3 ^ 40 * 6540144 * 2
def baseEnd_6540144 : Nat := 3358237421618764890222431

theorem tailTrace_6540144 : CollatzResearch.WordTrace tailWord_6540144 prefixEnd_6540144 3358237421618764890222431 := by
  unfold tailWord_6540144
  simp only [CollatzResearch.WordTrace]
  refine ⟨119269324209091365256985743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159025765612121820342647657 119269324209091365256985743)
  ·
    refine ⟨178903986313637047885478615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119269324209091365256985743 178903986313637047885478615)
    ·
      refine ⟨268355979470455571828217923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178903986313637047885478615 268355979470455571828217923)
      ·
        refine ⟨402533969205683357742326885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268355979470455571828217923 402533969205683357742326885)
        ·
          refine ⟨75475119226065629576686291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 402533969205683357742326885 75475119226065629576686291)
          ·
            refine ⟨113212678839098444365029437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75475119226065629576686291 113212678839098444365029437)
            ·
              refine ⟨42454754564661916636886039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113212678839098444365029437 42454754564661916636886039)
              ·
                refine ⟨63682131846992874955329059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42454754564661916636886039 63682131846992874955329059)
                ·
                  refine ⟨95523197770489312432993589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63682131846992874955329059 95523197770489312432993589)
                  ·
                    refine ⟨8955299790983373040593149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95523197770489312432993589 8955299790983373040593149)
                    ·
                      refine ⟨3358237421618764890222431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8955299790983373040593149 3358237421618764890222431)
                      ·
                        rfl

theorem cell23_6540144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 3].length) (baseStart_6540144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540144 prefixEnd_6540144 := by exact prefixLift 6540144
  have htrace : WordTrace (prefixWord ++ tailWord_6540144) baseStart_6540144 baseEnd_6540144 := by
    simpa [prefixWord, tailWord_6540144, baseEnd_6540144] using wordTrace_append hprefix tailTrace_6540144
  have hstable : (prefixWord ++ tailWord_6540144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540144).length < 2 ^ (prefixWord ++ tailWord_6540144).sum := by decide
  have hdescent : baseEnd_6540144 < baseStart_6540144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540168 : List Nat := [2, 1, 3, 3, 2, 2, 2, 3, 5]
def baseStart_6540168 : Nat := 118140960795 + 6540168 * 2 ^ 59
def prefixEnd_6540168 : Nat := 4983230072969 + 3 ^ 40 * 6540168 * 2
def baseEnd_6540168 : Nat := 373138860572719199591369

theorem tailTrace_6540168 : CollatzResearch.WordTrace tailWord_6540168 prefixEnd_6540168 373138860572719199591369 := by
  unfold tailWord_6540168
  simp only [CollatzResearch.WordTrace]
  refine ⟨119269761885047891306422579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159026349180063855075230105 119269761885047891306422579)
  ·
    refine ⟨178904642827571836959633869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119269761885047891306422579 178904642827571836959633869)
    ·
      refine ⟨67089241060339438859862701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178904642827571836959633869 67089241060339438859862701)
      ·
        refine ⟨25158465397627289572448513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67089241060339438859862701 25158465397627289572448513)
        ·
          refine ⟨18868849048220467179336385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25158465397627289572448513 18868849048220467179336385)
          ·
            refine ⟨14151636786165350384502289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18868849048220467179336385 14151636786165350384502289)
            ·
              refine ⟨10613727589624012788376717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14151636786165350384502289 10613727589624012788376717)
              ·
                refine ⟨3980147846109004795641269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10613727589624012788376717 3980147846109004795641269)
                ·
                  refine ⟨373138860572719199591369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3980147846109004795641269 373138860572719199591369)
                  ·
                    rfl

theorem cell23_6540168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 5].length) (baseStart_6540168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540168 prefixEnd_6540168 := by exact prefixLift 6540168
  have htrace : WordTrace (prefixWord ++ tailWord_6540168) baseStart_6540168 baseEnd_6540168 := by
    simpa [prefixWord, tailWord_6540168, baseEnd_6540168] using wordTrace_append hprefix tailTrace_6540168
  have hstable : (prefixWord ++ tailWord_6540168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540168).length < 2 ^ (prefixWord ++ tailWord_6540168).sum := by decide
  have hdescent : baseEnd_6540168 < baseStart_6540168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540201 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 2, 4, 2]
def baseStart_6540201 : Nat := 118140960795 + 6540201 * 2 ^ 59
def prefixEnd_6540201 : Nat := 4983230072969 + 3 ^ 40 * 6540201 * 2
def baseEnd_6540201 : Nat := 3358266690016071167209669

theorem tailTrace_6540201 : CollatzResearch.WordTrace tailWord_6540201 prefixEnd_6540201 3358266690016071167209669 := by
  unfold tailWord_6540201
  simp only [CollatzResearch.WordTrace]
  refine ⟨238540727378976229248796457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159027151585984152832530971 238540727378976229248796457)
  ·
    refine ⟨178905545534232171936597343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238540727378976229248796457 178905545534232171936597343)
    ·
      refine ⟨268358318301348257904896015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178905545534232171936597343 268358318301348257904896015)
      ·
        refine ⟨402537477452022386857344023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268358318301348257904896015 402537477452022386857344023)
        ·
          refine ⟨603806216178033580286016035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402537477452022386857344023 603806216178033580286016035)
          ·
            refine ⟨905709324267050370429024053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603806216178033580286016035 905709324267050370429024053)
            ·
              refine ⟨84910249150035972227721005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 905709324267050370429024053 84910249150035972227721005)
              ·
                refine ⟨31841343431263489585395377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84910249150035972227721005 31841343431263489585395377)
                ·
                  refine ⟨23881007573447617189046533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31841343431263489585395377 23881007573447617189046533)
                  ·
                    refine ⟨4477688920021428222946225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23881007573447617189046533 4477688920021428222946225)
                    ·
                      refine ⟨3358266690016071167209669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4477688920021428222946225 3358266690016071167209669)
                      ·
                        rfl

theorem cell23_6540201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 4, 2].length) (baseStart_6540201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540201 prefixEnd_6540201 := by exact prefixLift 6540201
  have htrace : WordTrace (prefixWord ++ tailWord_6540201) baseStart_6540201 baseEnd_6540201 := by
    simpa [prefixWord, tailWord_6540201, baseEnd_6540201] using wordTrace_append hprefix tailTrace_6540201
  have hstable : (prefixWord ++ tailWord_6540201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540201).length < 2 ^ (prefixWord ++ tailWord_6540201).sum := by decide
  have hdescent : baseEnd_6540201 < baseStart_6540201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540224 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 8]
def baseStart_6540224 : Nat := 118140960795 + 6540224 * 2 ^ 59
def prefixEnd_6540224 : Nat := 4983230072969 + 3 ^ 40 * 6540224 * 2
def baseEnd_6540224 : Nat := 373142055563458286358007

theorem tailTrace_6540224 : CollatzResearch.WordTrace tailWord_6540224 prefixEnd_6540224 373142055563458286358007 := by
  unfold tailWord_6540224
  simp only [CollatzResearch.WordTrace]
  refine ⟨119270783128946452088441863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159027710838595269451255817 119270783128946452088441863)
  ·
    refine ⟨178906174693419678132662795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119270783128946452088441863 178906174693419678132662795)
    ·
      refine ⟨268359262040129517198994193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178906174693419678132662795 268359262040129517198994193)
      ·
        refine ⟨201269446530097137899245645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268359262040129517198994193 201269446530097137899245645)
        ·
          refine ⟨75476042448786426712217117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201269446530097137899245645 75476042448786426712217117)
          ·
            refine ⟨28303515918294910017081419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75476042448786426712217117 28303515918294910017081419)
            ·
              refine ⟨42455273877442365025622129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28303515918294910017081419 42455273877442365025622129)
              ·
                refine ⟨31841455408081773769216597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42455273877442365025622129 31841455408081773769216597)
                ·
                  refine ⟨373142055563458286358007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31841455408081773769216597 373142055563458286358007)
                  ·
                    rfl

theorem cell23_6540224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 8].length) (baseStart_6540224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540224 prefixEnd_6540224 := by exact prefixLift 6540224
  have htrace : WordTrace (prefixWord ++ tailWord_6540224) baseStart_6540224 baseEnd_6540224 := by
    simpa [prefixWord, tailWord_6540224, baseEnd_6540224] using wordTrace_append hprefix tailTrace_6540224
  have hstable : (prefixWord ++ tailWord_6540224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540224).length < 2 ^ (prefixWord ++ tailWord_6540224).sum := by decide
  have hdescent : baseEnd_6540224 < baseStart_6540224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540238 : List Nat := [4, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3]
def baseStart_6540238 : Nat := 118140960795 + 6540238 * 2 ^ 59
def prefixEnd_6540238 : Nat := 4983230072969 + 3 ^ 40 * 6540238 * 2
def baseEnd_6540238 : Nat := 3358285688800287522446999

theorem tailTrace_6540238 : CollatzResearch.WordTrace tailWord_6540238 prefixEnd_6540238 3358285688800287522446999 := by
  unfold tailWord_6540238
  simp only [CollatzResearch.WordTrace]
  refine ⟨29817759609980273070986671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159028051253228123045262245 29817759609980273070986671)
  ·
    refine ⟨44726639414970409606480007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29817759609980273070986671 44726639414970409606480007)
    ·
      refine ⟨67089959122455614409720011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44726639414970409606480007 67089959122455614409720011)
      ·
        refine ⟨100634938683683421614580017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67089959122455614409720011 100634938683683421614580017)
        ·
          refine ⟨75476204012762566210935013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100634938683683421614580017 75476204012762566210935013)
          ·
            refine ⟨14151788252392981164550315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75476204012762566210935013 14151788252392981164550315)
            ·
              refine ⟨21227682378589471746825473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14151788252392981164550315 21227682378589471746825473)
              ·
                refine ⟨15920761783942103810119105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21227682378589471746825473 15920761783942103810119105)
                ·
                  refine ⟨11940571337956577857589329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15920761783942103810119105 11940571337956577857589329)
                  ·
                    refine ⟨8955428503467433393191997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11940571337956577857589329 8955428503467433393191997)
                    ·
                      refine ⟨3358285688800287522446999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8955428503467433393191997 3358285688800287522446999)
                      ·
                        rfl

theorem cell23_6540238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_6540238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540238 prefixEnd_6540238 := by exact prefixLift 6540238
  have htrace : WordTrace (prefixWord ++ tailWord_6540238) baseStart_6540238 baseEnd_6540238 := by
    simpa [prefixWord, tailWord_6540238, baseEnd_6540238] using wordTrace_append hprefix tailTrace_6540238
  have hstable : (prefixWord ++ tailWord_6540238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540238).length < 2 ^ (prefixWord ++ tailWord_6540238).sum := by decide
  have hdescent : baseEnd_6540238 < baseStart_6540238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540245 : List Nat := [1, 3, 2, 3, 3, 2, 1, 1, 3, 4]
def baseStart_6540245 : Nat := 118140960795 + 6540245 * 2 ^ 59
def prefixEnd_6540245 : Nat := 4983230072969 + 3 ^ 40 * 6540245 * 2
def baseEnd_6540245 : Nat := 1119429761054956331686489

theorem tailTrace_6540245 : CollatzResearch.WordTrace tailWord_6540245 prefixEnd_6540245 1119429761054956331686489 := by
  unfold tailWord_6540245
  simp only [CollatzResearch.WordTrace]
  refine ⟨238542332190816824763398189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159028221460544549842265459 238542332190816824763398189)
  ·
    refine ⟨89453374571556309286274321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238542332190816824763398189 89453374571556309286274321)
    ·
      refine ⟨67090030928667231964705741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89453374571556309286274321 67090030928667231964705741)
      ·
        refine ⟨25158761598250211986764653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67090030928667231964705741 25158761598250211986764653)
        ·
          refine ⟨9434535599343829495036745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25158761598250211986764653 9434535599343829495036745)
          ·
            refine ⟨7075901699507872121277559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9434535599343829495036745 7075901699507872121277559)
            ·
              refine ⟨10613852549261808181916339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7075901699507872121277559 10613852549261808181916339)
              ·
                refine ⟨15920778823892712272874509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10613852549261808181916339 15920778823892712272874509)
                ·
                  refine ⟨5970292058959767102327941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15920778823892712272874509 5970292058959767102327941)
                  ·
                    refine ⟨1119429761054956331686489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5970292058959767102327941 1119429761054956331686489)
                    ·
                      rfl

theorem cell23_6540245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_6540245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540245 prefixEnd_6540245 := by exact prefixLift 6540245
  have htrace : WordTrace (prefixWord ++ tailWord_6540245) baseStart_6540245 baseEnd_6540245 := by
    simpa [prefixWord, tailWord_6540245, baseEnd_6540245] using wordTrace_append hprefix tailTrace_6540245
  have hstable : (prefixWord ++ tailWord_6540245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540245).length < 2 ^ (prefixWord ++ tailWord_6540245).sum := by decide
  have hdescent : baseEnd_6540245 < baseStart_6540245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540271 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 3, 5]
def baseStart_6540271 : Nat := 118140960795 + 6540271 * 2 ^ 59
def prefixEnd_6540271 : Nat := 4983230072969 + 3 ^ 40 * 6540271 * 2
def baseEnd_6540271 : Nat := 1119434211220628631111449

theorem tailTrace_6540271 : CollatzResearch.WordTrace tailWord_6540271 prefixEnd_6540271 1119434211220628631111449 := by
  unfold tailWord_6540271
  simp only [CollatzResearch.WordTrace]
  refine ⟨238543280488722631203844667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159028853659148420802563111 238543280488722631203844667)
  ·
    refine ⟨357814920733083946805767001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238543280488722631203844667 357814920733083946805767001)
    ·
      refine ⟨268361190549812960104325251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357814920733083946805767001 268361190549812960104325251)
      ·
        refine ⟨402541785824719440156487877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268361190549812960104325251 402541785824719440156487877)
        ·
          refine ⟨75476584842134895029341477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 402541785824719440156487877 75476584842134895029341477)
          ·
            refine ⟨14151859657900292818001527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75476584842134895029341477 14151859657900292818001527)
            ·
              refine ⟨21227789486850439227002291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14151859657900292818001527 21227789486850439227002291)
              ·
                refine ⟨31841684230275658840503437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21227789486850439227002291 31841684230275658840503437)
                ·
                  refine ⟨11940631586353372065188789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31841684230275658840503437 11940631586353372065188789)
                  ·
                    refine ⟨1119434211220628631111449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11940631586353372065188789 1119434211220628631111449)
                    ·
                      rfl

theorem cell23_6540271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 5].length) (baseStart_6540271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540271 prefixEnd_6540271 := by exact prefixLift 6540271
  have htrace : WordTrace (prefixWord ++ tailWord_6540271) baseStart_6540271 baseEnd_6540271 := by
    simpa [prefixWord, tailWord_6540271, baseEnd_6540271] using wordTrace_append hprefix tailTrace_6540271
  have hstable : (prefixWord ++ tailWord_6540271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540271).length < 2 ^ (prefixWord ++ tailWord_6540271).sum := by decide
  have hdescent : baseEnd_6540271 < baseStart_6540271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540285 : List Nat := [1, 4, 1, 1, 1, 2, 1, 7, 1, 1, 3]
def baseStart_6540285 : Nat := 118140960795 + 6540285 * 2 ^ 59
def prefixEnd_6540285 : Nat := 4983230072969 + 3 ^ 40 * 6540285 * 2
def baseEnd_6540285 : Nat := 3358309822391048838559283

theorem tailTrace_6540285 : CollatzResearch.WordTrace tailWord_6540285 prefixEnd_6540285 3358309822391048838559283 := by
  unfold tailWord_6540285
  simp only [CollatzResearch.WordTrace]
  refine ⟨238543791110671911594854309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159029194073781274396569539 238543791110671911594854309)
  ·
    refine ⟨44726960833250983424035183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238543791110671911594854309 44726960833250983424035183)
    ·
      refine ⟨67090441249876475136052775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44726960833250983424035183 67090441249876475136052775)
      ·
        refine ⟨100635661874814712704079163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67090441249876475136052775 100635661874814712704079163)
        ·
          refine ⟨150953492812222069056118745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100635661874814712704079163 150953492812222069056118745)
          ·
            refine ⟨113215119609166551792089059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150953492812222069056118745 113215119609166551792089059)
            ·
              refine ⟨169822679413749827688133589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113215119609166551792089059 169822679413749827688133589)
              ·
                refine ⟨3980219048759761586440631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 169822679413749827688133589 3980219048759761586440631)
                ·
                  refine ⟨5970328573139642379660947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3980219048759761586440631 5970328573139642379660947)
                  ·
                    refine ⟨8955492859709463569491421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5970328573139642379660947 8955492859709463569491421)
                    ·
                      refine ⟨3358309822391048838559283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8955492859709463569491421 3358309822391048838559283)
                      ·
                        rfl

theorem cell23_6540285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 1, 1, 3].length) (baseStart_6540285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540285 prefixEnd_6540285 := by exact prefixLift 6540285
  have htrace : WordTrace (prefixWord ++ tailWord_6540285) baseStart_6540285 baseEnd_6540285 := by
    simpa [prefixWord, tailWord_6540285, baseEnd_6540285] using wordTrace_append hprefix tailTrace_6540285
  have hstable : (prefixWord ++ tailWord_6540285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540285).length < 2 ^ (prefixWord ++ tailWord_6540285).sum := by decide
  have hdescent : baseEnd_6540285 < baseStart_6540285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540302 : List Nat := [4, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3]
def baseStart_6540302 : Nat := 118140960795 + 6540302 * 2 ^ 59
def prefixEnd_6540302 : Nat := 4983230072969 + 3 ^ 40 * 6540302 * 2
def baseEnd_6540302 : Nat := 3358318551562175272046705

theorem tailTrace_6540302 : CollatzResearch.WordTrace tailWord_6540302 prefixEnd_6540302 3358318551562175272046705 := by
  unfold tailWord_6540302
  simp only [CollatzResearch.WordTrace]
  refine ⟨29818051393951290437277895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159029607434406882332148773 29818051393951290437277895)
  ·
    refine ⟨44727077090926935655916843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29818051393951290437277895 44727077090926935655916843)
    ·
      refine ⟨67090615636390403483875265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44727077090926935655916843 67090615636390403483875265)
      ·
        refine ⟨50317961727292802612906449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67090615636390403483875265 50317961727292802612906449)
        ·
          refine ⟨37738471295469601959679837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50317961727292802612906449 37738471295469601959679837)
          ·
            refine ⟨14151926735801100734879939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37738471295469601959679837 14151926735801100734879939)
            ·
              refine ⟨21227890103701651102319909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14151926735801100734879939 21227890103701651102319909)
              ·
                refine ⟨3980229394444059581684983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21227890103701651102319909 3980229394444059581684983)
                ·
                  refine ⟨5970344091666089372527475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3980229394444059581684983 5970344091666089372527475)
                  ·
                    refine ⟨8955516137499134058791213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5970344091666089372527475 8955516137499134058791213)
                    ·
                      refine ⟨3358318551562175272046705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8955516137499134058791213 3358318551562175272046705)
                      ·
                        rfl

theorem cell23_6540302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_6540302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540302 prefixEnd_6540302 := by exact prefixLift 6540302
  have htrace : WordTrace (prefixWord ++ tailWord_6540302) baseStart_6540302 baseEnd_6540302 := by
    simpa [prefixWord, tailWord_6540302, baseEnd_6540302] using wordTrace_append hprefix tailTrace_6540302
  have hstable : (prefixWord ++ tailWord_6540302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540302).length < 2 ^ (prefixWord ++ tailWord_6540302).sum := by decide
  have hdescent : baseEnd_6540302 < baseStart_6540302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540325 : List Nat := [1, 3, 1, 2, 2, 2, 3, 2, 3, 2, 2]
def baseStart_6540325 : Nat := 118140960795 + 6540325 * 2 ^ 59
def prefixEnd_6540325 : Nat := 4983230072969 + 3 ^ 40 * 6540325 * 2
def baseEnd_6540325 : Nat := 3358330361617228682059099

theorem tailTrace_6540325 : CollatzResearch.WordTrace tailWord_6540325 prefixEnd_6540325 3358330361617228682059099 := by
  unfold tailWord_6540325
  simp only [CollatzResearch.WordTrace]
  refine ⟨238545250030526998426310429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159030166687017998950873619 238545250030526998426310429)
  ·
    refine ⟨89454468761447624409866411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238545250030526998426310429 89454468761447624409866411)
    ·
      refine ⟨134181703142171436614799617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89454468761447624409866411 134181703142171436614799617)
      ·
        refine ⟨100636277356628577461099713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134181703142171436614799617 100636277356628577461099713)
        ·
          refine ⟨75477208017471433095824785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100636277356628577461099713 75477208017471433095824785)
          ·
            refine ⟨56607906013103574821868589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75477208017471433095824785 56607906013103574821868589)
            ·
              refine ⟨21227964754913840558200721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56607906013103574821868589 21227964754913840558200721)
              ·
                refine ⟨15920973566185380418650541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21227964754913840558200721 15920973566185380418650541)
                ·
                  refine ⟨5970365087319517656993953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15920973566185380418650541 5970365087319517656993953)
                  ·
                    refine ⟨4477773815489638242745465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5970365087319517656993953 4477773815489638242745465)
                    ·
                      refine ⟨3358330361617228682059099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4477773815489638242745465 3358330361617228682059099)
                      ·
                        rfl

theorem cell23_6540325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_6540325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540325 prefixEnd_6540325 := by exact prefixLift 6540325
  have htrace : WordTrace (prefixWord ++ tailWord_6540325) baseStart_6540325 baseEnd_6540325 := by
    simpa [prefixWord, tailWord_6540325, baseEnd_6540325] using wordTrace_append hprefix tailTrace_6540325
  have hstable : (prefixWord ++ tailWord_6540325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540325).length < 2 ^ (prefixWord ++ tailWord_6540325).sum := by decide
  have hdescent : baseEnd_6540325 < baseStart_6540325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540331 : List Nat := [1, 1, 1, 1, 2, 1, 9, 7]
def baseStart_6540331 : Nat := 118140960795 + 6540331 * 2 ^ 59
def prefixEnd_6540331 : Nat := 4983230072969 + 3 ^ 40 * 6540331 * 2
def baseEnd_6540331 : Nat := 124382720092635394762373

theorem tailTrace_6540331 : CollatzResearch.WordTrace tailWord_6540331 prefixEnd_6540331 124382720092635394762373 := by
  unfold tailWord_6540331
  simp only [CollatzResearch.WordTrace]
  refine ⟨238545468868505261451028847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159030312579003507634019231 238545468868505261451028847)
  ·
    refine ⟨357818203302757892176543271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238545468868505261451028847 357818203302757892176543271)
    ·
      refine ⟨536727304954136838264814907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357818203302757892176543271 536727304954136838264814907)
      ·
        refine ⟨805090957431205257397222361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536727304954136838264814907 805090957431205257397222361)
        ·
          refine ⟨603818218073403943047916771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 805090957431205257397222361 603818218073403943047916771)
          ·
            refine ⟨905727327110105914571875157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603818218073403943047916771 905727327110105914571875157)
            ·
              refine ⟨5306996057285776843194581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 905727327110105914571875157 5306996057285776843194581)
              ·
                refine ⟨124382720092635394762373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5306996057285776843194581 124382720092635394762373)
                ·
                  rfl

theorem cell23_6540331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 7].length) (baseStart_6540331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540331 prefixEnd_6540331 := by exact prefixLift 6540331
  have htrace : WordTrace (prefixWord ++ tailWord_6540331) baseStart_6540331 baseEnd_6540331 := by
    simpa [prefixWord, tailWord_6540331, baseEnd_6540331] using wordTrace_append hprefix tailTrace_6540331
  have hstable : (prefixWord ++ tailWord_6540331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540331).length < 2 ^ (prefixWord ++ tailWord_6540331).sum := by decide
  have hdescent : baseEnd_6540331 < baseStart_6540331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540342 : List Nat := [5, 1, 2, 1, 1, 2, 4, 1, 1, 1, 4]
def baseStart_6540342 : Nat := 118140960795 + 6540342 * 2 ^ 59
def prefixEnd_6540342 : Nat := 4983230072969 + 3 ^ 40 * 6540342 * 2
def baseEnd_6540342 : Nat := 3358339090788355115546521

theorem tailTrace_6540342 : CollatzResearch.WordTrace tailWord_6540342 prefixEnd_6540342 3358339090788355115546521 := by
  unfold tailWord_6540342
  simp only [CollatzResearch.WordTrace]
  refine ⟨14909116879466588145604955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159030580047643606886452853 14909116879466588145604955)
  ·
    refine ⟨22363675319199882218407433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14909116879466588145604955 22363675319199882218407433)
    ·
      refine ⟨16772756489399911663805575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22363675319199882218407433 16772756489399911663805575)
      ·
        refine ⟨25159134734099867495708363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16772756489399911663805575 25159134734099867495708363)
        ·
          refine ⟨37738702101149801243562545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25159134734099867495708363 37738702101149801243562545)
          ·
            refine ⟨28304026575862350932671909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37738702101149801243562545 28304026575862350932671909)
            ·
              refine ⟨5307004982974190799875983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28304026575862350932671909 5307004982974190799875983)
              ·
                refine ⟨7960507474461286199813975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5307004982974190799875983 7960507474461286199813975)
                ·
                  refine ⟨11940761211691929299720963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7960507474461286199813975 11940761211691929299720963)
                  ·
                    refine ⟨17911141817537893949581445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11940761211691929299720963 17911141817537893949581445)
                    ·
                      refine ⟨3358339090788355115546521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17911141817537893949581445 3358339090788355115546521)
                      ·
                        rfl

theorem cell23_6540342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_6540342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540342 prefixEnd_6540342 := by exact prefixLift 6540342
  have htrace : WordTrace (prefixWord ++ tailWord_6540342) baseStart_6540342 baseEnd_6540342 := by
    simpa [prefixWord, tailWord_6540342, baseEnd_6540342] using wordTrace_append hprefix tailTrace_6540342
  have hstable : (prefixWord ++ tailWord_6540342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540342).length < 2 ^ (prefixWord ++ tailWord_6540342).sum := by decide
  have hdescent : baseEnd_6540342 < baseStart_6540342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540345 : List Nat := [1, 2, 1, 5, 2, 2, 1, 3, 1, 2, 3]
def baseStart_6540345 : Nat := 118140960795 + 6540345 * 2 ^ 59
def prefixEnd_6540345 : Nat := 4983230072969 + 3 ^ 40 * 6540345 * 2
def baseEnd_6540345 : Nat := 3358340631230318603809007

theorem tailTrace_6540345 : CollatzResearch.WordTrace tailWord_6540345 prefixEnd_6540345 3358340631230318603809007 := by
  unfold tailWord_6540345
  simp only [CollatzResearch.WordTrace]
  refine ⟨238545979490454541842038489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159030652993636361228025659 238545979490454541842038489)
  ·
    refine ⟨178909484617840906381528867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238545979490454541842038489 178909484617840906381528867)
    ·
      refine ⟨268364226926761359572293301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178909484617840906381528867 268364226926761359572293301)
      ·
        refine ⟨25159146274383877459902497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 268364226926761359572293301 25159146274383877459902497)
        ·
          refine ⟨18869359705787908094926873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25159146274383877459902497 18869359705787908094926873)
          ·
            refine ⟨14152019779340931071195155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18869359705787908094926873 14152019779340931071195155)
            ·
              refine ⟨21228029669011396606792733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14152019779340931071195155 21228029669011396606792733)
              ·
                refine ⟨7960511125879273727547275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21228029669011396606792733 7960511125879273727547275)
                ·
                  refine ⟨11940766688818910591320913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7960511125879273727547275 11940766688818910591320913)
                  ·
                    refine ⟨8955575016614182943490685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11940766688818910591320913 8955575016614182943490685)
                    ·
                      refine ⟨3358340631230318603809007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8955575016614182943490685 3358340631230318603809007)
                      ·
                        rfl

theorem cell23_6540345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_6540345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540345 prefixEnd_6540345 := by exact prefixLift 6540345
  have htrace : WordTrace (prefixWord ++ tailWord_6540345) baseStart_6540345 baseEnd_6540345 := by
    simpa [prefixWord, tailWord_6540345, baseEnd_6540345] using wordTrace_append hprefix tailTrace_6540345
  have hstable : (prefixWord ++ tailWord_6540345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540345).length < 2 ^ (prefixWord ++ tailWord_6540345).sum := by decide
  have hdescent : baseEnd_6540345 < baseStart_6540345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540368 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 5, 3, 2]
def baseStart_6540368 : Nat := 118140960795 + 6540368 * 2 ^ 59
def prefixEnd_6540368 : Nat := 4983230072969 + 3 ^ 40 * 6540368 * 2
def baseEnd_6540368 : Nat := 3358352441285372013821401

theorem tailTrace_6540368 : CollatzResearch.WordTrace tailWord_6540368 prefixEnd_6540368 3358352441285372013821401 := by
  unfold tailWord_6540368
  simp only [CollatzResearch.WordTrace]
  refine ⟨119273409184685608385062879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159031212246247477846750505 119273409184685608385062879)
  ·
    refine ⟨178910113777028412577594319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119273409184685608385062879 178910113777028412577594319)
    ·
      refine ⟨268365170665542618866391479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178910113777028412577594319 268365170665542618866391479)
      ·
        refine ⟨402547755998313928299587219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268365170665542618866391479 402547755998313928299587219)
        ·
          refine ⟨603821633997470892449380829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402547755998313928299587219 603821633997470892449380829)
          ·
            refine ⟨226433112749051584668517811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 603821633997470892449380829 226433112749051584668517811)
            ·
              refine ⟨339649669123577377002776717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226433112749051584668517811 339649669123577377002776717)
              ·
                refine ⟨127368625921341516376041269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339649669123577377002776717 127368625921341516376041269)
                ·
                  refine ⟨11940808680125767160253869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127368625921341516376041269 11940808680125767160253869)
                  ·
                    refine ⟨4477803255047162685095201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11940808680125767160253869 4477803255047162685095201)
                    ·
                      refine ⟨3358352441285372013821401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4477803255047162685095201 3358352441285372013821401)
                      ·
                        rfl

theorem cell23_6540368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 5, 3, 2].length) (baseStart_6540368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540368 prefixEnd_6540368 := by exact prefixLift 6540368
  have htrace : WordTrace (prefixWord ++ tailWord_6540368) baseStart_6540368 baseEnd_6540368 := by
    simpa [prefixWord, tailWord_6540368, baseEnd_6540368] using wordTrace_append hprefix tailTrace_6540368
  have hstable : (prefixWord ++ tailWord_6540368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540368).length < 2 ^ (prefixWord ++ tailWord_6540368).sum := by decide
  have hdescent : baseEnd_6540368 < baseStart_6540368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540382 : List Nat := [4, 4, 1, 1, 1, 1, 4, 7]
def baseStart_6540382 : Nat := 118140960795 + 6540382 * 2 ^ 59
def prefixEnd_6540382 : Nat := 4983230072969 + 3 ^ 40 * 6540382 * 2
def baseEnd_6540382 : Nat := 124383690000538331816531

theorem tailTrace_6540382 : CollatzResearch.WordTrace tailWord_6540382 prefixEnd_6540382 124383690000538331816531 := by
  unfold tailWord_6540382
  simp only [CollatzResearch.WordTrace]
  refine ⟨29818416123915062145141925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159031552660880331440756933 29818416123915062145141925)
  ·
    refine ⟨5590953023234074152214111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29818416123915062145141925 5590953023234074152214111)
    ·
      refine ⟨8386429534851111228321167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5590953023234074152214111 8386429534851111228321167)
      ·
        refine ⟨12579644302276666842481751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8386429534851111228321167 12579644302276666842481751)
        ·
          refine ⟨18869466453415000263722627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12579644302276666842481751 18869466453415000263722627)
          ·
            refine ⟨28304199680122500395583941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18869466453415000263722627 28304199680122500395583941)
            ·
              refine ⟨5307037440022968824171989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28304199680122500395583941 5307037440022968824171989)
              ·
                refine ⟨124383690000538331816531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5307037440022968824171989 124383690000538331816531)
                ·
                  rfl

theorem cell23_6540382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 7].length) (baseStart_6540382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540382 prefixEnd_6540382 := by exact prefixLift 6540382
  have htrace : WordTrace (prefixWord ++ tailWord_6540382) baseStart_6540382 baseEnd_6540382 := by
    simpa [prefixWord, tailWord_6540382, baseEnd_6540382] using wordTrace_append hprefix tailTrace_6540382
  have hstable : (prefixWord ++ tailWord_6540382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540382).length < 2 ^ (prefixWord ++ tailWord_6540382).sum := by decide
  have hdescent : baseEnd_6540382 < baseStart_6540382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540385 : List Nat := [1, 2, 3, 1, 1, 2, 3, 4, 1, 3, 2]
def baseStart_6540385 : Nat := 118140960795 + 6540385 * 2 ^ 59
def prefixEnd_6540385 : Nat := 4983230072969 + 3 ^ 40 * 6540385 * 2
def baseEnd_6540385 : Nat := 3358361170456498447308823

theorem tailTrace_6540385 : CollatzResearch.WordTrace tailWord_6540385 prefixEnd_6540385 3358361170456498447308823 := by
  unfold tailWord_6540385
  simp only [CollatzResearch.WordTrace]
  refine ⟨238547438410309628673494609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159031625606873085782329739 238547438410309628673494609)
  ·
    refine ⟨178910578807732221505120957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238547438410309628673494609 178910578807732221505120957)
    ·
      refine ⟨67091467052899583064420359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178910578807732221505120957 67091467052899583064420359)
      ·
        refine ⟨100637200579349374596630539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67091467052899583064420359 100637200579349374596630539)
        ·
          refine ⟨150955800869024061894945809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100637200579349374596630539 150955800869024061894945809)
          ·
            refine ⟨113216850651768046421209357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150955800869024061894945809 113216850651768046421209357)
            ·
              refine ⟨42456318994413017407953509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113216850651768046421209357 42456318994413017407953509)
              ·
                refine ⟨7960559811452440763991283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42456318994413017407953509 7960559811452440763991283)
                ·
                  refine ⟨11940839717178661145986925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7960559811452440763991283 11940839717178661145986925)
                  ·
                    refine ⟨4477814893941997929745097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11940839717178661145986925 4477814893941997929745097)
                    ·
                      refine ⟨3358361170456498447308823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4477814893941997929745097 3358361170456498447308823)
                      ·
                        rfl

theorem cell23_6540385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_6540385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540385 prefixEnd_6540385 := by exact prefixLift 6540385
  have htrace : WordTrace (prefixWord ++ tailWord_6540385) baseStart_6540385 baseEnd_6540385 := by
    simpa [prefixWord, tailWord_6540385, baseEnd_6540385] using wordTrace_append hprefix tailTrace_6540385
  have hstable : (prefixWord ++ tailWord_6540385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540385).length < 2 ^ (prefixWord ++ tailWord_6540385).sum := by decide
  have hdescent : baseEnd_6540385 < baseStart_6540385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540411 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 4]
def baseStart_6540411 : Nat := 118140960795 + 6540411 * 2 ^ 59
def prefixEnd_6540411 : Nat := 4983230072969 + 3 ^ 40 * 6540411 * 2
def baseEnd_6540411 : Nat := 3358374520953515345583703

theorem tailTrace_6540411 : CollatzResearch.WordTrace tailWord_6540411 prefixEnd_6540411 3358374520953515345583703 := by
  unfold tailWord_6540411
  simp only [CollatzResearch.WordTrace]
  refine ⟨238548386708215435113941087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159032257805476956742627391 238548386708215435113941087)
  ·
    refine ⟨357822580062323152670911631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238548386708215435113941087 357822580062323152670911631)
    ·
      refine ⟨536733870093484729006367447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357822580062323152670911631 536733870093484729006367447)
      ·
        refine ⟨805100805140227093509551171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536733870093484729006367447 805100805140227093509551171)
        ·
          refine ⟨1207651207710340640264326757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805100805140227093509551171 1207651207710340640264326757)
          ·
            refine ⟨226434601445688870049561267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1207651207710340640264326757 226434601445688870049561267)
            ·
              refine ⟨339651902168533305074341901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226434601445688870049561267 339651902168533305074341901)
              ·
                refine ⟨127369463313199989402878213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339651902168533305074341901 127369463313199989402878213)
                ·
                  refine ⟨23881774371224998013039665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127369463313199989402878213 23881774371224998013039665)
                  ·
                    refine ⟨17911330778418748509779749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23881774371224998013039665 17911330778418748509779749)
                    ·
                      refine ⟨3358374520953515345583703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17911330778418748509779749 3358374520953515345583703)
                      ·
                        rfl

theorem cell23_6540411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 4].length) (baseStart_6540411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540411 prefixEnd_6540411 := by exact prefixLift 6540411
  have htrace : WordTrace (prefixWord ++ tailWord_6540411) baseStart_6540411 baseEnd_6540411 := by
    simpa [prefixWord, tailWord_6540411, baseEnd_6540411] using wordTrace_append hprefix tailTrace_6540411
  have hstable : (prefixWord ++ tailWord_6540411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540411).length < 2 ^ (prefixWord ++ tailWord_6540411).sum := by decide
  have hdescent : baseEnd_6540411 < baseStart_6540411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540451 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 1, 7]
def baseStart_6540451 : Nat := 118140960795 + 6540451 * 2 ^ 59
def prefixEnd_6540451 : Nat := 4983230072969 + 3 ^ 40 * 6540451 * 2
def baseEnd_6540451 : Nat := 1119465020059898396361173

theorem tailTrace_6540451 : CollatzResearch.WordTrace tailWord_6540451 prefixEnd_6540451 1119465020059898396361173 := by
  unfold tailWord_6540451
  simp only [CollatzResearch.WordTrace]
  refine ⟨238549845628070521945397207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159033230418713681296931471 238549845628070521945397207)
  ·
    refine ⟨357824768442105782918095811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238549845628070521945397207 357824768442105782918095811)
    ·
      refine ⟨536737152663158674377143717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357824768442105782918095811 536737152663158674377143717)
      ·
        refine ⟨100638216124342251445714447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 536737152663158674377143717 100638216124342251445714447)
        ·
          refine ⟨150957324186513377168571671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100638216124342251445714447 150957324186513377168571671)
          ·
            refine ⟨226435986279770065752857507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150957324186513377168571671 226435986279770065752857507)
            ·
              refine ⟨339653979419655098629286261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226435986279770065752857507 339653979419655098629286261)
              ·
                refine ⟨31842560570592665496495587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 339653979419655098629286261 31842560570592665496495587)
                ·
                  refine ⟨47763840855888998244743381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31842560570592665496495587 47763840855888998244743381)
                  ·
                    refine ⟨1119465020059898396361173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47763840855888998244743381 1119465020059898396361173)
                    ·
                      rfl

theorem cell23_6540451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 7].length) (baseStart_6540451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540451 prefixEnd_6540451 := by exact prefixLift 6540451
  have htrace : WordTrace (prefixWord ++ tailWord_6540451) baseStart_6540451 baseEnd_6540451 := by
    simpa [prefixWord, tailWord_6540451, baseEnd_6540451] using wordTrace_append hprefix tailTrace_6540451
  have hstable : (prefixWord ++ tailWord_6540451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540451).length < 2 ^ (prefixWord ++ tailWord_6540451).sum := by decide
  have hdescent : baseEnd_6540451 < baseStart_6540451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540488 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 4, 1, 4]
def baseStart_6540488 : Nat := 118140960795 + 6540488 * 2 ^ 59
def prefixEnd_6540488 : Nat := 4983230072969 + 3 ^ 40 * 6540488 * 2
def baseEnd_6540488 : Nat := 3358414058963911544320849

theorem tailTrace_6540488 : CollatzResearch.WordTrace tailWord_6540488 prefixEnd_6540488 3358414058963911544320849 := by
  unfold tailWord_6540488
  simp only [CollatzResearch.WordTrace]
  refine ⟨119275597564468238632247059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159034130085957651509662745 119275597564468238632247059)
  ·
    refine ⟨178913396346702357948370589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119275597564468238632247059 178913396346702357948370589)
    ·
      refine ⟨67092523630013384230638971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178913396346702357948370589 67092523630013384230638971)
      ·
        refine ⟨100638785445020076345958457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67092523630013384230638971 100638785445020076345958457)
        ·
          refine ⟨75479089083765057259468843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100638785445020076345958457 75479089083765057259468843)
          ·
            refine ⟨113218633625647585889203265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75479089083765057259468843 113218633625647585889203265)
            ·
              refine ⟨84913975219235689416902449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113218633625647585889203265 84913975219235689416902449)
              ·
                refine ⟨63685481414426767062676837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84913975219235689416902449 63685481414426767062676837)
                ·
                  refine ⟨11941027765205018824251907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63685481414426767062676837 11941027765205018824251907)
                  ·
                    refine ⟨17911541647807528236377861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11941027765205018824251907 17911541647807528236377861)
                    ·
                      refine ⟨3358414058963911544320849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17911541647807528236377861 3358414058963911544320849)
                      ·
                        rfl

theorem cell23_6540488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_6540488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540488 prefixEnd_6540488 := by exact prefixLift 6540488
  have htrace : WordTrace (prefixWord ++ tailWord_6540488) baseStart_6540488 baseEnd_6540488 := by
    simpa [prefixWord, tailWord_6540488, baseEnd_6540488] using wordTrace_append hprefix tailTrace_6540488
  have hstable : (prefixWord ++ tailWord_6540488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540488).length < 2 ^ (prefixWord ++ tailWord_6540488).sum := by decide
  have hdescent : baseEnd_6540488 < baseStart_6540488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540502 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_6540502 : Nat := 118140960795 + 6540502 * 2 ^ 59
def prefixEnd_6540502 : Nat := 4983230072969 + 3 ^ 40 * 6540502 * 2
def baseEnd_6540502 : Nat := 1119473749231024829848595

theorem tailTrace_6540502 : CollatzResearch.WordTrace tailWord_6540502 prefixEnd_6540502 1119473749231024829848595 := by
  unfold tailWord_6540502
  simp only [CollatzResearch.WordTrace]
  refine ⟨14909481609430359853468985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159034470500590505103669173 14909481609430359853468985)
  ·
    refine ⟨11182111207072769890101739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14909481609430359853468985 11182111207072769890101739)
    ·
      refine ⟨16773166810609154835152609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11182111207072769890101739 16773166810609154835152609)
      ·
        refine ⟨12579875107956866126364457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16773166810609154835152609 12579875107956866126364457)
        ·
          refine ⟨9434906330967649594773343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12579875107956866126364457 9434906330967649594773343)
          ·
            refine ⟨14152359496451474392160015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9434906330967649594773343 14152359496451474392160015)
            ·
              refine ⟨21228539244677211588240023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14152359496451474392160015 21228539244677211588240023)
              ·
                refine ⟨31842808867015817382360035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21228539244677211588240023 31842808867015817382360035)
                ·
                  refine ⟨47764213300523726073540053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31842808867015817382360035 47764213300523726073540053)
                  ·
                    refine ⟨1119473749231024829848595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47764213300523726073540053 1119473749231024829848595)
                    ·
                      rfl

theorem cell23_6540502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_6540502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540502 prefixEnd_6540502 := by exact prefixLift 6540502
  have htrace : WordTrace (prefixWord ++ tailWord_6540502) baseStart_6540502 baseEnd_6540502 := by
    simpa [prefixWord, tailWord_6540502, baseEnd_6540502] using wordTrace_append hprefix tailTrace_6540502
  have hstable : (prefixWord ++ tailWord_6540502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540502).length < 2 ^ (prefixWord ++ tailWord_6540502).sum := by decide
  have hdescent : baseEnd_6540502 < baseStart_6540502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540608 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 6]
def baseStart_6540608 : Nat := 118140960795 + 6540608 * 2 ^ 59
def prefixEnd_6540608 : Nat := 4983230072969 + 3 ^ 40 * 6540608 * 2
def baseEnd_6540608 : Nat := 3358475676642451074820297

theorem tailTrace_6540608 : CollatzResearch.WordTrace tailWord_6540608 prefixEnd_6540608 3358475676642451074820297 := by
  unfold tailWord_6540608
  simp only [CollatzResearch.WordTrace]
  refine ⟨119277785944250868879431239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159037047925667825172574985 119277785944250868879431239)
  ·
    refine ⟨178916678916376303319146859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119277785944250868879431239 178916678916376303319146859)
    ·
      refine ⟨268375018374564454978720289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178916678916376303319146859 268375018374564454978720289)
      ·
        refine ⟨201281263780923341234040217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268375018374564454978720289 201281263780923341234040217)
        ·
          refine ⟨150960947835692505925530163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201281263780923341234040217 150960947835692505925530163)
          ·
            refine ⟨226441421753538758888295245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150960947835692505925530163 226441421753538758888295245)
            ·
              refine ⟨84915533157577034583110717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226441421753538758888295245 84915533157577034583110717)
              ·
                refine ⟨31843324934091387968666519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84915533157577034583110717 31843324934091387968666519)
                ·
                  refine ⟨47764987401137081952999779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31843324934091387968666519 47764987401137081952999779)
                  ·
                    refine ⟨71647481101705622929499669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47764987401137081952999779 71647481101705622929499669)
                    ·
                      refine ⟨3358475676642451074820297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71647481101705622929499669 3358475676642451074820297)
                      ·
                        rfl

theorem cell23_6540608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_6540608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540608 prefixEnd_6540608 := by exact prefixLift 6540608
  have htrace : WordTrace (prefixWord ++ tailWord_6540608) baseStart_6540608 baseEnd_6540608 := by
    simpa [prefixWord, tailWord_6540608, baseEnd_6540608] using wordTrace_append hprefix tailTrace_6540608
  have hstable : (prefixWord ++ tailWord_6540608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540608).length < 2 ^ (prefixWord ++ tailWord_6540608).sum := by decide
  have hdescent : baseEnd_6540608 < baseStart_6540608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540609 : List Nat := [1, 2, 5, 2, 1, 3, 1, 2, 1, 5]
def baseStart_6540609 : Nat := 118140960795 + 6540609 * 2 ^ 59
def prefixEnd_6540609 : Nat := 4983230072969 + 3 ^ 40 * 6540609 * 2
def baseEnd_6540609 : Nat := 1119492063374368523635931

theorem tailTrace_6540609 : CollatzResearch.WordTrace tailWord_6540609 prefixEnd_6540609 1119492063374368523635931 := by
  unfold tailWord_6540609
  simp only [CollatzResearch.WordTrace]
  refine ⟨238555608361498114929648881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159037072240998743286432587 238555608361498114929648881)
  ·
    refine ⟨178916706271123586197236661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238555608361498114929648881 178916706271123586197236661)
    ·
      refine ⟨16773441212917836205990937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178916706271123586197236661 16773441212917836205990937)
      ·
        refine ⟨12580080909688377154493203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16773441212917836205990937 12580080909688377154493203)
        ·
          refine ⟨18870121364532565731739805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12580080909688377154493203 18870121364532565731739805)
          ·
            refine ⟨7076295511699712149402427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18870121364532565731739805 7076295511699712149402427)
            ·
              refine ⟨10614443267549568224103641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7076295511699712149402427 10614443267549568224103641)
              ·
                refine ⟨7960832450662176168077731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10614443267549568224103641 7960832450662176168077731)
                ·
                  refine ⟨11941248675993264252116597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7960832450662176168077731 11941248675993264252116597)
                  ·
                    refine ⟨1119492063374368523635931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11941248675993264252116597 1119492063374368523635931)
                    ·
                      rfl

theorem cell23_6540609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_6540609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540609 prefixEnd_6540609 := by exact prefixLift 6540609
  have htrace : WordTrace (prefixWord ++ tailWord_6540609) baseStart_6540609 baseEnd_6540609 := by
    simpa [prefixWord, tailWord_6540609, baseEnd_6540609] using wordTrace_append hprefix tailTrace_6540609
  have hstable : (prefixWord ++ tailWord_6540609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540609).length < 2 ^ (prefixWord ++ tailWord_6540609).sum := by decide
  have hdescent : baseEnd_6540609 < baseStart_6540609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540625 : List Nat := [1, 2, 2, 1, 4, 1, 3, 2, 1, 2, 4]
def baseStart_6540625 : Nat := 118140960795 + 6540625 * 2 ^ 59
def prefixEnd_6540625 : Nat := 4983230072969 + 3 ^ 40 * 6540625 * 2
def baseEnd_6540625 : Nat := 3358484405813577508307719

theorem tailTrace_6540625 : CollatzResearch.WordTrace tailWord_6540625 prefixEnd_6540625 3358484405813577508307719 := by
  unfold tailWord_6540625
  simp only [CollatzResearch.WordTrace]
  refine ⟨238556191929440149662231329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159037461286293433108154219 238556191929440149662231329)
  ·
    refine ⟨178917143947080112246673497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238556191929440149662231329 178917143947080112246673497)
    ·
      refine ⟨134187857960310084185005123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178917143947080112246673497 134187857960310084185005123)
      ·
        refine ⟨201281786940465126277507685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134187857960310084185005123 201281786940465126277507685)
        ·
          refine ⟨37740335051337211177032691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201281786940465126277507685 37740335051337211177032691)
          ·
            refine ⟨56610502577005816765549037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37740335051337211177032691 56610502577005816765549037)
            ·
              refine ⟨21228938466377181287080889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56610502577005816765549037 21228938466377181287080889)
              ·
                refine ⟨15921703849782885965310667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21228938466377181287080889 15921703849782885965310667)
                ·
                  refine ⟨23882555774674328947966001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15921703849782885965310667 23882555774674328947966001)
                  ·
                    refine ⟨17911916831005746710974501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23882555774674328947966001 17911916831005746710974501)
                    ·
                      refine ⟨3358484405813577508307719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17911916831005746710974501 3358484405813577508307719)
                      ·
                        rfl

theorem cell23_6540625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_6540625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540625 prefixEnd_6540625 := by exact prefixLift 6540625
  have htrace : WordTrace (prefixWord ++ tailWord_6540625) baseStart_6540625 baseEnd_6540625 := by
    simpa [prefixWord, tailWord_6540625, baseEnd_6540625] using wordTrace_append hprefix tailTrace_6540625
  have hstable : (prefixWord ++ tailWord_6540625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540625).length < 2 ^ (prefixWord ++ tailWord_6540625).sum := by decide
  have hdescent : baseEnd_6540625 < baseStart_6540625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540629 : List Nat := [1, 3, 2, 2, 3, 2, 3, 1, 1, 1, 4]
def baseStart_6540629 : Nat := 118140960795 + 6540629 * 2 ^ 59
def prefixEnd_6540629 : Nat := 4983230072969 + 3 ^ 40 * 6540629 * 2
def baseEnd_6540629 : Nat := 3358486459736195492657701

theorem tailTrace_6540629 : CollatzResearch.WordTrace tailWord_6540629 prefixEnd_6540629 3358486459736195492657701 := by
  unfold tailWord_6540629
  simp only [CollatzResearch.WordTrace]
  refine ⟨238556337821425658345376941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159037558547617105563584627 238556337821425658345376941)
  ·
    refine ⟨89458626683034621879516353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238556337821425658345376941 89458626683034621879516353)
    ·
      refine ⟨67093970012275966409637265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89458626683034621879516353 67093970012275966409637265)
      ·
        refine ⟨50320477509206974807227949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67093970012275966409637265 50320477509206974807227949)
        ·
          refine ⟨18870179065952615552710481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50320477509206974807227949 18870179065952615552710481)
          ·
            refine ⟨14152634299464461664532861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18870179065952615552710481 14152634299464461664532861)
            ·
              refine ⟨5307237862299173124199823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14152634299464461664532861 5307237862299173124199823)
              ·
                refine ⟨7960856793448759686299735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5307237862299173124199823 7960856793448759686299735)
                ·
                  refine ⟨11941285190173139529449603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7960856793448759686299735 11941285190173139529449603)
                  ·
                    refine ⟨17911927785259709294174405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11941285190173139529449603 17911927785259709294174405)
                    ·
                      refine ⟨3358486459736195492657701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17911927785259709294174405 3358486459736195492657701)
                      ·
                        rfl

theorem cell23_6540629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_6540629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540629 prefixEnd_6540629 := by exact prefixLift 6540629
  have htrace : WordTrace (prefixWord ++ tailWord_6540629) baseStart_6540629 baseEnd_6540629 := by
    simpa [prefixWord, tailWord_6540629, baseEnd_6540629] using wordTrace_append hprefix tailTrace_6540629
  have hstable : (prefixWord ++ tailWord_6540629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540629).length < 2 ^ (prefixWord ++ tailWord_6540629).sum := by decide
  have hdescent : baseEnd_6540629 < baseStart_6540629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540645 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 3, 3, 3]
def baseStart_6540645 : Nat := 118140960795 + 6540645 * 2 ^ 59
def prefixEnd_6540645 : Nat := 4983230072969 + 3 ^ 40 * 6540645 * 2
def baseEnd_6540645 : Nat := 3358494675426667430057627

theorem tailTrace_6540645 : CollatzResearch.WordTrace tailWord_6540645 prefixEnd_6540645 3358494675426667430057627 := by
  unfold tailWord_6540645
  simp only [CollatzResearch.WordTrace]
  refine ⟨238556921389367693077959389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159037947592911795385306259 238556921389367693077959389)
  ·
    refine ⟨89458845521012884904234771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238556921389367693077959389 89458845521012884904234771)
    ·
      refine ⟨134188268281519327356352157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89458845521012884904234771 134188268281519327356352157)
      ·
        refine ⟨50320600605569747758632059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134188268281519327356352157 50320600605569747758632059)
        ·
          refine ⟨75480900908354621637948089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50320600605569747758632059 75480900908354621637948089)
          ·
            refine ⟨56610675681265966228461067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75480900908354621637948089 56610675681265966228461067)
            ·
              refine ⟨84916013521898949342691601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56610675681265966228461067 84916013521898949342691601)
              ·
                refine ⟨63687010141424212007018701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84916013521898949342691601 63687010141424212007018701)
                ·
                  refine ⟨23882628803034079502632013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63687010141424212007018701 23882628803034079502632013)
                  ·
                    refine ⟨8955985801137779813487005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23882628803034079502632013 8955985801137779813487005)
                    ·
                      refine ⟨3358494675426667430057627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8955985801137779813487005 3358494675426667430057627)
                      ·
                        rfl

theorem cell23_6540645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_6540645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540645 prefixEnd_6540645 := by exact prefixLift 6540645
  have htrace : WordTrace (prefixWord ++ tailWord_6540645) baseStart_6540645 baseEnd_6540645 := by
    simpa [prefixWord, tailWord_6540645, baseEnd_6540645] using wordTrace_append hprefix tailTrace_6540645
  have hstable : (prefixWord ++ tailWord_6540645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540645).length < 2 ^ (prefixWord ++ tailWord_6540645).sum := by decide
  have hdescent : baseEnd_6540645 < baseStart_6540645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540719 : List Nat := [1, 1, 2, 1, 2, 2, 1, 7, 2, 2, 2]
def baseStart_6540719 : Nat := 118140960795 + 6540719 * 2 ^ 59
def prefixEnd_6540719 : Nat := 4983230072969 + 3 ^ 40 * 6540719 * 2
def baseEnd_6540719 : Nat := 3358532672995100140532287

theorem tailTrace_6540719 : CollatzResearch.WordTrace tailWord_6540719 prefixEnd_6540719 3358532672995100140532287 := by
  unfold tailWord_6540719
  simp only [CollatzResearch.WordTrace]
  refine ⟨238559620391099603716153211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159039746927399735810768807 238559620391099603716153211)
  ·
    refine ⟨357839430586649405574229817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238559620391099603716153211 357839430586649405574229817)
    ·
      refine ⟨268379572939987054180672363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357839430586649405574229817 268379572939987054180672363)
      ·
        refine ⟨402569359409980581271008545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268379572939987054180672363 402569359409980581271008545)
        ·
          refine ⟨301927019557485435953256409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402569359409980581271008545 301927019557485435953256409)
          ·
            refine ⟨226445264668114076964942307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301927019557485435953256409 226445264668114076964942307)
            ·
              refine ⟨339667897002171115447413461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226445264668114076964942307 339667897002171115447413461)
              ·
                refine ⟨7960966335988385518298753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 339667897002171115447413461 7960966335988385518298753)
                ·
                  refine ⟨5970724751991289138724065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7960966335988385518298753 5970724751991289138724065)
                  ·
                    refine ⟨4478043563993466854043049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5970724751991289138724065 4478043563993466854043049)
                    ·
                      refine ⟨3358532672995100140532287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4478043563993466854043049 3358532672995100140532287)
                      ·
                        rfl

theorem cell23_6540719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 2, 2].length) (baseStart_6540719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540719 prefixEnd_6540719 := by exact prefixLift 6540719
  have htrace : WordTrace (prefixWord ++ tailWord_6540719) baseStart_6540719 baseEnd_6540719 := by
    simpa [prefixWord, tailWord_6540719, baseEnd_6540719] using wordTrace_append hprefix tailTrace_6540719
  have hstable : (prefixWord ++ tailWord_6540719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540719).length < 2 ^ (prefixWord ++ tailWord_6540719).sum := by decide
  have hdescent : baseEnd_6540719 < baseStart_6540719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540735 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 3]
def baseStart_6540735 : Nat := 118140960795 + 6540735 * 2 ^ 59
def prefixEnd_6540735 : Nat := 4983230072969 + 3 ^ 40 * 6540735 * 2
def baseEnd_6540735 : Nat := 3358540888685572077932213

theorem tailTrace_6540735 : CollatzResearch.WordTrace tailWord_6540735 prefixEnd_6540735 3358540888685572077932213 := by
  unfold tailWord_6540735
  simp only [CollatzResearch.WordTrace]
  refine ⟨238560203959041638448735659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159040135972694425632490439 238560203959041638448735659)
  ·
    refine ⟨357840305938562457673103489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238560203959041638448735659 357840305938562457673103489)
    ·
      refine ⟨268380229453921843254827617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357840305938562457673103489 268380229453921843254827617)
      ·
        refine ⟨201285172090441382441120713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268380229453921843254827617 201285172090441382441120713)
        ·
          refine ⟨150963879067831036830840535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201285172090441382441120713 150963879067831036830840535)
          ·
            refine ⟨226445818601746555246260803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150963879067831036830840535 226445818601746555246260803)
            ·
              refine ⟨339668727902619832869391205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226445818601746555246260803 339668727902619832869391205)
              ·
                refine ⟨63687886481741218663010851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 339668727902619832869391205 63687886481741218663010851)
                ·
                  refine ⟨95531829722611827994516277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63687886481741218663010851 95531829722611827994516277)
                  ·
                    refine ⟨8956109036494858874485901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95531829722611827994516277 8956109036494858874485901)
                    ·
                      refine ⟨3358540888685572077932213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8956109036494858874485901 3358540888685572077932213)
                      ·
                        rfl

theorem cell23_6540735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_6540735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540735 prefixEnd_6540735 := by exact prefixLift 6540735
  have htrace : WordTrace (prefixWord ++ tailWord_6540735) baseStart_6540735 baseEnd_6540735 := by
    simpa [prefixWord, tailWord_6540735, baseEnd_6540735] using wordTrace_append hprefix tailTrace_6540735
  have hstable : (prefixWord ++ tailWord_6540735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540735).length < 2 ^ (prefixWord ++ tailWord_6540735).sum := by decide
  have hdescent : baseEnd_6540735 < baseStart_6540735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540789 : List Nat := [1, 3, 5, 1, 1, 1, 1, 3, 2, 5]
def baseStart_6540789 : Nat := 118140960795 + 6540789 * 2 ^ 59
def prefixEnd_6540789 : Nat := 4983230072969 + 3 ^ 40 * 6540789 * 2
def baseEnd_6540789 : Nat := 1119522872213638288885655

theorem tailTrace_6540789 : CollatzResearch.WordTrace tailWord_6540789 prefixEnd_6540789 1119522872213638288885655 := by
  unfold tailWord_6540789
  simp only [CollatzResearch.WordTrace]
  refine ⟨238562173500846005671201421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159041449000564003780800947 238562173500846005671201421)
  ·
    refine ⟨89460815062817252126700533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238562173500846005671201421 89460815062817252126700533)
    ·
      refine ⟨8386951412139117386878175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89460815062817252126700533 8386951412139117386878175)
      ·
        refine ⟨12580427118208676080317263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8386951412139117386878175 12580427118208676080317263)
        ·
          refine ⟨18870640677313014120475895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12580427118208676080317263 18870640677313014120475895)
          ·
            refine ⟨28305961015969521180713843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18870640677313014120475895 28305961015969521180713843)
            ·
              refine ⟨42458941523954281771070765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28305961015969521180713843 42458941523954281771070765)
              ·
                refine ⟨15922103071482855664151537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42458941523954281771070765 15922103071482855664151537)
                ·
                  refine ⟨11941577303612141748113653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15922103071482855664151537 11941577303612141748113653)
                  ·
                    refine ⟨1119522872213638288885655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11941577303612141748113653 1119522872213638288885655)
                    ·
                      rfl

theorem cell23_6540789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_6540789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540789 prefixEnd_6540789 := by exact prefixLift 6540789
  have htrace : WordTrace (prefixWord ++ tailWord_6540789) baseStart_6540789 baseEnd_6540789 := by
    simpa [prefixWord, tailWord_6540789, baseEnd_6540789] using wordTrace_append hprefix tailTrace_6540789
  have hstable : (prefixWord ++ tailWord_6540789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540789).length < 2 ^ (prefixWord ++ tailWord_6540789).sum := by decide
  have hdescent : baseEnd_6540789 < baseStart_6540789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540792 : List Nat := [2, 1, 2, 1, 1, 5, 1, 3, 2, 1, 4]
def baseStart_6540792 : Nat := 118140960795 + 6540792 * 2 ^ 59
def prefixEnd_6540792 : Nat := 4983230072969 + 3 ^ 40 * 6540792 * 2
def baseEnd_6540792 : Nat := 3358570157082878354919451

theorem tailTrace_6540792 : CollatzResearch.WordTrace tailWord_6540792 prefixEnd_6540792 3358570157082878354919451 := by
  unfold tailWord_6540792
  simp only [CollatzResearch.WordTrace]
  refine ⟨119281141459917568591780315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159041521946556758122373753 119281141459917568591780315)
  ·
    refine ⟨178921712189876352887670473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119281141459917568591780315 178921712189876352887670473)
    ·
      refine ⟨134191284142407264665752855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178921712189876352887670473 134191284142407264665752855)
      ·
        refine ⟨201286926213610896998629283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134191284142407264665752855 201286926213610896998629283)
        ·
          refine ⟨301930389320416345497943925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201286926213610896998629283 301930389320416345497943925)
          ·
            refine ⟨28305973998789032390432243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 301930389320416345497943925 28305973998789032390432243)
            ·
              refine ⟨42458960998183548585648365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28305973998789032390432243 42458960998183548585648365)
              ·
                refine ⟨15922110374318830719618137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42458960998183548585648365 15922110374318830719618137)
                ·
                  refine ⟨11941582780739123039713603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15922110374318830719618137 11941582780739123039713603)
                  ·
                    refine ⟨17912374171108684559570405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11941582780739123039713603 17912374171108684559570405)
                    ·
                      refine ⟨3358570157082878354919451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17912374171108684559570405 3358570157082878354919451)
                      ·
                        rfl

theorem cell23_6540792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_6540792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540792 prefixEnd_6540792 := by exact prefixLift 6540792
  have htrace : WordTrace (prefixWord ++ tailWord_6540792) baseStart_6540792 baseEnd_6540792 := by
    simpa [prefixWord, tailWord_6540792, baseEnd_6540792] using wordTrace_append hprefix tailTrace_6540792
  have hstable : (prefixWord ++ tailWord_6540792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540792).length < 2 ^ (prefixWord ++ tailWord_6540792).sum := by decide
  have hdescent : baseEnd_6540792 < baseStart_6540792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540805 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 2, 1, 6]
def baseStart_6540805 : Nat := 118140960795 + 6540805 * 2 ^ 59
def prefixEnd_6540805 : Nat := 4983230072969 + 3 ^ 40 * 6540805 * 2
def baseEnd_6540805 : Nat := 3358576832331386804056891

theorem tailTrace_6540805 : CollatzResearch.WordTrace tailWord_6540805 prefixEnd_6540805 3358576832331386804056891 := by
  unfold tailWord_6540805
  simp only [CollatzResearch.WordTrace]
  refine ⟨238562757068788040403783869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159041838045858693602522579 238562757068788040403783869)
  ·
    refine ⟨89461033900795515151418951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238562757068788040403783869 89461033900795515151418951)
    ·
      refine ⟨134191550851193272727128427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89461033900795515151418951 134191550851193272727128427)
      ·
        refine ⟨201287326276789909090692641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134191550851193272727128427 201287326276789909090692641)
        ·
          refine ⟨150965494707592431818019481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201287326276789909090692641 150965494707592431818019481)
          ·
            refine ⟨113224121030694323863514611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150965494707592431818019481 113224121030694323863514611)
            ·
              refine ⟨169836181546041485795271917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113224121030694323863514611 169836181546041485795271917)
              ·
                refine ⟨63688568079765557173226969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169836181546041485795271917 63688568079765557173226969)
                ·
                  refine ⟨47766426059824167879920227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63688568079765557173226969 47766426059824167879920227)
                  ·
                    refine ⟨71649639089736251819880341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47766426059824167879920227 71649639089736251819880341)
                    ·
                      refine ⟨3358576832331386804056891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71649639089736251819880341 3358576832331386804056891)
                      ·
                        rfl

theorem cell23_6540805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_6540805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540805 prefixEnd_6540805 := by exact prefixLift 6540805
  have htrace : WordTrace (prefixWord ++ tailWord_6540805) baseStart_6540805 baseEnd_6540805 := by
    simpa [prefixWord, tailWord_6540805, baseEnd_6540805] using wordTrace_append hprefix tailTrace_6540805
  have hstable : (prefixWord ++ tailWord_6540805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540805).length < 2 ^ (prefixWord ++ tailWord_6540805).sum := by decide
  have hdescent : baseEnd_6540805 < baseStart_6540805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540846 : List Nat := [4, 1, 3, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_6540846 : Nat := 118140960795 + 6540846 * 2 ^ 59
def prefixEnd_6540846 : Nat := 4983230072969 + 3 ^ 40 * 6540846 * 2
def baseEnd_6540846 : Nat := 3358597885038221143644203

theorem tailTrace_6540846 : CollatzResearch.WordTrace tailWord_6540846 prefixEnd_6540846 3358597885038221143644203 := by
  unfold tailWord_6540846
  simp only [CollatzResearch.WordTrace]
  refine ⟨29820531557704938050753299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159042834974426336270684261 29820531557704938050753299)
  ·
    refine ⟨44730797336557407076129949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29820531557704938050753299 44730797336557407076129949)
    ·
      refine ⟨16774049001209027653548731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44730797336557407076129949 16774049001209027653548731)
      ·
        refine ⟨25161073501813541480323097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16774049001209027653548731 25161073501813541480323097)
        ·
          refine ⟨18870805126360156110242323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25161073501813541480323097 18870805126360156110242323)
          ·
            refine ⟨28306207689540234165363485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18870805126360156110242323 28306207689540234165363485)
            ·
              refine ⟨10614827883577587812011307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28306207689540234165363485 10614827883577587812011307)
              ·
                refine ⟨15922241825366381718016961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10614827883577587812011307 15922241825366381718016961)
                ·
                  refine ⟨11941681369024786288512721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15922241825366381718016961 11941681369024786288512721)
                  ·
                    refine ⟨8956261026768589716384541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11941681369024786288512721 8956261026768589716384541)
                    ·
                      refine ⟨3358597885038221143644203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8956261026768589716384541 3358597885038221143644203)
                      ·
                        rfl

theorem cell23_6540846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_6540846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540846 prefixEnd_6540846 := by exact prefixLift 6540846
  have htrace : WordTrace (prefixWord ++ tailWord_6540846) baseStart_6540846 baseEnd_6540846 := by
    simpa [prefixWord, tailWord_6540846, baseEnd_6540846] using wordTrace_append hprefix tailTrace_6540846
  have hstable : (prefixWord ++ tailWord_6540846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540846).length < 2 ^ (prefixWord ++ tailWord_6540846).sum := by decide
  have hdescent : baseEnd_6540846 < baseStart_6540846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540869 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 4, 3, 2]
def baseStart_6540869 : Nat := 118140960795 + 6540869 * 2 ^ 59
def prefixEnd_6540869 : Nat := 4983230072969 + 3 ^ 40 * 6540869 * 2
def baseEnd_6540869 : Nat := 3358609695093274553656597

theorem tailTrace_6540869 : CollatzResearch.WordTrace tailWord_6540869 prefixEnd_6540869 3358609695093274553656597 := by
  unfold tailWord_6540869
  simp only [CollatzResearch.WordTrace]
  refine ⟨238565091340556179334113661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159043394227037452889409107 238565091340556179334113661)
  ·
    refine ⟨89461909252708567250292623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238565091340556179334113661 89461909252708567250292623)
    ·
      refine ⟨134192863879062850875438935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89461909252708567250292623 134192863879062850875438935)
      ·
        refine ⟨201289295818594276313158403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134192863879062850875438935 201289295818594276313158403)
        ·
          refine ⟨301933943727891414469737605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201289295818594276313158403 301933943727891414469737605)
          ·
            refine ⟨56612614448979640213075801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 301933943727891414469737605 56612614448979640213075801)
            ·
              refine ⟨42459460836734730159806851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56612614448979640213075801 42459460836734730159806851)
              ·
                refine ⟨63689191255102095239710277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42459460836734730159806851 63689191255102095239710277)
                ·
                  refine ⟨11941723360331642857445677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63689191255102095239710277 11941723360331642857445677)
                  ·
                    refine ⟨4478146260124366071542129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11941723360331642857445677 4478146260124366071542129)
                    ·
                      refine ⟨3358609695093274553656597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4478146260124366071542129 3358609695093274553656597)
                      ·
                        rfl

theorem cell23_6540869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 3, 2].length) (baseStart_6540869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540869 prefixEnd_6540869 := by exact prefixLift 6540869
  have htrace : WordTrace (prefixWord ++ tailWord_6540869) baseStart_6540869 baseEnd_6540869 := by
    simpa [prefixWord, tailWord_6540869, baseEnd_6540869] using wordTrace_append hprefix tailTrace_6540869
  have hstable : (prefixWord ++ tailWord_6540869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540869).length < 2 ^ (prefixWord ++ tailWord_6540869).sum := by decide
  have hdescent : baseEnd_6540869 < baseStart_6540869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540876 : List Nat := [2, 2, 1, 3, 1, 4, 2, 1, 3, 1, 3]
def baseStart_6540876 : Nat := 118140960795 + 6540876 * 2 ^ 59
def prefixEnd_6540876 : Nat := 4983230072969 + 3 ^ 40 * 6540876 * 2
def baseEnd_6540876 : Nat := 3358613289457856026269065

theorem tailTrace_6540876 : CollatzResearch.WordTrace tailWord_6540876 prefixEnd_6540876 3358613289457856026269065 := by
  unfold tailWord_6540876
  simp only [CollatzResearch.WordTrace]
  refine ⟨119282673325765409764809241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159043564434353879686412321 119282673325765409764809241)
  ·
    refine ⟨89462004994324057323606931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119282673325765409764809241 89462004994324057323606931)
    ·
      refine ⟨134193007491486085985410397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89462004994324057323606931 134193007491486085985410397)
      ·
        refine ⟨50322377809307282244528899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134193007491486085985410397 50322377809307282244528899)
        ·
          refine ⟨75483566713960923366793349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50322377809307282244528899 75483566713960923366793349)
          ·
            refine ⟨14153168758867673131273753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75483566713960923366793349 14153168758867673131273753)
            ·
              refine ⟨10614876569150754848455315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14153168758867673131273753 10614876569150754848455315)
              ·
                refine ⟨15922314853726132272682973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10614876569150754848455315 15922314853726132272682973)
                ·
                  refine ⟨5970868070147299602256115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15922314853726132272682973 5970868070147299602256115)
                  ·
                    refine ⟨8956302105220949403384173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5970868070147299602256115 8956302105220949403384173)
                    ·
                      refine ⟨3358613289457856026269065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8956302105220949403384173 3358613289457856026269065)
                      ·
                        rfl

theorem cell23_6540876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_6540876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540876 prefixEnd_6540876 := by exact prefixLift 6540876
  have htrace : WordTrace (prefixWord ++ tailWord_6540876) baseStart_6540876 baseEnd_6540876 := by
    simpa [prefixWord, tailWord_6540876, baseEnd_6540876] using wordTrace_append hprefix tailTrace_6540876
  have hstable : (prefixWord ++ tailWord_6540876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540876).length < 2 ^ (prefixWord ++ tailWord_6540876).sum := by decide
  have hdescent : baseEnd_6540876 < baseStart_6540876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540899 : List Nat := [1, 1, 1, 5, 1, 3, 1, 4, 1, 1, 4]
def baseStart_6540899 : Nat := 118140960795 + 6540899 * 2 ^ 59
def prefixEnd_6540899 : Nat := 4983230072969 + 3 ^ 40 * 6540899 * 2
def baseEnd_6540899 : Nat := 3358625099512909436281459

theorem tailTrace_6540899 : CollatzResearch.WordTrace tailWord_6540899 prefixEnd_6540899 3358625099512909436281459 := by
  unfold tailWord_6540899
  simp only [CollatzResearch.WordTrace]
  refine ⟨238566185530447494457705751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159044123686964996305137167 238566185530447494457705751)
  ·
    refine ⟨357849278295671241686558627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238566185530447494457705751 357849278295671241686558627)
    ·
      refine ⟨536773917443506862529837941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357849278295671241686558627 536773917443506862529837941)
      ·
        refine ⟨50322554760328768362172307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 536773917443506862529837941 50322554760328768362172307)
        ·
          refine ⟨75483832140493152543258461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50322554760328768362172307 75483832140493152543258461)
          ·
            refine ⟨28306437052684932203721923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75483832140493152543258461 28306437052684932203721923)
            ·
              refine ⟨42459655579027398305582885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28306437052684932203721923 42459655579027398305582885)
              ·
                refine ⟨7961185421067637182296791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42459655579027398305582885 7961185421067637182296791)
                ·
                  refine ⟨11941778131601455773445187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7961185421067637182296791 11941778131601455773445187)
                  ·
                    refine ⟨17912667197402183660167781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11941778131601455773445187 17912667197402183660167781)
                    ·
                      refine ⟨3358625099512909436281459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17912667197402183660167781 3358625099512909436281459)
                      ·
                        rfl

theorem cell23_6540899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_6540899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540899 prefixEnd_6540899 := by exact prefixLift 6540899
  have htrace : WordTrace (prefixWord ++ tailWord_6540899) baseStart_6540899 baseEnd_6540899 := by
    simpa [prefixWord, tailWord_6540899, baseEnd_6540899] using wordTrace_append hprefix tailTrace_6540899
  have hstable : (prefixWord ++ tailWord_6540899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540899).length < 2 ^ (prefixWord ++ tailWord_6540899).sum := by decide
  have hdescent : baseEnd_6540899 < baseStart_6540899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540972 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 4]
def baseStart_6540972 : Nat := 118140960795 + 6540972 * 2 ^ 59
def prefixEnd_6540972 : Nat := 4983230072969 + 3 ^ 40 * 6540972 * 2
def baseEnd_6540972 : Nat := 3358662583600687650668623

theorem tailTrace_6540972 : CollatzResearch.WordTrace tailWord_6540972 prefixEnd_6540972 3358662583600687650668623 := by
  unfold tailWord_6540972
  simp only [CollatzResearch.WordTrace]
  refine ⟨119284424029591513962556585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159045898706122018616742113 119284424029591513962556585)
  ·
    refine ⟨89463318022193635471917439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119284424029591513962556585 89463318022193635471917439)
    ·
      refine ⟨134194977033290453207876159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89463318022193635471917439 134194977033290453207876159)
      ·
        refine ⟨201292465549935679811814239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134194977033290453207876159 201292465549935679811814239)
        ·
          refine ⟨301938698324903519717721359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201292465549935679811814239 301938698324903519717721359)
          ·
            refine ⟨452908047487355279576582039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301938698324903519717721359 452908047487355279576582039)
            ·
              refine ⟨679362071231032919364873059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452908047487355279576582039 679362071231032919364873059)
              ·
                refine ⟨1019043106846549379047309589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 679362071231032919364873059 1019043106846549379047309589)
                ·
                  refine ⟨47767645633432002142842637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1019043106846549379047309589 47767645633432002142842637)
                  ·
                    refine ⟨17912867112537000803565989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47767645633432002142842637 17912867112537000803565989)
                    ·
                      refine ⟨3358662583600687650668623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17912867112537000803565989 3358662583600687650668623)
                      ·
                        rfl

theorem cell23_6540972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_6540972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540972 prefixEnd_6540972 := by exact prefixLift 6540972
  have htrace : WordTrace (prefixWord ++ tailWord_6540972) baseStart_6540972 baseEnd_6540972 := by
    simpa [prefixWord, tailWord_6540972, baseEnd_6540972] using wordTrace_append hprefix tailTrace_6540972
  have hstable : (prefixWord ++ tailWord_6540972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540972).length < 2 ^ (prefixWord ++ tailWord_6540972).sum := by decide
  have hdescent : baseEnd_6540972 < baseStart_6540972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540976 : List Nat := [2, 1, 1, 1, 2, 1, 4, 5, 1, 3, 2]
def baseStart_6540976 : Nat := 118140960795 + 6540976 * 2 ^ 59
def prefixEnd_6540976 : Nat := 4983230072969 + 3 ^ 40 * 6540976 * 2
def baseEnd_6540976 : Nat := 3358664637523305635018605

theorem tailTrace_6540976 : CollatzResearch.WordTrace tailWord_6540976 prefixEnd_6540976 3358664637523305635018605 := by
  unfold tailWord_6540976
  simp only [CollatzResearch.WordTrace]
  refine ⟨119284496975584268304129391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159045995967445691072172521 119284496975584268304129391)
  ·
    refine ⟨178926745463376402456194087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119284496975584268304129391 178926745463376402456194087)
    ·
      refine ⟨268390118195064603684291131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178926745463376402456194087 268390118195064603684291131)
      ·
        refine ⟨402585177292596905526436697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268390118195064603684291131 402585177292596905526436697)
        ·
          refine ⟨301938882969447679144827523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402585177292596905526436697 301938882969447679144827523)
          ·
            refine ⟨452908324454171518717241285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301938882969447679144827523 452908324454171518717241285)
            ·
              refine ⟨84920310835157159759482741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 452908324454171518717241285 84920310835157159759482741)
              ·
                refine ⟨7961279140795983727451507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84920310835157159759482741 7961279140795983727451507)
                ·
                  refine ⟨11941918711193975591177261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7961279140795983727451507 11941918711193975591177261)
                  ·
                    refine ⟨4478219516697740846691473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11941918711193975591177261 4478219516697740846691473)
                    ·
                      refine ⟨3358664637523305635018605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4478219516697740846691473 3358664637523305635018605)
                      ·
                        rfl

theorem cell23_6540976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 1, 3, 2].length) (baseStart_6540976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540976 prefixEnd_6540976 := by exact prefixLift 6540976
  have htrace : WordTrace (prefixWord ++ tailWord_6540976) baseStart_6540976 baseEnd_6540976 := by
    simpa [prefixWord, tailWord_6540976, baseEnd_6540976] using wordTrace_append hprefix tailTrace_6540976
  have hstable : (prefixWord ++ tailWord_6540976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540976).length < 2 ^ (prefixWord ++ tailWord_6540976).sum := by decide
  have hdescent : baseEnd_6540976 < baseStart_6540976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6540983 : List Nat := [1, 1, 3, 1, 5, 2, 2, 2, 2, 1, 3]
def baseStart_6540983 : Nat := 118140960795 + 6540983 * 2 ^ 59
def prefixEnd_6540983 : Nat := 4983230072969 + 3 ^ 40 * 6540983 * 2
def baseEnd_6540983 : Nat := 3358668231887887107631073

theorem tailTrace_6540983 : CollatzResearch.WordTrace tailWord_6540983 prefixEnd_6540983 3358668231887887107631073 := by
  unfold tailWord_6540983
  simp only [CollatzResearch.WordTrace]
  refine ⟨238569249262143176803763603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159046166174762117869175735 238569249262143176803763603)
  ·
    refine ⟨357853873893214765205645405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238569249262143176803763603 357853873893214765205645405)
    ·
      refine ⟨134195202709955536952117027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357853873893214765205645405 134195202709955536952117027)
      ·
        refine ⟨201292804064933305428175541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134195202709955536952117027 201292804064933305428175541)
        ·
          refine ⟨18871200381087497383891457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201292804064933305428175541 18871200381087497383891457)
          ·
            refine ⟨14153400285815623037918593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18871200381087497383891457 14153400285815623037918593)
            ·
              refine ⟨10615050214361717278438945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14153400285815623037918593 10615050214361717278438945)
              ·
                refine ⟨7961287660771287958829209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10615050214361717278438945 7961287660771287958829209)
                ·
                  refine ⟨5970965745578465969121907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7961287660771287958829209 5970965745578465969121907)
                  ·
                    refine ⟨8956448618367698953682861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5970965745578465969121907 8956448618367698953682861)
                    ·
                      refine ⟨3358668231887887107631073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8956448618367698953682861 3358668231887887107631073)
                      ·
                        rfl

theorem cell23_6540983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 1, 3].length) (baseStart_6540983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6540983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6540983 prefixEnd_6540983 := by exact prefixLift 6540983
  have htrace : WordTrace (prefixWord ++ tailWord_6540983) baseStart_6540983 baseEnd_6540983 := by
    simpa [prefixWord, tailWord_6540983, baseEnd_6540983] using wordTrace_append hprefix tailTrace_6540983
  have hstable : (prefixWord ++ tailWord_6540983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6540983).length < 2 ^ (prefixWord ++ tailWord_6540983).sum := by decide
  have hdescent : baseEnd_6540983 < baseStart_6540983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6540983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541027 : List Nat := [1, 1, 1, 7, 2, 2, 2, 1, 1, 3, 2]
def baseStart_6541027 : Nat := 118140960795 + 6541027 * 2 ^ 59
def prefixEnd_6541027 : Nat := 4983230072969 + 3 ^ 40 * 6541027 * 2
def baseEnd_6541027 : Nat := 3358690825036684935480871

theorem tailTrace_6541027 : CollatzResearch.WordTrace tailWord_6541027 prefixEnd_6541027 3358690825036684935480871 := by
  unfold tailWord_6541027
  simp only [CollatzResearch.WordTrace]
  refine ⟨238570854073983772318365335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159047236049322514878910223 238570854073983772318365335)
  ·
    refine ⟨357856281110975658477548003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238570854073983772318365335 357856281110975658477548003)
    ·
      refine ⟨536784421666463487716322005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357856281110975658477548003 536784421666463487716322005)
      ·
        refine ⟨12580884882807737993351297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 536784421666463487716322005 12580884882807737993351297)
        ·
          refine ⟨9435663662105803495013473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12580884882807737993351297 9435663662105803495013473)
          ·
            refine ⟨7076747746579352621260105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9435663662105803495013473 7076747746579352621260105)
            ·
              refine ⟨5307560809934514465945079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7076747746579352621260105 5307560809934514465945079)
              ·
                refine ⟨7961341214901771698917619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5307560809934514465945079 7961341214901771698917619)
                ·
                  refine ⟨11942011822352657548376429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7961341214901771698917619 11942011822352657548376429)
                  ·
                    refine ⟨4478254433382246580641161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11942011822352657548376429 4478254433382246580641161)
                    ·
                      refine ⟨3358690825036684935480871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4478254433382246580641161 3358690825036684935480871)
                      ·
                        rfl

theorem cell23_6541027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_6541027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541027 prefixEnd_6541027 := by exact prefixLift 6541027
  have htrace : WordTrace (prefixWord ++ tailWord_6541027) baseStart_6541027 baseEnd_6541027 := by
    simpa [prefixWord, tailWord_6541027, baseEnd_6541027] using wordTrace_append hprefix tailTrace_6541027
  have hstable : (prefixWord ++ tailWord_6541027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541027).length < 2 ^ (prefixWord ++ tailWord_6541027).sum := by decide
  have hdescent : baseEnd_6541027 < baseStart_6541027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541039 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 3]
def baseStart_6541039 : Nat := 118140960795 + 6541039 * 2 ^ 59
def prefixEnd_6541039 : Nat := 4983230072969 + 3 ^ 40 * 6541039 * 2
def baseEnd_6541039 : Nat := 3358696986804538888530815

theorem tailTrace_6541039 : CollatzResearch.WordTrace tailWord_6541039 prefixEnd_6541039 3358696986804538888530815 := by
  unfold tailWord_6541039
  simp only [CollatzResearch.WordTrace]
  refine ⟨238571291749940298367802171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159047527833293532245201447 238571291749940298367802171)
  ·
    refine ⟨357856937624910447551703257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238571291749940298367802171 357856937624910447551703257)
    ·
      refine ⟨268392703218682835663777443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357856937624910447551703257 268392703218682835663777443)
      ·
        refine ⟨402589054828024253495666165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268392703218682835663777443 402589054828024253495666165)
        ·
          refine ⟨37742723890127273765218703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 402589054828024253495666165 37742723890127273765218703)
          ·
            refine ⟨56614085835190910647828055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37742723890127273765218703 56614085835190910647828055)
            ·
              refine ⟨84921128752786365971742083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56614085835190910647828055 84921128752786365971742083)
              ·
                refine ⟨127381693129179548957613125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84921128752786365971742083 127381693129179548957613125)
                ·
                  refine ⟨23884067461721165429552461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127381693129179548957613125 23884067461721165429552461)
                  ·
                    refine ⟨8956525298145437036082173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23884067461721165429552461 8956525298145437036082173)
                    ·
                      refine ⟨3358696986804538888530815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8956525298145437036082173 3358696986804538888530815)
                      ·
                        rfl

theorem cell23_6541039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 3].length) (baseStart_6541039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541039 prefixEnd_6541039 := by exact prefixLift 6541039
  have htrace : WordTrace (prefixWord ++ tailWord_6541039) baseStart_6541039 baseEnd_6541039 := by
    simpa [prefixWord, tailWord_6541039, baseEnd_6541039] using wordTrace_append hprefix tailTrace_6541039
  have hstable : (prefixWord ++ tailWord_6541039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541039).length < 2 ^ (prefixWord ++ tailWord_6541039).sum := by decide
  have hdescent : baseEnd_6541039 < baseStart_6541039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541046 : List Nat := [5, 1, 1, 1, 1, 4, 2, 1, 7]
def baseStart_6541046 : Nat := 118140960795 + 6541046 * 2 ^ 59
def prefixEnd_6541046 : Nat := 4983230072969 + 3 ^ 40 * 6541046 * 2
def baseEnd_6541046 : Nat := 373188953463235595682587

theorem tailTrace_6541046 : CollatzResearch.WordTrace tailWord_6541046 prefixEnd_6541046 373188953463235595682587 := by
  unfold tailWord_6541046
  simp only [CollatzResearch.WordTrace]
  refine ⟨14910721691307183660206687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159047698040609959042204661 14910721691307183660206687)
  ·
    refine ⟨22366082536960775490310031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14910721691307183660206687 22366082536960775490310031)
    ·
      refine ⟨33549123805441163235465047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22366082536960775490310031 33549123805441163235465047)
      ·
        refine ⟨50323685708161744853197571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33549123805441163235465047 50323685708161744853197571)
        ·
          refine ⟨75485528562242617279796357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50323685708161744853197571 75485528562242617279796357)
          ·
            refine ⟨14153536605420490739961817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75485528562242617279796357 14153536605420490739961817)
            ·
              refine ⟨10615152454065368054971363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14153536605420490739961817 10615152454065368054971363)
              ·
                refine ⟨15922728681098052082457045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10615152454065368054971363 15922728681098052082457045)
                ·
                  refine ⟨373188953463235595682587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15922728681098052082457045 373188953463235595682587)
                  ·
                    rfl

theorem cell23_6541046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_6541046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541046 prefixEnd_6541046 := by exact prefixLift 6541046
  have htrace : WordTrace (prefixWord ++ tailWord_6541046) baseStart_6541046 baseEnd_6541046 := by
    simpa [prefixWord, tailWord_6541046, baseEnd_6541046] using wordTrace_append hprefix tailTrace_6541046
  have hstable : (prefixWord ++ tailWord_6541046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541046).length < 2 ^ (prefixWord ++ tailWord_6541046).sum := by decide
  have hdescent : baseEnd_6541046 < baseStart_6541046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541096 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_6541096 : Nat := 118140960795 + 6541096 * 2 ^ 59
def prefixEnd_6541096 : Nat := 4983230072969 + 3 ^ 40 * 6541096 * 2
def baseEnd_6541096 : Nat := 3358726255201845165518053

theorem tailTrace_6541096 : CollatzResearch.WordTrace tailWord_6541096 prefixEnd_6541096 3358726255201845165518053 := by
  unfold tailWord_6541096
  simp only [CollatzResearch.WordTrace]
  refine ⟨119286685355366898551313571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159048913807155864735084761 119286685355366898551313571)
  ·
    refine ⟨178930028033050347826970357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119286685355366898551313571 178930028033050347826970357)
    ·
      refine ⟨16774690128098470108778471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178930028033050347826970357 16774690128098470108778471)
      ·
        refine ⟨25162035192147705163167707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16774690128098470108778471 25162035192147705163167707)
        ·
          refine ⟨37743052788221557744751561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25162035192147705163167707 37743052788221557744751561)
          ·
            refine ⟨28307289591166168308563671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37743052788221557744751561 28307289591166168308563671)
            ·
              refine ⟨42460934386749252462845507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28307289591166168308563671 42460934386749252462845507)
              ·
                refine ⟨63691401580123878694268261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42460934386749252462845507 63691401580123878694268261)
                ·
                  refine ⟨11942137796273227255175299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63691401580123878694268261 11942137796273227255175299)
                  ·
                    refine ⟨17913206694409840882762949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11942137796273227255175299 17913206694409840882762949)
                    ·
                      refine ⟨3358726255201845165518053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17913206694409840882762949 3358726255201845165518053)
                      ·
                        rfl

theorem cell23_6541096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_6541096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541096 prefixEnd_6541096 := by exact prefixLift 6541096
  have htrace : WordTrace (prefixWord ++ tailWord_6541096) baseStart_6541096 baseEnd_6541096 := by
    simpa [prefixWord, tailWord_6541096, baseEnd_6541096] using wordTrace_append hprefix tailTrace_6541096
  have hstable : (prefixWord ++ tailWord_6541096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541096).length < 2 ^ (prefixWord ++ tailWord_6541096).sum := by decide
  have hdescent : baseEnd_6541096 < baseStart_6541096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541173 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 1, 5, 2]
def baseStart_6541173 : Nat := 118140960795 + 6541173 * 2 ^ 59
def prefixEnd_6541173 : Nat := 4983230072969 + 3 ^ 40 * 6541173 * 2
def baseEnd_6541173 : Nat := 3358765793212241364255199

theorem tailTrace_6541173 : CollatzResearch.WordTrace tailWord_6541173 prefixEnd_6541173 3358765793212241364255199 := by
  unfold tailWord_6541173
  simp only [CollatzResearch.WordTrace]
  refine ⟨238576179131454839253180173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159050786087636559502120115 238576179131454839253180173)
  ·
    refine ⟨89466067174295564719942565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238576179131454839253180173 89466067174295564719942565)
    ·
      refine ⟨16774887595180418384989231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89466067174295564719942565 16774887595180418384989231)
      ·
        refine ⟨25162331392770627577483847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16774887595180418384989231 25162331392770627577483847)
        ·
          refine ⟨37743497089155941366225771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25162331392770627577483847 37743497089155941366225771)
          ·
            refine ⟨56615245633733912049338657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37743497089155941366225771 56615245633733912049338657)
            ·
              refine ⟨42461434225300434037003993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56615245633733912049338657 42461434225300434037003993)
              ·
                refine ⟨31846075668975325527752995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42461434225300434037003993 31846075668975325527752995)
                ·
                  refine ⟨47769113503462988291629493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31846075668975325527752995 47769113503462988291629493)
                  ·
                    refine ⟨4478354390949655152340265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47769113503462988291629493 4478354390949655152340265)
                    ·
                      refine ⟨3358765793212241364255199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4478354390949655152340265 3358765793212241364255199)
                      ·
                        rfl

theorem cell23_6541173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_6541173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541173 prefixEnd_6541173 := by exact prefixLift 6541173
  have htrace : WordTrace (prefixWord ++ tailWord_6541173) baseStart_6541173 baseEnd_6541173 := by
    simpa [prefixWord, tailWord_6541173, baseEnd_6541173] using wordTrace_append hprefix tailTrace_6541173
  have hstable : (prefixWord ++ tailWord_6541173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541173).length < 2 ^ (prefixWord ++ tailWord_6541173).sum := by decide
  have hdescent : baseEnd_6541173 < baseStart_6541173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541196 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 4, 4]
def baseStart_6541196 : Nat := 118140960795 + 6541196 * 2 ^ 59
def prefixEnd_6541196 : Nat := 4983230072969 + 3 ^ 40 * 6541196 * 2
def baseEnd_6541196 : Nat := 1119592534422431591422531

theorem tailTrace_6541196 : CollatzResearch.WordTrace tailWord_6541196 prefixEnd_6541196 1119592534422431591422531 := by
  unfold tailWord_6541196
  simp only [CollatzResearch.WordTrace]
  refine ⟨119288509005185757090633721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159051345340247676120844961 119288509005185757090633721)
  ·
    refine ⟨89466381753889317817975291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119288509005185757090633721 89466381753889317817975291)
    ·
      refine ⟨134199572630833976726962937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89466381753889317817975291 134199572630833976726962937)
      ·
        refine ⟨100649679473125482545222203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134199572630833976726962937 100649679473125482545222203)
        ·
          refine ⟨150974519209688223817833305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100649679473125482545222203 150974519209688223817833305)
          ·
            refine ⟨113230889407266167863374979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150974519209688223817833305 113230889407266167863374979)
            ·
              refine ⟨169846334110899251795062469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113230889407266167863374979 169846334110899251795062469)
              ·
                refine ⟨31846187645793609711574213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169846334110899251795062469 31846187645793609711574213)
                ·
                  refine ⟨5971160183586301820920165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31846187645793609711574213 5971160183586301820920165)
                  ·
                    refine ⟨1119592534422431591422531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5971160183586301820920165 1119592534422431591422531)
                    ·
                      rfl

theorem cell23_6541196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 4, 4].length) (baseStart_6541196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541196 prefixEnd_6541196 := by exact prefixLift 6541196
  have htrace : WordTrace (prefixWord ++ tailWord_6541196) baseStart_6541196 baseEnd_6541196 := by
    simpa [prefixWord, tailWord_6541196, baseEnd_6541196] using wordTrace_append hprefix tailTrace_6541196
  have hstable : (prefixWord ++ tailWord_6541196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541196).length < 2 ^ (prefixWord ++ tailWord_6541196).sum := by decide
  have hdescent : baseEnd_6541196 < baseStart_6541196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541199 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 4]
def baseStart_6541199 : Nat := 118140960795 + 6541199 * 2 ^ 59
def prefixEnd_6541199 : Nat := 4983230072969 + 3 ^ 40 * 6541199 * 2
def baseEnd_6541199 : Nat := 3358779143709258262530079

theorem tailTrace_6541199 : CollatzResearch.WordTrace tailWord_6541199 prefixEnd_6541199 3358779143709258262530079 := by
  unfold tailWord_6541199
  simp only [CollatzResearch.WordTrace]
  refine ⟨238577127429360645693626651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159051418286240430462417767 238577127429360645693626651)
  ·
    refine ⟨357865691144040968540439977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238577127429360645693626651 357865691144040968540439977)
    ·
      refine ⟨268399268358030726405329983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357865691144040968540439977 268399268358030726405329983)
      ·
        refine ⟨402598902537046089607994975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268399268358030726405329983 402598902537046089607994975)
        ·
          refine ⟨603898353805569134411992463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402598902537046089607994975 603898353805569134411992463)
          ·
            refine ⟨905847530708353701617988695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603898353805569134411992463 905847530708353701617988695)
            ·
              refine ⟨1358771296062530552426983043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 905847530708353701617988695 1358771296062530552426983043)
              ·
                refine ⟨2038156944093795828640474565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1358771296062530552426983043 2038156944093795828640474565)
                ·
                  refine ⟨382154427017586717870088981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2038156944093795828640474565 382154427017586717870088981)
                  ·
                    refine ⟨17913488766449377400160421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 382154427017586717870088981 17913488766449377400160421)
                    ·
                      refine ⟨3358779143709258262530079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17913488766449377400160421 3358779143709258262530079)
                      ·
                        rfl

theorem cell23_6541199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 4].length) (baseStart_6541199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541199 prefixEnd_6541199 := by exact prefixLift 6541199
  have htrace : WordTrace (prefixWord ++ tailWord_6541199) baseStart_6541199 baseEnd_6541199 := by
    simpa [prefixWord, tailWord_6541199, baseEnd_6541199] using wordTrace_append hprefix tailTrace_6541199
  have hstable : (prefixWord ++ tailWord_6541199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541199).length < 2 ^ (prefixWord ++ tailWord_6541199).sum := by decide
  have hdescent : baseEnd_6541199 < baseStart_6541199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541213 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 4, 4]
def baseStart_6541213 : Nat := 118140960795 + 6541213 * 2 ^ 59
def prefixEnd_6541213 : Nat := 4983230072969 + 3 ^ 40 * 6541213 * 2
def baseEnd_6541213 : Nat := 1119595444146140402585005

theorem tailTrace_6541213 : CollatzResearch.WordTrace tailWord_6541213 prefixEnd_6541213 1119595444146140402585005 := by
  unfold tailWord_6541213
  simp only [CollatzResearch.WordTrace]
  refine ⟨238577638051309926084636293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159051758700873284056424195 238577638051309926084636293)
  ·
    refine ⟨44733307134620611140869305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238577638051309926084636293 44733307134620611140869305)
    ·
      refine ⟨33549980350965458355651979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44733307134620611140869305 33549980350965458355651979)
      ·
        refine ⟨50324970526448187533477969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33549980350965458355651979 50324970526448187533477969)
        ·
          refine ⟨37743727894836140650108477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50324970526448187533477969 37743727894836140650108477)
          ·
            refine ⟨14153897960563552743790679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37743727894836140650108477 14153897960563552743790679)
            ·
              refine ⟨21230846940845329115686019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14153897960563552743790679 21230846940845329115686019)
              ·
                refine ⟨31846270411267993673529029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21230846940845329115686019 31846270411267993673529029)
                ·
                  refine ⟨5971175702112748813786693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31846270411267993673529029 5971175702112748813786693)
                  ·
                    refine ⟨1119595444146140402585005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5971175702112748813786693 1119595444146140402585005)
                    ·
                      rfl

theorem cell23_6541213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_6541213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541213 prefixEnd_6541213 := by exact prefixLift 6541213
  have htrace : WordTrace (prefixWord ++ tailWord_6541213) baseStart_6541213 baseEnd_6541213 := by
    simpa [prefixWord, tailWord_6541213, baseEnd_6541213] using wordTrace_append hprefix tailTrace_6541213
  have hstable : (prefixWord ++ tailWord_6541213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541213).length < 2 ^ (prefixWord ++ tailWord_6541213).sum := by decide
  have hdescent : baseEnd_6541213 < baseStart_6541213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541214 : List Nat := [4, 3, 1, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_6541214 : Nat := 118140960795 + 6541214 * 2 ^ 59
def prefixEnd_6541214 : Nat := 4983230072969 + 3 ^ 40 * 6541214 * 2
def baseEnd_6541214 : Nat := 3358786845919075703842511

theorem tailTrace_6541214 : CollatzResearch.WordTrace tailWord_6541214 prefixEnd_6541214 3358786845919075703842511 := by
  unfold tailWord_6541214
  simp only [CollatzResearch.WordTrace]
  refine ⟨29822209315538287906927837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159051783016204202170281797 29822209315538287906927837)
  ·
    refine ⟨11183328493326857965097939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29822209315538287906927837 11183328493326857965097939)
    ·
      refine ⟨16774992739990286947646909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11183328493326857965097939 16774992739990286947646909)
      ·
        refine ⟨6290622277496357605367591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16774992739990286947646909 6290622277496357605367591)
        ·
          refine ⟨9435933416244536408051387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6290622277496357605367591 9435933416244536408051387)
          ·
            refine ⟨14153900124366804612077081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9435933416244536408051387 14153900124366804612077081)
            ·
              refine ⟨10615425093275103459057811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14153900124366804612077081 10615425093275103459057811)
              ·
                refine ⟨15923137639912655188586717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10615425093275103459057811 15923137639912655188586717)
                ·
                  refine ⟨5971176614967245695720019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15923137639912655188586717 5971176614967245695720019)
                  ·
                    refine ⟨8956764922450868543580029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5971176614967245695720019 8956764922450868543580029)
                    ·
                      refine ⟨3358786845919075703842511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8956764922450868543580029 3358786845919075703842511)
                      ·
                        rfl

theorem cell23_6541214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_6541214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541214 prefixEnd_6541214 := by exact prefixLift 6541214
  have htrace : WordTrace (prefixWord ++ tailWord_6541214) baseStart_6541214 baseEnd_6541214 := by
    simpa [prefixWord, tailWord_6541214, baseEnd_6541214] using wordTrace_append hprefix tailTrace_6541214
  have hstable : (prefixWord ++ tailWord_6541214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541214).length < 2 ^ (prefixWord ++ tailWord_6541214).sum := by decide
  have hdescent : baseEnd_6541214 < baseStart_6541214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541219 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 7]
def baseStart_6541219 : Nat := 118140960795 + 6541219 * 2 ^ 59
def prefixEnd_6541219 : Nat := 4983230072969 + 3 ^ 40 * 6541219 * 2
def baseEnd_6541219 : Nat := 3358789413322348184279987

theorem tailTrace_6541219 : CollatzResearch.WordTrace tailWord_6541219 prefixEnd_6541219 3358789413322348184279987 := by
  unfold tailWord_6541219
  simp only [CollatzResearch.WordTrace]
  refine ⟨238577856889288189109354711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159051904592858792739569807 238577856889288189109354711)
  ·
    refine ⟨357866785333932283664032067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238577856889288189109354711 357866785333932283664032067)
    ·
      refine ⟨536800178000898425496048101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357866785333932283664032067 536800178000898425496048101)
      ·
        refine ⟨100650033375168454780509019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 536800178000898425496048101 100650033375168454780509019)
        ·
          refine ⟨150975050062752682170763529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100650033375168454780509019 150975050062752682170763529)
          ·
            refine ⟨113231287547064511628072647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150975050062752682170763529 113231287547064511628072647)
            ·
              refine ⟨169846931320596767442108971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113231287547064511628072647 169846931320596767442108971)
              ·
                refine ⟨254770396980895151163163457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169846931320596767442108971 254770396980895151163163457)
                ·
                  refine ⟨191077797735671363372372593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254770396980895151163163457 191077797735671363372372593)
                  ·
                    refine ⟨143308348301753522529279445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 191077797735671363372372593 143308348301753522529279445)
                    ·
                      refine ⟨3358789413322348184279987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143308348301753522529279445 3358789413322348184279987)
                      ·
                        rfl

theorem cell23_6541219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_6541219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541219 prefixEnd_6541219 := by exact prefixLift 6541219
  have htrace : WordTrace (prefixWord ++ tailWord_6541219) baseStart_6541219 baseEnd_6541219 := by
    simpa [prefixWord, tailWord_6541219, baseEnd_6541219] using wordTrace_append hprefix tailTrace_6541219
  have hstable : (prefixWord ++ tailWord_6541219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541219).length < 2 ^ (prefixWord ++ tailWord_6541219).sum := by decide
  have hdescent : baseEnd_6541219 < baseStart_6541219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541220 : List Nat := [2, 3, 1, 2, 1, 3, 1, 3, 3, 2, 2]
def baseStart_6541220 : Nat := 118140960795 + 6541220 * 2 ^ 59
def prefixEnd_6541220 : Nat := 4983230072969 + 3 ^ 40 * 6541220 * 2
def baseEnd_6541220 : Nat := 3358789926803002680367483

theorem tailTrace_6541220 : CollatzResearch.WordTrace tailWord_6541220 prefixEnd_6541220 3358789926803002680367483 := by
  unfold tailWord_6541220
  simp only [CollatzResearch.WordTrace]
  refine ⟨119288946681142283140070557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159051928908189710853427409 119288946681142283140070557)
  ·
    refine ⟨44733355005428356177526459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119288946681142283140070557 44733355005428356177526459)
    ·
      refine ⟨67100032508142534266289689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44733355005428356177526459 67100032508142534266289689)
      ·
        refine ⟨50325024381106900699717267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67100032508142534266289689 50325024381106900699717267)
        ·
          refine ⟨75487536571660351049575901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50325024381106900699717267 75487536571660351049575901)
          ·
            refine ⟨28307826214372631643590963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75487536571660351049575901 28307826214372631643590963)
            ·
              refine ⟨42461739321558947465386445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28307826214372631643590963 42461739321558947465386445)
              ·
                refine ⟨15923152245584605299519917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42461739321558947465386445 15923152245584605299519917)
                ·
                  refine ⟨5971182092094226987319969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15923152245584605299519917 5971182092094226987319969)
                  ·
                    refine ⟨4478386569070670240489977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5971182092094226987319969 4478386569070670240489977)
                    ·
                      refine ⟨3358789926803002680367483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4478386569070670240489977 3358789926803002680367483)
                      ·
                        rfl

theorem cell23_6541220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_6541220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541220 prefixEnd_6541220 := by exact prefixLift 6541220
  have htrace : WordTrace (prefixWord ++ tailWord_6541220) baseStart_6541220 baseEnd_6541220 := by
    simpa [prefixWord, tailWord_6541220, baseEnd_6541220] using wordTrace_append hprefix tailTrace_6541220
  have hstable : (prefixWord ++ tailWord_6541220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541220).length < 2 ^ (prefixWord ++ tailWord_6541220).sum := by decide
  have hdescent : baseEnd_6541220 < baseStart_6541220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541223 : List Nat := [1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_6541223 : Nat := 118140960795 + 6541223 * 2 ^ 59
def prefixEnd_6541223 : Nat := 4983230072969 + 3 ^ 40 * 6541223 * 2
def baseEnd_6541223 : Nat := 3358791467244966168629969

theorem tailTrace_6541223 : CollatzResearch.WordTrace tailWord_6541223 prefixEnd_6541223 3358791467244966168629969 := by
  unfold tailWord_6541223
  simp only [CollatzResearch.WordTrace]
  refine ⟨238578002781273697792500323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159052001854182465195000215 238578002781273697792500323)
  ·
    refine ⟨357867004171910546688750485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238578002781273697792500323 357867004171910546688750485)
    ·
      refine ⟨16775015820558306876035179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 357867004171910546688750485 16775015820558306876035179)
      ·
        refine ⟨25162523730837460314052769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16775015820558306876035179 25162523730837460314052769)
        ·
          refine ⟨18871892798128095235539577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25162523730837460314052769 18871892798128095235539577)
          ·
            refine ⟨14153919598596071426654683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18871892798128095235539577 14153919598596071426654683)
            ·
              refine ⟨21230879397894107139982025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14153919598596071426654683 21230879397894107139982025)
              ·
                refine ⟨15923159548420580354986519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21230879397894107139982025 15923159548420580354986519)
                ·
                  refine ⟨23884739322630870532479779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15923159548420580354986519 23884739322630870532479779)
                  ·
                    refine ⟨35827108983946305798719669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23884739322630870532479779 35827108983946305798719669)
                    ·
                      refine ⟨3358791467244966168629969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35827108983946305798719669 3358791467244966168629969)
                      ·
                        rfl

theorem cell23_6541223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_6541223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541223 prefixEnd_6541223 := by exact prefixLift 6541223
  have htrace : WordTrace (prefixWord ++ tailWord_6541223) baseStart_6541223 baseEnd_6541223 := by
    simpa [prefixWord, tailWord_6541223, baseEnd_6541223] using wordTrace_append hprefix tailTrace_6541223
  have hstable : (prefixWord ++ tailWord_6541223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541223).length < 2 ^ (prefixWord ++ tailWord_6541223).sum := by decide
  have hdescent : baseEnd_6541223 < baseStart_6541223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541233 : List Nat := [1, 2, 2, 4, 2, 1, 3, 1, 1, 2, 4]
def baseStart_6541233 : Nat := 118140960795 + 6541233 * 2 ^ 59
def prefixEnd_6541233 : Nat := 4983230072969 + 3 ^ 40 * 6541233 * 2
def baseEnd_6541233 : Nat := 3358796602051511129504923

theorem tailTrace_6541233 : CollatzResearch.WordTrace tailWord_6541233 prefixEnd_6541233 3358796602051511129504923 := by
  unfold tailWord_6541233
  simp only [CollatzResearch.WordTrace]
  refine ⟨238578367511237469500364353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159052245007491646333576235 238578367511237469500364353)
  ·
    refine ⟨178933775633428102125273265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238578367511237469500364353 178933775633428102125273265)
    ·
      refine ⟨134200331725071076593954949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178933775633428102125273265 134200331725071076593954949)
      ·
        refine ⟨25162562198450826861366553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134200331725071076593954949 25162562198450826861366553)
        ·
          refine ⟨18871921648838120146024915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25162562198450826861366553 18871921648838120146024915)
          ·
            refine ⟨28307882473257180219037373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18871921648838120146024915 28307882473257180219037373)
            ·
              refine ⟨10615455927471442582139015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28307882473257180219037373 10615455927471442582139015)
              ·
                refine ⟨15923183891207163873208523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10615455927471442582139015 15923183891207163873208523)
                ·
                  refine ⟨23884775836810745809812785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15923183891207163873208523 23884775836810745809812785)
                  ·
                    refine ⟨17913581877608059357359589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23884775836810745809812785 17913581877608059357359589)
                    ·
                      refine ⟨3358796602051511129504923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17913581877608059357359589 3358796602051511129504923)
                      ·
                        rfl

theorem cell23_6541233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_6541233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541233 prefixEnd_6541233 := by exact prefixLift 6541233
  have htrace : WordTrace (prefixWord ++ tailWord_6541233) baseStart_6541233 baseEnd_6541233 := by
    simpa [prefixWord, tailWord_6541233, baseEnd_6541233] using wordTrace_append hprefix tailTrace_6541233
  have hstable : (prefixWord ++ tailWord_6541233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541233).length < 2 ^ (prefixWord ++ tailWord_6541233).sum := by decide
  have hdescent : baseEnd_6541233 < baseStart_6541233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541287 : List Nat := [1, 1, 5, 2, 3, 1, 1, 3, 2, 1, 3]
def baseStart_6541287 : Nat := 118140960795 + 6541287 * 2 ^ 59
def prefixEnd_6541287 : Nat := 4983230072969 + 3 ^ 40 * 6541287 * 2
def baseEnd_6541287 : Nat := 3358824330006853918229675

theorem tailTrace_6541287 : CollatzResearch.WordTrace tailWord_6541287 prefixEnd_6541287 3358824330006853918229675 := by
  unfold tailWord_6541287
  simp only [CollatzResearch.WordTrace]
  refine ⟨238580337053041836722830115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159053558035361224481886743 238580337053041836722830115)
  ·
    refine ⟨357870505579562755084245173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238580337053041836722830115 357870505579562755084245173)
    ·
      refine ⟨33550359898084008289147985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 357870505579562755084245173 33550359898084008289147985)
      ·
        refine ⟨25162769923563006216860989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33550359898084008289147985 25162769923563006216860989)
        ·
          refine ⟨9436038721336127331322871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25162769923563006216860989 9436038721336127331322871)
          ·
            refine ⟨14154058082004190996984307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9436038721336127331322871 14154058082004190996984307)
            ·
              refine ⟨21231087123006286495476461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14154058082004190996984307 21231087123006286495476461)
              ·
                refine ⟨7961657671127357435803673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21231087123006286495476461 7961657671127357435803673)
                ·
                  refine ⟨5971243253345518076852755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7961657671127357435803673 5971243253345518076852755)
                  ·
                    refine ⟨8956864880018277115279133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5971243253345518076852755 8956864880018277115279133)
                    ·
                      refine ⟨3358824330006853918229675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8956864880018277115279133 3358824330006853918229675)
                      ·
                        rfl

theorem cell23_6541287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_6541287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541287 prefixEnd_6541287 := by exact prefixLift 6541287
  have htrace : WordTrace (prefixWord ++ tailWord_6541287) baseStart_6541287 baseEnd_6541287 := by
    simpa [prefixWord, tailWord_6541287, baseEnd_6541287] using wordTrace_append hprefix tailTrace_6541287
  have hstable : (prefixWord ++ tailWord_6541287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541287).length < 2 ^ (prefixWord ++ tailWord_6541287).sum := by decide
  have hdescent : baseEnd_6541287 < baseStart_6541287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541296 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 5]
def baseStart_6541296 : Nat := 118140960795 + 6541296 * 2 ^ 59
def prefixEnd_6541296 : Nat := 4983230072969 + 3 ^ 40 * 6541296 * 2
def baseEnd_6541296 : Nat := 3358828951332744383017133

theorem tailTrace_6541296 : CollatzResearch.WordTrace tailWord_6541296 prefixEnd_6541296 3358828951332744383017133 := by
  unfold tailWord_6541296
  simp only [CollatzResearch.WordTrace]
  refine ⟨119290332655004615629953871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159053776873339487506605161 119290332655004615629953871)
  ·
    refine ⟨178935498982506923444930807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119290332655004615629953871 178935498982506923444930807)
    ·
      refine ⟨268403248473760385167396211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178935498982506923444930807 268403248473760385167396211)
      ·
        refine ⟨402604872710640577751094317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268403248473760385167396211 402604872710640577751094317)
        ·
          refine ⟨150976827266490216656660369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 402604872710640577751094317 150976827266490216656660369)
          ·
            refine ⟨113232620449867662492495277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150976827266490216656660369 113232620449867662492495277)
            ·
              refine ⟨42462232668700373434685729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113232620449867662492495277 42462232668700373434685729)
              ·
                refine ⟨31846674501525280076014297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42462232668700373434685729 31846674501525280076014297)
                ·
                  refine ⟨23885005876143960057010723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31846674501525280076014297 23885005876143960057010723)
                  ·
                    refine ⟨35827508814215940085516085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23885005876143960057010723 35827508814215940085516085)
                    ·
                      refine ⟨3358828951332744383017133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35827508814215940085516085 3358828951332744383017133)
                      ·
                        rfl

theorem cell23_6541296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 5].length) (baseStart_6541296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541296 prefixEnd_6541296 := by exact prefixLift 6541296
  have htrace : WordTrace (prefixWord ++ tailWord_6541296) baseStart_6541296 baseEnd_6541296 := by
    simpa [prefixWord, tailWord_6541296, baseEnd_6541296] using wordTrace_append hprefix tailTrace_6541296
  have hstable : (prefixWord ++ tailWord_6541296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541296).length < 2 ^ (prefixWord ++ tailWord_6541296).sum := by decide
  have hdescent : baseEnd_6541296 < baseStart_6541296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541306 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4]
def baseStart_6541306 : Nat := 118140960795 + 6541306 * 2 ^ 59
def prefixEnd_6541306 : Nat := 4983230072969 + 3 ^ 40 * 6541306 * 2
def baseEnd_6541306 : Nat := 3358834086139289343892087

theorem tailTrace_6541306 : CollatzResearch.WordTrace tailWord_6541306 prefixEnd_6541306 3358834086139289343892087 := by
  unfold tailWord_6541306
  simp only [CollatzResearch.WordTrace]
  refine ⟨59645257509993250741942943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159054020026648668645181181 59645257509993250741942943)
  ·
    refine ⟨89467886264989876112914415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59645257509993250741942943 89467886264989876112914415)
    ·
      refine ⟨134201829397484814169371623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89467886264989876112914415 134201829397484814169371623)
      ·
        refine ⟨201302744096227221254057435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134201829397484814169371623 201302744096227221254057435)
        ·
          refine ⟨301954116144340831881086153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201302744096227221254057435 301954116144340831881086153)
          ·
            refine ⟨226465587108255623910814615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301954116144340831881086153 226465587108255623910814615)
            ·
              refine ⟨339698380662383435866221923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226465587108255623910814615 339698380662383435866221923)
              ·
                refine ⟨509547570993575153799332885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339698380662383435866221923 509547570993575153799332885)
                ·
                  refine ⟨23885042390323835334343729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 509547570993575153799332885 23885042390323835334343729)
                  ·
                    refine ⟨17913781792742876500757797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23885042390323835334343729 17913781792742876500757797)
                    ·
                      refine ⟨3358834086139289343892087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17913781792742876500757797 3358834086139289343892087)
                      ·
                        rfl

theorem cell23_6541306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_6541306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541306 prefixEnd_6541306 := by exact prefixLift 6541306
  have htrace : WordTrace (prefixWord ++ tailWord_6541306) baseStart_6541306 baseEnd_6541306 := by
    simpa [prefixWord, tailWord_6541306, baseEnd_6541306] using wordTrace_append hprefix tailTrace_6541306
  have hstable : (prefixWord ++ tailWord_6541306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541306).length < 2 ^ (prefixWord ++ tailWord_6541306).sum := by decide
  have hdescent : baseEnd_6541306 < baseStart_6541306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541343 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 3]
def baseStart_6541343 : Nat := 118140960795 + 6541343 * 2 ^ 59
def prefixEnd_6541343 : Nat := 4983230072969 + 3 ^ 40 * 6541343 * 2
def baseEnd_6541343 : Nat := 3358853084923505699129417

theorem tailTrace_6541343 : CollatzResearch.WordTrace tailWord_6541343 prefixEnd_6541343 3358853084923505699129417 := by
  unfold tailWord_6541343
  simp only [CollatzResearch.WordTrace]
  refine ⟨238582379540838958286868683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159054919693892638857912455 238582379540838958286868683)
  ·
    refine ⟨357873569311258437430303025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238582379540838958286868683 357873569311258437430303025)
    ·
      refine ⟨268405176983443828072727269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357873569311258437430303025 268405176983443828072727269)
      ·
        refine ⟨50325970684395717763636363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 268405176983443828072727269 50325970684395717763636363)
        ·
          refine ⟨75488956026593576645454545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50325970684395717763636363 75488956026593576645454545)
          ·
            refine ⟨56616717019945182484090909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75488956026593576645454545 56616717019945182484090909)
            ·
              refine ⟨21231268882479443431534091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56616717019945182484090909 21231268882479443431534091)
              ·
                refine ⟨31846903323719165147301137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21231268882479443431534091 31846903323719165147301137)
                ·
                  refine ⟨23885177492789373860475853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31846903323719165147301137 23885177492789373860475853)
                  ·
                    refine ⟨8956941559796015197678445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23885177492789373860475853 8956941559796015197678445)
                    ·
                      refine ⟨3358853084923505699129417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8956941559796015197678445 3358853084923505699129417)
                      ·
                        rfl

theorem cell23_6541343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_6541343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541343 prefixEnd_6541343 := by exact prefixLift 6541343
  have htrace : WordTrace (prefixWord ++ tailWord_6541343) baseStart_6541343 baseEnd_6541343 := by
    simpa [prefixWord, tailWord_6541343, baseEnd_6541343] using wordTrace_append hprefix tailTrace_6541343
  have hstable : (prefixWord ++ tailWord_6541343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541343).length < 2 ^ (prefixWord ++ tailWord_6541343).sum := by decide
  have hdescent : baseEnd_6541343 < baseStart_6541343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541356 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 5]
def baseStart_6541356 : Nat := 118140960795 + 6541356 * 2 ^ 59
def prefixEnd_6541356 : Nat := 4983230072969 + 3 ^ 40 * 6541356 * 2
def baseEnd_6541356 : Nat := 3358859760172014148266857

theorem tailTrace_6541356 : CollatzResearch.WordTrace tailWord_6541356 prefixEnd_6541356 3358859760172014148266857 := by
  unfold tailWord_6541356
  simp only [CollatzResearch.WordTrace]
  refine ⟨119291426844895930753545961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159055235793194574338061281 119291426844895930753545961)
  ·
    refine ⟨89468570133671948065159471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119291426844895930753545961 89468570133671948065159471)
    ·
      refine ⟨134202855200507922097739207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89468570133671948065159471 134202855200507922097739207)
      ·
        refine ⟨201304282800761883146608811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134202855200507922097739207 201304282800761883146608811)
        ·
          refine ⟨301956424201142824719913217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201304282800761883146608811 301956424201142824719913217)
          ·
            refine ⟨226467318150857118539934913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301956424201142824719913217 226467318150857118539934913)
            ·
              refine ⟨169850488613142838904951185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226467318150857118539934913 169850488613142838904951185)
              ·
                refine ⟨127387866459857129178713389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169850488613142838904951185 127387866459857129178713389)
                ·
                  refine ⟨47770449922446423442017521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127387866459857129178713389 47770449922446423442017521)
                  ·
                    refine ⟨35827837441834817581513141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47770449922446423442017521 35827837441834817581513141)
                    ·
                      refine ⟨3358859760172014148266857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35827837441834817581513141 3358859760172014148266857)
                      ·
                        rfl

theorem cell23_6541356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_6541356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541356 prefixEnd_6541356 := by exact prefixLift 6541356
  have htrace : WordTrace (prefixWord ++ tailWord_6541356) baseStart_6541356 baseEnd_6541356 := by
    simpa [prefixWord, tailWord_6541356, baseEnd_6541356] using wordTrace_append hprefix tailTrace_6541356
  have hstable : (prefixWord ++ tailWord_6541356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541356).length < 2 ^ (prefixWord ++ tailWord_6541356).sum := by decide
  have hdescent : baseEnd_6541356 < baseStart_6541356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541363 : List Nat := [1, 1, 1, 2, 4, 1, 5, 1, 2, 5]
def baseStart_6541363 : Nat := 118140960795 + 6541363 * 2 ^ 59
def prefixEnd_6541363 : Nat := 4983230072969 + 3 ^ 40 * 6541363 * 2
def baseEnd_6541363 : Nat := 1119621118178865206959775

theorem tailTrace_6541363 : CollatzResearch.WordTrace tailWord_6541363 prefixEnd_6541363 1119621118178865206959775 := by
  unfold tailWord_6541363
  simp only [CollatzResearch.WordTrace]
  refine ⟨238583109000766501702596743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159055406000511001135064495 238583109000766501702596743)
  ·
    refine ⟨357874663501149752553895115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238583109000766501702596743 357874663501149752553895115)
    ·
      refine ⟨536811995251724628830842673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357874663501149752553895115 536811995251724628830842673)
      ·
        refine ⟨402608996438793471623132005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536811995251724628830842673 402608996438793471623132005)
        ·
          refine ⟨75489186832273775929337251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 402608996438793471623132005 75489186832273775929337251)
          ·
            refine ⟨113233780248410663894005877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75489186832273775929337251 113233780248410663894005877)
            ·
              refine ⟨10615666898288499740063051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113233780248410663894005877 10615666898288499740063051)
              ·
                refine ⟨15923500347432749610094577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10615666898288499740063051 15923500347432749610094577)
                ·
                  refine ⟨11942625260574562207570933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15923500347432749610094577 11942625260574562207570933)
                  ·
                    refine ⟨1119621118178865206959775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11942625260574562207570933 1119621118178865206959775)
                    ·
                      rfl

theorem cell23_6541363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 5].length) (baseStart_6541363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541363 prefixEnd_6541363 := by exact prefixLift 6541363
  have htrace : WordTrace (prefixWord ++ tailWord_6541363) baseStart_6541363 baseEnd_6541363 := by
    simpa [prefixWord, tailWord_6541363, baseEnd_6541363] using wordTrace_append hprefix tailTrace_6541363
  have hstable : (prefixWord ++ tailWord_6541363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541363).length < 2 ^ (prefixWord ++ tailWord_6541363).sum := by decide
  have hdescent : baseEnd_6541363 < baseStart_6541363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541383 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 4]
def baseStart_6541383 : Nat := 118140960795 + 6541383 * 2 ^ 59
def prefixEnd_6541383 : Nat := 4983230072969 + 3 ^ 40 * 6541383 * 2
def baseEnd_6541383 : Nat := 3358873624149685542629233

theorem tailTrace_6541383 : CollatzResearch.WordTrace tailWord_6541383 prefixEnd_6541383 3358873624149685542629233 := by
  unfold tailWord_6541383
  simp only [CollatzResearch.WordTrace]
  refine ⟨238583838460694045118324803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159055892307129363412216535 238583838460694045118324803)
  ·
    refine ⟨357875757691041067677487205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238583838460694045118324803 357875757691041067677487205)
    ·
      refine ⟨67101704567070200189528851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 357875757691041067677487205 67101704567070200189528851)
      ·
        refine ⟨100652556850605300284293277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67101704567070200189528851 100652556850605300284293277)
        ·
          refine ⟨37744708818976987606609979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100652556850605300284293277 37744708818976987606609979)
          ·
            refine ⟨56617063228465481409914969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37744708818976987606609979 56617063228465481409914969)
            ·
              refine ⟨42462797421349111057436227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56617063228465481409914969 42462797421349111057436227)
              ·
                refine ⟨63694196132023666586154341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42462797421349111057436227 63694196132023666586154341)
                ·
                  refine ⟨11942661774754437484903939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63694196132023666586154341 11942661774754437484903939)
                  ·
                    refine ⟨17913992662131656227355909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11942661774754437484903939 17913992662131656227355909)
                    ·
                      refine ⟨3358873624149685542629233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17913992662131656227355909 3358873624149685542629233)
                      ·
                        rfl

theorem cell23_6541383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_6541383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541383 prefixEnd_6541383 := by exact prefixLift 6541383
  have htrace : WordTrace (prefixWord ++ tailWord_6541383) baseStart_6541383 baseEnd_6541383 := by
    simpa [prefixWord, tailWord_6541383, baseEnd_6541383] using wordTrace_append hprefix tailTrace_6541383
  have hstable : (prefixWord ++ tailWord_6541383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541383).length < 2 ^ (prefixWord ++ tailWord_6541383).sum := by decide
  have hdescent : baseEnd_6541383 < baseStart_6541383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541400 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 2, 4, 2]
def baseStart_6541400 : Nat := 118140960795 + 6541400 * 2 ^ 59
def prefixEnd_6541400 : Nat := 4983230072969 + 3 ^ 40 * 6541400 * 2
def baseEnd_6541400 : Nat := 3358882353320811976116655

theorem tailTrace_6541400 : CollatzResearch.WordTrace tailWord_6541400 prefixEnd_6541400 3358882353320811976116655 := by
  unfold tailWord_6541400
  simp only [CollatzResearch.WordTrace]
  refine ⟨119292229250816228510846827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159056305667754971347795769 119292229250816228510846827)
  ·
    refine ⟨178938343876224342766270241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119292229250816228510846827 178938343876224342766270241)
    ·
      refine ⟨134203757907168257074702681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178938343876224342766270241 134203757907168257074702681)
      ·
        refine ⟨100652818430376192806027011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134203757907168257074702681 100652818430376192806027011)
        ·
          refine ⟨150979227645564289209040517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100652818430376192806027011 150979227645564289209040517)
          ·
            refine ⟨28308605183543304226695097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150979227645564289209040517 28308605183543304226695097)
            ·
              refine ⟨21231453887657478170021323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28308605183543304226695097 21231453887657478170021323)
              ·
                refine ⟨31847180831486217255031985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21231453887657478170021323 31847180831486217255031985)
                ·
                  refine ⟨23885385623614662941273989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31847180831486217255031985 23885385623614662941273989)
                  ·
                    refine ⟨4478509804427749301488873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23885385623614662941273989 4478509804427749301488873)
                    ·
                      refine ⟨3358882353320811976116655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4478509804427749301488873 3358882353320811976116655)
                      ·
                        rfl

theorem cell23_6541400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_6541400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541400 prefixEnd_6541400 := by exact prefixLift 6541400
  have htrace : WordTrace (prefixWord ++ tailWord_6541400) baseStart_6541400 baseEnd_6541400 := by
    simpa [prefixWord, tailWord_6541400, baseEnd_6541400] using wordTrace_append hprefix tailTrace_6541400
  have hstable : (prefixWord ++ tailWord_6541400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541400).length < 2 ^ (prefixWord ++ tailWord_6541400).sum := by decide
  have hdescent : baseEnd_6541400 < baseStart_6541400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541444 : List Nat := [2, 3, 2, 1, 2, 1, 5, 2, 1, 4]
def baseStart_6541444 : Nat := 118140960795 + 6541444 * 2 ^ 59
def prefixEnd_6541444 : Nat := 4983230072969 + 3 ^ 40 * 6541444 * 2
def baseEnd_6541444 : Nat := 1119634982156536601322151

theorem tailTrace_6541444 : CollatzResearch.WordTrace tailWord_6541444 prefixEnd_6541444 1119634982156536601322151 := by
  unfold tailWord_6541444
  simp only [CollatzResearch.WordTrace]
  refine ⟨119293031656736526268147693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159057375542315368357530257 119293031656736526268147693)
  ·
    refine ⟨44734886871276197350555385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119293031656736526268147693 44734886871276197350555385)
    ·
      refine ⟨33551165153457148012916539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44734886871276197350555385 33551165153457148012916539)
      ·
        refine ⟨50326747730185722019374809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33551165153457148012916539 50326747730185722019374809)
        ·
          refine ⟨37745060797639291514531107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50326747730185722019374809 37745060797639291514531107)
          ·
            refine ⟨56617591196458937271796661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37745060797639291514531107 56617591196458937271796661)
            ·
              refine ⟨5307899174668025369230937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56617591196458937271796661 5307899174668025369230937)
              ·
                refine ⟨3980924381001019026923203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5307899174668025369230937 3980924381001019026923203)
                ·
                  refine ⟨5971386571501528540384805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3980924381001019026923203 5971386571501528540384805)
                  ·
                    refine ⟨1119634982156536601322151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5971386571501528540384805 1119634982156536601322151)
                    ·
                      rfl

theorem cell23_6541444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_6541444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541444 prefixEnd_6541444 := by exact prefixLift 6541444
  have htrace : WordTrace (prefixWord ++ tailWord_6541444) baseStart_6541444 baseEnd_6541444 := by
    simpa [prefixWord, tailWord_6541444, baseEnd_6541444] using wordTrace_append hprefix tailTrace_6541444
  have hstable : (prefixWord ++ tailWord_6541444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541444).length < 2 ^ (prefixWord ++ tailWord_6541444).sum := by decide
  have hdescent : baseEnd_6541444 < baseStart_6541444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541477 : List Nat := [1, 3, 1, 2, 1, 3, 4, 1, 2, 3, 2]
def baseStart_6541477 : Nat := 118140960795 + 6541477 * 2 ^ 59
def prefixEnd_6541477 : Nat := 4983230072969 + 3 ^ 40 * 6541477 * 2
def baseEnd_6541477 : Nat := 3358921891331208174853801

theorem tailTrace_6541477 : CollatzResearch.WordTrace tailWord_6541477 prefixEnd_6541477 3358921891331208174853801 := by
  unfold tailWord_6541477
  simp only [CollatzResearch.WordTrace]
  refine ⟨238587266922353499172246685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159058177948235666114831123 238587266922353499172246685)
  ·
    refine ⟨89470225095882562189592507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238587266922353499172246685 89470225095882562189592507)
    ·
      refine ⟨134205337643823843284388761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89470225095882562189592507 134205337643823843284388761)
      ·
        refine ⟨100654003232867882463291571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134205337643823843284388761 100654003232867882463291571)
        ·
          refine ⟨150981004849301823694937357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100654003232867882463291571 150981004849301823694937357)
          ·
            refine ⟨56617876818488183885601509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150981004849301823694937357 56617876818488183885601509)
            ·
              refine ⟨10615851903466534478550283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56617876818488183885601509 10615851903466534478550283)
              ·
                refine ⟨15923777855199801717825425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10615851903466534478550283 15923777855199801717825425)
                ·
                  refine ⟨11942833391399851288369069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15923777855199801717825425 11942833391399851288369069)
                  ·
                    refine ⟨4478562521774944233138401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11942833391399851288369069 4478562521774944233138401)
                    ·
                      refine ⟨3358921891331208174853801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4478562521774944233138401 3358921891331208174853801)
                      ·
                        rfl

theorem cell23_6541477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_6541477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541477 prefixEnd_6541477 := by exact prefixLift 6541477
  have htrace : WordTrace (prefixWord ++ tailWord_6541477) baseStart_6541477 baseEnd_6541477 := by
    simpa [prefixWord, tailWord_6541477, baseEnd_6541477] using wordTrace_append hprefix tailTrace_6541477
  have hstable : (prefixWord ++ tailWord_6541477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541477).length < 2 ^ (prefixWord ++ tailWord_6541477).sum := by decide
  have hdescent : baseEnd_6541477 < baseStart_6541477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541503 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 4]
def baseStart_6541503 : Nat := 118140960795 + 6541503 * 2 ^ 59
def prefixEnd_6541503 : Nat := 4983230072969 + 3 ^ 40 * 6541503 * 2
def baseEnd_6541503 : Nat := 3358935241828225073128681

theorem tailTrace_6541503 : CollatzResearch.WordTrace tailWord_6541503 prefixEnd_6541503 3358935241828225073128681 := by
  unfold tailWord_6541503
  simp only [CollatzResearch.WordTrace]
  refine ⟨238588215220259305612693163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159058810146839537075128775 238588215220259305612693163)
  ·
    refine ⟨357882322830388958419039745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238588215220259305612693163 357882322830388958419039745)
    ·
      refine ⟨268411742122791718814279809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357882322830388958419039745 268411742122791718814279809)
      ·
        refine ⟨201308806592093789110709857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268411742122791718814279809 201308806592093789110709857)
        ·
          refine ⟨150981604944070341833032393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201308806592093789110709857 150981604944070341833032393)
          ·
            refine ⟨113236203708052756374774295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150981604944070341833032393 113236203708052756374774295)
            ·
              refine ⟨169854305562079134562161443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113236203708052756374774295 169854305562079134562161443)
              ·
                refine ⟨254781458343118701843242165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169854305562079134562161443 254781458343118701843242165)
                ·
                  refine ⟨23885761719667378297803953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 254781458343118701843242165 23885761719667378297803953)
                  ·
                    refine ⟨17914321289750533723352965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23885761719667378297803953 17914321289750533723352965)
                    ·
                      refine ⟨3358935241828225073128681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17914321289750533723352965 3358935241828225073128681)
                      ·
                        rfl

theorem cell23_6541503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_6541503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541503 prefixEnd_6541503 := by exact prefixLift 6541503
  have htrace : WordTrace (prefixWord ++ tailWord_6541503) baseStart_6541503 baseEnd_6541503 := by
    simpa [prefixWord, tailWord_6541503, baseEnd_6541503] using wordTrace_append hprefix tailTrace_6541503
  have hstable : (prefixWord ++ tailWord_6541503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541503).length < 2 ^ (prefixWord ++ tailWord_6541503).sum := by decide
  have hdescent : baseEnd_6541503 < baseStart_6541503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541541 : List Nat := [1, 3, 1, 4, 2, 1, 1, 5, 1, 2, 2]
def baseStart_6541541 : Nat := 118140960795 + 6541541 * 2 ^ 59
def prefixEnd_6541541 : Nat := 4983230072969 + 3 ^ 40 * 6541541 * 2
def baseEnd_6541541 : Nat := 3358954754093095924453507

theorem tailTrace_6541541 : CollatzResearch.WordTrace tailWord_6541541 prefixEnd_6541541 3358954754093095924453507 := by
  unfold tailWord_6541541
  simp only [CollatzResearch.WordTrace]
  refine ⟨238589601194121638102576477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159059734129414425401717651 238589601194121638102576477)
  ·
    refine ⟨89471100447795614288466179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238589601194121638102576477 89471100447795614288466179)
    ·
      refine ⟨134206650671693421432699269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89471100447795614288466179 134206650671693421432699269)
      ·
        refine ⟨25163747000942516518631113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134206650671693421432699269 25163747000942516518631113)
        ·
          refine ⟨18872810250706887388973335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25163747000942516518631113 18872810250706887388973335)
          ·
            refine ⟨28309215376060331083460003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18872810250706887388973335 28309215376060331083460003)
            ·
              refine ⟨42463823064090496625190005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28309215376060331083460003 42463823064090496625190005)
              ·
                refine ⟨3980983412258484058611563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42463823064090496625190005 3980983412258484058611563)
                ·
                  refine ⟨5971475118387726087917345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3980983412258484058611563 5971475118387726087917345)
                  ·
                    refine ⟨4478606338790794565938009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5971475118387726087917345 4478606338790794565938009)
                    ·
                      refine ⟨3358954754093095924453507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4478606338790794565938009 3358954754093095924453507)
                      ·
                        rfl

theorem cell23_6541541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_6541541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541541 prefixEnd_6541541 := by exact prefixLift 6541541
  have htrace : WordTrace (prefixWord ++ tailWord_6541541) baseStart_6541541 baseEnd_6541541 := by
    simpa [prefixWord, tailWord_6541541, baseEnd_6541541] using wordTrace_append hprefix tailTrace_6541541
  have hstable : (prefixWord ++ tailWord_6541541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541541).length < 2 ^ (prefixWord ++ tailWord_6541541).sum := by decide
  have hdescent : baseEnd_6541541 < baseStart_6541541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541544 : List Nat := [2, 1, 4, 1, 2, 2, 4, 1, 1, 2, 3]
def baseStart_6541544 : Nat := 118140960795 + 6541544 * 2 ^ 59
def prefixEnd_6541544 : Nat := 4983230072969 + 3 ^ 40 * 6541544 * 2
def baseEnd_6541544 : Nat := 3358956294535059412715993

theorem tailTrace_6541544 : CollatzResearch.WordTrace tailWord_6541544 prefixEnd_6541544 3358956294535059412715993 := by
  unfold tailWord_6541544
  simp only [CollatzResearch.WordTrace]
  refine ⟨119294855306555384807467843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159059807075407179743290457 119294855306555384807467843)
  ·
    refine ⟨178942282959833077211201765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119294855306555384807467843 178942282959833077211201765)
    ·
      refine ⟨33551678054968701977100331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178942282959833077211201765 33551678054968701977100331)
      ·
        refine ⟨50327517082453052965650497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33551678054968701977100331 50327517082453052965650497)
        ·
          refine ⟨37745637811839789724237873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50327517082453052965650497 37745637811839789724237873)
          ·
            refine ⟨28309228358879842293178405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37745637811839789724237873 28309228358879842293178405)
            ·
              refine ⟨5307980317289970429970951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28309228358879842293178405 5307980317289970429970951)
              ·
                refine ⟨7961970475934955644956427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5307980317289970429970951 7961970475934955644956427)
                ·
                  refine ⟨11942955713902433467434641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7961970475934955644956427 11942955713902433467434641)
                  ·
                    refine ⟨8957216785426825100575981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11942955713902433467434641 8957216785426825100575981)
                    ·
                      refine ⟨3358956294535059412715993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8957216785426825100575981 3358956294535059412715993)
                      ·
                        rfl

theorem cell23_6541544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_6541544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541544 prefixEnd_6541544 := by exact prefixLift 6541544
  have htrace : WordTrace (prefixWord ++ tailWord_6541544) baseStart_6541544 baseEnd_6541544 := by
    simpa [prefixWord, tailWord_6541544, baseEnd_6541544] using wordTrace_append hprefix tailTrace_6541544
  have hstable : (prefixWord ++ tailWord_6541544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541544).length < 2 ^ (prefixWord ++ tailWord_6541544).sum := by decide
  have hdescent : baseEnd_6541544 < baseStart_6541544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541573 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 1, 8]
def baseStart_6541573 : Nat := 118140960795 + 6541573 * 2 ^ 59
def prefixEnd_6541573 : Nat := 4983230072969 + 3 ^ 40 * 6541573 * 2
def baseEnd_6541573 : Nat := 1119657061824679933084453

theorem tailTrace_6541573 : CollatzResearch.WordTrace tailWord_6541573 prefixEnd_6541573 1119657061824679933084453 := by
  unfold tailWord_6541573
  simp only [CollatzResearch.WordTrace]
  refine ⟨238590768330005707567741373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159060512220003805045160915 238590768330005707567741373)
  ·
    refine ⟨89471538123752140337903015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238590768330005707567741373 89471538123752140337903015)
    ·
      refine ⟨134207307185628210506854523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89471538123752140337903015 134207307185628210506854523)
      ·
        refine ⟨201310960778442315760281785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134207307185628210506854523 201310960778442315760281785)
        ·
          refine ⟨150983220583831736820211339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201310960778442315760281785 150983220583831736820211339)
          ·
            refine ⟨226474830875747605230317009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150983220583831736820211339 226474830875747605230317009)
            ·
              refine ⟨169856123156810703922737757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226474830875747605230317009 169856123156810703922737757)
              ·
                refine ⟨63696046183804013971026659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169856123156810703922737757 63696046183804013971026659)
                ·
                  refine ⟨95544069275706020956539989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63696046183804013971026659 95544069275706020956539989)
                  ·
                    refine ⟨1119657061824679933084453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95544069275706020956539989 1119657061824679933084453)
                    ·
                      rfl

theorem cell23_6541573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_6541573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541573 prefixEnd_6541573 := by exact prefixLift 6541573
  have htrace : WordTrace (prefixWord ++ tailWord_6541573) baseStart_6541573 baseEnd_6541573 := by
    simpa [prefixWord, tailWord_6541573, baseEnd_6541573] using wordTrace_append hprefix tailTrace_6541573
  have hstable : (prefixWord ++ tailWord_6541573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541573).length < 2 ^ (prefixWord ++ tailWord_6541573).sum := by decide
  have hdescent : baseEnd_6541573 < baseStart_6541573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541583 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 5]
def baseStart_6541583 : Nat := 118140960795 + 6541583 * 2 ^ 59
def prefixEnd_6541583 : Nat := 4983230072969 + 3 ^ 40 * 6541583 * 2
def baseEnd_6541583 : Nat := 3358976320280584760128313

theorem tailTrace_6541583 : CollatzResearch.WordTrace tailWord_6541583 prefixEnd_6541583 3358976320280584760128313 := by
  unfold tailWord_6541583
  simp only [CollatzResearch.WordTrace]
  refine ⟨238591133059969479275605403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159060755373312986183736935 238591133059969479275605403)
  ·
    refine ⟨357886699589954218913408105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238591133059969479275605403 357886699589954218913408105)
    ·
      refine ⟨268415024692465664185056079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357886699589954218913408105 268415024692465664185056079)
      ·
        refine ⟨402622537038698496277584119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268415024692465664185056079 402622537038698496277584119)
        ·
          refine ⟨603933805558047744416376179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402622537038698496277584119 603933805558047744416376179)
          ·
            refine ⟨905900708337071616624564269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603933805558047744416376179 905900708337071616624564269)
            ·
              refine ⟨339712765626401856234211601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 905900708337071616624564269 339712765626401856234211601)
              ·
                refine ⟨254784574219801392175658701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339712765626401856234211601 254784574219801392175658701)
                ·
                  refine ⟨95544215332425522065872013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254784574219801392175658701 95544215332425522065872013)
                  ·
                    refine ⟨35829080749659570774702005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95544215332425522065872013 35829080749659570774702005)
                    ·
                      refine ⟨3358976320280584760128313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35829080749659570774702005 3358976320280584760128313)
                      ·
                        rfl

theorem cell23_6541583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_6541583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541583 prefixEnd_6541583 := by exact prefixLift 6541583
  have htrace : WordTrace (prefixWord ++ tailWord_6541583) baseStart_6541583 baseEnd_6541583 := by
    simpa [prefixWord, tailWord_6541583, baseEnd_6541583] using wordTrace_append hprefix tailTrace_6541583
  have hstable : (prefixWord ++ tailWord_6541583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541583).length < 2 ^ (prefixWord ++ tailWord_6541583).sum := by decide
  have hdescent : baseEnd_6541583 < baseStart_6541583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541600 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 5]
def baseStart_6541600 : Nat := 118140960795 + 6541600 * 2 ^ 59
def prefixEnd_6541600 : Nat := 4983230072969 + 3 ^ 40 * 6541600 * 2
def baseEnd_6541600 : Nat := 3358985049451711193615735

theorem tailTrace_6541600 : CollatzResearch.WordTrace tailWord_6541600 prefixEnd_6541600 3358985049451711193615735 := by
  unfold tailWord_6541600
  simp only [CollatzResearch.WordTrace]
  refine ⟨119295876550453945589487127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159061168733938594119316169 119295876550453945589487127)
  ·
    refine ⟨178943814825680918384230691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119295876550453945589487127 178943814825680918384230691)
    ·
      refine ⟨268415722238521377576346037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178943814825680918384230691 268415722238521377576346037)
      ·
        refine ⟨25163973959861379147782441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 268415722238521377576346037 25163973959861379147782441)
        ·
          refine ⟨18872980469896034360836831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25163973959861379147782441 18872980469896034360836831)
          ·
            refine ⟨28309470704844051541255247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18872980469896034360836831 28309470704844051541255247)
            ·
              refine ⟨42464206057266077311882871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28309470704844051541255247 42464206057266077311882871)
              ·
                refine ⟨63696309085899115967824307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42464206057266077311882871 63696309085899115967824307)
                ·
                  refine ⟨95544463628848673951736461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63696309085899115967824307 95544463628848673951736461)
                  ·
                    refine ⟨35829173860818252731901173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95544463628848673951736461 35829173860818252731901173)
                    ·
                      refine ⟨3358985049451711193615735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35829173860818252731901173 3358985049451711193615735)
                      ·
                        rfl

theorem cell23_6541600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_6541600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541600 prefixEnd_6541600 := by exact prefixLift 6541600
  have htrace : WordTrace (prefixWord ++ tailWord_6541600) baseStart_6541600 baseEnd_6541600 := by
    simpa [prefixWord, tailWord_6541600, baseEnd_6541600] using wordTrace_append hprefix tailTrace_6541600
  have hstable : (prefixWord ++ tailWord_6541600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541600).length < 2 ^ (prefixWord ++ tailWord_6541600).sum := by decide
  have hdescent : baseEnd_6541600 < baseStart_6541600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541650 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 1, 7]
def baseStart_6541650 : Nat := 118140960795 + 6541650 * 2 ^ 59
def prefixEnd_6541650 : Nat := 4983230072969 + 3 ^ 40 * 6541650 * 2
def baseEnd_6541650 : Nat := 1119670241161478665996835

theorem tailTrace_6541650 : CollatzResearch.WordTrace tailWord_6541650 prefixEnd_6541650 1119670241161478665996835 := by
  unfold tailWord_6541650
  simp only [CollatzResearch.WordTrace]
  refine ⟨59648394187681687429573601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159062384500484499812196269 59648394187681687429573601)
  ·
    refine ⟨44736295640761265572180201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59648394187681687429573601 44736295640761265572180201)
    ·
      refine ⟨33552221730570949179135151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44736295640761265572180201 33552221730570949179135151)
      ·
        refine ⟨50328332595856423768702727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33552221730570949179135151 50328332595856423768702727)
        ·
          refine ⟨75492498893784635653054091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50328332595856423768702727 75492498893784635653054091)
          ·
            refine ⟨113238748340676953479581137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75492498893784635653054091 113238748340676953479581137)
            ·
              refine ⟨84929061255507715109685853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113238748340676953479581137 84929061255507715109685853)
              ·
                refine ⟨31848397970815393166132195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84929061255507715109685853 31848397970815393166132195)
                ·
                  refine ⟨47772596956223089749198293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31848397970815393166132195 47772596956223089749198293)
                  ·
                    refine ⟨1119670241161478665996835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47772596956223089749198293 1119670241161478665996835)
                    ·
                      rfl

theorem cell23_6541650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_6541650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541650 prefixEnd_6541650 := by exact prefixLift 6541650
  have htrace : WordTrace (prefixWord ++ tailWord_6541650) baseStart_6541650 baseEnd_6541650 := by
    simpa [prefixWord, tailWord_6541650, baseEnd_6541650] using wordTrace_append hprefix tailTrace_6541650
  have hstable : (prefixWord ++ tailWord_6541650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541650).length < 2 ^ (prefixWord ++ tailWord_6541650).sum := by decide
  have hdescent : baseEnd_6541650 < baseStart_6541650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541671 : List Nat := [1, 1, 5, 1, 3, 3, 2, 2, 5]
def baseStart_6541671 : Nat := 118140960795 + 6541671 * 2 ^ 59
def prefixEnd_6541671 : Nat := 4983230072969 + 3 ^ 40 * 6541671 * 2
def baseEnd_6541671 : Nat := 373224611842020046203101

theorem tailTrace_6541671 : CollatzResearch.WordTrace tailWord_6541671 prefixEnd_6541671 373224611842020046203101 := by
  unfold tailWord_6541671
  simp only [CollatzResearch.WordTrace]
  refine ⟨238594342683650670304808867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159062895122433780203205911 238594342683650670304808867)
  ·
    refine ⟨357891514025476005457213301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238594342683650670304808867 357891514025476005457213301)
    ·
      refine ⟨33552329439888375511613747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 357891514025476005457213301 33552329439888375511613747)
      ·
        refine ⟨50328494159832563267420621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33552329439888375511613747 50328494159832563267420621)
        ·
          refine ⟨18873185309937211225282733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50328494159832563267420621 18873185309937211225282733)
          ·
            refine ⟨7077444491226454209481025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18873185309937211225282733 7077444491226454209481025)
            ·
              refine ⟨5308083368419840657110769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7077444491226454209481025 5308083368419840657110769)
              ·
                refine ⟨3981062526314880492833077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5308083368419840657110769 3981062526314880492833077)
                ·
                  refine ⟨373224611842020046203101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3981062526314880492833077 373224611842020046203101)
                  ·
                    rfl

theorem cell23_6541671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 5].length) (baseStart_6541671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541671 prefixEnd_6541671 := by exact prefixLift 6541671
  have htrace : WordTrace (prefixWord ++ tailWord_6541671) baseStart_6541671 baseEnd_6541671 := by
    simpa [prefixWord, tailWord_6541671, baseEnd_6541671] using wordTrace_append hprefix tailTrace_6541671
  have hstable : (prefixWord ++ tailWord_6541671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541671).length < 2 ^ (prefixWord ++ tailWord_6541671).sum := by decide
  have hdescent : baseEnd_6541671 < baseStart_6541671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541674 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 2, 5, 2]
def baseStart_6541674 : Nat := 118140960795 + 6541674 * 2 ^ 59
def prefixEnd_6541674 : Nat := 4983230072969 + 3 ^ 40 * 6541674 * 2
def baseEnd_6541674 : Nat := 3359023047020143904090395

theorem tailTrace_6541674 : CollatzResearch.WordTrace tailWord_6541674 prefixEnd_6541674 3359023047020143904090395 := by
  unfold tailWord_6541674
  simp only [CollatzResearch.WordTrace]
  refine ⟨59648613025659950454292019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159062968068426534544778717 59648613025659950454292019)
  ·
    refine ⟨89472919538489925681438029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59648613025659950454292019 89472919538489925681438029)
    ·
      refine ⟨33552344826933722130539261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89472919538489925681438029 33552344826933722130539261)
      ·
        refine ⟨12582129310100145798952223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33552344826933722130539261 12582129310100145798952223)
        ·
          refine ⟨18873193965150218698428335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12582129310100145798952223 18873193965150218698428335)
          ·
            refine ⟨28309790947725328047642503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18873193965150218698428335 28309790947725328047642503)
            ·
              refine ⟨42464686421587992071463755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28309790947725328047642503 42464686421587992071463755)
              ·
                refine ⟨63697029632381988107195633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42464686421587992071463755 63697029632381988107195633)
                ·
                  refine ⟨47772772224286491080396725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63697029632381988107195633 47772772224286491080396725)
                  ·
                    refine ⟨4478697396026858538787193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47772772224286491080396725 4478697396026858538787193)
                    ·
                      refine ⟨3359023047020143904090395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4478697396026858538787193 3359023047020143904090395)
                      ·
                        rfl

theorem cell23_6541674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_6541674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541674 prefixEnd_6541674 := by exact prefixLift 6541674
  have htrace : WordTrace (prefixWord ++ tailWord_6541674) baseStart_6541674 baseEnd_6541674 := by
    simpa [prefixWord, tailWord_6541674, baseEnd_6541674] using wordTrace_append hprefix tailTrace_6541674
  have hstable : (prefixWord ++ tailWord_6541674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541674).length < 2 ^ (prefixWord ++ tailWord_6541674).sum := by decide
  have hdescent : baseEnd_6541674 < baseStart_6541674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541707 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 3]
def baseStart_6541707 : Nat := 118140960795 + 6541707 * 2 ^ 59
def prefixEnd_6541707 : Nat := 4983230072969 + 3 ^ 40 * 6541707 * 2
def baseEnd_6541707 : Nat := 3359039991881742274977743

theorem tailTrace_6541707 : CollatzResearch.WordTrace tailWord_6541707 prefixEnd_6541707 3359039991881742274977743 := by
  unfold tailWord_6541707
  simp only [CollatzResearch.WordTrace]
  refine ⟨238595655711520248453119375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159063770474346832302079583 238595655711520248453119375)
  ·
    refine ⟨357893483567280372679679063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238595655711520248453119375 357893483567280372679679063)
    ·
      refine ⟨536840225350920559019518595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357893483567280372679679063 536840225350920559019518595)
      ·
        refine ⟨805260338026380838529277893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536840225350920559019518595 805260338026380838529277893)
        ·
          refine ⟨150986313379946407224239605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 805260338026380838529277893 150986313379946407224239605)
          ·
            refine ⟨14154966879369975677272463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150986313379946407224239605 14154966879369975677272463)
            ·
              refine ⟨21232450319054963515908695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14154966879369975677272463 21232450319054963515908695)
              ·
                refine ⟨31848675478582445273863043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21232450319054963515908695 31848675478582445273863043)
                ·
                  refine ⟨47773013217873667910794565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31848675478582445273863043 47773013217873667910794565)
                  ·
                    refine ⟨8957439978351312733273981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47773013217873667910794565 8957439978351312733273981)
                    ·
                      refine ⟨3359039991881742274977743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8957439978351312733273981 3359039991881742274977743)
                      ·
                        rfl

theorem cell23_6541707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 3].length) (baseStart_6541707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541707 prefixEnd_6541707 := by exact prefixLift 6541707
  have htrace : WordTrace (prefixWord ++ tailWord_6541707) baseStart_6541707 baseEnd_6541707 := by
    simpa [prefixWord, tailWord_6541707, baseEnd_6541707] using wordTrace_append hprefix tailTrace_6541707
  have hstable : (prefixWord ++ tailWord_6541707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541707).length < 2 ^ (prefixWord ++ tailWord_6541707).sum := by decide
  have hdescent : baseEnd_6541707 < baseStart_6541707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541781 : List Nat := [1, 3, 2, 3, 1, 3, 1, 2, 2, 3, 2]
def baseStart_6541781 : Nat := 118140960795 + 6541781 * 2 ^ 59
def prefixEnd_6541781 : Nat := 4983230072969 + 3 ^ 40 * 6541781 * 2
def baseEnd_6541781 : Nat := 3359077989450174985452403

theorem tailTrace_6541781 : CollatzResearch.WordTrace tailWord_6541781 prefixEnd_6541781 3359077989450174985452403 := by
  unfold tailWord_6541781
  simp only [CollatzResearch.WordTrace]
  refine ⟨238598354713252159091313197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159065569808834772727542131 238598354713252159091313197)
  ·
    refine ⟨89474383017469559659242449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238598354713252159091313197 89474383017469559659242449)
    ·
      refine ⟨67105787263102169744431837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89474383017469559659242449 67105787263102169744431837)
      ·
        refine ⟨25164670223663313654161939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67105787263102169744431837 25164670223663313654161939)
        ·
          refine ⟨37747005335494970481242909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25164670223663313654161939 37747005335494970481242909)
          ·
            refine ⟨14155127000810613930466091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37747005335494970481242909 14155127000810613930466091)
            ·
              refine ⟨21232690501215920895699137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14155127000810613930466091 21232690501215920895699137)
              ·
                refine ⟨15924517875911940671774353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21232690501215920895699137 15924517875911940671774353)
                ·
                  refine ⟨11943388406933955503830765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15924517875911940671774353 11943388406933955503830765)
                  ·
                    refine ⟨4478770652600233313936537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11943388406933955503830765 4478770652600233313936537)
                    ·
                      refine ⟨3359077989450174985452403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4478770652600233313936537 3359077989450174985452403)
                      ·
                        rfl

theorem cell23_6541781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_6541781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541781 prefixEnd_6541781 := by exact prefixLift 6541781
  have htrace : WordTrace (prefixWord ++ tailWord_6541781) baseStart_6541781 baseEnd_6541781 := by
    simpa [prefixWord, tailWord_6541781, baseEnd_6541781] using wordTrace_append hprefix tailTrace_6541781
  have hstable : (prefixWord ++ tailWord_6541781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541781).length < 2 ^ (prefixWord ++ tailWord_6541781).sum := by decide
  have hdescent : baseEnd_6541781 < baseStart_6541781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541804 : List Nat := [2, 2, 1, 1, 2, 1, 5, 3, 2, 4]
def baseStart_6541804 : Nat := 118140960795 + 6541804 * 2 ^ 59
def prefixEnd_6541804 : Nat := 4983230072969 + 3 ^ 40 * 6541804 * 2
def baseEnd_6541804 : Nat := 1119696599835076131821599

theorem tailTrace_6541804 : CollatzResearch.WordTrace tailWord_6541804 prefixEnd_6541804 1119696599835076131821599 := by
  unfold tailWord_6541804
  simp only [CollatzResearch.WordTrace]
  refine ⟨119299596796084417009700233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159066129061445889346266977 119299596796084417009700233)
  ·
    refine ⟨89474697597063312757275175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119299596796084417009700233 89474697597063312757275175)
    ·
      refine ⟨134212046395594969135912763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89474697597063312757275175 134212046395594969135912763)
      ·
        refine ⟨201318069593392453703869145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134212046395594969135912763 201318069593392453703869145)
        ·
          refine ⟨150988552195044340277901859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201318069593392453703869145 150988552195044340277901859)
          ·
            refine ⟨226482828292566510416852789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150988552195044340277901859 226482828292566510416852789)
            ·
              refine ⟨21232765152428110351579949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 226482828292566510416852789 21232765152428110351579949)
              ·
                refine ⟨7962286932160541381842481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21232765152428110351579949 7962286932160541381842481)
                ·
                  refine ⟨5971715199120406036381861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7962286932160541381842481 5971715199120406036381861)
                  ·
                    refine ⟨1119696599835076131821599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5971715199120406036381861 1119696599835076131821599)
                    ·
                      rfl

theorem cell23_6541804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 4].length) (baseStart_6541804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541804 prefixEnd_6541804 := by exact prefixLift 6541804
  have htrace : WordTrace (prefixWord ++ tailWord_6541804) baseStart_6541804 baseEnd_6541804 := by
    simpa [prefixWord, tailWord_6541804, baseEnd_6541804] using wordTrace_append hprefix tailTrace_6541804
  have hstable : (prefixWord ++ tailWord_6541804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541804).length < 2 ^ (prefixWord ++ tailWord_6541804).sum := by decide
  have hdescent : baseEnd_6541804 < baseStart_6541804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541807 : List Nat := [1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 4]
def baseStart_6541807 : Nat := 118140960795 + 6541807 * 2 ^ 59
def prefixEnd_6541807 : Nat := 4983230072969 + 3 ^ 40 * 6541807 * 2
def baseEnd_6541807 : Nat := 3359091339947191883727283

theorem tailTrace_6541807 : CollatzResearch.WordTrace tailWord_6541807 prefixEnd_6541807 3359091339947191883727283 := by
  unfold tailWord_6541807
  simp only [CollatzResearch.WordTrace]
  refine ⟨238599303011157965531759675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159066202007438643687839783 238599303011157965531759675)
  ·
    refine ⟨357898954516736948297639513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238599303011157965531759675 357898954516736948297639513)
    ·
      refine ⟨268424215887552711223229635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357898954516736948297639513 268424215887552711223229635)
      ·
        refine ⟨402636323831329066834844453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268424215887552711223229635 402636323831329066834844453)
        ·
          refine ⟨75494310718374200031533335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 402636323831329066834844453 75494310718374200031533335)
          ·
            refine ⟨113241466077561300047300003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75494310718374200031533335 113241466077561300047300003)
            ·
              refine ⟨169862199116341950070950005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113241466077561300047300003 169862199116341950070950005)
              ·
                refine ⟨15924581167157057819151563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169862199116341950070950005 15924581167157057819151563)
                ·
                  refine ⟨23886871750735586728727345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15924581167157057819151563 23886871750735586728727345)
                  ·
                    refine ⟨17915153813051690046545509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23886871750735586728727345 17915153813051690046545509)
                    ·
                      refine ⟨3359091339947191883727283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17915153813051690046545509 3359091339947191883727283)
                      ·
                        rfl

theorem cell23_6541807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 4].length) (baseStart_6541807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541807 prefixEnd_6541807 := by exact prefixLift 6541807
  have htrace : WordTrace (prefixWord ++ tailWord_6541807) baseStart_6541807 baseEnd_6541807 := by
    simpa [prefixWord, tailWord_6541807, baseEnd_6541807] using wordTrace_append hprefix tailTrace_6541807
  have hstable : (prefixWord ++ tailWord_6541807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541807).length < 2 ^ (prefixWord ++ tailWord_6541807).sum := by decide
  have hdescent : baseEnd_6541807 < baseStart_6541807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541828 : List Nat := [2, 3, 2, 3, 1, 2, 3, 1, 1, 1, 4]
def baseStart_6541828 : Nat := 118140960795 + 6541828 * 2 ^ 59
def prefixEnd_6541828 : Nat := 4983230072969 + 3 ^ 40 * 6541828 * 2
def baseEnd_6541828 : Nat := 3359102123040936301564687

theorem tailTrace_6541828 : CollatzResearch.WordTrace tailWord_6541828 prefixEnd_6541828 3359102123040936301564687 := by
  unfold tailWord_6541828
  simp only [CollatzResearch.WordTrace]
  refine ⟨119300034472040943059137069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159066712629387924078849425 119300034472040943059137069)
  ·
    refine ⟨44737512927015353647176401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119300034472040943059137069 44737512927015353647176401)
    ·
      refine ⟨33553134695261515235382301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44737512927015353647176401 33553134695261515235382301)
      ·
        refine ⟨12582425510723068213268363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33553134695261515235382301 12582425510723068213268363)
        ·
          refine ⟨18873638266084602319902545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12582425510723068213268363 18873638266084602319902545)
          ·
            refine ⟨14155228699563451739926909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18873638266084602319902545 14155228699563451739926909)
            ·
              refine ⟨5308210762336294402472591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14155228699563451739926909 5308210762336294402472591)
              ·
                refine ⟨7962316143504441603708887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5308210762336294402472591 7962316143504441603708887)
                ·
                  refine ⟨11943474215256662405563331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7962316143504441603708887 11943474215256662405563331)
                  ·
                    refine ⟨17915211322884993608344997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11943474215256662405563331 17915211322884993608344997)
                    ·
                      refine ⟨3359102123040936301564687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17915211322884993608344997 3359102123040936301564687)
                      ·
                        rfl

theorem cell23_6541828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_6541828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541828 prefixEnd_6541828 := by exact prefixLift 6541828
  have htrace : WordTrace (prefixWord ++ tailWord_6541828) baseStart_6541828 baseEnd_6541828 := by
    simpa [prefixWord, tailWord_6541828, baseEnd_6541828] using wordTrace_append hprefix tailTrace_6541828
  have hstable : (prefixWord ++ tailWord_6541828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541828).length < 2 ^ (prefixWord ++ tailWord_6541828).sum := by decide
  have hdescent : baseEnd_6541828 < baseStart_6541828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541831 : List Nat := [1, 1, 4, 3, 3, 2, 1, 1, 1, 1, 5]
def baseStart_6541831 : Nat := 118140960795 + 6541831 * 2 ^ 59
def prefixEnd_6541831 : Nat := 4983230072969 + 3 ^ 40 * 6541831 * 2
def baseEnd_6541831 : Nat := 3359103663482899789827173

theorem tailTrace_6541831 : CollatzResearch.WordTrace tailWord_6541831 prefixEnd_6541831 3359103663482899789827173 := by
  unfold tailWord_6541831
  simp only [CollatzResearch.WordTrace]
  refine ⟨238600178363071017630633347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159066785575380678420422231 238600178363071017630633347)
  ·
    refine ⟨357900267544606526445950021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238600178363071017630633347 357900267544606526445950021)
    ·
      refine ⟨67106300164613723708615629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 357900267544606526445950021 67106300164613723708615629)
      ·
        refine ⟨25164862561730146390730861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67106300164613723708615629 25164862561730146390730861)
        ·
          refine ⟨9436823460648804896524073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25164862561730146390730861 9436823460648804896524073)
          ·
            refine ⟨7077617595486603672393055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9436823460648804896524073 7077617595486603672393055)
            ·
              refine ⟨10616426393229905508589583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7077617595486603672393055 10616426393229905508589583)
              ·
                refine ⟨15924639589844858262884375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10616426393229905508589583 15924639589844858262884375)
                ·
                  refine ⟨23886959384767287394326563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15924639589844858262884375 23886959384767287394326563)
                  ·
                    refine ⟨35830439077150931091489845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23886959384767287394326563 35830439077150931091489845)
                    ·
                      refine ⟨3359103663482899789827173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35830439077150931091489845 3359103663482899789827173)
                      ·
                        rfl

theorem cell23_6541831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_6541831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541831 prefixEnd_6541831 := by exact prefixLift 6541831
  have htrace : WordTrace (prefixWord ++ tailWord_6541831) baseStart_6541831 baseEnd_6541831 := by
    simpa [prefixWord, tailWord_6541831, baseEnd_6541831] using wordTrace_append hprefix tailTrace_6541831
  have hstable : (prefixWord ++ tailWord_6541831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541831).length < 2 ^ (prefixWord ++ tailWord_6541831).sum := by decide
  have hdescent : baseEnd_6541831 < baseStart_6541831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541861 : List Nat := [1, 3, 1, 2, 2, 1, 4, 3, 2, 1, 3]
def baseStart_6541861 : Nat := 118140960795 + 6541861 * 2 ^ 59
def prefixEnd_6541861 : Nat := 4983230072969 + 3 ^ 40 * 6541861 * 2
def baseEnd_6541861 : Nat := 3359119067902534672452035

theorem tailTrace_6541861 : CollatzResearch.WordTrace tailWord_6541861 prefixEnd_6541861 3359119067902534672452035 := by
  unfold tailWord_6541861
  simp only [CollatzResearch.WordTrace]
  refine ⟨238601272552962332754225437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159067515035308221836150291 238601272552962332754225437)
  ·
    refine ⟨89475477207360874782834539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238601272552962332754225437 89475477207360874782834539)
    ·
      refine ⟨134213215811041312174251809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89475477207360874782834539 134213215811041312174251809)
      ·
        refine ⟨100659911858280984130688857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134213215811041312174251809 100659911858280984130688857)
        ·
          refine ⟨75494933893710738098016643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100659911858280984130688857 75494933893710738098016643)
          ·
            refine ⟨113242400840566107147024965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75494933893710738098016643 113242400840566107147024965)
            ·
              refine ⟨21232950157606145090067181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113242400840566107147024965 21232950157606145090067181)
              ·
                refine ⟨7962356309102304408775193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21232950157606145090067181 7962356309102304408775193)
                ·
                  refine ⟨5971767231826728306581395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7962356309102304408775193 5971767231826728306581395)
                  ·
                    refine ⟨8957650847740092459872093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5971767231826728306581395 8957650847740092459872093)
                    ·
                      refine ⟨3359119067902534672452035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8957650847740092459872093 3359119067902534672452035)
                      ·
                        rfl

theorem cell23_6541861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_6541861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541861 prefixEnd_6541861 := by exact prefixLift 6541861
  have htrace : WordTrace (prefixWord ++ tailWord_6541861) baseStart_6541861 baseEnd_6541861 := by
    simpa [prefixWord, tailWord_6541861, baseEnd_6541861] using wordTrace_append hprefix tailTrace_6541861
  have hstable : (prefixWord ++ tailWord_6541861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541861).length < 2 ^ (prefixWord ++ tailWord_6541861).sum := by decide
  have hdescent : baseEnd_6541861 < baseStart_6541861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541877 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 1, 8]
def baseStart_6541877 : Nat := 118140960795 + 6541877 * 2 ^ 59
def prefixEnd_6541877 : Nat := 4983230072969 + 3 ^ 40 * 6541877 * 2
def baseEnd_6541877 : Nat := 1119709094531002203283987

theorem tailTrace_6541877 : CollatzResearch.WordTrace tailWord_6541877 prefixEnd_6541877 1119709094531002203283987 := by
  unfold tailWord_6541877
  simp only [CollatzResearch.WordTrace]
  refine ⟨238601856120904367486807885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159067904080602911657871923 238601856120904367486807885)
  ·
    refine ⟨89475696045339137807552957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238601856120904367486807885 89475696045339137807552957)
    ·
      refine ⟨33553386017002176677832359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89475696045339137807552957 33553386017002176677832359)
      ·
        refine ⟨50330079025503265016748539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33553386017002176677832359 50330079025503265016748539)
        ·
          refine ⟨75495118538254897525122809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50330079025503265016748539 75495118538254897525122809)
          ·
            refine ⟨56621338903691173143842107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75495118538254897525122809 56621338903691173143842107)
            ·
              refine ⟨84932008355536759715763161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56621338903691173143842107 84932008355536759715763161)
              ·
                refine ⟨63699006266652569786822371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84932008355536759715763161 63699006266652569786822371)
                ·
                  refine ⟨95548509399978854680233557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63699006266652569786822371 95548509399978854680233557)
                  ·
                    refine ⟨1119709094531002203283987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95548509399978854680233557 1119709094531002203283987)
                    ·
                      rfl

theorem cell23_6541877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_6541877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541877 prefixEnd_6541877 := by exact prefixLift 6541877
  have htrace : WordTrace (prefixWord ++ tailWord_6541877) baseStart_6541877 baseEnd_6541877 := by
    simpa [prefixWord, tailWord_6541877, baseEnd_6541877] using wordTrace_append hprefix tailTrace_6541877
  have hstable : (prefixWord ++ tailWord_6541877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541877).length < 2 ^ (prefixWord ++ tailWord_6541877).sum := by decide
  have hdescent : baseEnd_6541877 < baseStart_6541877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541887 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 5]
def baseStart_6541887 : Nat := 118140960795 + 6541887 * 2 ^ 59
def prefixEnd_6541887 : Nat := 4983230072969 + 3 ^ 40 * 6541887 * 2
def baseEnd_6541887 : Nat := 3359132418399551570726915

theorem tailTrace_6541887 : CollatzResearch.WordTrace tailWord_6541887 prefixEnd_6541887 3359132418399551570726915 := by
  unfold tailWord_6541887
  simp only [CollatzResearch.WordTrace]
  refine ⟨238602220850868139194671915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159068147233912092796447943 238602220850868139194671915)
  ·
    refine ⟨357903331276302208792007873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238602220850868139194671915 357903331276302208792007873)
    ·
      refine ⟨268427498457226656594005905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357903331276302208792007873 268427498457226656594005905)
      ·
        refine ⟨201320623842919992445504429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268427498457226656594005905 201320623842919992445504429)
        ·
          refine ⟨75495233941094997167064161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201320623842919992445504429 75495233941094997167064161)
          ·
            refine ⟨56621425455821247875298121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75495233941094997167064161 56621425455821247875298121)
            ·
              refine ⟨42466069091865935906473591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56621425455821247875298121 42466069091865935906473591)
              ·
                refine ⟨63699103637798903859710387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42466069091865935906473591 63699103637798903859710387)
                ·
                  refine ⟨95548655456698355789565581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63699103637798903859710387 95548655456698355789565581)
                  ·
                    refine ⟨35830745796261883421087093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95548655456698355789565581 35830745796261883421087093)
                    ·
                      refine ⟨3359132418399551570726915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35830745796261883421087093 3359132418399551570726915)
                      ·
                        rfl

theorem cell23_6541887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_6541887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541887 prefixEnd_6541887 := by exact prefixLift 6541887
  have htrace : WordTrace (prefixWord ++ tailWord_6541887) baseStart_6541887 baseEnd_6541887 := by
    simpa [prefixWord, tailWord_6541887, baseEnd_6541887] using wordTrace_append hprefix tailTrace_6541887
  have hstable : (prefixWord ++ tailWord_6541887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541887).length < 2 ^ (prefixWord ++ tailWord_6541887).sum := by decide
  have hdescent : baseEnd_6541887 < baseStart_6541887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541888 : List Nat := [2, 1, 1, 2, 2, 2, 6, 1, 1, 3, 2]
def baseStart_6541888 : Nat := 118140960795 + 6541888 * 2 ^ 59
def prefixEnd_6541888 : Nat := 4983230072969 + 3 ^ 40 * 6541888 * 2
def baseEnd_6541888 : Nat := 3359132931880206066814411

theorem tailTrace_6541888 : CollatzResearch.WordTrace tailWord_6541888 prefixEnd_6541888 3359132931880206066814411 := by
  unfold tailWord_6541888
  simp only [CollatzResearch.WordTrace]
  refine ⟨119301128661932258182729159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159068171549243010910305545 119301128661932258182729159)
  ·
    refine ⟨178951692992898387274093739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119301128661932258182729159 178951692992898387274093739)
    ·
      refine ⟨268427539489347580911140609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178951692992898387274093739 268427539489347580911140609)
      ·
        refine ⟨201320654617010685683355457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268427539489347580911140609 201320654617010685683355457)
        ·
          refine ⟨150990490962758014262516593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201320654617010685683355457 150990490962758014262516593)
          ·
            refine ⟨113242868222068510696887445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150990490962758014262516593 113242868222068510696887445)
            ·
              refine ⟨5308259447909461438916599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113242868222068510696887445 5308259447909461438916599)
              ·
                refine ⟨7962389171864192158374899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5308259447909461438916599 7962389171864192158374899)
                ·
                  refine ⟨11943583757796288237562349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7962389171864192158374899 11943583757796288237562349)
                  ·
                    refine ⟨4478843909173608089085881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11943583757796288237562349 4478843909173608089085881)
                    ·
                      refine ⟨3359132931880206066814411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4478843909173608089085881 3359132931880206066814411)
                      ·
                        rfl

theorem cell23_6541888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 1, 3, 2].length) (baseStart_6541888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541888 prefixEnd_6541888 := by exact prefixLift 6541888
  have htrace : WordTrace (prefixWord ++ tailWord_6541888) baseStart_6541888 baseEnd_6541888 := by
    simpa [prefixWord, tailWord_6541888, baseEnd_6541888] using wordTrace_append hprefix tailTrace_6541888
  have hstable : (prefixWord ++ tailWord_6541888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541888).length < 2 ^ (prefixWord ++ tailWord_6541888).sum := by decide
  have hdescent : baseEnd_6541888 < baseStart_6541888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6541922 : List Nat := [3, 3, 2, 3, 1, 1, 2, 2, 1, 3, 2]
def baseStart_6541922 : Nat := 118140960795 + 6541922 * 2 ^ 59
def prefixEnd_6541922 : Nat := 4983230072969 + 3 ^ 40 * 6541922 * 2
def baseEnd_6541922 : Nat := 3359150390222458933789255

theorem tailTrace_6541922 : CollatzResearch.WordTrace tailWord_6541922 prefixEnd_6541922 3359150390222458933789255 := by
  unfold tailWord_6541922
  simp only [CollatzResearch.WordTrace]
  refine ⟨59650874351435335043049005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159068998270494226781464013 59650874351435335043049005)
  ·
    refine ⟨22369077881788250641143377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59650874351435335043049005 22369077881788250641143377)
    ·
      refine ⟨16776808411341187980857533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22369077881788250641143377 16776808411341187980857533)
      ·
        refine ⟨6291303154252945492821575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16776808411341187980857533 6291303154252945492821575)
        ·
          refine ⟨9436954731379418239232363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6291303154252945492821575 9436954731379418239232363)
          ·
            refine ⟨14155432097069127358848545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9436954731379418239232363 14155432097069127358848545)
            ·
              refine ⟨10616574072801845519136409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14155432097069127358848545 10616574072801845519136409)
              ·
                refine ⟨7962430554601384139352307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10616574072801845519136409 7962430554601384139352307)
                ·
                  refine ⟨11943645831902076209028461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7962430554601384139352307 11943645831902076209028461)
                  ·
                    refine ⟨4478867186963278578385673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11943645831902076209028461 4478867186963278578385673)
                    ·
                      refine ⟨3359150390222458933789255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4478867186963278578385673 3359150390222458933789255)
                      ·
                        rfl

theorem cell23_6541922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_6541922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6541922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6541922 prefixEnd_6541922 := by exact prefixLift 6541922
  have htrace : WordTrace (prefixWord ++ tailWord_6541922) baseStart_6541922 baseEnd_6541922 := by
    simpa [prefixWord, tailWord_6541922, baseEnd_6541922] using wordTrace_append hprefix tailTrace_6541922
  have hstable : (prefixWord ++ tailWord_6541922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6541922).length < 2 ^ (prefixWord ++ tailWord_6541922).sum := by decide
  have hdescent : baseEnd_6541922 < baseStart_6541922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6541922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542074 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 3, 6]
def baseStart_6542074 : Nat := 118140960795 + 6542074 * 2 ^ 59
def prefixEnd_6542074 : Nat := 4983230072969 + 3 ^ 40 * 6542074 * 2
def baseEnd_6542074 : Nat := 1119742813093980779696185

theorem tailTrace_6542074 : CollatzResearch.WordTrace tailWord_6542074 prefixEnd_6542074 1119742813093980779696185 := by
  unfold tailWord_6542074
  simp only [CollatzResearch.WordTrace]
  refine ⟨59652260325297667532932319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159072694200793780087819517 59652260325297667532932319)
  ·
    refine ⟨89478390487946501299398479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59652260325297667532932319 89478390487946501299398479)
    ·
      refine ⟨134217585731919751949097719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89478390487946501299398479 134217585731919751949097719)
      ·
        refine ⟨201326378597879627923646579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134217585731919751949097719 201326378597879627923646579)
        ·
          refine ⟨301989567896819441885469869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201326378597879627923646579 301989567896819441885469869)
          ·
            refine ⟨113246087961307290707051201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301989567896819441885469869 113246087961307290707051201)
            ·
              refine ⟨84934565970980468030288401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113246087961307290707051201 84934565970980468030288401)
              ·
                refine ⟨63700924478235351022716301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84934565970980468030288401 63700924478235351022716301)
                ·
                  refine ⟨23887846679338256633518613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63700924478235351022716301 23887846679338256633518613)
                  ·
                    refine ⟨1119742813093980779696185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23887846679338256633518613 1119742813093980779696185)
                    ·
                      rfl

theorem cell23_6542074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_6542074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542074 prefixEnd_6542074 := by exact prefixLift 6542074
  have htrace : WordTrace (prefixWord ++ tailWord_6542074) baseStart_6542074 baseEnd_6542074 := by
    simpa [prefixWord, tailWord_6542074, baseEnd_6542074] using wordTrace_append hprefix tailTrace_6542074
  have hstable : (prefixWord ++ tailWord_6542074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542074).length < 2 ^ (prefixWord ++ tailWord_6542074).sum := by decide
  have hdescent : baseEnd_6542074 < baseStart_6542074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542188 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 3, 4, 2]
def baseStart_6542188 : Nat := 118140960795 + 6542188 * 2 ^ 59
def prefixEnd_6542188 : Nat := 4983230072969 + 3 ^ 40 * 6542188 * 2
def baseEnd_6542188 : Nat := 3359286976076554893063031

theorem tailTrace_6542188 : CollatzResearch.WordTrace tailWord_6542188 prefixEnd_6542188 3359286976076554893063031 := by
  unfold tailWord_6542188
  simp only [CollatzResearch.WordTrace]
  refine ⟨119306599611388833800689609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159075466148518445067586145 119306599611388833800689609)
  ·
    refine ⟨89479949708541625350517207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119306599611388833800689609 89479949708541625350517207)
    ·
      refine ⟨134219924562812438025775811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89479949708541625350517207 134219924562812438025775811)
      ·
        refine ⟨201329886844218657038663717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134219924562812438025775811 201329886844218657038663717)
        ·
          refine ⟨37749353783290998194749447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201329886844218657038663717 37749353783290998194749447)
          ·
            refine ⟨56624030674936497292124171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37749353783290998194749447 56624030674936497292124171)
            ·
              refine ⟨84936046012404745938186257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56624030674936497292124171 84936046012404745938186257)
              ·
                refine ⟨63702034509303559453639693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84936046012404745938186257 63702034509303559453639693)
                ·
                  refine ⟨23888262940988834795114885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63702034509303559453639693 23888262940988834795114885)
                  ·
                    refine ⟨4479049301435406524084041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23888262940988834795114885 4479049301435406524084041)
                    ·
                      refine ⟨3359286976076554893063031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4479049301435406524084041 3359286976076554893063031)
                      ·
                        rfl

theorem cell23_6542188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 4, 2].length) (baseStart_6542188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542188 prefixEnd_6542188 := by exact prefixLift 6542188
  have htrace : WordTrace (prefixWord ++ tailWord_6542188) baseStart_6542188 baseEnd_6542188 := by
    simpa [prefixWord, tailWord_6542188, baseEnd_6542188] using wordTrace_append hprefix tailTrace_6542188
  have hstable : (prefixWord ++ tailWord_6542188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542188).length < 2 ^ (prefixWord ++ tailWord_6542188).sum := by decide
  have hdescent : baseEnd_6542188 < baseStart_6542188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542198 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_6542198 : Nat := 118140960795 + 6542198 * 2 ^ 59
def prefixEnd_6542198 : Nat := 4983230072969 + 3 ^ 40 * 6542198 * 2
def baseEnd_6542198 : Nat := 1119764036961033284645995

theorem tailTrace_6542198 : CollatzResearch.WordTrace tailWord_6542198 prefixEnd_6542198 1119764036961033284645995 := by
  unfold tailWord_6542198
  simp only [CollatzResearch.WordTrace]
  refine ⟨14913347747046339956827703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159075709301827626206162165 14913347747046339956827703)
  ·
    refine ⟨22370021620569509935241555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14913347747046339956827703 22370021620569509935241555)
    ·
      refine ⟨33555032430854264902862333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22370021620569509935241555 33555032430854264902862333)
      ·
        refine ⟨12583137161570349338573375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33555032430854264902862333 12583137161570349338573375)
        ·
          refine ⟨18874705742355524007860063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12583137161570349338573375 18874705742355524007860063)
          ·
            refine ⟨28312058613533286011790095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18874705742355524007860063 28312058613533286011790095)
            ·
              refine ⟨42468087920299929017685143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28312058613533286011790095 42468087920299929017685143)
              ·
                refine ⟨63702131880449893526527715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42468087920299929017685143 63702131880449893526527715)
                ·
                  refine ⟨95553197820674840289791573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63702131880449893526527715 95553197820674840289791573)
                  ·
                    refine ⟨1119764036961033284645995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95553197820674840289791573 1119764036961033284645995)
                    ·
                      rfl

theorem cell23_6542198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_6542198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542198 prefixEnd_6542198 := by exact prefixLift 6542198
  have htrace : WordTrace (prefixWord ++ tailWord_6542198) baseStart_6542198 baseEnd_6542198 := by
    simpa [prefixWord, tailWord_6542198, baseEnd_6542198] using wordTrace_append hprefix tailTrace_6542198
  have hstable : (prefixWord ++ tailWord_6542198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542198).length < 2 ^ (prefixWord ++ tailWord_6542198).sum := by decide
  have hdescent : baseEnd_6542198 < baseStart_6542198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542201 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 1, 4, 4]
def baseStart_6542201 : Nat := 118140960795 + 6542201 * 2 ^ 59
def prefixEnd_6542201 : Nat := 4983230072969 + 3 ^ 40 * 6542201 * 2
def baseEnd_6542201 : Nat := 3359293651325063342200471

theorem tailTrace_6542201 : CollatzResearch.WordTrace tailWord_6542201 prefixEnd_6542201 3359293651325063342200471 := by
  unfold tailWord_6542201
  simp only [CollatzResearch.WordTrace]
  refine ⟨238613673371730570821602457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159075782247820380547734971 238613673371730570821602457)
  ·
    refine ⟨178960255028797928116201843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238613673371730570821602457 178960255028797928116201843)
    ·
      refine ⟨268440382543196892174302765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178960255028797928116201843 268440382543196892174302765)
      ·
        refine ⟨100665143453698834565363537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268440382543196892174302765 100665143453698834565363537)
        ·
          refine ⟨75498857590274125924022653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100665143453698834565363537 75498857590274125924022653)
          ·
            refine ⟨28312071596352797221508495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75498857590274125924022653 28312071596352797221508495)
            ·
              refine ⟨42468107394529195832262743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28312071596352797221508495 42468107394529195832262743)
              ·
                refine ⟨63702161091793793748394115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42468107394529195832262743 63702161091793793748394115)
                ·
                  refine ⟨95553241637690690622591173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63702161091793793748394115 95553241637690690622591173)
                  ·
                    refine ⟨17916232807067004491735845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95553241637690690622591173 17916232807067004491735845)
                    ·
                      refine ⟨3359293651325063342200471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17916232807067004491735845 3359293651325063342200471)
                      ·
                        rfl

theorem cell23_6542201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_6542201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542201 prefixEnd_6542201 := by exact prefixLift 6542201
  have htrace : WordTrace (prefixWord ++ tailWord_6542201) baseStart_6542201 baseEnd_6542201 := by
    simpa [prefixWord, tailWord_6542201, baseEnd_6542201] using wordTrace_append hprefix tailTrace_6542201
  have hstable : (prefixWord ++ tailWord_6542201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542201).length < 2 ^ (prefixWord ++ tailWord_6542201).sum := by decide
  have hdescent : baseEnd_6542201 < baseStart_6542201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542211 : List Nat := [1, 1, 1, 3, 4, 1, 3, 2, 7]
def baseStart_6542211 : Nat := 118140960795 + 6542211 * 2 ^ 59
def prefixEnd_6542211 : Nat := 4983230072969 + 3 ^ 40 * 6542211 * 2
def baseEnd_6542211 : Nat := 373255420681289811452825

theorem tailTrace_6542211 : CollatzResearch.WordTrace tailWord_6542211 prefixEnd_6542211 373255420681289811452825 := by
  unfold tailWord_6542211
  simp only [CollatzResearch.WordTrace]
  refine ⟨238614038101694342529466487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159076025401129561686310991 238614038101694342529466487)
  ·
    refine ⟨357921057152541513794199731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238614038101694342529466487 357921057152541513794199731)
    ·
      refine ⟨536881585728812270691299597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357921057152541513794199731 536881585728812270691299597)
      ·
        refine ⟨201330594648304601509237349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 536881585728812270691299597 201330594648304601509237349)
        ·
          refine ⟨37749486496557112782982003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201330594648304601509237349 37749486496557112782982003)
          ·
            refine ⟨56624229744835669174473005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37749486496557112782982003 56624229744835669174473005)
            ·
              refine ⟨21234086154313375940427377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56624229744835669174473005 21234086154313375940427377)
              ·
                refine ⟨15925564615735031955320533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21234086154313375940427377 15925564615735031955320533)
                ·
                  refine ⟨373255420681289811452825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15925564615735031955320533 373255420681289811452825)
                  ·
                    rfl

theorem cell23_6542211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 7].length) (baseStart_6542211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542211 prefixEnd_6542211 := by exact prefixLift 6542211
  have htrace : WordTrace (prefixWord ++ tailWord_6542211) baseStart_6542211 baseEnd_6542211 := by
    simpa [prefixWord, tailWord_6542211, baseEnd_6542211] using wordTrace_append hprefix tailTrace_6542211
  have hstable : (prefixWord ++ tailWord_6542211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542211).length < 2 ^ (prefixWord ++ tailWord_6542211).sum := by decide
  have hdescent : baseEnd_6542211 < baseStart_6542211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542226 : List Nat := [3, 2, 3, 2, 2, 2, 2, 1, 1, 3, 2]
def baseStart_6542226 : Nat := 118140960795 + 6542226 * 2 ^ 59
def prefixEnd_6542226 : Nat := 4983230072969 + 3 ^ 40 * 6542226 * 2
def baseEnd_6542226 : Nat := 3359306488341425744387857

theorem tailTrace_6542226 : CollatzResearch.WordTrace tailWord_6542226 prefixEnd_6542226 3359306488341425744387857 := by
  unfold tailWord_6542226
  simp only [CollatzResearch.WordTrace]
  refine ⟨59653646299160000022815633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159076390131093333394175021 59653646299160000022815633)
  ·
    refine ⟨44740234724370000017111725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59653646299160000022815633 44740234724370000017111725)
    ·
      refine ⟨16777588021638750006416897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44740234724370000017111725 16777588021638750006416897)
      ·
        refine ⟨12583191016229062504812673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16777588021638750006416897 12583191016229062504812673)
        ·
          refine ⟨9437393262171796878609505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12583191016229062504812673 9437393262171796878609505)
          ·
            refine ⟨7078044946628847658957129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9437393262171796878609505 7078044946628847658957129)
            ·
              refine ⟨5308533709971635744217847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7078044946628847658957129 5308533709971635744217847)
              ·
                refine ⟨7962800564957453616326771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5308533709971635744217847 7962800564957453616326771)
                ·
                  refine ⟨11944200847436180424490157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7962800564957453616326771 11944200847436180424490157)
                  ·
                    refine ⟨4479075317788567659183809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11944200847436180424490157 4479075317788567659183809)
                    ·
                      refine ⟨3359306488341425744387857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4479075317788567659183809 3359306488341425744387857)
                      ·
                        rfl

theorem cell23_6542226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_6542226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542226 prefixEnd_6542226 := by exact prefixLift 6542226
  have htrace : WordTrace (prefixWord ++ tailWord_6542226) baseStart_6542226 baseEnd_6542226 := by
    simpa [prefixWord, tailWord_6542226, baseEnd_6542226] using wordTrace_append hprefix tailTrace_6542226
  have hstable : (prefixWord ++ tailWord_6542226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542226).length < 2 ^ (prefixWord ++ tailWord_6542226).sum := by decide
  have hdescent : baseEnd_6542226 < baseStart_6542226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542239 : List Nat := [1, 1, 2, 5, 2, 3, 1, 2, 2, 2, 2]
def baseStart_6542239 : Nat := 118140960795 + 6542239 * 2 ^ 59
def prefixEnd_6542239 : Nat := 4983230072969 + 3 ^ 40 * 6542239 * 2
def baseEnd_6542239 : Nat := 3359313163589934193525297

theorem tailTrace_6542239 : CollatzResearch.WordTrace tailWord_6542239 prefixEnd_6542239 3359313163589934193525297 := by
  unfold tailWord_6542239
  simp only [CollatzResearch.WordTrace]
  refine ⟨238615059345592903311485771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159076706230395268874323847 238615059345592903311485771)
  ·
    refine ⟨357922589018389354967228657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238615059345592903311485771 357922589018389354967228657)
    ·
      refine ⟨268441941763792016225421493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357922589018389354967228657 268441941763792016225421493)
      ·
        refine ⟨25166432040355501521133265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 268441941763792016225421493 25166432040355501521133265)
        ·
          refine ⟨18874824030266626140849949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25166432040355501521133265 18874824030266626140849949)
          ·
            refine ⟨7078059011349984802818731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18874824030266626140849949 7078059011349984802818731)
            ·
              refine ⟨10617088517024977204228097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7078059011349984802818731 10617088517024977204228097)
              ·
                refine ⟨7962816387768732903171073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10617088517024977204228097 7962816387768732903171073)
                ·
                  refine ⟨5972112290826549677378305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7962816387768732903171073 5972112290826549677378305)
                  ·
                    refine ⟨4479084218119912258033729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5972112290826549677378305 4479084218119912258033729)
                    ·
                      refine ⟨3359313163589934193525297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4479084218119912258033729 3359313163589934193525297)
                      ·
                        rfl

theorem cell23_6542239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_6542239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542239 prefixEnd_6542239 := by exact prefixLift 6542239
  have htrace : WordTrace (prefixWord ++ tailWord_6542239) baseStart_6542239 baseEnd_6542239 := by
    simpa [prefixWord, tailWord_6542239, baseEnd_6542239] using wordTrace_append hprefix tailTrace_6542239
  have hstable : (prefixWord ++ tailWord_6542239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542239).length < 2 ^ (prefixWord ++ tailWord_6542239).sum := by decide
  have hdescent : baseEnd_6542239 < baseStart_6542239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542385 : List Nat := [1, 2, 2, 3, 1, 2, 2, 4, 1, 1, 4]
def baseStart_6542385 : Nat := 118140960795 + 6542385 * 2 ^ 59
def prefixEnd_6542385 : Nat := 4983230072969 + 3 ^ 40 * 6542385 * 2
def baseEnd_6542385 : Nat := 3359388131765490622299625

theorem tailTrace_6542385 : CollatzResearch.WordTrace tailWord_6542385 prefixEnd_6542385 3359388131765490622299625 := by
  unfold tailWord_6542385
  simp only [CollatzResearch.WordTrace]
  refine ⟨238620384403063970246300609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159080256268709313497533739 238620384403063970246300609)
  ·
    refine ⟨178965288302297977684725457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238620384403063970246300609 178965288302297977684725457)
    ·
      refine ⟨134223966226723483263544093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178965288302297977684725457 134223966226723483263544093)
      ·
        refine ⟨50333987335021306223829035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134223966226723483263544093 50333987335021306223829035)
        ·
          refine ⟨75500981002531959335743553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50333987335021306223829035 75500981002531959335743553)
          ·
            refine ⟨56625735751898969501807665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75500981002531959335743553 56625735751898969501807665)
            ·
              refine ⟨42469301813924227126355749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56625735751898969501807665 42469301813924227126355749)
              ·
                refine ⟨7962994090110792586191703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42469301813924227126355749 7962994090110792586191703)
                ·
                  refine ⟨11944491135166188879287555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7962994090110792586191703 11944491135166188879287555)
                  ·
                    refine ⟨17916736702749283318931333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11944491135166188879287555 17916736702749283318931333)
                    ·
                      refine ⟨3359388131765490622299625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17916736702749283318931333 3359388131765490622299625)
                      ·
                        rfl

theorem cell23_6542385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_6542385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542385 prefixEnd_6542385 := by exact prefixLift 6542385
  have htrace : WordTrace (prefixWord ++ tailWord_6542385) baseStart_6542385 baseEnd_6542385 := by
    simpa [prefixWord, tailWord_6542385, baseEnd_6542385] using wordTrace_append hprefix tailTrace_6542385
  have hstable : (prefixWord ++ tailWord_6542385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542385).length < 2 ^ (prefixWord ++ tailWord_6542385).sum := by decide
  have hdescent : baseEnd_6542385 < baseStart_6542385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542429 : List Nat := [1, 4, 4, 1, 2, 2, 1, 1, 1, 6]
def baseStart_6542429 : Nat := 118140960795 + 6542429 * 2 ^ 59
def prefixEnd_6542429 : Nat := 4983230072969 + 3 ^ 40 * 6542429 * 2
def baseEnd_6542429 : Nat := 1119803574971429483383141

theorem tailTrace_6542429 : CollatzResearch.WordTrace tailWord_6542429 prefixEnd_6542429 1119803574971429483383141 := by
  unfold tailWord_6542429
  simp only [CollatzResearch.WordTrace]
  refine ⟨238621989214904565760902341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159081326143269710507268227 238621989214904565760902341)
  ·
    refine ⟨44741622977794606080169189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238621989214904565760902341 44741622977794606080169189)
    ·
      refine ⟨8389054308336488640031723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44741622977794606080169189 8389054308336488640031723)
      ·
        refine ⟨12583581462504732960047585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8389054308336488640031723 12583581462504732960047585)
        ·
          refine ⟨9437686096878549720035689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12583581462504732960047585 9437686096878549720035689)
          ·
            refine ⟨7078264572658912290026767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9437686096878549720035689 7078264572658912290026767)
            ·
              refine ⟨10617396858988368435040151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7078264572658912290026767 10617396858988368435040151)
              ·
                refine ⟨15926095288482552652560227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10617396858988368435040151 15926095288482552652560227)
                ·
                  refine ⟨23889142932723828978840341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15926095288482552652560227 23889142932723828978840341)
                  ·
                    refine ⟨1119803574971429483383141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23889142932723828978840341 1119803574971429483383141)
                    ·
                      rfl

theorem cell23_6542429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_6542429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542429 prefixEnd_6542429 := by exact prefixLift 6542429
  have htrace : WordTrace (prefixWord ++ tailWord_6542429) baseStart_6542429 baseEnd_6542429 := by
    simpa [prefixWord, tailWord_6542429, baseEnd_6542429] using wordTrace_append hprefix tailTrace_6542429
  have hstable : (prefixWord ++ tailWord_6542429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542429).length < 2 ^ (prefixWord ++ tailWord_6542429).sum := by decide
  have hdescent : baseEnd_6542429 < baseStart_6542429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542442 : List Nat := [3, 1, 3, 2, 2, 3, 2, 7]
def baseStart_6542442 : Nat := 118140960795 + 6542442 * 2 ^ 59
def prefixEnd_6542442 : Nat := 4983230072969 + 3 ^ 40 * 6542442 * 2
def baseEnd_6542442 : Nat := 124422866672696181455069

theorem tailTrace_6542442 : CollatzResearch.WordTrace tailWord_6542442 prefixEnd_6542442 124422866672696181455069 := by
  unfold tailWord_6542442
  simp only [CollatzResearch.WordTrace]
  refine ⟨59655615840964367245281395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159081642242571645987417053 59655615840964367245281395)
  ·
    refine ⟨89483423761446550867922093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59655615840964367245281395 89483423761446550867922093)
    ·
      refine ⟨33556283910542456575470785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89483423761446550867922093 33556283910542456575470785)
      ·
        refine ⟨25167212932906842431603089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33556283910542456575470785 25167212932906842431603089)
        ·
          refine ⟨18875409699680131823702317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25167212932906842431603089 18875409699680131823702317)
          ·
            refine ⟨7078278637380049433888369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18875409699680131823702317 7078278637380049433888369)
            ·
              refine ⟨5308708978035037075416277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7078278637380049433888369 5308708978035037075416277)
              ·
                refine ⟨124422866672696181455069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5308708978035037075416277 124422866672696181455069)
                ·
                  rfl

theorem cell23_6542442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 7].length) (baseStart_6542442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542442 prefixEnd_6542442 := by exact prefixLift 6542442
  have htrace : WordTrace (prefixWord ++ tailWord_6542442) baseStart_6542442 baseEnd_6542442 := by
    simpa [prefixWord, tailWord_6542442, baseEnd_6542442] using wordTrace_append hprefix tailTrace_6542442
  have hstable : (prefixWord ++ tailWord_6542442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542442).length < 2 ^ (prefixWord ++ tailWord_6542442).sum := by decide
  have hdescent : baseEnd_6542442 < baseStart_6542442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542448 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 5]
def baseStart_6542448 : Nat := 118140960795 + 6542448 * 2 ^ 59
def prefixEnd_6542448 : Nat := 4983230072969 + 3 ^ 40 * 6542448 * 2
def baseEnd_6542448 : Nat := 3359420481046723875811835

theorem tailTrace_6542448 : CollatzResearch.WordTrace tailWord_6542448 prefixEnd_6542448 3359420481046723875811835 := by
  unfold tailWord_6542448
  simp only [CollatzResearch.WordTrace]
  refine ⟨119311341100917866002921999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159081788134557154670562665 119311341100917866002921999)
  ·
    refine ⟨178967011651376799004382999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119311341100917866002921999 178967011651376799004382999)
    ·
      refine ⟨268450517477065198506574499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178967011651376799004382999 268450517477065198506574499)
      ·
        refine ⟨402675776215597797759861749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268450517477065198506574499 402675776215597797759861749)
        ·
          refine ⟨37750854020212293539987039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 402675776215597797759861749 37750854020212293539987039)
          ·
            refine ⟨56626281030318440309980559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37750854020212293539987039 56626281030318440309980559)
            ·
              refine ⟨84939421545477660464970839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56626281030318440309980559 84939421545477660464970839)
              ·
                refine ⟨127409132318216490697456259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84939421545477660464970839 127409132318216490697456259)
                ·
                  refine ⟨191113698477324736046184389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127409132318216490697456259 191113698477324736046184389)
                  ·
                    refine ⟨35833818464498388008659573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 191113698477324736046184389 35833818464498388008659573)
                    ·
                      refine ⟨3359420481046723875811835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35833818464498388008659573 3359420481046723875811835)
                      ·
                        rfl

theorem cell23_6542448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_6542448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542448 prefixEnd_6542448 := by exact prefixLift 6542448
  have htrace : WordTrace (prefixWord ++ tailWord_6542448) baseStart_6542448 baseEnd_6542448 := by
    simpa [prefixWord, tailWord_6542448, baseEnd_6542448] using wordTrace_append hprefix tailTrace_6542448
  have hstable : (prefixWord ++ tailWord_6542448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542448).length < 2 ^ (prefixWord ++ tailWord_6542448).sum := by decide
  have hdescent : baseEnd_6542448 < baseStart_6542448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542508 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 7]
def baseStart_6542508 : Nat := 118140960795 + 6542508 * 2 ^ 59
def prefixEnd_6542508 : Nat := 4983230072969 + 3 ^ 40 * 6542508 * 2
def baseEnd_6542508 : Nat := 3359451289885993641061559

theorem tailTrace_6542508 : CollatzResearch.WordTrace tailWord_6542508 prefixEnd_6542508 3359451289885993641061559 := by
  unfold tailWord_6542508
  simp only [CollatzResearch.WordTrace]
  refine ⟨119312435290809181126514089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159083247054412241502018785 119312435290809181126514089)
  ·
    refine ⟨89484326468106885844885567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119312435290809181126514089 89484326468106885844885567)
    ·
      refine ⟨134226489702160328767328351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89484326468106885844885567 134226489702160328767328351)
      ·
        refine ⟨201339734553240493150992527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134226489702160328767328351 201339734553240493150992527)
        ·
          refine ⟨302009601829860739726488791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201339734553240493150992527 302009601829860739726488791)
          ·
            refine ⟨453014402744791109589733187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302009601829860739726488791 453014402744791109589733187)
            ·
              refine ⟨679521604117186664384599781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453014402744791109589733187 679521604117186664384599781)
              ·
                refine ⟨127410300771972499572112459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 679521604117186664384599781 127410300771972499572112459)
                ·
                  refine ⟨191115451157958749358168689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127410300771972499572112459 191115451157958749358168689)
                  ·
                    refine ⟨143336588368469062018626517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 191115451157958749358168689 143336588368469062018626517)
                    ·
                      refine ⟨3359451289885993641061559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143336588368469062018626517 3359451289885993641061559)
                      ·
                        rfl

theorem cell23_6542508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_6542508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542508 prefixEnd_6542508 := by exact prefixLift 6542508
  have htrace : WordTrace (prefixWord ++ tailWord_6542508) baseStart_6542508 baseEnd_6542508 := by
    simpa [prefixWord, tailWord_6542508, baseEnd_6542508] using wordTrace_append hprefix tailTrace_6542508
  have hstable : (prefixWord ++ tailWord_6542508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542508).length < 2 ^ (prefixWord ++ tailWord_6542508).sum := by decide
  have hdescent : baseEnd_6542508 < baseStart_6542508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542526 : List Nat := [4, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2]
def baseStart_6542526 : Nat := 118140960795 + 6542526 * 2 ^ 59
def prefixEnd_6542526 : Nat := 4983230072969 + 3 ^ 40 * 6542526 * 2
def baseEnd_6542526 : Nat := 3359460532537774570636477

theorem tailTrace_6542526 : CollatzResearch.WordTrace tailWord_6542526 prefixEnd_6542526 3359460532537774570636477 := by
  unfold tailWord_6542526
  simp only [CollatzResearch.WordTrace]
  refine ⟨29828190886944143915897929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159083684730368767551455621 29828190886944143915897929)
  ·
    refine ⟨22371143165208107936923447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29828190886944143915897929 22371143165208107936923447)
    ·
      refine ⟨33556714747812161905385171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22371143165208107936923447 33556714747812161905385171)
      ·
        refine ⟨50335072121718242858077757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33556714747812161905385171 50335072121718242858077757)
        ·
          refine ⟨18875652045644341071779159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50335072121718242858077757 18875652045644341071779159)
          ·
            refine ⟨28313478068466511607668739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18875652045644341071779159 28313478068466511607668739)
            ·
              refine ⟨42470217102699767411503109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28313478068466511607668739 42470217102699767411503109)
              ·
                refine ⟨7963165706756206389656833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42470217102699767411503109 7963165706756206389656833)
                ·
                  refine ⟨5972374280067154792242625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7963165706756206389656833 5972374280067154792242625)
                  ·
                    refine ⟨4479280710050366094181969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5972374280067154792242625 4479280710050366094181969)
                    ·
                      refine ⟨3359460532537774570636477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4479280710050366094181969 3359460532537774570636477)
                      ·
                        rfl

theorem cell23_6542526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_6542526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542526 prefixEnd_6542526 := by exact prefixLift 6542526
  have htrace : WordTrace (prefixWord ++ tailWord_6542526) baseStart_6542526 baseEnd_6542526 := by
    simpa [prefixWord, tailWord_6542526, baseEnd_6542526] using wordTrace_append hprefix tailTrace_6542526
  have hstable : (prefixWord ++ tailWord_6542526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542526).length < 2 ^ (prefixWord ++ tailWord_6542526).sum := by decide
  have hdescent : baseEnd_6542526 < baseStart_6542526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542582 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_6542582 : Nat := 118140960795 + 6542582 * 2 ^ 59
def prefixEnd_6542582 : Nat := 4983230072969 + 3 ^ 40 * 6542582 * 2
def baseEnd_6542582 : Nat := 3359489287454426351536219

theorem tailTrace_6542582 : CollatzResearch.WordTrace tailWord_6542582 prefixEnd_6542582 3359489287454426351536219 := by
  unfold tailWord_6542582
  simp only [CollatzResearch.WordTrace]
  refine ⟨14914223098959392055701375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159085046388900181927481333 14914223098959392055701375)
  ·
    refine ⟨22371334648439088083552063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14914223098959392055701375 22371334648439088083552063)
    ·
      refine ⟨33557001972658632125328095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22371334648439088083552063 33557001972658632125328095)
      ·
        refine ⟨50335502958987948187992143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33557001972658632125328095 50335502958987948187992143)
        ·
          refine ⟨75503254438481922281988215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50335502958987948187992143 75503254438481922281988215)
          ·
            refine ⟨113254881657722883422982323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75503254438481922281988215 113254881657722883422982323)
            ·
              refine ⟨169882322486584325134473485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113254881657722883422982323 169882322486584325134473485)
              ·
                refine ⟨63705870932469121925427557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169882322486584325134473485 63705870932469121925427557)
                ·
                  refine ⟨11944850799837960361017667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63705870932469121925427557 11944850799837960361017667)
                  ·
                    refine ⟨17917276199756940541526501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11944850799837960361017667 17917276199756940541526501)
                    ·
                      refine ⟨3359489287454426351536219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17917276199756940541526501 3359489287454426351536219)
                      ·
                        rfl

theorem cell23_6542582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_6542582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542582 prefixEnd_6542582 := by exact prefixLift 6542582
  have htrace : WordTrace (prefixWord ++ tailWord_6542582) baseStart_6542582 baseEnd_6542582 := by
    simpa [prefixWord, tailWord_6542582, baseEnd_6542582] using wordTrace_append hprefix tailTrace_6542582
  have hstable : (prefixWord ++ tailWord_6542582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542582).length < 2 ^ (prefixWord ++ tailWord_6542582).sum := by decide
  have hdescent : baseEnd_6542582 < baseStart_6542582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542672 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 4]
def baseStart_6542672 : Nat := 118140960795 + 6542672 * 2 ^ 59
def prefixEnd_6542672 : Nat := 4983230072969 + 3 ^ 40 * 6542672 * 2
def baseEnd_6542672 : Nat := 3359535500713330999410805

theorem tailTrace_6542672 : CollatzResearch.WordTrace tailWord_6542672 prefixEnd_6542672 3359535500713330999410805 := by
  unfold tailWord_6542672
  simp only [CollatzResearch.WordTrace]
  refine ⟨119315426076512109130999135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159087234768682812174665513 119315426076512109130999135)
  ·
    refine ⟨178973139114768163696498703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119315426076512109130999135 178973139114768163696498703)
    ·
      refine ⟨268459708672152245544748055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178973139114768163696498703 268459708672152245544748055)
      ·
        refine ⟨402689563008228368317122083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268459708672152245544748055 402689563008228368317122083)
        ·
          refine ⟨604034344512342552475683125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402689563008228368317122083 604034344512342552475683125)
          ·
            refine ⟨56628219798032114294595293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 604034344512342552475683125 56628219798032114294595293)
            ·
              refine ⟨21235582424262042860473235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56628219798032114294595293 21235582424262042860473235)
              ·
                refine ⟨31853373636393064290709853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21235582424262042860473235 31853373636393064290709853)
                ·
                  refine ⟨11945015113647399109016195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31853373636393064290709853 11945015113647399109016195)
                  ·
                    refine ⟨17917522670471098663524293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11945015113647399109016195 17917522670471098663524293)
                    ·
                      refine ⟨3359535500713330999410805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17917522670471098663524293 3359535500713330999410805)
                      ·
                        rfl

theorem cell23_6542672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 4].length) (baseStart_6542672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542672 prefixEnd_6542672 := by exact prefixLift 6542672
  have htrace : WordTrace (prefixWord ++ tailWord_6542672) baseStart_6542672 baseEnd_6542672 := by
    simpa [prefixWord, tailWord_6542672, baseEnd_6542672] using wordTrace_append hprefix tailTrace_6542672
  have hstable : (prefixWord ++ tailWord_6542672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542672).length < 2 ^ (prefixWord ++ tailWord_6542672).sum := by decide
  have hdescent : baseEnd_6542672 < baseStart_6542672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542676 : List Nat := [2, 4, 1, 1, 2, 1, 4, 1, 2, 3, 2]
def baseStart_6542676 : Nat := 118140960795 + 6542676 * 2 ^ 59
def prefixEnd_6542676 : Nat := 4983230072969 + 3 ^ 40 * 6542676 * 2
def baseEnd_6542676 : Nat := 3359537554635948983760787

theorem tailTrace_6542676 : CollatzResearch.WordTrace tailWord_6542676 prefixEnd_6542676 3359537554635948983760787 := by
  unfold tailWord_6542676
  simp only [CollatzResearch.WordTrace]
  refine ⟨119315499022504863472571941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159087332030006484630095921 119315499022504863472571941)
  ·
    refine ⟨22371656066719661901107239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119315499022504863472571941 22371656066719661901107239)
    ·
      refine ⟨33557484100079492851660859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22371656066719661901107239 33557484100079492851660859)
      ·
        refine ⟨50336226150119239277491289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33557484100079492851660859 50336226150119239277491289)
        ·
          refine ⟨37752169612589429458118467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50336226150119239277491289 37752169612589429458118467)
          ·
            refine ⟨56628254418884144187177701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37752169612589429458118467 56628254418884144187177701)
            ·
              refine ⟨10617797703540777035095819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56628254418884144187177701 10617797703540777035095819)
              ·
                refine ⟨15926696555311165552643729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10617797703540777035095819 15926696555311165552643729)
                ·
                  refine ⟨11945022416483374164482797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15926696555311165552643729 11945022416483374164482797)
                  ·
                    refine ⟨4479383406181265311681049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11945022416483374164482797 4479383406181265311681049)
                    ·
                      refine ⟨3359537554635948983760787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4479383406181265311681049 3359537554635948983760787)
                      ·
                        rfl

theorem cell23_6542676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_6542676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542676 prefixEnd_6542676 := by exact prefixLift 6542676
  have htrace : WordTrace (prefixWord ++ tailWord_6542676) baseStart_6542676 baseEnd_6542676 := by
    simpa [prefixWord, tailWord_6542676, baseEnd_6542676] using wordTrace_append hprefix tailTrace_6542676
  have hstable : (prefixWord ++ tailWord_6542676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542676).length < 2 ^ (prefixWord ++ tailWord_6542676).sum := by decide
  have hdescent : baseEnd_6542676 < baseStart_6542676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542682 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 6, 4]
def baseStart_6542682 : Nat := 118140960795 + 6542682 * 2 ^ 59
def prefixEnd_6542682 : Nat := 4983230072969 + 3 ^ 40 * 6542682 * 2
def baseEnd_6542682 : Nat := 1119846878506625320095253

theorem tailTrace_6542682 : CollatzResearch.WordTrace tailWord_6542682 prefixEnd_6542682 1119846878506625320095253 := by
  unfold tailWord_6542682
  simp only [CollatzResearch.WordTrace]
  refine ⟨59657804220746997492465575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159087477921991993313241533 59657804220746997492465575)
  ·
    refine ⟨89486706331120496238698363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59657804220746997492465575 89486706331120496238698363)
    ·
      refine ⟨134230059496680744358047545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89486706331120496238698363 134230059496680744358047545)
      ·
        refine ⟨100672544622510558268535659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134230059496680744358047545 100672544622510558268535659)
        ·
          refine ⟨151008816933765837402803489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100672544622510558268535659 151008816933765837402803489)
          ·
            refine ⟨113256612700324378052102617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151008816933765837402803489 113256612700324378052102617)
            ·
              refine ⟨84942459525243283539076963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113256612700324378052102617 84942459525243283539076963)
              ·
                refine ⟨127413689287864925308615445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84942459525243283539076963 127413689287864925308615445)
                ·
                  refine ⟨5972516685368668373841349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127413689287864925308615445 5972516685368668373841349)
                  ·
                    refine ⟨1119846878506625320095253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5972516685368668373841349 1119846878506625320095253)
                    ·
                      rfl

theorem cell23_6542682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 6, 4].length) (baseStart_6542682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542682 prefixEnd_6542682 := by exact prefixLift 6542682
  have htrace : WordTrace (prefixWord ++ tailWord_6542682) baseStart_6542682 baseEnd_6542682 := by
    simpa [prefixWord, tailWord_6542682, baseEnd_6542682] using wordTrace_append hprefix tailTrace_6542682
  have hstable : (prefixWord ++ tailWord_6542682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542682).length < 2 ^ (prefixWord ++ tailWord_6542682).sum := by decide
  have hdescent : baseEnd_6542682 < baseStart_6542682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542695 : List Nat := [1, 1, 5, 1, 15]
def baseStart_6542695 : Nat := 118140960795 + 6542695 * 2 ^ 59
def prefixEnd_6542695 : Nat := 4983230072969 + 3 ^ 40 * 6542695 * 2
def baseEnd_6542695 : Nat := 4608432525059512221431

theorem tailTrace_6542695 : CollatzResearch.WordTrace tailWord_6542695 prefixEnd_6542695 4608432525059512221431 := by
  unfold tailWord_6542695
  simp only [CollatzResearch.WordTrace]
  refine ⟨238631691031940893190085539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159087794021293928793390359 238631691031940893190085539)
  ·
    refine ⟨357947536547911339785128309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238631691031940893190085539 357947536547911339785128309)
    ·
      refine ⟨33557581551366688104855779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 357947536547911339785128309 33557581551366688104855779)
      ·
        refine ⟨50336372327050032157283669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33557581551366688104855779 50336372327050032157283669)
        ·
          refine ⟨4608432525059512221431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 50336372327050032157283669 4608432525059512221431)
          ·
            rfl

theorem cell23_6542695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 15].length) (baseStart_6542695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542695 prefixEnd_6542695 := by exact prefixLift 6542695
  have htrace : WordTrace (prefixWord ++ tailWord_6542695) baseStart_6542695 baseEnd_6542695 := by
    simpa [prefixWord, tailWord_6542695, baseEnd_6542695] using wordTrace_append hprefix tailTrace_6542695
  have hstable : (prefixWord ++ tailWord_6542695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542695).length < 2 ^ (prefixWord ++ tailWord_6542695).sum := by decide
  have hdescent : baseEnd_6542695 < baseStart_6542695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542700 : List Nat := [2, 2, 1, 1, 5, 3, 2, 2, 1, 1, 3]
def baseStart_6542700 : Nat := 118140960795 + 6542700 * 2 ^ 59
def prefixEnd_6542700 : Nat := 4983230072969 + 3 ^ 40 * 6542700 * 2
def baseEnd_6542700 : Nat := 3359549878171656889860677

theorem tailTrace_6542700 : CollatzResearch.WordTrace tailWord_6542700 prefixEnd_6542700 3359549878171656889860677 := by
  unfold tailWord_6542700
  simp only [CollatzResearch.WordTrace]
  refine ⟨119315936698461389522008777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159087915597948519362678369 119315936698461389522008777)
  ·
    refine ⟨89486952523846042141506583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119315936698461389522008777 89486952523846042141506583)
    ·
      refine ⟨134230428785769063212259875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89486952523846042141506583 134230428785769063212259875)
      ·
        refine ⟨201345643178653594818389813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134230428785769063212259875 201345643178653594818389813)
        ·
          refine ⟨18876154047998774514224045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201345643178653594818389813 18876154047998774514224045)
          ·
            refine ⟨7078557767999540442834017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18876154047998774514224045 7078557767999540442834017)
            ·
              refine ⟨5308918325999655332125513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7078557767999540442834017 5308918325999655332125513)
              ·
                refine ⟨3981688744499741499094135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5308918325999655332125513 3981688744499741499094135)
                ·
                  refine ⟨5972533116749612248641203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3981688744499741499094135 5972533116749612248641203)
                  ·
                    refine ⟨8958799675124418372961805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5972533116749612248641203 8958799675124418372961805)
                    ·
                      refine ⟨3359549878171656889860677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8958799675124418372961805 3359549878171656889860677)
                      ·
                        rfl

theorem cell23_6542700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 1, 1, 3].length) (baseStart_6542700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542700 prefixEnd_6542700 := by exact prefixLift 6542700
  have htrace : WordTrace (prefixWord ++ tailWord_6542700) baseStart_6542700 baseEnd_6542700 := by
    simpa [prefixWord, tailWord_6542700, baseEnd_6542700] using wordTrace_append hprefix tailTrace_6542700
  have hstable : (prefixWord ++ tailWord_6542700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542700).length < 2 ^ (prefixWord ++ tailWord_6542700).sum := by decide
  have hdescent : baseEnd_6542700 < baseStart_6542700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542706 : List Nat := [3, 2, 1, 2, 1, 2, 2, 3, 3, 2, 2]
def baseStart_6542706 : Nat := 118140960795 + 6542706 * 2 ^ 59
def prefixEnd_6542706 : Nat := 4983230072969 + 3 ^ 40 * 6542706 * 2
def baseEnd_6542706 : Nat := 3359552959055583866385649

theorem tailTrace_6542706 : CollatzResearch.WordTrace tailWord_6542706 prefixEnd_6542706 3359552959055583866385649 := by
  unfold tailWord_6542706
  simp only [CollatzResearch.WordTrace]
  refine ⟨59658023058725260517183993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159088061489934028045823981 59658023058725260517183993)
  ·
    refine ⟨44743517294043945387887995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59658023058725260517183993 44743517294043945387887995)
    ·
      refine ⟨67115275941065918081831993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44743517294043945387887995 67115275941065918081831993)
      ·
        refine ⟨50336456955799438561373995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67115275941065918081831993 50336456955799438561373995)
        ·
          refine ⟨75504685433699157842060993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50336456955799438561373995 75504685433699157842060993)
          ·
            refine ⟨56628514075274368381545745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75504685433699157842060993 56628514075274368381545745)
            ·
              refine ⟨42471385556455776286159309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56628514075274368381545745 42471385556455776286159309)
              ·
                refine ⟨15926769583670916107309741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42471385556455776286159309 15926769583670916107309741)
                ·
                  refine ⟨5972538593876593540241153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15926769583670916107309741 5972538593876593540241153)
                  ·
                    refine ⟨4479403945407445155180865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5972538593876593540241153 4479403945407445155180865)
                    ·
                      refine ⟨3359552959055583866385649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4479403945407445155180865 3359552959055583866385649)
                      ·
                        rfl

theorem cell23_6542706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_6542706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542706 prefixEnd_6542706 := by exact prefixLift 6542706
  have htrace : WordTrace (prefixWord ++ tailWord_6542706) baseStart_6542706 baseEnd_6542706 := by
    simpa [prefixWord, tailWord_6542706, baseEnd_6542706] using wordTrace_append hprefix tailTrace_6542706
  have hstable : (prefixWord ++ tailWord_6542706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542706).length < 2 ^ (prefixWord ++ tailWord_6542706).sum := by decide
  have hdescent : baseEnd_6542706 < baseStart_6542706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542729 : List Nat := [1, 2, 1, 1, 7, 1, 3, 7]
def baseStart_6542729 : Nat := 118140960795 + 6542729 * 2 ^ 59
def prefixEnd_6542729 : Nat := 4983230072969 + 3 ^ 40 * 6542729 * 2
def baseEnd_6542729 : Nat := 124428324781875454681409

theorem tailTrace_6542729 : CollatzResearch.WordTrace tailWord_6542729 prefixEnd_6542729 124428324781875454681409 := by
  unfold tailWord_6542729
  simp only [CollatzResearch.WordTrace]
  refine ⟨238632931113817716996823241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159088620742545144664548827 238632931113817716996823241)
  ·
    refine ⟨178974698335363287747617431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238632931113817716996823241 178974698335363287747617431)
    ·
      refine ⟨268462047503044931621426147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178974698335363287747617431 268462047503044931621426147)
      ·
        refine ⟨402693071254567397432139221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268462047503044931621426147 402693071254567397432139221)
        ·
          refine ⟨9438118857528923377315763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 402693071254567397432139221 9438118857528923377315763)
          ·
            refine ⟨14157178286293385065973645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9438118857528923377315763 14157178286293385065973645)
            ·
              refine ⟨5308941857360019399740117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14157178286293385065973645 5308941857360019399740117)
              ·
                refine ⟨124428324781875454681409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5308941857360019399740117 124428324781875454681409)
                ·
                  rfl

theorem cell23_6542729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 7].length) (baseStart_6542729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542729 prefixEnd_6542729 := by exact prefixLift 6542729
  have htrace : WordTrace (prefixWord ++ tailWord_6542729) baseStart_6542729 baseEnd_6542729 := by
    simpa [prefixWord, tailWord_6542729, baseEnd_6542729] using wordTrace_append hprefix tailTrace_6542729
  have hstable : (prefixWord ++ tailWord_6542729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542729).length < 2 ^ (prefixWord ++ tailWord_6542729).sum := by decide
  have hdescent : baseEnd_6542729 < baseStart_6542729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542735 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 11]
def baseStart_6542735 : Nat := 118140960795 + 6542735 * 2 ^ 59
def prefixEnd_6542735 : Nat := 4983230072969 + 3 ^ 40 * 6542735 * 2
def baseEnd_6542735 : Nat := 3359567849994564252923015

theorem tailTrace_6542735 : CollatzResearch.WordTrace tailWord_6542735 prefixEnd_6542735 3359567849994564252923015 := by
  unfold tailWord_6542735
  simp only [CollatzResearch.WordTrace]
  refine ⟨238633149951795980021541659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159088766634530653347694439 238633149951795980021541659)
  ·
    refine ⟨357949724927693970032312489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238633149951795980021541659 357949724927693970032312489)
    ·
      refine ⟨268462293695770477524234367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357949724927693970032312489 268462293695770477524234367)
      ·
        refine ⟨402693440543655716286351551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268462293695770477524234367 402693440543655716286351551)
        ·
          refine ⟨604040160815483574429527327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402693440543655716286351551 604040160815483574429527327)
          ·
            refine ⟨906060241223225361644290991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604040160815483574429527327 906060241223225361644290991)
            ·
              refine ⟨1359090361834838042466436487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906060241223225361644290991 1359090361834838042466436487)
              ·
                refine ⟨2038635542752257063699654731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359090361834838042466436487 2038635542752257063699654731)
                ·
                  refine ⟨3057953314128385595549482097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2038635542752257063699654731 3057953314128385595549482097)
                  ·
                    refine ⟨2293464985596289196662111573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3057953314128385595549482097 2293464985596289196662111573)
                    ·
                      refine ⟨3359567849994564252923015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 2293464985596289196662111573 3359567849994564252923015)
                      ·
                        rfl

theorem cell23_6542735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_6542735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542735 prefixEnd_6542735 := by exact prefixLift 6542735
  have htrace : WordTrace (prefixWord ++ tailWord_6542735) baseStart_6542735 baseEnd_6542735 := by
    simpa [prefixWord, tailWord_6542735, baseEnd_6542735] using wordTrace_append hprefix tailTrace_6542735
  have hstable : (prefixWord ++ tailWord_6542735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542735).length < 2 ^ (prefixWord ++ tailWord_6542735).sum := by decide
  have hdescent : baseEnd_6542735 < baseStart_6542735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542740 : List Nat := [2, 4, 2, 1, 2, 1, 1, 5, 1, 2, 2]
def baseStart_6542740 : Nat := 118140960795 + 6542740 * 2 ^ 59
def prefixEnd_6542740 : Nat := 4983230072969 + 3 ^ 40 * 6542740 * 2
def baseEnd_6542740 : Nat := 3359570417397836733360493

theorem tailTrace_6542740 : CollatzResearch.WordTrace tailWord_6542740 prefixEnd_6542740 3359570417397836733360493 := by
  unfold tailWord_6542740
  simp only [CollatzResearch.WordTrace]
  refine ⟨119316666158388932937736837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159088888211185243916982449 119316666158388932937736837)
  ·
    refine ⟨22371874904697924925825657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119316666158388932937736837 22371874904697924925825657)
    ·
      refine ⟨16778906178523443694369243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22371874904697924925825657 16778906178523443694369243)
      ·
        refine ⟨25168359267785165541553865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16778906178523443694369243 25168359267785165541553865)
        ·
          refine ⟨18876269450838874156165399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25168359267785165541553865 18876269450838874156165399)
          ·
            refine ⟨28314404176258311234248099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18876269450838874156165399 28314404176258311234248099)
            ·
              refine ⟨42471606264387466851372149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28314404176258311234248099 42471606264387466851372149)
              ·
                refine ⟨3981713087286325017316139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42471606264387466851372149 3981713087286325017316139)
                ·
                  refine ⟨5972569630929487525974209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3981713087286325017316139 5972569630929487525974209)
                  ·
                    refine ⟨4479427223197115644480657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5972569630929487525974209 4479427223197115644480657)
                    ·
                      refine ⟨3359570417397836733360493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4479427223197115644480657 3359570417397836733360493)
                      ·
                        rfl

theorem cell23_6542740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_6542740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542740 prefixEnd_6542740 := by exact prefixLift 6542740
  have htrace : WordTrace (prefixWord ++ tailWord_6542740) baseStart_6542740 baseEnd_6542740 := by
    simpa [prefixWord, tailWord_6542740, baseEnd_6542740] using wordTrace_append hprefix tailTrace_6542740
  have hstable : (prefixWord ++ tailWord_6542740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542740).length < 2 ^ (prefixWord ++ tailWord_6542740).sum := by decide
  have hdescent : baseEnd_6542740 < baseStart_6542740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542750 : List Nat := [4, 3, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_6542750 : Nat := 118140960795 + 6542750 * 2 ^ 59
def prefixEnd_6542750 : Nat := 4983230072969 + 3 ^ 40 * 6542750 * 2
def baseEnd_6542750 : Nat := 1119858517401460564745149

theorem tailTrace_6542750 : CollatzResearch.WordTrace tailWord_6542750 prefixEnd_6542750 1119858517401460564745149 := by
  unfold tailWord_6542750
  simp only [CollatzResearch.WordTrace]
  refine ⟨29829212130842704697917213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159089131364494425055558469 29829212130842704697917213)
  ·
    refine ⟨11185954549066014261718955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29829212130842704697917213 11185954549066014261718955)
    ·
      refine ⟨16778931823599021392578433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11185954549066014261718955 16778931823599021392578433)
      ·
        refine ⟨12584198867699266044433825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16778931823599021392578433 12584198867699266044433825)
        ·
          refine ⟨9438149150774449533325369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12584198867699266044433825 9438149150774449533325369)
          ·
            refine ⟨7078611863080837149994027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9438149150774449533325369 7078611863080837149994027)
            ·
              refine ⟨10617917794621255724991041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7078611863080837149994027 10617917794621255724991041)
              ·
                refine ⟨7963438345965941793743281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10617917794621255724991041 7963438345965941793743281)
                ·
                  refine ⟨5972578759474456345307461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7963438345965941793743281 5972578759474456345307461)
                  ·
                    refine ⟨1119858517401460564745149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5972578759474456345307461 1119858517401460564745149)
                    ·
                      rfl

theorem cell23_6542750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_6542750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542750 prefixEnd_6542750 := by exact prefixLift 6542750
  have htrace : WordTrace (prefixWord ++ tailWord_6542750) baseStart_6542750 baseEnd_6542750 := by
    simpa [prefixWord, tailWord_6542750, baseEnd_6542750] using wordTrace_append hprefix tailTrace_6542750
  have hstable : (prefixWord ++ tailWord_6542750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542750).length < 2 ^ (prefixWord ++ tailWord_6542750).sum := by decide
  have hdescent : baseEnd_6542750 < baseStart_6542750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542813 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 4, 2, 2]
def baseStart_6542813 : Nat := 118140960795 + 6542813 * 2 ^ 59
def prefixEnd_6542813 : Nat := 4983230072969 + 3 ^ 40 * 6542813 * 2
def baseEnd_6542813 : Nat := 3359607901485614947747657

theorem tailTrace_6542813 : CollatzResearch.WordTrace tailWord_6542813 prefixEnd_6542813 3359607901485614947747657 := by
  unfold tailWord_6542813
  simp only [CollatzResearch.WordTrace]
  refine ⟨238635994845513399342881093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159090663230342266228587395 238635994845513399342881093)
  ·
    refine ⟨44744249033533762376790205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238635994845513399342881093 44744249033533762376790205)
    ·
      refine ⟨16779093387575160891296327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44744249033533762376790205 16779093387575160891296327)
      ·
        refine ⟨25168640081362741336944491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16779093387575160891296327 25168640081362741336944491)
        ·
          refine ⟨37752960122044112005416737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25168640081362741336944491 37752960122044112005416737)
          ·
            refine ⟨28314720091533084004062553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37752960122044112005416737 28314720091533084004062553)
            ·
              refine ⟨21236040068649813003046915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28314720091533084004062553 21236040068649813003046915)
              ·
                refine ⟨31854060102974719504570373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21236040068649813003046915 31854060102974719504570373)
                ·
                  refine ⟨5972636269307759907106945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31854060102974719504570373 5972636269307759907106945)
                  ·
                    refine ⟨4479477201980819930330209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5972636269307759907106945 4479477201980819930330209)
                    ·
                      refine ⟨3359607901485614947747657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4479477201980819930330209 3359607901485614947747657)
                      ·
                        rfl

theorem cell23_6542813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_6542813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542813 prefixEnd_6542813 := by exact prefixLift 6542813
  have htrace : WordTrace (prefixWord ++ tailWord_6542813) baseStart_6542813 baseEnd_6542813 := by
    simpa [prefixWord, tailWord_6542813, baseEnd_6542813] using wordTrace_append hprefix tailTrace_6542813
  have hstable : (prefixWord ++ tailWord_6542813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542813).length < 2 ^ (prefixWord ++ tailWord_6542813).sum := by decide
  have hdescent : baseEnd_6542813 < baseStart_6542813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542819 : List Nat := [1, 1, 1, 6, 2, 1, 3, 1, 7]
def baseStart_6542819 : Nat := 118140960795 + 6542819 * 2 ^ 59
def prefixEnd_6542819 : Nat := 4983230072969 + 3 ^ 40 * 6542819 * 2
def baseEnd_6542819 : Nat := 373290109152171324919181

theorem tailTrace_6542819 : CollatzResearch.WordTrace tailWord_6542819 prefixEnd_6542819 373290109152171324919181 := by
  unfold tailWord_6542819
  simp only [CollatzResearch.WordTrace]
  refine ⟨238636213683491662367599511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159090809122327774911733007 238636213683491662367599511)
  ·
    refine ⟨357954320525237493551399267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238636213683491662367599511 357954320525237493551399267)
    ·
      refine ⟨536931480787856240327098901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357954320525237493551399267 536931480787856240327098901)
      ·
        refine ⟨25168663161930761265332761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 536931480787856240327098901 25168663161930761265332761)
        ·
          refine ⟨18876497371448070948999571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25168663161930761265332761 18876497371448070948999571)
          ·
            refine ⟨28314746057172106423499357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18876497371448070948999571 28314746057172106423499357)
            ·
              refine ⟨10618029771439539908812259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28314746057172106423499357 10618029771439539908812259)
              ·
                refine ⟨15927044657159309863218389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10618029771439539908812259 15927044657159309863218389)
                ·
                  refine ⟨373290109152171324919181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15927044657159309863218389 373290109152171324919181)
                  ·
                    rfl

theorem cell23_6542819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 7].length) (baseStart_6542819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542819 prefixEnd_6542819 := by exact prefixLift 6542819
  have htrace : WordTrace (prefixWord ++ tailWord_6542819) baseStart_6542819 baseEnd_6542819 := by
    simpa [prefixWord, tailWord_6542819, baseEnd_6542819] using wordTrace_append hprefix tailTrace_6542819
  have hstable : (prefixWord ++ tailWord_6542819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542819).length < 2 ^ (prefixWord ++ tailWord_6542819).sum := by decide
  have hdescent : baseEnd_6542819 < baseStart_6542819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542839 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 4, 5, 2]
def baseStart_6542839 : Nat := 118140960795 + 6542839 * 2 ^ 59
def prefixEnd_6542839 : Nat := 4983230072969 + 3 ^ 40 * 6542839 * 2
def baseEnd_6542839 : Nat := 3359621251982631846022537

theorem tailTrace_6542839 : CollatzResearch.WordTrace tailWord_6542839 prefixEnd_6542839 3359621251982631846022537 := by
  unfold tailWord_6542839
  simp only [CollatzResearch.WordTrace]
  refine ⟨238636943143419205783327571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159091295428946137188885047 238636943143419205783327571)
  ·
    refine ⟨357955414715128808674991357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238636943143419205783327571 357955414715128808674991357)
    ·
      refine ⟨134233280518173303253121759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357955414715128808674991357 134233280518173303253121759)
      ·
        refine ⟨201349920777259954879682639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134233280518173303253121759 201349920777259954879682639)
        ·
          refine ⟨302024881165889932319523959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201349920777259954879682639 302024881165889932319523959)
          ·
            refine ⟨453037321748834898479285939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302024881165889932319523959 453037321748834898479285939)
            ·
              refine ⟨679555982623252347718928909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453037321748834898479285939 679555982623252347718928909)
              ·
                refine ⟨254833493483719630394598341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 679555982623252347718928909 254833493483719630394598341)
                ·
                  refine ⟨47781280028197430698987189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 254833493483719630394598341 47781280028197430698987189)
                  ·
                    refine ⟨4479495002643509128030049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47781280028197430698987189 4479495002643509128030049)
                    ·
                      refine ⟨3359621251982631846022537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4479495002643509128030049 3359621251982631846022537)
                      ·
                        rfl

theorem cell23_6542839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 5, 2].length) (baseStart_6542839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542839 prefixEnd_6542839 := by exact prefixLift 6542839
  have htrace : WordTrace (prefixWord ++ tailWord_6542839) baseStart_6542839 baseEnd_6542839 := by
    simpa [prefixWord, tailWord_6542839, baseEnd_6542839] using wordTrace_append hprefix tailTrace_6542839
  have hstable : (prefixWord ++ tailWord_6542839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542839).length < 2 ^ (prefixWord ++ tailWord_6542839).sum := by decide
  have hdescent : baseEnd_6542839 < baseStart_6542839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542842 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7]
def baseStart_6542842 : Nat := 118140960795 + 6542842 * 2 ^ 59
def prefixEnd_6542842 : Nat := 4983230072969 + 3 ^ 40 * 6542842 * 2
def baseEnd_6542842 : Nat := 3359622792424595334285023

theorem tailTrace_6542842 : CollatzResearch.WordTrace tailWord_6542842 prefixEnd_6542842 3359622792424595334285023 := by
  unfold tailWord_6542842
  simp only [CollatzResearch.WordTrace]
  refine ⟨59659263140602084323921695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159091368374938891530457853 59659263140602084323921695)
  ·
    refine ⟨89488894710903126485882543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59659263140602084323921695 89488894710903126485882543)
    ·
      refine ⟨134233342066354689728823815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89488894710903126485882543 134233342066354689728823815)
      ·
        refine ⟨201350013099532034593235723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134233342066354689728823815 201350013099532034593235723)
        ·
          refine ⟨302025019649298051889853585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201350013099532034593235723 302025019649298051889853585)
          ·
            refine ⟨226518764736973538917390189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302025019649298051889853585 226518764736973538917390189)
            ·
              refine ⟨84944536776365077094021321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226518764736973538917390189 84944536776365077094021321)
              ·
                refine ⟨63708402582273807820515991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84944536776365077094021321 63708402582273807820515991)
                ·
                  refine ⟨95562603873410711730773987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63708402582273807820515991 95562603873410711730773987)
                  ·
                    refine ⟨143343905810116067596160981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95562603873410711730773987 143343905810116067596160981)
                    ·
                      refine ⟨3359622792424595334285023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143343905810116067596160981 3359622792424595334285023)
                      ·
                        rfl

theorem cell23_6542842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_6542842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542842 prefixEnd_6542842 := by exact prefixLift 6542842
  have htrace : WordTrace (prefixWord ++ tailWord_6542842) baseStart_6542842 baseEnd_6542842 := by
    simpa [prefixWord, tailWord_6542842, baseEnd_6542842] using wordTrace_append hprefix tailTrace_6542842
  have hstable : (prefixWord ++ tailWord_6542842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542842).length < 2 ^ (prefixWord ++ tailWord_6542842).sum := by decide
  have hdescent : baseEnd_6542842 < baseStart_6542842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542892 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 12]
def baseStart_6542892 : Nat := 118140960795 + 6542892 * 2 ^ 59
def prefixEnd_6542892 : Nat := 4983230072969 + 3 ^ 40 * 6542892 * 2
def baseEnd_6542892 : Nat := 373294274050813348739977

theorem tailTrace_6542892 : CollatzResearch.WordTrace tailWord_6542892 prefixEnd_6542892 373294274050813348739977 := by
  unfold tailWord_6542892
  simp only [CollatzResearch.WordTrace]
  refine ⟨119319438106113597917503465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159092584141484797223337953 119319438106113597917503465)
  ·
    refine ⟨89489578579585198438127599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119319438106113597917503465 89489578579585198438127599)
    ·
      refine ⟨134234367869377797657191399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89489578579585198438127599 134234367869377797657191399)
      ·
        refine ⟨201351551804066696485787099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134234367869377797657191399 201351551804066696485787099)
        ·
          refine ⟨302027327706100044728680649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201351551804066696485787099 302027327706100044728680649)
          ·
            refine ⟨226520495779575033546510487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302027327706100044728680649 226520495779575033546510487)
            ·
              refine ⟨339780743669362550319765731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226520495779575033546510487 339780743669362550319765731)
              ·
                refine ⟨509671115504043825479648597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339780743669362550319765731 509671115504043825479648597)
                ·
                  refine ⟨373294274050813348739977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 509671115504043825479648597 373294274050813348739977)
                  ·
                    rfl

theorem cell23_6542892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 12].length) (baseStart_6542892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542892 prefixEnd_6542892 := by exact prefixLift 6542892
  have htrace : WordTrace (prefixWord ++ tailWord_6542892) baseStart_6542892 baseEnd_6542892 := by
    simpa [prefixWord, tailWord_6542892, baseEnd_6542892] using wordTrace_append hprefix tailTrace_6542892
  have hstable : (prefixWord ++ tailWord_6542892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542892).length < 2 ^ (prefixWord ++ tailWord_6542892).sum := by decide
  have hdescent : baseEnd_6542892 < baseStart_6542892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542969 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 3, 6]
def baseStart_6542969 : Nat := 118140960795 + 6542969 * 2 ^ 59
def prefixEnd_6542969 : Nat := 4983230072969 + 3 ^ 40 * 6542969 * 2
def baseEnd_6542969 : Nat := 1119896001489238779132313

theorem tailTrace_6542969 : CollatzResearch.WordTrace tailWord_6542969 prefixEnd_6542969 1119896001489238779132313 := by
  unfold tailWord_6542969
  simp only [CollatzResearch.WordTrace]
  refine ⟨238641684632948237985559961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159094456421965491990373307 238641684632948237985559961)
  ·
    refine ⟨178981263474711178489169971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238641684632948237985559961 178981263474711178489169971)
    ·
      refine ⟨268471895212066767733754957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178981263474711178489169971 268471895212066767733754957)
      ·
        refine ⟨100676960704525037900158109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268471895212066767733754957 100676960704525037900158109)
        ·
          refine ⟨37753860264196889212559291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100676960704525037900158109 37753860264196889212559291)
          ·
            refine ⟨56630790396295333818838937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37753860264196889212559291 56630790396295333818838937)
            ·
              refine ⟨42473092797221500364129203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56630790396295333818838937 42473092797221500364129203)
              ·
                refine ⟨63709639195832250546193805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42473092797221500364129203 63709639195832250546193805)
                ·
                  refine ⟨23891114698437093954822677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63709639195832250546193805 23891114698437093954822677)
                  ·
                    refine ⟨1119896001489238779132313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23891114698437093954822677 1119896001489238779132313)
                    ·
                      rfl

theorem cell23_6542969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 6].length) (baseStart_6542969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542969 prefixEnd_6542969 := by exact prefixLift 6542969
  have htrace : WordTrace (prefixWord ++ tailWord_6542969) baseStart_6542969 baseEnd_6542969 := by
    simpa [prefixWord, tailWord_6542969, baseEnd_6542969] using wordTrace_append hprefix tailTrace_6542969
  have hstable : (prefixWord ++ tailWord_6542969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542969).length < 2 ^ (prefixWord ++ tailWord_6542969).sum := by decide
  have hdescent : baseEnd_6542969 < baseStart_6542969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542976 : List Nat := [2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 4]
def baseStart_6542976 : Nat := 118140960795 + 6542976 * 2 ^ 59
def prefixEnd_6542976 : Nat := 4983230072969 + 3 ^ 40 * 6542976 * 2
def baseEnd_6542976 : Nat := 3359691598832297810009407

theorem tailTrace_6542976 : CollatzResearch.WordTrace tailWord_6542976 prefixEnd_6542976 3359691598832297810009407 := by
  unfold tailWord_6542976
  simp only [CollatzResearch.WordTrace]
  refine ⟨119320969971961439090532391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159094626629281918787376521 119320969971961439090532391)
  ·
    refine ⟨178981454957942158635798587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119320969971961439090532391 178981454957942158635798587)
    ·
      refine ⟨268472182436913237953697881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178981454957942158635798587 268472182436913237953697881)
      ·
        refine ⟨201354136827684928465273411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268472182436913237953697881 201354136827684928465273411)
        ·
          refine ⟨302031205241527392697910117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201354136827684928465273411 302031205241527392697910117)
          ·
            refine ⟨56630850982786386130858147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 302031205241527392697910117 56630850982786386130858147)
            ·
              refine ⟨84946276474179579196287221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56630850982786386130858147 84946276474179579196287221)
              ·
                refine ⟨7963713419454335549651927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84946276474179579196287221 7963713419454335549651927)
                ·
                  refine ⟨11945570129181503324477891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7963713419454335549651927 11945570129181503324477891)
                  ·
                    refine ⟨17918355193772254986716837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11945570129181503324477891 17918355193772254986716837)
                    ·
                      refine ⟨3359691598832297810009407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17918355193772254986716837 3359691598832297810009407)
                      ·
                        rfl

theorem cell23_6542976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 4].length) (baseStart_6542976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542976 prefixEnd_6542976 := by exact prefixLift 6542976
  have htrace : WordTrace (prefixWord ++ tailWord_6542976) baseStart_6542976 baseEnd_6542976 := by
    simpa [prefixWord, tailWord_6542976, baseEnd_6542976] using wordTrace_append hprefix tailTrace_6542976
  have hstable : (prefixWord ++ tailWord_6542976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542976).length < 2 ^ (prefixWord ++ tailWord_6542976).sum := by decide
  have hdescent : baseEnd_6542976 < baseStart_6542976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542980 : List Nat := [2, 3, 2, 1, 4, 1, 1, 2, 2, 3, 2]
def baseStart_6542980 : Nat := 118140960795 + 6542980 * 2 ^ 59
def prefixEnd_6542980 : Nat := 4983230072969 + 3 ^ 40 * 6542980 * 2
def baseEnd_6542980 : Nat := 3359693652754915794359389

theorem tailTrace_6542980 : CollatzResearch.WordTrace tailWord_6542980 prefixEnd_6542980 3359693652754915794359389 := by
  unfold tailWord_6542980
  simp only [CollatzResearch.WordTrace]
  refine ⟨119321042917954193432105197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159094723890605591242806929 119321042917954193432105197)
  ·
    refine ⟨44745391094232822537039449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119321042917954193432105197 44745391094232822537039449)
    ·
      refine ⟨33559043320674616902779587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44745391094232822537039449 33559043320674616902779587)
      ·
        refine ⟨50338564981011925354169381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33559043320674616902779587 50338564981011925354169381)
        ·
          refine ⟨9438480933939736003906759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50338564981011925354169381 9438480933939736003906759)
          ·
            refine ⟨14157721400909604005860139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9438480933939736003906759 14157721400909604005860139)
            ·
              refine ⟨21236582101364406008790209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14157721400909604005860139 21236582101364406008790209)
              ·
                refine ⟨15927436576023304506592657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21236582101364406008790209 15927436576023304506592657)
                ·
                  refine ⟨11945577432017478379944493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15927436576023304506592657 11945577432017478379944493)
                  ·
                    refine ⟨4479591537006554392479185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11945577432017478379944493 4479591537006554392479185)
                    ·
                      refine ⟨3359693652754915794359389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4479591537006554392479185 3359693652754915794359389)
                      ·
                        rfl

theorem cell23_6542980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_6542980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542980 prefixEnd_6542980 := by exact prefixLift 6542980
  have htrace : WordTrace (prefixWord ++ tailWord_6542980) baseStart_6542980 baseEnd_6542980 := by
    simpa [prefixWord, tailWord_6542980, baseEnd_6542980] using wordTrace_append hprefix tailTrace_6542980
  have hstable : (prefixWord ++ tailWord_6542980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542980).length < 2 ^ (prefixWord ++ tailWord_6542980).sum := by decide
  have hdescent : baseEnd_6542980 < baseStart_6542980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542993 : List Nat := [1, 2, 2, 1, 1, 1, 1, 7, 3, 2, 2]
def baseStart_6542993 : Nat := 118140960795 + 6542993 * 2 ^ 59
def prefixEnd_6542993 : Nat := 4983230072969 + 3 ^ 40 * 6542993 * 2
def baseEnd_6542993 : Nat := 3359700328003424243496829

theorem tailTrace_6542993 : CollatzResearch.WordTrace tailWord_6542993 prefixEnd_6542993 3359700328003424243496829 := by
  unfold tailWord_6542993
  simp only [CollatzResearch.WordTrace]
  refine ⟨238642559984861290084433633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159095039989907526722955755 238642559984861290084433633)
  ·
    refine ⟨178981919988645967563325225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238642559984861290084433633 178981919988645967563325225)
    ·
      refine ⟨134236439991484475672493919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178981919988645967563325225 134236439991484475672493919)
      ·
        refine ⟨201354659987226713508740879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134236439991484475672493919 201354659987226713508740879)
        ·
          refine ⟨302031989980840070263111319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201354659987226713508740879 302031989980840070263111319)
          ·
            refine ⟨453047984971260105394666979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302031989980840070263111319 453047984971260105394666979)
            ·
              refine ⟨679571977456890158092000469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453047984971260105394666979 679571977456890158092000469)
              ·
                refine ⟨15927468221645863080281261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 679571977456890158092000469 15927468221645863080281261)
                ·
                  refine ⟨5972800583117198655105473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15927468221645863080281261 5972800583117198655105473)
                  ·
                    refine ⟨4479600437337898991329105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5972800583117198655105473 4479600437337898991329105)
                    ·
                      refine ⟨3359700328003424243496829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4479600437337898991329105 3359700328003424243496829)
                      ·
                        rfl

theorem cell23_6542993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 2, 2].length) (baseStart_6542993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542993 prefixEnd_6542993 := by exact prefixLift 6542993
  have htrace : WordTrace (prefixWord ++ tailWord_6542993) baseStart_6542993 baseEnd_6542993 := by
    simpa [prefixWord, tailWord_6542993, baseEnd_6542993] using wordTrace_append hprefix tailTrace_6542993
  have hstable : (prefixWord ++ tailWord_6542993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542993).length < 2 ^ (prefixWord ++ tailWord_6542993).sum := by decide
  have hdescent : baseEnd_6542993 < baseStart_6542993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542999 : List Nat := [1, 1, 3, 3, 2, 2, 1, 10]
def baseStart_6542999 : Nat := 118140960795 + 6542999 * 2 ^ 59
def prefixEnd_6542999 : Nat := 4983230072969 + 3 ^ 40 * 6542999 * 2
def baseEnd_6542999 : Nat := 124433459588420415556363

theorem tailTrace_6542999 : CollatzResearch.WordTrace tailWord_6542999 prefixEnd_6542999 124433459588420415556363 := by
  unfold tailWord_6542999
  simp only [CollatzResearch.WordTrace]
  refine ⟨238642778822839553109152051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159095185881893035406101367 238642778822839553109152051)
  ·
    refine ⟨357964168234259329663728077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238642778822839553109152051 357964168234259329663728077)
    ·
      refine ⟨134236563087847248623898029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357964168234259329663728077 134236563087847248623898029)
      ·
        refine ⟨50338711157942718233961761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134236563087847248623898029 50338711157942718233961761)
        ·
          refine ⟨37754033368457038675471321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50338711157942718233961761 37754033368457038675471321)
          ·
            refine ⟨28315525026342779006603491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37754033368457038675471321 28315525026342779006603491)
            ·
              refine ⟨42473287539514168509905237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28315525026342779006603491 42473287539514168509905237)
              ·
                refine ⟨124433459588420415556363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42473287539514168509905237 124433459588420415556363)
                ·
                  rfl

theorem cell23_6542999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 10].length) (baseStart_6542999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6542999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6542999 prefixEnd_6542999 := by exact prefixLift 6542999
  have htrace : WordTrace (prefixWord ++ tailWord_6542999) baseStart_6542999 baseEnd_6542999 := by
    simpa [prefixWord, tailWord_6542999, baseEnd_6542999] using wordTrace_append hprefix tailTrace_6542999
  have hstable : (prefixWord ++ tailWord_6542999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542999).length < 2 ^ (prefixWord ++ tailWord_6542999).sum := by decide
  have hdescent : baseEnd_6542999 < baseStart_6542999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
