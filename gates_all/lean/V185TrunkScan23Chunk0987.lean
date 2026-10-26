import V185TrunkScan23Chunk0986

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5842808 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 6, 4, 2]
def baseStart_5842808 : Nat := 118140960795 + 5842808 * 2 ^ 59
def prefixEnd_5842808 : Nat := 4983230072969 + 3 ^ 40 * 5842808 * 2
def baseEnd_5842808 : Nat := 3000168875935081220529421

theorem tailTrace_5842808 : CollatzResearch.WordTrace tailWord_5842808 prefixEnd_5842808 3000168875935081220529421 := by
  unfold tailWord_5842808
  simp only [CollatzResearch.WordTrace]
  refine ⟨106552357508255981503424539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142069810011007975337899385 106552357508255981503424539)
  ·
    refine ⟨159828536262383972255136809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106552357508255981503424539 159828536262383972255136809)
    ·
      refine ⟨119871402196787979191352607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159828536262383972255136809 119871402196787979191352607)
      ·
        refine ⟨179807103295181968787028911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119871402196787979191352607 179807103295181968787028911)
        ·
          refine ⟨269710654942772953180543367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179807103295181968787028911 269710654942772953180543367)
          ·
            refine ⟨404565982414159429770815051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269710654942772953180543367 404565982414159429770815051)
            ·
              refine ⟨606848973621239144656222577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404565982414159429770815051 606848973621239144656222577)
              ·
                refine ⟨455136730215929358492166933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 606848973621239144656222577 455136730215929358492166933)
                ·
                  refine ⟨21334534228871688679320325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 455136730215929358492166933 21334534228871688679320325)
                  ·
                    refine ⟨4000225167913441627372561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21334534228871688679320325 4000225167913441627372561)
                    ·
                      refine ⟨3000168875935081220529421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4000225167913441627372561 3000168875935081220529421)
                      ·
                        rfl

theorem cell23_5842808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 6, 4, 2].length) (baseStart_5842808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842808 prefixEnd_5842808 := by exact prefixLift 5842808
  have htrace : WordTrace (prefixWord ++ tailWord_5842808) baseStart_5842808 baseEnd_5842808 := by
    simpa [prefixWord, tailWord_5842808, baseEnd_5842808] using wordTrace_append hprefix tailTrace_5842808
  have hstable : (prefixWord ++ tailWord_5842808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842808).length < 2 ^ (prefixWord ++ tailWord_5842808).sum := by decide
  have hdescent : baseEnd_5842808 < baseStart_5842808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842845 : List Nat := [1, 4, 2, 1, 2, 2, 2, 2, 2, 2, 3]
def baseStart_5842845 : Nat := 118140960795 + 5842845 * 2 ^ 59
def prefixEnd_5842845 : Nat := 4983230072969 + 3 ^ 40 * 5842845 * 2
def baseEnd_5842845 : Nat := 3000187874719297575766751

theorem tailTrace_5842845 : CollatzResearch.WordTrace tailWord_5842845 prefixEnd_5842845 3000187874719297575766751 := by
  unfold tailWord_5842845
  simp only [CollatzResearch.WordTrace]
  refine ⟨213106064517377918325945989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142070709678251945550630659 213106064517377918325945989)
  ·
    refine ⟨39957387097008359686114873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213106064517377918325945989 39957387097008359686114873)
    ·
      refine ⟨29968040322756269764586155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39957387097008359686114873 29968040322756269764586155)
      ·
        refine ⟨44952060484134404646879233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29968040322756269764586155 44952060484134404646879233)
        ·
          refine ⟨33714045363100803485159425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44952060484134404646879233 33714045363100803485159425)
          ·
            refine ⟨25285534022325602613869569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33714045363100803485159425 25285534022325602613869569)
            ·
              refine ⟨18964150516744201960402177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25285534022325602613869569 18964150516744201960402177)
              ·
                refine ⟨14223112887558151470301633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18964150516744201960402177 14223112887558151470301633)
                ·
                  refine ⟨10667334665668613602726225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14223112887558151470301633 10667334665668613602726225)
                  ·
                    refine ⟨8000500999251460202044669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10667334665668613602726225 8000500999251460202044669)
                    ·
                      refine ⟨3000187874719297575766751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8000500999251460202044669 3000187874719297575766751)
                      ·
                        rfl

theorem cell23_5842845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_5842845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842845 prefixEnd_5842845 := by exact prefixLift 5842845
  have htrace : WordTrace (prefixWord ++ tailWord_5842845) baseStart_5842845 baseEnd_5842845 := by
    simpa [prefixWord, tailWord_5842845, baseEnd_5842845] using wordTrace_append hprefix tailTrace_5842845
  have hstable : (prefixWord ++ tailWord_5842845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842845).length < 2 ^ (prefixWord ++ tailWord_5842845).sum := by decide
  have hdescent : baseEnd_5842845 < baseStart_5842845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842851 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 6]
def baseStart_5842851 : Nat := 118140960795 + 5842851 * 2 ^ 59
def prefixEnd_5842851 : Nat := 4983230072969 + 3 ^ 40 * 5842851 * 2
def baseEnd_5842851 : Nat := 3000190955603224552291723

theorem tailTrace_5842851 : CollatzResearch.WordTrace tailWord_5842851 prefixEnd_5842851 3000190955603224552291723 := by
  unfold tailWord_5842851
  simp only [CollatzResearch.WordTrace]
  refine ⟨213106283355356181350664407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142070855570237454233776271 213106283355356181350664407)
  ·
    refine ⟨319659425033034272025996611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213106283355356181350664407 319659425033034272025996611)
    ·
      refine ⟨479489137549551408038994917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319659425033034272025996611 479489137549551408038994917)
      ·
        refine ⟨89904213290540889007311547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 479489137549551408038994917 89904213290540889007311547)
        ·
          refine ⟨134856319935811333510967321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89904213290540889007311547 134856319935811333510967321)
          ·
            refine ⟨101142239951858500133225491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134856319935811333510967321 101142239951858500133225491)
            ·
              refine ⟨151713359927787750199838237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101142239951858500133225491 151713359927787750199838237)
              ·
                refine ⟨56892509972920406324939339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151713359927787750199838237 56892509972920406324939339)
                ·
                  refine ⟨85338764959380609487409009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56892509972920406324939339 85338764959380609487409009)
                  ·
                    refine ⟨64004073719535457115556757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85338764959380609487409009 64004073719535457115556757)
                    ·
                      refine ⟨3000190955603224552291723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64004073719535457115556757 3000190955603224552291723)
                      ·
                        rfl

theorem cell23_5842851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_5842851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842851 prefixEnd_5842851 := by exact prefixLift 5842851
  have htrace : WordTrace (prefixWord ++ tailWord_5842851) baseStart_5842851 baseEnd_5842851 := by
    simpa [prefixWord, tailWord_5842851, baseEnd_5842851] using wordTrace_append hprefix tailTrace_5842851
  have hstable : (prefixWord ++ tailWord_5842851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842851).length < 2 ^ (prefixWord ++ tailWord_5842851).sum := by decide
  have hdescent : baseEnd_5842851 < baseStart_5842851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842852 : List Nat := [2, 3, 1, 2, 1, 4, 1, 4, 1, 4]
def baseStart_5842852 : Nat := 118140960795 + 5842852 * 2 ^ 59
def prefixEnd_5842852 : Nat := 4983230072969 + 3 ^ 40 * 5842852 * 2
def baseEnd_5842852 : Nat := 1000063823027959682793073

theorem tailTrace_5842852 : CollatzResearch.WordTrace tailWord_5842852 prefixEnd_5842852 1000063823027959682793073 := by
  unfold tailWord_5842852
  simp only [CollatzResearch.WordTrace]
  refine ⟨106553159914176279260725405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142070879885568372347633873 106553159914176279260725405)
  ·
    refine ⟨39957434967816104722772027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106553159914176279260725405 39957434967816104722772027)
    ·
      refine ⟨59936152451724157084158041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39957434967816104722772027 59936152451724157084158041)
      ·
        refine ⟨44952114338793117813118531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59936152451724157084158041 44952114338793117813118531)
        ·
          refine ⟨67428171508189676719677797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44952114338793117813118531 67428171508189676719677797)
          ·
            refine ⟨12642782157785564384939587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67428171508189676719677797 12642782157785564384939587)
            ·
              refine ⟨18964173236678346577409381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12642782157785564384939587 18964173236678346577409381)
              ·
                refine ⟨3555782481877189983264259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18964173236678346577409381 3555782481877189983264259)
                ·
                  refine ⟨5333673722815784974896389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3555782481877189983264259 5333673722815784974896389)
                  ·
                    refine ⟨1000063823027959682793073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5333673722815784974896389 1000063823027959682793073)
                    ·
                      rfl

theorem cell23_5842852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_5842852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842852 prefixEnd_5842852 := by exact prefixLift 5842852
  have htrace : WordTrace (prefixWord ++ tailWord_5842852) baseStart_5842852 baseEnd_5842852 := by
    simpa [prefixWord, tailWord_5842852, baseEnd_5842852] using wordTrace_append hprefix tailTrace_5842852
  have hstable : (prefixWord ++ tailWord_5842852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842852).length < 2 ^ (prefixWord ++ tailWord_5842852).sum := by decide
  have hdescent : baseEnd_5842852 < baseStart_5842852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842871 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 7]
def baseStart_5842871 : Nat := 118140960795 + 5842871 * 2 ^ 59
def prefixEnd_5842871 : Nat := 4983230072969 + 3 ^ 40 * 5842871 * 2
def baseEnd_5842871 : Nat := 3000201225216314474041631

theorem tailTrace_5842871 : CollatzResearch.WordTrace tailWord_5842871 prefixEnd_5842871 3000201225216314474041631 := by
  unfold tailWord_5842871
  simp only [CollatzResearch.WordTrace]
  refine ⟨213107012815283724766392467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142071341876855816510928311 213107012815283724766392467)
  ·
    refine ⟨319660519222925587149588701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213107012815283724766392467 319660519222925587149588701)
    ·
      refine ⟨119872694708597095181095763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319660519222925587149588701 119872694708597095181095763)
      ·
        refine ⟨179809042062895642771643645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119872694708597095181095763 179809042062895642771643645)
        ·
          refine ⟨67428390773585866039366367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179809042062895642771643645 67428390773585866039366367)
          ·
            refine ⟨101142586160378799059049551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67428390773585866039366367 101142586160378799059049551)
            ·
              refine ⟨151713879240568198588574327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101142586160378799059049551 151713879240568198588574327)
              ·
                refine ⟨227570818860852297882861491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151713879240568198588574327 227570818860852297882861491)
                ·
                  refine ⟨341356228291278446824292237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227570818860852297882861491 341356228291278446824292237)
                  ·
                    refine ⟨128008585609229417559109589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 341356228291278446824292237 128008585609229417559109589)
                    ·
                      refine ⟨3000201225216314474041631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128008585609229417559109589 3000201225216314474041631)
                      ·
                        rfl

theorem cell23_5842871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_5842871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842871 prefixEnd_5842871 := by exact prefixLift 5842871
  have htrace : WordTrace (prefixWord ++ tailWord_5842871) baseStart_5842871 baseEnd_5842871 := by
    simpa [prefixWord, tailWord_5842871, baseEnd_5842871] using wordTrace_append hprefix tailTrace_5842871
  have hstable : (prefixWord ++ tailWord_5842871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842871).length < 2 ^ (prefixWord ++ tailWord_5842871).sum := by decide
  have hdescent : baseEnd_5842871 < baseStart_5842871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842885 : List Nat := [1, 3, 1, 1, 1, 1, 1, 7, 2, 3, 2]
def baseStart_5842885 : Nat := 118140960795 + 5842885 * 2 ^ 59
def prefixEnd_5842885 : Nat := 4983230072969 + 3 ^ 40 * 5842885 * 2
def baseEnd_5842885 : Nat := 3000208413945477419266567

theorem tailTrace_5842885 : CollatzResearch.WordTrace tailWord_5842885 prefixEnd_5842885 3000208413945477419266567 := by
  unfold tailWord_5842885
  simp only [CollatzResearch.WordTrace]
  refine ⟨213107523437233005157402109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142071682291488670104934739 213107523437233005157402109)
  ·
    refine ⟨79915321288962376934025791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213107523437233005157402109 79915321288962376934025791)
    ·
      refine ⟨119872981933443565401038687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79915321288962376934025791 119872981933443565401038687)
      ·
        refine ⟨179809472900165348101558031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119872981933443565401038687 179809472900165348101558031)
        ·
          refine ⟨269714209350248022152337047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179809472900165348101558031 269714209350248022152337047)
          ·
            refine ⟨404571314025372033228505571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269714209350248022152337047 404571314025372033228505571)
            ·
              refine ⟨606856971038058049842758357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404571314025372033228505571 606856971038058049842758357)
              ·
                refine ⟨14223210258704485543189649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 606856971038058049842758357 14223210258704485543189649)
                ·
                  refine ⟨10667407694028364157392237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14223210258704485543189649 10667407694028364157392237)
                  ·
                    refine ⟨4000277885260636559022089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10667407694028364157392237 4000277885260636559022089)
                    ·
                      refine ⟨3000208413945477419266567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4000277885260636559022089 3000208413945477419266567)
                      ·
                        rfl

theorem cell23_5842885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 3, 2].length) (baseStart_5842885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842885 prefixEnd_5842885 := by exact prefixLift 5842885
  have htrace : WordTrace (prefixWord ++ tailWord_5842885) baseStart_5842885 baseEnd_5842885 := by
    simpa [prefixWord, tailWord_5842885, baseEnd_5842885] using wordTrace_append hprefix tailTrace_5842885
  have hstable : (prefixWord ++ tailWord_5842885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842885).length < 2 ^ (prefixWord ++ tailWord_5842885).sum := by decide
  have hdescent : baseEnd_5842885 < baseStart_5842885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842909 : List Nat := [1, 4, 3, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_5842909 : Nat := 118140960795 + 5842909 * 2 ^ 59
def prefixEnd_5842909 : Nat := 4983230072969 + 3 ^ 40 * 5842909 * 2
def baseEnd_5842909 : Nat := 3000220737481185325366457

theorem tailTrace_5842909 : CollatzResearch.WordTrace tailWord_5842909 prefixEnd_5842909 3000220737481185325366457 := by
  unfold tailWord_5842909
  simp only [CollatzResearch.WordTrace]
  refine ⟨213108398789146057256275781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142072265859430704837517187 213108398789146057256275781)
  ·
    refine ⟨39957824772964885735551709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213108398789146057256275781 39957824772964885735551709)
    ·
      refine ⟨14984184289861832150831891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39957824772964885735551709 14984184289861832150831891)
      ·
        refine ⟨22476276434792748226247837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14984184289861832150831891 22476276434792748226247837)
        ·
          refine ⟨8428603663047280584842939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22476276434792748226247837 8428603663047280584842939)
          ·
            refine ⟨12642905494570920877264409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8428603663047280584842939 12642905494570920877264409)
            ·
              refine ⟨9482179120928190657948307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12642905494570920877264409 9482179120928190657948307)
              ·
                refine ⟨14223268681392285986922461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9482179120928190657948307 14223268681392285986922461)
                ·
                  refine ⟨5333725755522107245095923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14223268681392285986922461 5333725755522107245095923)
                  ·
                    refine ⟨8000588633283160867643885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5333725755522107245095923 8000588633283160867643885)
                    ·
                      refine ⟨3000220737481185325366457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8000588633283160867643885 3000220737481185325366457)
                      ·
                        rfl

theorem cell23_5842909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_5842909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842909 prefixEnd_5842909 := by exact prefixLift 5842909
  have htrace : WordTrace (prefixWord ++ tailWord_5842909) baseStart_5842909 baseEnd_5842909 := by
    simpa [prefixWord, tailWord_5842909, baseEnd_5842909] using wordTrace_append hprefix tailTrace_5842909
  have hstable : (prefixWord ++ tailWord_5842909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842909).length < 2 ^ (prefixWord ++ tailWord_5842909).sum := by decide
  have hdescent : baseEnd_5842909 < baseStart_5842909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842942 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 4, 4]
def baseStart_5842942 : Nat := 118140960795 + 5842942 * 2 ^ 59
def prefixEnd_5842942 : Nat := 4983230072969 + 3 ^ 40 * 5842942 * 2
def baseEnd_5842942 : Nat := 1000079227447594565417935

theorem tailTrace_5842942 : CollatzResearch.WordTrace tailWord_5842942 prefixEnd_5842942 1000079227447594565417935 := by
  unfold tailWord_5842942
  simp only [CollatzResearch.WordTrace]
  refine ⟨26638700299753312986528385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142073068265351002594818053 26638700299753312986528385)
  ·
    refine ⟨19979025224814984739896289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26638700299753312986528385 19979025224814984739896289)
    ·
      refine ⟨14984268918611238554922217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19979025224814984739896289 14984268918611238554922217)
      ·
        refine ⟨11238201688958428916191663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14984268918611238554922217 11238201688958428916191663)
        ·
          refine ⟨16857302533437643374287495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11238201688958428916191663 16857302533437643374287495)
          ·
            refine ⟨25285953800156465061431243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16857302533437643374287495 25285953800156465061431243)
            ·
              refine ⟨37928930700234697592146865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25285953800156465061431243 37928930700234697592146865)
              ·
                refine ⟨28446698025176023194110149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37928930700234697592146865 28446698025176023194110149)
                ·
                  refine ⟨5333755879720504348895653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28446698025176023194110149 5333755879720504348895653)
                  ·
                    refine ⟨1000079227447594565417935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5333755879720504348895653 1000079227447594565417935)
                    ·
                      rfl

theorem cell23_5842942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_5842942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842942 prefixEnd_5842942 := by exact prefixLift 5842942
  have htrace : WordTrace (prefixWord ++ tailWord_5842942) baseStart_5842942 baseEnd_5842942 := by
    simpa [prefixWord, tailWord_5842942, baseEnd_5842942] using wordTrace_append hprefix tailTrace_5842942
  have hstable : (prefixWord ++ tailWord_5842942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842942).length < 2 ^ (prefixWord ++ tailWord_5842942).sum := by decide
  have hdescent : baseEnd_5842942 < baseStart_5842942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842968 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 2, 7]
def baseStart_5842968 : Nat := 118140960795 + 5842968 * 2 ^ 59
def prefixEnd_5842968 : Nat := 4983230072969 + 3 ^ 40 * 5842968 * 2
def baseEnd_5842968 : Nat := 1000083677613266864842895

theorem tailTrace_5842968 : CollatzResearch.WordTrace tailWord_5842968 prefixEnd_5842968 1000083677613266864842895 := by
  unfold tailWord_5842968
  simp only [CollatzResearch.WordTrace]
  refine ⟨106555275347966155166336779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142073700463954873555115705 106555275347966155166336779)
  ·
    refine ⟨159832913021949232749505169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106555275347966155166336779 159832913021949232749505169)
    ·
      refine ⟨119874684766461924562128877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159832913021949232749505169 119874684766461924562128877)
      ·
        refine ⟨44953006787423221710798329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119874684766461924562128877 44953006787423221710798329)
        ·
          refine ⟨33714755090567416283098747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44953006787423221710798329 33714755090567416283098747)
          ·
            refine ⟨50572132635851124424648121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33714755090567416283098747 50572132635851124424648121)
            ·
              refine ⟨37929099476888343318486091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50572132635851124424648121 37929099476888343318486091)
              ·
                refine ⟨56893649215332514977729137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37929099476888343318486091 56893649215332514977729137)
                ·
                  refine ⟨42670236911499386233296853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56893649215332514977729137 42670236911499386233296853)
                  ·
                    refine ⟨1000083677613266864842895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42670236911499386233296853 1000083677613266864842895)
                    ·
                      rfl

theorem cell23_5842968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_5842968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842968 prefixEnd_5842968 := by exact prefixLift 5842968
  have htrace : WordTrace (prefixWord ++ tailWord_5842968) baseStart_5842968 baseEnd_5842968 := by
    simpa [prefixWord, tailWord_5842968, baseEnd_5842968] using wordTrace_append hprefix tailTrace_5842968
  have hstable : (prefixWord ++ tailWord_5842968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842968).length < 2 ^ (prefixWord ++ tailWord_5842968).sum := by decide
  have hdescent : baseEnd_5842968 < baseStart_5842968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842988 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 4]
def baseStart_5842988 : Nat := 118140960795 + 5842988 * 2 ^ 59
def prefixEnd_5842988 : Nat := 4983230072969 + 3 ^ 40 * 5842988 * 2
def baseEnd_5842988 : Nat := 3000261302452890516278593

theorem tailTrace_5842988 : CollatzResearch.WordTrace tailWord_5842988 prefixEnd_5842988 3000261302452890516278593 := by
  unfold tailWord_5842988
  simp only [CollatzResearch.WordTrace]
  refine ⟨106555640077929926874200809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142074186770573235832267745 106555640077929926874200809)
  ·
    refine ⟨79916730058447445155650607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106555640077929926874200809 79916730058447445155650607)
    ·
      refine ⟨119875095087671167733475911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79916730058447445155650607 119875095087671167733475911)
      ·
        refine ⟨179812642631506751600213867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119875095087671167733475911 179812642631506751600213867)
        ·
          refine ⟨269718963947260127400320801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179812642631506751600213867 269718963947260127400320801)
          ·
            refine ⟨202289222960445095550240601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269718963947260127400320801 202289222960445095550240601)
            ·
              refine ⟨151716917220333821662680451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202289222960445095550240601 151716917220333821662680451)
              ·
                refine ⟨227575375830500732494020677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151716917220333821662680451 227575375830500732494020677)
                ·
                  refine ⟨42670382968218887342628877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 227575375830500732494020677 42670382968218887342628877)
                  ·
                    refine ⟨16001393613082082753485829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42670382968218887342628877 16001393613082082753485829)
                    ·
                      refine ⟨3000261302452890516278593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16001393613082082753485829 3000261302452890516278593)
                      ·
                        rfl

theorem cell23_5842988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_5842988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842988 prefixEnd_5842988 := by exact prefixLift 5842988
  have htrace : WordTrace (prefixWord ++ tailWord_5842988) baseStart_5842988 baseEnd_5842988 := by
    simpa [prefixWord, tailWord_5842988, baseEnd_5842988] using wordTrace_append hprefix tailTrace_5842988
  have hstable : (prefixWord ++ tailWord_5842988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842988).length < 2 ^ (prefixWord ++ tailWord_5842988).sum := by decide
  have hdescent : baseEnd_5842988 < baseStart_5842988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842992 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 3, 3, 2]
def baseStart_5842992 : Nat := 118140960795 + 5842992 * 2 ^ 59
def prefixEnd_5842992 : Nat := 4983230072969 + 3 ^ 40 * 5842992 * 2
def baseEnd_5842992 : Nat := 3000263356375508500628575

theorem tailTrace_5842992 : CollatzResearch.WordTrace tailWord_5842992 prefixEnd_5842992 3000263356375508500628575 := by
  unfold tailWord_5842992
  simp only [CollatzResearch.WordTrace]
  refine ⟨106555713023922681215773615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142074284031896908287698153 106555713023922681215773615)
  ·
    refine ⟨159833569535884021823660423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106555713023922681215773615 159833569535884021823660423)
    ·
      refine ⟨239750354303826032735490635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159833569535884021823660423 239750354303826032735490635)
      ·
        refine ⟨359625531455739049103235953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239750354303826032735490635 359625531455739049103235953)
        ·
          refine ⟨269719148591804286827426965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359625531455739049103235953 269719148591804286827426965)
          ·
            refine ⟨12643085090240825945035639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 269719148591804286827426965 12643085090240825945035639)
            ·
              refine ⟨18964627635361238917553459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12643085090240825945035639 18964627635361238917553459)
              ·
                refine ⟨28446941453041858376330189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18964627635361238917553459 28446941453041858376330189)
                ·
                  refine ⟨10667603044890696891123821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28446941453041858376330189 10667603044890696891123821)
                  ·
                    refine ⟨4000351141834011334171433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10667603044890696891123821 4000351141834011334171433)
                    ·
                      refine ⟨3000263356375508500628575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4000351141834011334171433 3000263356375508500628575)
                      ·
                        rfl

theorem cell23_5842992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 3, 3, 2].length) (baseStart_5842992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842992 prefixEnd_5842992 := by exact prefixLift 5842992
  have htrace : WordTrace (prefixWord ++ tailWord_5842992) baseStart_5842992 baseEnd_5842992 := by
    simpa [prefixWord, tailWord_5842992, baseEnd_5842992] using wordTrace_append hprefix tailTrace_5842992
  have hstable : (prefixWord ++ tailWord_5842992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842992).length < 2 ^ (prefixWord ++ tailWord_5842992).sum := by decide
  have hdescent : baseEnd_5842992 < baseStart_5842992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843018 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_5843018 : Nat := 118140960795 + 5843018 * 2 ^ 59
def prefixEnd_5843018 : Nat := 4983230072969 + 3 ^ 40 * 5843018 * 2
def baseEnd_5843018 : Nat := 3000276706872525398903455

theorem tailTrace_5843018 : CollatzResearch.WordTrace tailWord_5843018 prefixEnd_5843018 3000276706872525398903455 := by
  unfold tailWord_5843018
  simp only [CollatzResearch.WordTrace]
  refine ⟨53278093586437792217998427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142074916230500779247995805 53278093586437792217998427)
  ·
    refine ⟨79917140379656688326997641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53278093586437792217998427 79917140379656688326997641)
    ·
      refine ⟨59937855284742516245248231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79917140379656688326997641 59937855284742516245248231)
      ·
        refine ⟨89906782927113774367872347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59937855284742516245248231 89906782927113774367872347)
        ·
          refine ⟨134860174390670661551808521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89906782927113774367872347 134860174390670661551808521)
          ·
            refine ⟨101145130793002996163856391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134860174390670661551808521 101145130793002996163856391)
            ·
              refine ⟨151717696189504494245784587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101145130793002996163856391 151717696189504494245784587)
              ·
                refine ⟨227576544284256741368676881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151717696189504494245784587 227576544284256741368676881)
                ·
                  refine ⟨170682408213192556026507661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227576544284256741368676881 170682408213192556026507661)
                  ·
                    refine ⟨64005903079947208509940373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 170682408213192556026507661 64005903079947208509940373)
                    ·
                      refine ⟨3000276706872525398903455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64005903079947208509940373 3000276706872525398903455)
                      ·
                        rfl

theorem cell23_5843018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_5843018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843018 prefixEnd_5843018 := by exact prefixLift 5843018
  have htrace : WordTrace (prefixWord ++ tailWord_5843018) baseStart_5843018 baseEnd_5843018 := by
    simpa [prefixWord, tailWord_5843018, baseEnd_5843018] using wordTrace_append hprefix tailTrace_5843018
  have hstable : (prefixWord ++ tailWord_5843018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843018).length < 2 ^ (prefixWord ++ tailWord_5843018).sum := by decide
  have hdescent : baseEnd_5843018 < baseStart_5843018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843045 : List Nat := [1, 3, 1, 3, 2, 3, 1, 2, 7]
def baseStart_5843045 : Nat := 118140960795 + 5843045 * 2 ^ 59
def prefixEnd_5843045 : Nat := 4983230072969 + 3 ^ 40 * 5843045 * 2
def baseEnd_5843045 : Nat := 333365618983355199251759

theorem tailTrace_5843045 : CollatzResearch.WordTrace tailWord_5843045 prefixEnd_5843045 333365618983355199251759 := by
  unfold tailWord_5843045
  simp only [CollatzResearch.WordTrace]
  refine ⟨213113359116653352483226589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142075572744435568322151059 213113359116653352483226589)
  ·
    refine ⟨79917509668745007181209971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213113359116653352483226589 79917509668745007181209971)
    ·
      refine ⟨119876264503117510771814957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79917509668745007181209971 119876264503117510771814957)
      ·
        refine ⟨44953599188669066539430609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119876264503117510771814957 44953599188669066539430609)
        ·
          refine ⟨33715199391501799904572957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44953599188669066539430609 33715199391501799904572957)
          ·
            refine ⟨12643199771813174964214859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33715199391501799904572957 12643199771813174964214859)
            ·
              refine ⟨18964799657719762446322289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12643199771813174964214859 18964799657719762446322289)
              ·
                refine ⟨14223599743289821834741717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18964799657719762446322289 14223599743289821834741717)
                ·
                  refine ⟨333365618983355199251759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14223599743289821834741717 333365618983355199251759)
                  ·
                    rfl

theorem cell23_5843045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 7].length) (baseStart_5843045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843045 prefixEnd_5843045 := by exact prefixLift 5843045
  have htrace : WordTrace (prefixWord ++ tailWord_5843045) baseStart_5843045 baseEnd_5843045 := by
    simpa [prefixWord, tailWord_5843045, baseEnd_5843045] using wordTrace_append hprefix tailTrace_5843045
  have hstable : (prefixWord ++ tailWord_5843045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843045).length < 2 ^ (prefixWord ++ tailWord_5843045).sum := by decide
  have hdescent : baseEnd_5843045 < baseStart_5843045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843073 : List Nat := [1, 2, 4, 2, 3, 2, 1, 2, 2, 2, 2]
def baseStart_5843073 : Nat := 118140960795 + 5843073 * 2 ^ 59
def prefixEnd_5843073 : Nat := 4983230072969 + 3 ^ 40 * 5843073 * 2
def baseEnd_5843073 : Nat := 3000304948308522683715703

theorem tailTrace_5843073 : CollatzResearch.WordTrace tailWord_5843073 prefixEnd_5843073 3000304948308522683715703 := by
  unfold tailWord_5843073
  simp only [CollatzResearch.WordTrace]
  refine ⟨213114380360551913265245873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142076253573701275510163915 213114380360551913265245873)
  ·
    refine ⟨159835785270413934948934405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213114380360551913265245873 159835785270413934948934405)
    ·
      refine ⟨29969209738202612802925201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159835785270413934948934405 29969209738202612802925201)
      ·
        refine ⟨22476907303651959602193901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29969209738202612802925201 22476907303651959602193901)
        ·
          refine ⟨8428840238869484850822713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22476907303651959602193901 8428840238869484850822713)
          ·
            refine ⟨6321630179152113638117035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8428840238869484850822713 6321630179152113638117035)
            ·
              refine ⟨9482445268728170457175553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6321630179152113638117035 9482445268728170457175553)
              ·
                refine ⟨7111833951546127842881665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9482445268728170457175553 7111833951546127842881665)
                ·
                  refine ⟨5333875463659595882161249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7111833951546127842881665 5333875463659595882161249)
                  ·
                    refine ⟨4000406597744696911620937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5333875463659595882161249 4000406597744696911620937)
                    ·
                      refine ⟨3000304948308522683715703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4000406597744696911620937 3000304948308522683715703)
                      ·
                        rfl

theorem cell23_5843073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_5843073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843073 prefixEnd_5843073 := by exact prefixLift 5843073
  have htrace : WordTrace (prefixWord ++ tailWord_5843073) baseStart_5843073 baseEnd_5843073 := by
    simpa [prefixWord, tailWord_5843073, baseEnd_5843073] using wordTrace_append hprefix tailTrace_5843073
  have hstable : (prefixWord ++ tailWord_5843073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843073).length < 2 ^ (prefixWord ++ tailWord_5843073).sum := by decide
  have hdescent : baseEnd_5843073 < baseStart_5843073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843135 : List Nat := [1, 1, 2, 2, 2, 2, 1, 6, 6]
def baseStart_5843135 : Nat := 118140960795 + 5843135 * 2 ^ 59
def prefixEnd_5843135 : Nat := 4983230072969 + 3 ^ 40 * 5843135 * 2
def baseEnd_5843135 : Nat := 333370753789900160126713

theorem tailTrace_5843135 : CollatzResearch.WordTrace tailWord_5843135 prefixEnd_5843135 333370753789900160126713 := by
  unfold tailWord_5843135
  simp only [CollatzResearch.WordTrace]
  refine ⟨213116641686327297854002859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142077761124218198569335239 213116641686327297854002859)
  ·
    refine ⟨319674962529490946781004289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213116641686327297854002859 319674962529490946781004289)
    ·
      refine ⟨239756221897118210085753217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319674962529490946781004289 239756221897118210085753217)
      ·
        refine ⟨179817166422838657564314913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239756221897118210085753217 179817166422838657564314913)
        ·
          refine ⟨134862874817128993173236185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179817166422838657564314913 134862874817128993173236185)
          ·
            refine ⟨101147156112846744879927139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134862874817128993173236185 101147156112846744879927139)
            ·
              refine ⟨151720734169270117319890709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101147156112846744879927139 151720734169270117319890709)
              ·
                refine ⟨7111909414184536749369877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 151720734169270117319890709 7111909414184536749369877)
                ·
                  refine ⟨333370753789900160126713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7111909414184536749369877 333370753789900160126713)
                  ·
                    rfl

theorem cell23_5843135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 6].length) (baseStart_5843135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843135 prefixEnd_5843135 := by exact prefixLift 5843135
  have htrace : WordTrace (prefixWord ++ tailWord_5843135) baseStart_5843135 baseEnd_5843135 := by
    simpa [prefixWord, tailWord_5843135, baseEnd_5843135] using wordTrace_append hprefix tailTrace_5843135
  have hstable : (prefixWord ++ tailWord_5843135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843135).length < 2 ^ (prefixWord ++ tailWord_5843135).sum := by decide
  have hdescent : baseEnd_5843135 < baseStart_5843135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843145 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 2, 5, 3]
def baseStart_5843145 : Nat := 118140960795 + 5843145 * 2 ^ 59
def prefixEnd_5843145 : Nat := 4983230072969 + 3 ^ 40 * 5843145 * 2
def baseEnd_5843145 : Nat := 3000341918915646402015371

theorem tailTrace_5843145 : CollatzResearch.WordTrace tailWord_5843145 prefixEnd_5843145 3000341918915646402015371 := by
  unfold tailWord_5843145
  simp only [CollatzResearch.WordTrace]
  refine ⟨213117006416291069561866889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142078004277527379707911259 213117006416291069561866889)
  ·
    refine ⟨159837754812218302171400167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213117006416291069561866889 159837754812218302171400167)
    ·
      refine ⟨239756632218327453257100251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159837754812218302171400167 239756632218327453257100251)
      ·
        refine ⟨359634948327491179885650377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239756632218327453257100251 359634948327491179885650377)
        ·
          refine ⟨269726211245618384914237783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359634948327491179885650377 269726211245618384914237783)
          ·
            refine ⟨404589316868427577371356675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269726211245618384914237783 404589316868427577371356675)
            ·
              refine ⟨606883975302641366057035013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404589316868427577371356675 606883975302641366057035013)
              ·
                refine ⟨113790745369245256135694065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 606883975302641366057035013 113790745369245256135694065)
                ·
                  refine ⟨85343059026933942101770549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113790745369245256135694065 85343059026933942101770549)
                  ·
                    refine ⟨8000911783775057072040989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85343059026933942101770549 8000911783775057072040989)
                    ·
                      refine ⟨3000341918915646402015371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8000911783775057072040989 3000341918915646402015371)
                      ·
                        rfl

theorem cell23_5843145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 5, 3].length) (baseStart_5843145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843145 prefixEnd_5843145 := by exact prefixLift 5843145
  have htrace : WordTrace (prefixWord ++ tailWord_5843145) baseStart_5843145 baseEnd_5843145 := by
    simpa [prefixWord, tailWord_5843145, baseEnd_5843145] using wordTrace_append hprefix tailTrace_5843145
  have hstable : (prefixWord ++ tailWord_5843145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843145).length < 2 ^ (prefixWord ++ tailWord_5843145).sum := by decide
  have hdescent : baseEnd_5843145 < baseStart_5843145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843212 : List Nat := [2, 2, 1, 2, 2, 2, 4, 1, 1, 6]
def baseStart_5843212 : Nat := 118140960795 + 5843212 * 2 ^ 59
def prefixEnd_5843212 : Nat := 4983230072969 + 3 ^ 40 * 5843212 * 2
def baseEnd_5843212 : Nat := 1000125440706499213292521

theorem tailTrace_5843212 : CollatzResearch.WordTrace tailWord_5843212 prefixEnd_5843212 1000125440706499213292521 := by
  unfold tailWord_5843212
  simp only [CollatzResearch.WordTrace]
  refine ⟨106559725053524170002277945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142079633404698893336370593 106559725053524170002277945)
  ·
    refine ⟨79919793790143127501708459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106559725053524170002277945 79919793790143127501708459)
    ·
      refine ⟨119879690685214691252562689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79919793790143127501708459 119879690685214691252562689)
      ·
        refine ⟨89909768013911018439422017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119879690685214691252562689 89909768013911018439422017)
        ·
          refine ⟨67432326010433263829566513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89909768013911018439422017 67432326010433263829566513)
          ·
            refine ⟨50574244507824947872174885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67432326010433263829566513 50574244507824947872174885)
            ·
              refine ⟨9482670845217177726032791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50574244507824947872174885 9482670845217177726032791)
              ·
                refine ⟨14224006267825766589049187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9482670845217177726032791 14224006267825766589049187)
                ·
                  refine ⟨21336009401738649883573781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14224006267825766589049187 21336009401738649883573781)
                  ·
                    refine ⟨1000125440706499213292521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21336009401738649883573781 1000125440706499213292521)
                    ·
                      rfl

theorem cell23_5843212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 1, 6].length) (baseStart_5843212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843212 prefixEnd_5843212 := by exact prefixLift 5843212
  have htrace : WordTrace (prefixWord ++ tailWord_5843212) baseStart_5843212 baseEnd_5843212 := by
    simpa [prefixWord, tailWord_5843212, baseEnd_5843212] using wordTrace_append hprefix tailTrace_5843212
  have hstable : (prefixWord ++ tailWord_5843212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843212).length < 2 ^ (prefixWord ++ tailWord_5843212).sum := by decide
  have hdescent : baseEnd_5843212 < baseStart_5843212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843215 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 6]
def baseStart_5843215 : Nat := 118140960795 + 5843215 * 2 ^ 59
def prefixEnd_5843215 : Nat := 4983230072969 + 3 ^ 40 * 5843215 * 2
def baseEnd_5843215 : Nat := 3000377862561461128140049

theorem tailTrace_5843215 : CollatzResearch.WordTrace tailWord_5843215 prefixEnd_5843215 3000377862561461128140049 := by
  unfold tailWord_5843215
  simp only [CollatzResearch.WordTrace]
  refine ⟨213119559526037471516915099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142079706350691647677943399 213119559526037471516915099)
  ·
    refine ⟨319679339289056207275372649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213119559526037471516915099 319679339289056207275372649)
    ·
      refine ⟨239759504466792155456529487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319679339289056207275372649 239759504466792155456529487)
      ·
        refine ⟨359639256700188233184794231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239759504466792155456529487 359639256700188233184794231)
        ·
          refine ⟨539458885050282349777191347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359639256700188233184794231 539458885050282349777191347)
          ·
            refine ⟨809188327575423524665787021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539458885050282349777191347 809188327575423524665787021)
            ·
              refine ⟨303445622840783821749670133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 809188327575423524665787021 303445622840783821749670133)
              ·
                refine ⟨28448027141323483289031575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 303445622840783821749670133 28448027141323483289031575)
                ·
                  refine ⟨42672040711985224933547363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28448027141323483289031575 42672040711985224933547363)
                  ·
                    refine ⟨64008061067977837400321045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42672040711985224933547363 64008061067977837400321045)
                    ·
                      refine ⟨3000377862561461128140049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64008061067977837400321045 3000377862561461128140049)
                      ·
                        rfl

theorem cell23_5843215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 6].length) (baseStart_5843215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843215 prefixEnd_5843215 := by exact prefixLift 5843215
  have htrace : WordTrace (prefixWord ++ tailWord_5843215) baseStart_5843215 baseEnd_5843215 := by
    simpa [prefixWord, tailWord_5843215, baseEnd_5843215] using wordTrace_append hprefix tailTrace_5843215
  have hstable : (prefixWord ++ tailWord_5843215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843215).length < 2 ^ (prefixWord ++ tailWord_5843215).sum := by decide
  have hdescent : baseEnd_5843215 < baseStart_5843215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843230 : List Nat := [4, 3, 2, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_5843230 : Nat := 118140960795 + 5843230 * 2 ^ 59
def prefixEnd_5843230 : Nat := 4983230072969 + 3 ^ 40 * 5843230 * 2
def baseEnd_5843230 : Nat := 3000385564771278569452481

theorem tailTrace_5843230 : CollatzResearch.WordTrace tailWord_5843230 prefixEnd_5843230 3000385564771278569452481 := by
  unfold tailWord_5843230
  simp only [CollatzResearch.WordTrace]
  refine ⟨26640013327622891134838893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142080071080655419385807429 26640013327622891134838893)
  ·
    refine ⟨9990004997858584175564585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26640013327622891134838893 9990004997858584175564585)
    ·
      refine ⟨7492503748393938131673439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9990004997858584175564585 7492503748393938131673439)
      ·
        refine ⟨11238755622590907197510159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7492503748393938131673439 11238755622590907197510159)
        ·
          refine ⟨16858133433886360796265239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11238755622590907197510159 16858133433886360796265239)
          ·
            refine ⟨25287200150829541194397859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16858133433886360796265239 25287200150829541194397859)
            ·
              refine ⟨37930800226244311791596789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25287200150829541194397859 37930800226244311791596789)
              ·
                refine ⟨3556012521210404230462199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37930800226244311791596789 3556012521210404230462199)
                ·
                  refine ⟨5334018781815606345693299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3556012521210404230462199 5334018781815606345693299)
                  ·
                    refine ⟨8001028172723409518539949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5334018781815606345693299 8001028172723409518539949)
                    ·
                      refine ⟨3000385564771278569452481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8001028172723409518539949 3000385564771278569452481)
                      ·
                        rfl

theorem cell23_5843230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_5843230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843230 prefixEnd_5843230 := by exact prefixLift 5843230
  have htrace : WordTrace (prefixWord ++ tailWord_5843230) baseStart_5843230 baseEnd_5843230 := by
    simpa [prefixWord, tailWord_5843230, baseEnd_5843230] using wordTrace_append hprefix tailTrace_5843230
  have hstable : (prefixWord ++ tailWord_5843230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843230).length < 2 ^ (prefixWord ++ tailWord_5843230).sum := by decide
  have hdescent : baseEnd_5843230 < baseStart_5843230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843236 : List Nat := [2, 3, 1, 3, 1, 2, 4, 1, 1, 1, 4]
def baseStart_5843236 : Nat := 118140960795 + 5843236 * 2 ^ 59
def prefixEnd_5843236 : Nat := 4983230072969 + 3 ^ 40 * 5843236 * 2
def baseEnd_5843236 : Nat := 3000388645655205545977453

theorem tailTrace_5843236 : CollatzResearch.WordTrace tailWord_5843236 prefixEnd_5843236 3000388645655205545977453 := by
  unfold tailWord_5843236
  simp only [CollatzResearch.WordTrace]
  refine ⟨106560162729480696051714781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142080216972640928068953041 106560162729480696051714781)
  ·
    refine ⟨39960061023555261019393043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106560162729480696051714781 39960061023555261019393043)
    ·
      refine ⟨59940091535332891529089565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39960061023555261019393043 59940091535332891529089565)
      ·
        refine ⟨22477534325749834323408587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59940091535332891529089565 22477534325749834323408587)
        ·
          refine ⟨33716301488624751485112881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22477534325749834323408587 33716301488624751485112881)
          ·
            refine ⟨25287226116468563613834661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33716301488624751485112881 25287226116468563613834661)
            ·
              refine ⟨4741354896837855677593999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25287226116468563613834661 4741354896837855677593999)
              ·
                refine ⟨7112032345256783516390999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4741354896837855677593999 7112032345256783516390999)
                ·
                  refine ⟨10668048517885175274586499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7112032345256783516390999 10668048517885175274586499)
                  ·
                    refine ⟨16002072776827762911879749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10668048517885175274586499 16002072776827762911879749)
                    ·
                      refine ⟨3000388645655205545977453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16002072776827762911879749 3000388645655205545977453)
                      ·
                        rfl

theorem cell23_5843236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_5843236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843236 prefixEnd_5843236 := by exact prefixLift 5843236
  have htrace : WordTrace (prefixWord ++ tailWord_5843236) baseStart_5843236 baseEnd_5843236 := by
    simpa [prefixWord, tailWord_5843236, baseEnd_5843236] using wordTrace_append hprefix tailTrace_5843236
  have hstable : (prefixWord ++ tailWord_5843236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843236).length < 2 ^ (prefixWord ++ tailWord_5843236).sum := by decide
  have hdescent : baseEnd_5843236 < baseStart_5843236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843253 : List Nat := [1, 3, 3, 1, 2, 1, 1, 6, 1, 2, 2]
def baseStart_5843253 : Nat := 118140960795 + 5843253 * 2 ^ 59
def prefixEnd_5843253 : Nat := 4983230072969 + 3 ^ 40 * 5843253 * 2
def baseEnd_5843253 : Nat := 3000397374826331979464875

theorem tailTrace_5843253 : CollatzResearch.WordTrace tailWord_5843253 prefixEnd_5843253 3000397374826331979464875 := by
  unfold tailWord_5843253
  simp only [CollatzResearch.WordTrace]
  refine ⟨213120945499899804006798413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142080630333266536004532275 213120945499899804006798413)
  ·
    refine ⟨79920354562462426502549405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213120945499899804006798413 79920354562462426502549405)
    ·
      refine ⟨29970132960923409938456027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79920354562462426502549405 29970132960923409938456027)
      ·
        refine ⟨44955199441385114907684041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29970132960923409938456027 44955199441385114907684041)
        ·
          refine ⟨33716399581038836180763031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44955199441385114907684041 33716399581038836180763031)
          ·
            refine ⟨50574599371558254271144547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33716399581038836180763031 50574599371558254271144547)
            ·
              refine ⟨75861899057337381406716821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50574599371558254271144547 75861899057337381406716821)
              ·
                refine ⟨3556026518312689753439851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75861899057337381406716821 3556026518312689753439851)
                ·
                  refine ⟨5334039777469034630159777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3556026518312689753439851 5334039777469034630159777)
                  ·
                    refine ⟨4000529833101775972619833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5334039777469034630159777 4000529833101775972619833)
                    ·
                      refine ⟨3000397374826331979464875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4000529833101775972619833 3000397374826331979464875)
                      ·
                        rfl

theorem cell23_5843253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_5843253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843253 prefixEnd_5843253 := by exact prefixLift 5843253
  have htrace : WordTrace (prefixWord ++ tailWord_5843253) baseStart_5843253 baseEnd_5843253 := by
    simpa [prefixWord, tailWord_5843253, baseEnd_5843253] using wordTrace_append hprefix tailTrace_5843253
  have hstable : (prefixWord ++ tailWord_5843253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843253).length < 2 ^ (prefixWord ++ tailWord_5843253).sum := by decide
  have hdescent : baseEnd_5843253 < baseStart_5843253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843255 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 1, 9]
def baseStart_5843255 : Nat := 118140960795 + 5843255 * 2 ^ 59
def prefixEnd_5843255 : Nat := 4983230072969 + 3 ^ 40 * 5843255 * 2
def baseEnd_5843255 : Nat := 1000132800595880323879955

theorem tailTrace_5843255 : CollatzResearch.WordTrace tailWord_5843255 prefixEnd_5843255 1000132800595880323879955 := by
  unfold tailWord_5843255
  simp only [CollatzResearch.WordTrace]
  refine ⟨213121018445892558348371219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142080678963928372232247479 213121018445892558348371219)
  ·
    refine ⟨319681527668838837522556829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213121018445892558348371219 319681527668838837522556829)
    ·
      refine ⟨119880572875814564070958811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319681527668838837522556829 119880572875814564070958811)
      ·
        refine ⟨179820859313721846106438217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119880572875814564070958811 179820859313721846106438217)
        ·
          refine ⟨134865644485291384579828663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179820859313721846106438217 134865644485291384579828663)
          ·
            refine ⟨202298466727937076869742995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134865644485291384579828663 202298466727937076869742995)
            ·
              refine ⟨303447700091905615304614493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202298466727937076869742995 303447700091905615304614493)
              ·
                refine ⟨113792887534464605739230435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303447700091905615304614493 113792887534464605739230435)
                ·
                  refine ⟨170689331301696908608845653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113792887534464605739230435 170689331301696908608845653)
                  ·
                    refine ⟨1000132800595880323879955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 170689331301696908608845653 1000132800595880323879955)
                    ·
                      rfl

theorem cell23_5843255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_5843255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843255 prefixEnd_5843255 := by exact prefixLift 5843255
  have htrace : WordTrace (prefixWord ++ tailWord_5843255) baseStart_5843255 baseEnd_5843255 := by
    simpa [prefixWord, tailWord_5843255, baseEnd_5843255] using wordTrace_append hprefix tailTrace_5843255
  have hstable : (prefixWord ++ tailWord_5843255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843255).length < 2 ^ (prefixWord ++ tailWord_5843255).sum := by decide
  have hdescent : baseEnd_5843255 < baseStart_5843255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843275 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 8]
def baseStart_5843275 : Nat := 118140960795 + 5843275 * 2 ^ 59
def prefixEnd_5843275 : Nat := 4983230072969 + 3 ^ 40 * 5843275 * 2
def baseEnd_5843275 : Nat := 3000408671400730893389773

theorem tailTrace_5843275 : CollatzResearch.WordTrace tailWord_5843275 prefixEnd_5843275 3000408671400730893389773 := by
  unfold tailWord_5843275
  simp only [CollatzResearch.WordTrace]
  refine ⟨213121747905820101764099279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142081165270546734509399519 213121747905820101764099279)
  ·
    refine ⟨319682621858730152646148919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213121747905820101764099279 319682621858730152646148919)
    ·
      refine ⟨479523932788095228969223379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319682621858730152646148919 479523932788095228969223379)
      ·
        refine ⟨719285899182142843453835069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479523932788095228969223379 719285899182142843453835069)
        ·
          refine ⟨269732212193303566295188151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 719285899182142843453835069 269732212193303566295188151)
          ·
            refine ⟨404598318289955349442782227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269732212193303566295188151 404598318289955349442782227)
            ·
              refine ⟨606897477434933024164173341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404598318289955349442782227 606897477434933024164173341)
              ·
                refine ⟨227586554038099884061565003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 606897477434933024164173341 227586554038099884061565003)
                ·
                  refine ⟨341379831057149826092347505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227586554038099884061565003 341379831057149826092347505)
                  ·
                    refine ⟨256034873292862369569260629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 341379831057149826092347505 256034873292862369569260629)
                    ·
                      refine ⟨3000408671400730893389773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 256034873292862369569260629 3000408671400730893389773)
                      ·
                        rfl

theorem cell23_5843275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 8].length) (baseStart_5843275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843275 prefixEnd_5843275 := by exact prefixLift 5843275
  have htrace : WordTrace (prefixWord ++ tailWord_5843275) baseStart_5843275 baseEnd_5843275 := by
    simpa [prefixWord, tailWord_5843275, baseEnd_5843275] using wordTrace_append hprefix tailTrace_5843275
  have hstable : (prefixWord ++ tailWord_5843275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843275).length < 2 ^ (prefixWord ++ tailWord_5843275).sum := by decide
  have hdescent : baseEnd_5843275 < baseStart_5843275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843282 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_5843282 : Nat := 118140960795 + 5843282 * 2 ^ 59
def prefixEnd_5843282 : Nat := 4983230072969 + 3 ^ 40 * 5843282 * 2
def baseEnd_5843282 : Nat := 3000412265765312366002241

theorem tailTrace_5843282 : CollatzResearch.WordTrace tailWord_5843282 prefixEnd_5843282 3000412265765312366002241 := by
  unfold tailWord_5843282
  simp only [CollatzResearch.WordTrace]
  refine ⟨53280500804198685489901025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142081335477863161306402733 53280500804198685489901025)
  ·
    refine ⟨39960375603149014117425769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53280500804198685489901025 39960375603149014117425769)
    ·
      refine ⟨29970281702361760588069327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39960375603149014117425769 29970281702361760588069327)
      ·
        refine ⟨44955422553542640882103991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29970281702361760588069327 44955422553542640882103991)
        ·
          refine ⟨67433133830313961323155987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44955422553542640882103991 67433133830313961323155987)
          ·
            refine ⟨101149700745470941984733981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67433133830313961323155987 101149700745470941984733981)
            ·
              refine ⟨37931137779551603244275243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101149700745470941984733981 37931137779551603244275243)
              ·
                refine ⟨56896706669327404866412865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37931137779551603244275243 56896706669327404866412865)
                ·
                  refine ⟨42672530001995553649809649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56896706669327404866412865 42672530001995553649809649)
                  ·
                    refine ⟨32004397501496665237357237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42672530001995553649809649 32004397501496665237357237)
                    ·
                      refine ⟨3000412265765312366002241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32004397501496665237357237 3000412265765312366002241)
                      ·
                        rfl

theorem cell23_5843282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_5843282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843282 prefixEnd_5843282 := by exact prefixLift 5843282
  have htrace : WordTrace (prefixWord ++ tailWord_5843282) baseStart_5843282 baseEnd_5843282 := by
    simpa [prefixWord, tailWord_5843282, baseEnd_5843282] using wordTrace_append hprefix tailTrace_5843282
  have hstable : (prefixWord ++ tailWord_5843282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843282).length < 2 ^ (prefixWord ++ tailWord_5843282).sum := by decide
  have hdescent : baseEnd_5843282 < baseStart_5843282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843329 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_5843329 : Nat := 118140960795 + 5843329 * 2 ^ 59
def prefixEnd_5843329 : Nat := 4983230072969 + 3 ^ 40 * 5843329 * 2
def baseEnd_5843329 : Nat := 3000436399356073682114525

theorem tailTrace_5843329 : CollatzResearch.WordTrace tailWord_5843329 prefixEnd_5843329 3000436399356073682114525 := by
  unfold tailWord_5843329
  simp only [CollatzResearch.WordTrace]
  refine ⟨213123717447624468986565041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142082478298416312657710027 213123717447624468986565041)
  ·
    refine ⟨159842788085718351739923781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213123717447624468986565041 159842788085718351739923781)
    ·
      refine ⟨29970522766072190951235709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159842788085718351739923781 29970522766072190951235709)
      ·
        refine ⟨11238946037277071606713391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29970522766072190951235709 11238946037277071606713391)
        ·
          refine ⟨16858419055915607410070087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11238946037277071606713391 16858419055915607410070087)
          ·
            refine ⟨25287628583873411115105131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16858419055915607410070087 25287628583873411115105131)
            ·
              refine ⟨37931442875810116672657697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25287628583873411115105131 37931442875810116672657697)
              ·
                refine ⟨28448582156857587504493273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37931442875810116672657697 28448582156857587504493273)
                ·
                  refine ⟨21336436617643190628369955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28448582156857587504493273 21336436617643190628369955)
                  ·
                    refine ⟨32004654926464785942554933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21336436617643190628369955 32004654926464785942554933)
                    ·
                      refine ⟨3000436399356073682114525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32004654926464785942554933 3000436399356073682114525)
                      ·
                        rfl

theorem cell23_5843329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_5843329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843329 prefixEnd_5843329 := by exact prefixLift 5843329
  have htrace : WordTrace (prefixWord ++ tailWord_5843329) baseStart_5843329 baseEnd_5843329 := by
    simpa [prefixWord, tailWord_5843329, baseEnd_5843329] using wordTrace_append hprefix tailTrace_5843329
  have hstable : (prefixWord ++ tailWord_5843329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843329).length < 2 ^ (prefixWord ++ tailWord_5843329).sum := by decide
  have hdescent : baseEnd_5843329 < baseStart_5843329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843330 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_5843330 : Nat := 118140960795 + 5843330 * 2 ^ 59
def prefixEnd_5843330 : Nat := 4983230072969 + 3 ^ 40 * 5843330 * 2
def baseEnd_5843330 : Nat := 3000436912836728178202021

theorem tailTrace_5843330 : CollatzResearch.WordTrace tailWord_5843330 prefixEnd_5843330 3000436912836728178202021 := by
  unfold tailWord_5843330
  simp only [CollatzResearch.WordTrace]
  refine ⟨53280938480155211539337861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142082502613747230771567629 53280938480155211539337861)
  ·
    refine ⟨9990175965029102163625849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53280938480155211539337861 9990175965029102163625849)
    ·
      refine ⟨7492631973771826622719387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9990175965029102163625849 7492631973771826622719387)
      ·
        refine ⟨11238947960657739934079081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7492631973771826622719387 11238947960657739934079081)
        ·
          refine ⟨8429210970493304950559311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11238947960657739934079081 8429210970493304950559311)
          ·
            refine ⟨12643816455739957425838967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8429210970493304950559311 12643816455739957425838967)
            ·
              refine ⟨18965724683609936138758451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12643816455739957425838967 18965724683609936138758451)
              ·
                refine ⟨28448587025414904208137677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18965724683609936138758451 28448587025414904208137677)
                ·
                  refine ⟨10668220134530589078051629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28448587025414904208137677 10668220134530589078051629)
                  ·
                    refine ⟨4000582550448970904269361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10668220134530589078051629 4000582550448970904269361)
                    ·
                      refine ⟨3000436912836728178202021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4000582550448970904269361 3000436912836728178202021)
                      ·
                        rfl

theorem cell23_5843330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_5843330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843330 prefixEnd_5843330 := by exact prefixLift 5843330
  have htrace : WordTrace (prefixWord ++ tailWord_5843330) baseStart_5843330 baseEnd_5843330 := by
    simpa [prefixWord, tailWord_5843330, baseEnd_5843330] using wordTrace_append hprefix tailTrace_5843330
  have hstable : (prefixWord ++ tailWord_5843330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843330).length < 2 ^ (prefixWord ++ tailWord_5843330).sum := by decide
  have hdescent : baseEnd_5843330 < baseStart_5843330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843332 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 9]
def baseStart_5843332 : Nat := 118140960795 + 5843332 * 2 ^ 59
def prefixEnd_5843332 : Nat := 4983230072969 + 3 ^ 40 * 5843332 * 2
def baseEnd_5843332 : Nat := 333381993310893018930779

theorem tailTrace_5843332 : CollatzResearch.WordTrace tailWord_5843332 prefixEnd_5843332 333381993310893018930779 := by
  unfold tailWord_5843332
  simp only [CollatzResearch.WordTrace]
  refine ⟨106561913433306800249462125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142082551244409066999282833 106561913433306800249462125)
  ·
    refine ⟨39960717537490050093548297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106561913433306800249462125 39960717537490050093548297)
    ·
      refine ⟨29970538153117537570161223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39960717537490050093548297 29970538153117537570161223)
      ·
        refine ⟨44955807229676306355241835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29970538153117537570161223 44955807229676306355241835)
        ·
          refine ⟨67433710844514459532862753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44955807229676306355241835 67433710844514459532862753)
          ·
            refine ⟨50575283133385844649647065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67433710844514459532862753 50575283133385844649647065)
            ·
              refine ⟨37931462350039383487235299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50575283133385844649647065 37931462350039383487235299)
              ·
                refine ⟨56897193525059075230852949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37931462350039383487235299 56897193525059075230852949)
                ·
                  refine ⟨333381993310893018930779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56897193525059075230852949 333381993310893018930779)
                  ·
                    rfl

theorem cell23_5843332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_5843332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843332 prefixEnd_5843332 := by exact prefixLift 5843332
  have htrace : WordTrace (prefixWord ++ tailWord_5843332) baseStart_5843332 baseEnd_5843332 := by
    simpa [prefixWord, tailWord_5843332, baseEnd_5843332] using wordTrace_append hprefix tailTrace_5843332
  have hstable : (prefixWord ++ tailWord_5843332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843332).length < 2 ^ (prefixWord ++ tailWord_5843332).sum := by decide
  have hdescent : baseEnd_5843332 < baseStart_5843332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843349 : List Nat := [1, 3, 2, 1, 1, 2, 1, 7, 5]
def baseStart_5843349 : Nat := 118140960795 + 5843349 * 2 ^ 59
def prefixEnd_5843349 : Nat := 4983230072969 + 3 ^ 40 * 5843349 * 2
def baseEnd_5843349 : Nat := 333382963218795955984937

theorem tailTrace_5843349 : CollatzResearch.WordTrace tailWord_5843349 prefixEnd_5843349 333382963218795955984937 := by
  unfold tailWord_5843349
  simp only [CollatzResearch.WordTrace]
  refine ⟨213124446907552012402293101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142082964605034674934862067 213124446907552012402293101)
  ·
    refine ⟨79921667590332004650859913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213124446907552012402293101 79921667590332004650859913)
    ·
      refine ⟨59941250692749003488144935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79921667590332004650859913 59941250692749003488144935)
      ·
        refine ⟨89911876039123505232217403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59941250692749003488144935 89911876039123505232217403)
        ·
          refine ⟨134867814058685257848326105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89911876039123505232217403 134867814058685257848326105)
          ·
            refine ⟨101150860544013943386244579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134867814058685257848326105 101150860544013943386244579)
            ·
              refine ⟨151726290816020915079366869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101150860544013943386244579 151726290816020915079366869)
              ·
                refine ⟨3556084941000490197172661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 151726290816020915079366869 3556084941000490197172661)
                ·
                  refine ⟨333382963218795955984937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3556084941000490197172661 333382963218795955984937)
                  ·
                    rfl

theorem cell23_5843349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 5].length) (baseStart_5843349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843349 prefixEnd_5843349 := by exact prefixLift 5843349
  have htrace : WordTrace (prefixWord ++ tailWord_5843349) baseStart_5843349 baseEnd_5843349 := by
    simpa [prefixWord, tailWord_5843349, baseEnd_5843349] using wordTrace_append hprefix tailTrace_5843349
  have hstable : (prefixWord ++ tailWord_5843349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843349).length < 2 ^ (prefixWord ++ tailWord_5843349).sum := by decide
  have hdescent : baseEnd_5843349 < baseStart_5843349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843359 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 3]
def baseStart_5843359 : Nat := 118140960795 + 5843359 * 2 ^ 59
def prefixEnd_5843359 : Nat := 4983230072969 + 3 ^ 40 * 5843359 * 2
def baseEnd_5843359 : Nat := 3000451803775708564739387

theorem tailTrace_5843359 : CollatzResearch.WordTrace tailWord_5843359 prefixEnd_5843359 3000451803775708564739387 := by
  unfold tailWord_5843359
  simp only [CollatzResearch.WordTrace]
  refine ⟨213124811637515784110157131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142083207758343856073438087 213124811637515784110157131)
  ·
    refine ⟨319687217456273676165235697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213124811637515784110157131 319687217456273676165235697)
    ·
      refine ⟨239765413092205257123926773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319687217456273676165235697 239765413092205257123926773)
      ·
        refine ⟨22478007477394242855368135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 239765413092205257123926773 22478007477394242855368135)
        ·
          refine ⟨33717011216091364283052203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22478007477394242855368135 33717011216091364283052203)
          ·
            refine ⟨50575516824137046424578305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33717011216091364283052203 50575516824137046424578305)
            ·
              refine ⟨37931637618102784818433729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50575516824137046424578305 37931637618102784818433729)
              ·
                refine ⟨28448728213577088613825297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37931637618102784818433729 28448728213577088613825297)
                ·
                  refine ⟨21336546160182816460368973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28448728213577088613825297 21336546160182816460368973)
                  ·
                    refine ⟨8001204810068556172638365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21336546160182816460368973 8001204810068556172638365)
                    ·
                      refine ⟨3000451803775708564739387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8001204810068556172638365 3000451803775708564739387)
                      ·
                        rfl

theorem cell23_5843359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_5843359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843359 prefixEnd_5843359 := by exact prefixLift 5843359
  have htrace : WordTrace (prefixWord ++ tailWord_5843359) baseStart_5843359 baseEnd_5843359 := by
    simpa [prefixWord, tailWord_5843359, baseEnd_5843359] using wordTrace_append hprefix tailTrace_5843359
  have hstable : (prefixWord ++ tailWord_5843359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843359).length < 2 ^ (prefixWord ++ tailWord_5843359).sum := by decide
  have hdescent : baseEnd_5843359 < baseStart_5843359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843396 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 1, 7]
def baseStart_5843396 : Nat := 118140960795 + 5843396 * 2 ^ 59
def prefixEnd_5843396 : Nat := 4983230072969 + 3 ^ 40 * 5843396 * 2
def baseEnd_5843396 : Nat := 1000156934186641639992239

theorem tailTrace_5843396 : CollatzResearch.WordTrace tailWord_5843396 prefixEnd_5843396 1000156934186641639992239 := by
  unfold tailWord_5843396
  simp only [CollatzResearch.WordTrace]
  refine ⟨106563080569190869714627021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142084107425587826286169361 106563080569190869714627021)
  ·
    refine ⟨39961155213446576142985133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106563080569190869714627021 39961155213446576142985133)
    ·
      refine ⟨14985433205042466053619425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39961155213446576142985133 14985433205042466053619425)
      ·
        refine ⟨11239074903781849540214569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14985433205042466053619425 11239074903781849540214569)
        ·
          refine ⟨8429306177836387155160927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11239074903781849540214569 8429306177836387155160927)
          ·
            refine ⟨12643959266754580732741391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8429306177836387155160927 12643959266754580732741391)
            ·
              refine ⟨18965938900131871099112087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12643959266754580732741391 18965938900131871099112087)
              ·
                refine ⟨28448908350197806648668131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18965938900131871099112087 28448908350197806648668131)
                ·
                  refine ⟨42673362525296709973002197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28448908350197806648668131 42673362525296709973002197)
                  ·
                    refine ⟨1000156934186641639992239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42673362525296709973002197 1000156934186641639992239)
                    ·
                      rfl

theorem cell23_5843396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_5843396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843396 prefixEnd_5843396 := by exact prefixLift 5843396
  have htrace : WordTrace (prefixWord ++ tailWord_5843396) baseStart_5843396 baseEnd_5843396 := by
    simpa [prefixWord, tailWord_5843396, baseEnd_5843396] using wordTrace_append hprefix tailTrace_5843396
  have hstable : (prefixWord ++ tailWord_5843396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843396).length < 2 ^ (prefixWord ++ tailWord_5843396).sum := by decide
  have hdescent : baseEnd_5843396 < baseStart_5843396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843399 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 4]
def baseStart_5843399 : Nat := 118140960795 + 5843399 * 2 ^ 59
def prefixEnd_5843399 : Nat := 4983230072969 + 3 ^ 40 * 5843399 * 2
def baseEnd_5843399 : Nat := 3000472343001888408239203

theorem tailTrace_5843399 : CollatzResearch.WordTrace tailWord_5843399 prefixEnd_5843399 3000472343001888408239203 := by
  unfold tailWord_5843399
  simp only [CollatzResearch.WordTrace]
  refine ⟨213126270557370870941613251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142084180371580580627742167 213126270557370870941613251)
  ·
    refine ⟨319689405836056306412419877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213126270557370870941613251 319689405836056306412419877)
    ·
      refine ⟨59941763594260557452328727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319689405836056306412419877 59941763594260557452328727)
      ·
        refine ⟨89912645391390836178493091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59941763594260557452328727 89912645391390836178493091)
        ·
          refine ⟨134868968087086254267739637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89912645391390836178493091 134868968087086254267739637)
          ·
            refine ⟨12643965758164336337600591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134868968087086254267739637 12643965758164336337600591)
            ·
              refine ⟨18965948637246504506400887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12643965758164336337600591 18965948637246504506400887)
              ·
                refine ⟨28448922955869756759601331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18965948637246504506400887 28448922955869756759601331)
                ·
                  refine ⟨42673384433804635139401997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28448922955869756759601331 42673384433804635139401997)
                  ·
                    refine ⟨16002519162676738177275749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42673384433804635139401997 16002519162676738177275749)
                    ·
                      refine ⟨3000472343001888408239203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16002519162676738177275749 3000472343001888408239203)
                      ·
                        rfl

theorem cell23_5843399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_5843399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843399 prefixEnd_5843399 := by exact prefixLift 5843399
  have htrace : WordTrace (prefixWord ++ tailWord_5843399) baseStart_5843399 baseEnd_5843399 := by
    simpa [prefixWord, tailWord_5843399, baseEnd_5843399] using wordTrace_append hprefix tailTrace_5843399
  have hstable : (prefixWord ++ tailWord_5843399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843399).length < 2 ^ (prefixWord ++ tailWord_5843399).sum := by decide
  have hdescent : baseEnd_5843399 < baseStart_5843399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843460 : List Nat := [2, 3, 2, 3, 1, 1, 3, 3, 1, 4]
def baseStart_5843460 : Nat := 118140960795 + 5843460 * 2 ^ 59
def prefixEnd_5843460 : Nat := 4983230072969 + 3 ^ 40 * 5843460 * 2
def baseEnd_5843460 : Nat := 1000167888440604223192141

theorem tailTrace_5843460 : CollatzResearch.WordTrace tailWord_5843460 prefixEnd_5843460 1000167888440604223192141 := by
  unfold tailWord_5843460
  simp only [CollatzResearch.WordTrace]
  refine ⟨106564247705074939179791917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142085663606766585573055889 106564247705074939179791917)
  ·
    refine ⟨39961592889403102192421969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106564247705074939179791917 39961592889403102192421969)
    ·
      refine ⟨29971194667052326644316477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39961592889403102192421969 29971194667052326644316477)
      ·
        refine ⟨11239198000144622491618679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29971194667052326644316477 11239198000144622491618679)
        ·
          refine ⟨16858797000216933737428019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11239198000144622491618679 16858797000216933737428019)
          ·
            refine ⟨25288195500325400606142029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16858797000216933737428019 25288195500325400606142029)
            ·
              refine ⟨9483073312622025227303261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25288195500325400606142029 9483073312622025227303261)
              ·
                refine ⟨3556152492233259460238723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9483073312622025227303261 3556152492233259460238723)
                ·
                  refine ⟨5334228738349889190358085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3556152492233259460238723 5334228738349889190358085)
                  ·
                    refine ⟨1000167888440604223192141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5334228738349889190358085 1000167888440604223192141)
                    ·
                      rfl

theorem cell23_5843460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_5843460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843460 prefixEnd_5843460 := by exact prefixLift 5843460
  have htrace : WordTrace (prefixWord ++ tailWord_5843460) baseStart_5843460 baseEnd_5843460 := by
    simpa [prefixWord, tailWord_5843460, baseEnd_5843460] using wordTrace_append hprefix tailTrace_5843460
  have hstable : (prefixWord ++ tailWord_5843460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843460).length < 2 ^ (prefixWord ++ tailWord_5843460).sum := by decide
  have hdescent : baseEnd_5843460 < baseStart_5843460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843506 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2]
def baseStart_5843506 : Nat := 118140960795 + 5843506 * 2 ^ 59
def prefixEnd_5843506 : Nat := 4983230072969 + 3 ^ 40 * 5843506 * 2
def baseEnd_5843506 : Nat := 3000527285431919489601211

theorem tailTrace_5843506 : CollatzResearch.WordTrace tailWord_5843506 prefixEnd_5843506 3000527285431919489601211 := by
  unfold tailWord_5843506
  simp only [CollatzResearch.WordTrace]
  refine ⟨53282543291995807053939593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142086782111988818810505581 53282543291995807053939593)
  ·
    refine ⟨39961907468996855290454695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53282543291995807053939593 39961907468996855290454695)
    ·
      refine ⟨59942861203495282935682043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39961907468996855290454695 59942861203495282935682043)
      ·
        refine ⟨89914291805242924403523065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59942861203495282935682043 89914291805242924403523065)
        ·
          refine ⟨67435718853932193302642299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89914291805242924403523065 67435718853932193302642299)
          ·
            refine ⟨101153578280898289953963449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67435718853932193302642299 101153578280898289953963449)
            ·
              refine ⟨75865183710673717465472587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101153578280898289953963449 75865183710673717465472587)
              ·
                refine ⟨113797775566010576198208881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75865183710673717465472587 113797775566010576198208881)
                ·
                  refine ⟨85348331674507932148656661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113797775566010576198208881 85348331674507932148656661)
                  ·
                    refine ⟨4000703047242559319468281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85348331674507932148656661 4000703047242559319468281)
                    ·
                      refine ⟨3000527285431919489601211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4000703047242559319468281 3000527285431919489601211)
                      ·
                        rfl

theorem cell23_5843506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_5843506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843506 prefixEnd_5843506 := by exact prefixLift 5843506
  have htrace : WordTrace (prefixWord ++ tailWord_5843506) baseStart_5843506 baseEnd_5843506 := by
    simpa [prefixWord, tailWord_5843506, baseEnd_5843506] using wordTrace_append hprefix tailTrace_5843506
  have hstable : (prefixWord ++ tailWord_5843506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843506).length < 2 ^ (prefixWord ++ tailWord_5843506).sum := by decide
  have hdescent : baseEnd_5843506 < baseStart_5843506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843510 : List Nat := [5, 1, 2, 1, 2, 1, 1, 3, 2, 3, 2]
def baseStart_5843510 : Nat := 118140960795 + 5843510 * 2 ^ 59
def prefixEnd_5843510 : Nat := 4983230072969 + 3 ^ 40 * 5843510 * 2
def baseEnd_5843510 : Nat := 3000529339354537473951193

theorem tailTrace_5843510 : CollatzResearch.WordTrace tailWord_5843510 prefixEnd_5843510 3000529339354537473951193 := by
  unfold tailWord_5843510
  simp only [CollatzResearch.WordTrace]
  refine ⟨13320644941248046056181499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142086879373312491265935989 13320644941248046056181499)
  ·
    refine ⟨19980967411872069084272249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13320644941248046056181499 19980967411872069084272249)
    ·
      refine ⟨14985725558904051813204187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19980967411872069084272249 14985725558904051813204187)
      ·
        refine ⟨22478588338356077719806281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14985725558904051813204187 22478588338356077719806281)
        ·
          refine ⟨16858941253767058289854711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22478588338356077719806281 16858941253767058289854711)
          ·
            refine ⟨25288411880650587434782067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16858941253767058289854711 25288411880650587434782067)
            ·
              refine ⟨37932617820975881152173101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25288411880650587434782067 37932617820975881152173101)
              ·
                refine ⟨14224731682865955432064913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37932617820975881152173101 14224731682865955432064913)
                ·
                  refine ⟨10668548762149466574048685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14224731682865955432064913 10668548762149466574048685)
                  ·
                    refine ⟨4000705785806049965268257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10668548762149466574048685 4000705785806049965268257)
                    ·
                      refine ⟨3000529339354537473951193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4000705785806049965268257 3000529339354537473951193)
                      ·
                        rfl

theorem cell23_5843510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_5843510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843510 prefixEnd_5843510 := by exact prefixLift 5843510
  have htrace : WordTrace (prefixWord ++ tailWord_5843510) baseStart_5843510 baseEnd_5843510 := by
    simpa [prefixWord, tailWord_5843510, baseEnd_5843510] using wordTrace_append hprefix tailTrace_5843510
  have hstable : (prefixWord ++ tailWord_5843510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843510).length < 2 ^ (prefixWord ++ tailWord_5843510).sum := by decide
  have hdescent : baseEnd_5843510 < baseStart_5843510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843516 : List Nat := [2, 2, 2, 2, 3, 2, 1, 2, 1, 6]
def baseStart_5843516 : Nat := 118140960795 + 5843516 * 2 ^ 59
def prefixEnd_5843516 : Nat := 4983230072969 + 3 ^ 40 * 5843516 * 2
def baseEnd_5843516 : Nat := 1000177473412821483492055

theorem tailTrace_5843516 : CollatzResearch.WordTrace tailWord_5843516 prefixEnd_5843516 1000177473412821483492055 := by
  unfold tailWord_5843516
  simp only [CollatzResearch.WordTrace]
  refine ⟨106565268948973499961811201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142087025265297999949081601 106565268948973499961811201)
  ·
    refine ⟨79923951711730124971358401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106565268948973499961811201 79923951711730124971358401)
    ·
      refine ⟨59942963783797593728518801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79923951711730124971358401 59942963783797593728518801)
      ·
        refine ⟨44957222837848195296389101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59942963783797593728518801 44957222837848195296389101)
        ·
          refine ⟨16858958564193073236145913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44957222837848195296389101 16858958564193073236145913)
          ·
            refine ⟨12644218923144804927109435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16858958564193073236145913 12644218923144804927109435)
            ·
              refine ⟨18966328384717207390664153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12644218923144804927109435 18966328384717207390664153)
              ·
                refine ⟨14224746288537905542998115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18966328384717207390664153 14224746288537905542998115)
                ·
                  refine ⟨21337119432806858314497173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14224746288537905542998115 21337119432806858314497173)
                  ·
                    refine ⟨1000177473412821483492055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21337119432806858314497173 1000177473412821483492055)
                    ·
                      rfl

theorem cell23_5843516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_5843516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843516 prefixEnd_5843516 := by exact prefixLift 5843516
  have htrace : WordTrace (prefixWord ++ tailWord_5843516) baseStart_5843516 baseEnd_5843516 := by
    simpa [prefixWord, tailWord_5843516, baseEnd_5843516] using wordTrace_append hprefix tailTrace_5843516
  have hstable : (prefixWord ++ tailWord_5843516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843516).length < 2 ^ (prefixWord ++ tailWord_5843516).sum := by decide
  have hdescent : baseEnd_5843516 < baseStart_5843516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843539 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 3]
def baseStart_5843539 : Nat := 118140960795 + 5843539 * 2 ^ 59
def prefixEnd_5843539 : Nat := 4983230072969 + 3 ^ 40 * 5843539 * 2
def baseEnd_5843539 : Nat := 3000544230293517860488559

theorem tailTrace_5843539 : CollatzResearch.WordTrace tailWord_5843539 prefixEnd_5843539 3000544230293517860488559 := by
  unfold tailWord_5843539
  simp only [CollatzResearch.WordTrace]
  refine ⟨213131376776863674851709671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142087584517909116567806447 213131376776863674851709671)
  ·
    refine ⟨319697065165295512277564507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213131376776863674851709671 319697065165295512277564507)
    ·
      refine ⟨479545597747943268416346761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319697065165295512277564507 479545597747943268416346761)
      ·
        refine ⟨359659198310957451312260071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479545597747943268416346761 359659198310957451312260071)
        ·
          refine ⟨539488797466436176968390107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359659198310957451312260071 539488797466436176968390107)
          ·
            refine ⟨809233196199654265452585161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539488797466436176968390107 809233196199654265452585161)
            ·
              refine ⟨606924897149740699089438871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 809233196199654265452585161 606924897149740699089438871)
              ·
                refine ⟨910387345724611048634158307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 606924897149740699089438871 910387345724611048634158307)
                ·
                  refine ⟨1365581018586916572951237461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 910387345724611048634158307 1365581018586916572951237461)
                  ·
                    refine ⟨8001451280782714294636157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1365581018586916572951237461 8001451280782714294636157)
                    ·
                      refine ⟨3000544230293517860488559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8001451280782714294636157 3000544230293517860488559)
                      ·
                        rfl

theorem cell23_5843539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 3].length) (baseStart_5843539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843539 prefixEnd_5843539 := by exact prefixLift 5843539
  have htrace : WordTrace (prefixWord ++ tailWord_5843539) baseStart_5843539 baseEnd_5843539 := by
    simpa [prefixWord, tailWord_5843539, baseEnd_5843539] using wordTrace_append hprefix tailTrace_5843539
  have hstable : (prefixWord ++ tailWord_5843539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843539).length < 2 ^ (prefixWord ++ tailWord_5843539).sum := by decide
  have hdescent : baseEnd_5843539 < baseStart_5843539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843559 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 4, 7]
def baseStart_5843559 : Nat := 118140960795 + 5843559 * 2 ^ 59
def prefixEnd_5843559 : Nat := 4983230072969 + 3 ^ 40 * 5843559 * 2
def baseEnd_5843559 : Nat := 1000184833302202594079489

theorem tailTrace_5843559 : CollatzResearch.WordTrace tailWord_5843559 prefixEnd_5843559 1000184833302202594079489 := by
  unfold tailWord_5843559
  simp only [CollatzResearch.WordTrace]
  refine ⟨213132106236791218267437731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142088070824527478844958487 213132106236791218267437731)
  ·
    refine ⟨319698159355186827401156597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213132106236791218267437731 319698159355186827401156597)
    ·
      refine ⟨29971702439548765068858431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 319698159355186827401156597 29971702439548765068858431)
      ·
        refine ⟨44957553659323147603287647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29971702439548765068858431 44957553659323147603287647)
        ·
          refine ⟨67436330488984721404931471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44957553659323147603287647 67436330488984721404931471)
          ·
            refine ⟨101154495733477082107397207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67436330488984721404931471 101154495733477082107397207)
            ·
              refine ⟨151731743600215623161095811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101154495733477082107397207 151731743600215623161095811)
              ·
                refine ⟨227597615400323434741643717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151731743600215623161095811 227597615400323434741643717)
                ·
                  refine ⟨42674552887560644014058197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 227597615400323434741643717 42674552887560644014058197)
                  ·
                    refine ⟨1000184833302202594079489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42674552887560644014058197 1000184833302202594079489)
                    ·
                      rfl

theorem cell23_5843559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_5843559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843559 prefixEnd_5843559 := by exact prefixLift 5843559
  have htrace : WordTrace (prefixWord ++ tailWord_5843559) baseStart_5843559 baseEnd_5843559 := by
    simpa [prefixWord, tailWord_5843559, baseEnd_5843559] using wordTrace_append hprefix tailTrace_5843559
  have hstable : (prefixWord ++ tailWord_5843559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843559).length < 2 ^ (prefixWord ++ tailWord_5843559).sum := by decide
  have hdescent : baseEnd_5843559 < baseStart_5843559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843574 : List Nat := [5, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4]
def baseStart_5843574 : Nat := 118140960795 + 5843574 * 2 ^ 59
def prefixEnd_5843574 : Nat := 4983230072969 + 3 ^ 40 * 5843574 * 2
def baseEnd_5843574 : Nat := 3000562202116425223550899

theorem tailTrace_5843574 : CollatzResearch.WordTrace tailWord_5843574 prefixEnd_5843574 3000562202116425223550899 := by
  unfold tailWord_5843574
  simp only [CollatzResearch.WordTrace]
  refine ⟨13320790833233554739327111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142088435554491250552822517 13320790833233554739327111)
  ·
    refine ⟨19981186249850332108990667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13320790833233554739327111 19981186249850332108990667)
    ·
      refine ⟨29971779374775498163486001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19981186249850332108990667 29971779374775498163486001)
      ·
        refine ⟨22478834531081623622614501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29971779374775498163486001 22478834531081623622614501)
        ·
          refine ⟨4214781474577804429240219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22478834531081623622614501 4214781474577804429240219)
          ·
            refine ⟨6322172211866706643860329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4214781474577804429240219 6322172211866706643860329)
            ·
              refine ⟨4741629158900029982895247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6322172211866706643860329 4741629158900029982895247)
              ·
                refine ⟨7112443738350044974342871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4741629158900029982895247 7112443738350044974342871)
                ·
                  refine ⟨10668665607525067461514307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7112443738350044974342871 10668665607525067461514307)
                  ·
                    refine ⟨16002998411287601192271461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10668665607525067461514307 16002998411287601192271461)
                    ·
                      refine ⟨3000562202116425223550899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16002998411287601192271461 3000562202116425223550899)
                      ·
                        rfl

theorem cell23_5843574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_5843574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843574 prefixEnd_5843574 := by exact prefixLift 5843574
  have htrace : WordTrace (prefixWord ++ tailWord_5843574) baseStart_5843574 baseEnd_5843574 := by
    simpa [prefixWord, tailWord_5843574, baseEnd_5843574] using wordTrace_append hprefix tailTrace_5843574
  have hstable : (prefixWord ++ tailWord_5843574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843574).length < 2 ^ (prefixWord ++ tailWord_5843574).sum := by decide
  have hdescent : baseEnd_5843574 < baseStart_5843574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843579 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 4]
def baseStart_5843579 : Nat := 118140960795 + 5843579 * 2 ^ 59
def prefixEnd_5843579 : Nat := 4983230072969 + 3 ^ 40 * 5843579 * 2
def baseEnd_5843579 : Nat := 3000564769519697703988375

theorem tailTrace_5843579 : CollatzResearch.WordTrace tailWord_5843579 prefixEnd_5843579 3000564769519697703988375 := by
  unfold tailWord_5843579
  simp only [CollatzResearch.WordTrace]
  refine ⟨213132835696718761683165791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142088557131145841122110527 213132835696718761683165791)
  ·
    refine ⟨319699253545078142524748687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213132835696718761683165791 319699253545078142524748687)
    ·
      refine ⟨479548880317617213787123031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319699253545078142524748687 479548880317617213787123031)
      ·
        refine ⟨719323320476425820680684547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479548880317617213787123031 719323320476425820680684547)
        ·
          refine ⟨1078984980714638731021026821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719323320476425820680684547 1078984980714638731021026821)
          ·
            refine ⟨202309683883994762066442529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1078984980714638731021026821 202309683883994762066442529)
            ·
              refine ⟨151732262912996071549831897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202309683883994762066442529 151732262912996071549831897)
              ·
                refine ⟨113799197184747053662373923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151732262912996071549831897 113799197184747053662373923)
                ·
                  refine ⟨170698795777120580493560885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113799197184747053662373923 170698795777120580493560885)
                  ·
                    refine ⟨16003012104105054421271333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 170698795777120580493560885 16003012104105054421271333)
                    ·
                      refine ⟨3000564769519697703988375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16003012104105054421271333 3000564769519697703988375)
                      ·
                        rfl

theorem cell23_5843579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 4].length) (baseStart_5843579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843579 prefixEnd_5843579 := by exact prefixLift 5843579
  have htrace : WordTrace (prefixWord ++ tailWord_5843579) baseStart_5843579 baseEnd_5843579 := by
    simpa [prefixWord, tailWord_5843579, baseEnd_5843579] using wordTrace_append hprefix tailTrace_5843579
  have hstable : (prefixWord ++ tailWord_5843579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843579).length < 2 ^ (prefixWord ++ tailWord_5843579).sum := by decide
  have hdescent : baseEnd_5843579 < baseStart_5843579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843599 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 5]
def baseStart_5843599 : Nat := 118140960795 + 5843599 * 2 ^ 59
def prefixEnd_5843599 : Nat := 4983230072969 + 3 ^ 40 * 5843599 * 2
def baseEnd_5843599 : Nat := 3000575039132787625738283

theorem tailTrace_5843599 : CollatzResearch.WordTrace tailWord_5843599 prefixEnd_5843599 3000575039132787625738283 := by
  unfold tailWord_5843599
  simp only [CollatzResearch.WordTrace]
  refine ⟨213133565156646305098893851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142089043437764203399262567 213133565156646305098893851)
  ·
    refine ⟨319700347734969457648340777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213133565156646305098893851 319700347734969457648340777)
    ·
      refine ⟨239775260801227093236255583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319700347734969457648340777 239775260801227093236255583)
      ·
        refine ⟨359662891201840639854383375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239775260801227093236255583 359662891201840639854383375)
        ·
          refine ⟨539494336802760959781575063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359662891201840639854383375 539494336802760959781575063)
          ·
            refine ⟨809241505204141439672362595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539494336802760959781575063 809241505204141439672362595)
            ·
              refine ⟨1213862257806212159508543893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809241505204141439672362595 1213862257806212159508543893)
              ·
                refine ⟨56899793334666194976962995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1213862257806212159508543893 56899793334666194976962995)
                ·
                  refine ⟨85349690001999292465444493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56899793334666194976962995 85349690001999292465444493)
                  ·
                    refine ⟨32006133750749734674541685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85349690001999292465444493 32006133750749734674541685)
                    ·
                      refine ⟨3000575039132787625738283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32006133750749734674541685 3000575039132787625738283)
                      ·
                        rfl

theorem cell23_5843599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_5843599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843599 prefixEnd_5843599 := by exact prefixLift 5843599
  have htrace : WordTrace (prefixWord ++ tailWord_5843599) baseStart_5843599 baseEnd_5843599 := by
    simpa [prefixWord, tailWord_5843599, baseEnd_5843599] using wordTrace_append hprefix tailTrace_5843599
  have hstable : (prefixWord ++ tailWord_5843599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843599).length < 2 ^ (prefixWord ++ tailWord_5843599).sum := by decide
  have hdescent : baseEnd_5843599 < baseStart_5843599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843617 : List Nat := [1, 2, 3, 3, 3, 1, 2, 2, 1, 3, 2]
def baseStart_5843617 : Nat := 118140960795 + 5843617 * 2 ^ 59
def prefixEnd_5843617 : Nat := 4983230072969 + 3 ^ 40 * 5843617 * 2
def baseEnd_5843617 : Nat := 3000584281784568555313201

theorem tailTrace_5843617 : CollatzResearch.WordTrace tailWord_5843617 prefixEnd_5843617 3000584281784568555313201 := by
  unfold tailWord_5843617
  simp only [CollatzResearch.WordTrace]
  refine ⟨213134221670581094173049105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142089481113720729448699403 213134221670581094173049105)
  ·
    refine ⟨159850666252935820629786829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213134221670581094173049105 159850666252935820629786829)
    ·
      refine ⟨59943999844850932736170061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159850666252935820629786829 59943999844850932736170061)
      ·
        refine ⟨22478999941819099776063773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59943999844850932736170061 22478999941819099776063773)
        ·
          refine ⟨8429624978182162416023915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22478999941819099776063773 8429624978182162416023915)
          ·
            refine ⟨12644437467273243624035873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8429624978182162416023915 12644437467273243624035873)
            ·
              refine ⟨9483328100454932718026905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12644437467273243624035873 9483328100454932718026905)
              ·
                refine ⟨7112496075341199538520179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9483328100454932718026905 7112496075341199538520179)
                ·
                  refine ⟨10668744113011799307780269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7112496075341199538520179 10668744113011799307780269)
                  ·
                    refine ⟨4000779042379424740417601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10668744113011799307780269 4000779042379424740417601)
                    ·
                      refine ⟨3000584281784568555313201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4000779042379424740417601 3000584281784568555313201)
                      ·
                        rfl

theorem cell23_5843617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_5843617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843617 prefixEnd_5843617 := by exact prefixLift 5843617
  have htrace : WordTrace (prefixWord ++ tailWord_5843617) baseStart_5843617 baseEnd_5843617 := by
    simpa [prefixWord, tailWord_5843617, baseEnd_5843617] using wordTrace_append hprefix tailTrace_5843617
  have hstable : (prefixWord ++ tailWord_5843617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843617).length < 2 ^ (prefixWord ++ tailWord_5843617).sum := by decide
  have hdescent : baseEnd_5843617 < baseStart_5843617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843619 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 9]
def baseStart_5843619 : Nat := 118140960795 + 5843619 * 2 ^ 59
def prefixEnd_5843619 : Nat := 4983230072969 + 3 ^ 40 * 5843619 * 2
def baseEnd_5843619 : Nat := 333398367638430838609799

theorem tailTrace_5843619 : CollatzResearch.WordTrace tailWord_5843619 prefixEnd_5843619 333398367638430838609799 := by
  unfold tailWord_5843619
  simp only [CollatzResearch.WordTrace]
  refine ⟨213134294616573848514621911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142089529744382565676414607 213134294616573848514621911)
  ·
    refine ⟨319701441924860772771932867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213134294616573848514621911 319701441924860772771932867)
    ·
      refine ⟨479552162887291159157899301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319701441924860772771932867 479552162887291159157899301)
      ·
        refine ⟨89916030541367092342106119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 479552162887291159157899301 89916030541367092342106119)
        ·
          refine ⟨134874045812050638513159179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89916030541367092342106119 134874045812050638513159179)
          ·
            refine ⟨202311068718075957769738769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134874045812050638513159179 202311068718075957769738769)
            ·
              refine ⟨151733301538556968327304077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202311068718075957769738769 151733301538556968327304077)
              ·
                refine ⟨56899988076958863122739029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151733301538556968327304077 56899988076958863122739029)
                ·
                  refine ⟨333398367638430838609799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56899988076958863122739029 333398367638430838609799)
                  ·
                    rfl

theorem cell23_5843619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 9].length) (baseStart_5843619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843619 prefixEnd_5843619 := by exact prefixLift 5843619
  have htrace : WordTrace (prefixWord ++ tailWord_5843619) baseStart_5843619 baseEnd_5843619 := by
    simpa [prefixWord, tailWord_5843619, baseEnd_5843619] using wordTrace_append hprefix tailTrace_5843619
  have hstable : (prefixWord ++ tailWord_5843619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843619).length < 2 ^ (prefixWord ++ tailWord_5843619).sum := by decide
  have hdescent : baseEnd_5843619 < baseStart_5843619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843646 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_5843646 : Nat := 118140960795 + 5843646 * 2 ^ 59
def prefixEnd_5843646 : Nat := 4983230072969 + 3 ^ 40 * 5843646 * 2
def baseEnd_5843646 : Nat := 3000599172723548941850567

theorem tailTrace_5843646 : CollatzResearch.WordTrace tailWord_5843646 prefixEnd_5843646 3000599172723548941850567 := by
  unfold tailWord_5843646
  simp only [CollatzResearch.WordTrace]
  refine ⟨26641909923434504015731849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142090186258317354750569861 26641909923434504015731849)
  ·
    refine ⟨19981432442575878011798887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26641909923434504015731849 19981432442575878011798887)
    ·
      refine ⟨29972148663863817017698331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19981432442575878011798887 29972148663863817017698331)
      ·
        refine ⟨44958222995795725526547497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29972148663863817017698331 44958222995795725526547497)
        ·
          refine ⟨33718667246846794144910623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44958222995795725526547497 33718667246846794144910623)
          ·
            refine ⟨50578000870270191217365935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33718667246846794144910623 50578000870270191217365935)
            ·
              refine ⟨75867001305405286826048903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50578000870270191217365935 75867001305405286826048903)
              ·
                refine ⟨113800501958107930239073355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75867001305405286826048903 113800501958107930239073355)
                ·
                  refine ⟨170700752937161895358610033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113800501958107930239073355 170700752937161895358610033)
                  ·
                    refine ⟨128025564702871421518957525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 170700752937161895358610033 128025564702871421518957525)
                    ·
                      refine ⟨3000599172723548941850567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128025564702871421518957525 3000599172723548941850567)
                      ·
                        rfl

theorem cell23_5843646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_5843646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843646 prefixEnd_5843646 := by exact prefixLift 5843646
  have htrace : WordTrace (prefixWord ++ tailWord_5843646) baseStart_5843646 baseEnd_5843646 := by
    simpa [prefixWord, tailWord_5843646, baseEnd_5843646] using wordTrace_append hprefix tailTrace_5843646
  have hstable : (prefixWord ++ tailWord_5843646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843646).length < 2 ^ (prefixWord ++ tailWord_5843646).sum := by decide
  have hdescent : baseEnd_5843646 < baseStart_5843646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843683 : List Nat := [1, 1, 1, 7, 1, 1, 1, 3, 2, 5]
def baseStart_5843683 : Nat := 118140960795 + 5843683 * 2 ^ 59
def prefixEnd_5843683 : Nat := 4983230072969 + 3 ^ 40 * 5843683 * 2
def baseEnd_5843683 : Nat := 1000206057169255099029299

theorem tailTrace_5843683 : CollatzResearch.WordTrace tailWord_5843683 prefixEnd_5843683 1000206057169255099029299 := by
  unfold tailWord_5843683
  simp only [CollatzResearch.WordTrace]
  refine ⟨213136628888341987444951703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142091085925561324963301135 213136628888341987444951703)
  ·
    refine ⟨319704943332512981167427555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213136628888341987444951703 319704943332512981167427555)
    ·
      refine ⟨479557414998769471751141333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319704943332512981167427555 479557414998769471751141333)
      ·
        refine ⟨11239626914033659494167375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 479557414998769471751141333 11239626914033659494167375)
        ·
          refine ⟨16859440371050489241251063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11239626914033659494167375 16859440371050489241251063)
          ·
            refine ⟨25289160556575733861876595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16859440371050489241251063 25289160556575733861876595)
            ·
              refine ⟨37933740834863600792814893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25289160556575733861876595 37933740834863600792814893)
              ·
                refine ⟨14225152813073850297305585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37933740834863600792814893 14225152813073850297305585)
                ·
                  refine ⟨10668864609805387722979189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14225152813073850297305585 10668864609805387722979189)
                  ·
                    refine ⟨1000206057169255099029299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10668864609805387722979189 1000206057169255099029299)
                    ·
                      rfl

theorem cell23_5843683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 5].length) (baseStart_5843683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843683 prefixEnd_5843683 := by exact prefixLift 5843683
  have htrace : WordTrace (prefixWord ++ tailWord_5843683) baseStart_5843683 baseEnd_5843683 := by
    simpa [prefixWord, tailWord_5843683, baseEnd_5843683] using wordTrace_append hprefix tailTrace_5843683
  have hstable : (prefixWord ++ tailWord_5843683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843683).length < 2 ^ (prefixWord ++ tailWord_5843683).sum := by decide
  have hdescent : baseEnd_5843683 < baseStart_5843683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843703 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 2, 4, 2]
def baseStart_5843703 : Nat := 118140960795 + 5843703 * 2 ^ 59
def prefixEnd_5843703 : Nat := 4983230072969 + 3 ^ 40 * 5843703 * 2
def baseEnd_5843703 : Nat := 3000628441120855218837805

theorem tailTrace_5843703 : CollatzResearch.WordTrace tailWord_5843703 prefixEnd_5843703 3000628441120855218837805 := by
  unfold tailWord_5843703
  simp only [CollatzResearch.WordTrace]
  refine ⟨213137358348269530860679763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142091572232179687240453175 213137358348269530860679763)
  ·
    refine ⟨319706037522404296291019645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213137358348269530860679763 319706037522404296291019645)
    ·
      refine ⟨119889764070901611109132367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319706037522404296291019645 119889764070901611109132367)
      ·
        refine ⟨179834646106352416663698551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119889764070901611109132367 179834646106352416663698551)
        ·
          refine ⟨269751969159528624995547827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179834646106352416663698551 269751969159528624995547827)
          ·
            refine ⟨404627953739292937493321741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269751969159528624995547827 404627953739292937493321741)
            ·
              refine ⟨151735482652234851559995653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 404627953739292937493321741 151735482652234851559995653)
              ·
                refine ⟨28450402997294034667499185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151735482652234851559995653 28450402997294034667499185)
                ·
                  refine ⟨21337802247970526000624389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28450402997294034667499185 21337802247970526000624389)
                  ·
                    refine ⟨4000837921494473625117073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21337802247970526000624389 4000837921494473625117073)
                    ·
                      refine ⟨3000628441120855218837805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4000837921494473625117073 3000628441120855218837805)
                      ·
                        rfl

theorem cell23_5843703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 4, 2].length) (baseStart_5843703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843703 prefixEnd_5843703 := by exact prefixLift 5843703
  have htrace : WordTrace (prefixWord ++ tailWord_5843703) baseStart_5843703 baseEnd_5843703 := by
    simpa [prefixWord, tailWord_5843703, baseEnd_5843703] using wordTrace_append hprefix tailTrace_5843703
  have hstable : (prefixWord ++ tailWord_5843703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843703).length < 2 ^ (prefixWord ++ tailWord_5843703).sum := by decide
  have hdescent : baseEnd_5843703 < baseStart_5843703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843713 : List Nat := [1, 2, 4, 1, 1, 1, 1, 5, 3, 4]
def baseStart_5843713 : Nat := 118140960795 + 5843713 * 2 ^ 59
def prefixEnd_5843713 : Nat := 4983230072969 + 3 ^ 40 * 5843713 * 2
def baseEnd_5843713 : Nat := 1000211191975800059904253

theorem tailTrace_5843713 : CollatzResearch.WordTrace tailWord_5843713 prefixEnd_5843713 1000211191975800059904253 := by
  unfold tailWord_5843713
  simp only [CollatzResearch.WordTrace]
  refine ⟨213137723078233302568543793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142091815385488868379029195 213137723078233302568543793)
  ·
    refine ⟨159853292308674976926407845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213137723078233302568543793 159853292308674976926407845)
    ·
      refine ⟨29972492307876558173701471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159853292308674976926407845 29972492307876558173701471)
      ·
        refine ⟨44958738461814837260552207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29972492307876558173701471 44958738461814837260552207)
        ·
          refine ⟨67438107692722255890828311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44958738461814837260552207 67438107692722255890828311)
          ·
            refine ⟨101157161539083383836242467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67438107692722255890828311 101157161539083383836242467)
            ·
              refine ⟨151735742308625075754363701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101157161539083383836242467 151735742308625075754363701)
              ·
                refine ⟨14225225841433600851971597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151735742308625075754363701 14225225841433600851971597)
                ·
                  refine ⟨5334459690537600319489349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14225225841433600851971597 5334459690537600319489349)
                  ·
                    refine ⟨1000211191975800059904253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5334459690537600319489349 1000211191975800059904253)
                    ·
                      rfl

theorem cell23_5843713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_5843713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843713 prefixEnd_5843713 := by exact prefixLift 5843713
  have htrace : WordTrace (prefixWord ++ tailWord_5843713) baseStart_5843713 baseEnd_5843713 := by
    simpa [prefixWord, tailWord_5843713, baseEnd_5843713] using wordTrace_append hprefix tailTrace_5843713
  have hstable : (prefixWord ++ tailWord_5843713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843713).length < 2 ^ (prefixWord ++ tailWord_5843713).sum := by decide
  have hdescent : baseEnd_5843713 < baseStart_5843713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843720 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 2, 4, 2]
def baseStart_5843720 : Nat := 118140960795 + 5843720 * 2 ^ 59
def prefixEnd_5843720 : Nat := 4983230072969 + 3 ^ 40 * 5843720 * 2
def baseEnd_5843720 : Nat := 3000637170291981652325227

theorem tailTrace_5843720 : CollatzResearch.WordTrace tailWord_5843720 prefixEnd_5843720 3000637170291981652325227 := by
  unfold tailWord_5843720
  simp only [CollatzResearch.WordTrace]
  refine ⟨106568989194603971382024307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142091985592805295176032409 106568989194603971382024307)
  ·
    refine ⟨159853483791905957073036461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106568989194603971382024307 159853483791905957073036461)
    ·
      refine ⟨59945056421964733902388673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159853483791905957073036461 59945056421964733902388673)
      ·
        refine ⟨44958792316473550426791505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59945056421964733902388673 44958792316473550426791505)
        ·
          refine ⟨33719094237355162820093629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44958792316473550426791505 33719094237355162820093629)
          ·
            refine ⟨12644660339008186057535111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33719094237355162820093629 12644660339008186057535111)
            ·
              refine ⟨18966990508512279086302667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12644660339008186057535111 18966990508512279086302667)
              ·
                refine ⟨28450485762768418629454001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18966990508512279086302667 28450485762768418629454001)
                ·
                  refine ⟨21337864322076313972090501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28450485762768418629454001 21337864322076313972090501)
                  ·
                    refine ⟨4000849560389308869766969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21337864322076313972090501 4000849560389308869766969)
                    ·
                      refine ⟨3000637170291981652325227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4000849560389308869766969 3000637170291981652325227)
                      ·
                        rfl

theorem cell23_5843720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_5843720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843720 prefixEnd_5843720 := by exact prefixLift 5843720
  have htrace : WordTrace (prefixWord ++ tailWord_5843720) baseStart_5843720 baseEnd_5843720 := by
    simpa [prefixWord, tailWord_5843720, baseEnd_5843720] using wordTrace_append hprefix tailTrace_5843720
  have hstable : (prefixWord ++ tailWord_5843720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843720).length < 2 ^ (prefixWord ++ tailWord_5843720).sum := by decide
  have hdescent : baseEnd_5843720 < baseStart_5843720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843726 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 10]
def baseStart_5843726 : Nat := 118140960795 + 5843726 * 2 ^ 59
def prefixEnd_5843726 : Nat := 4983230072969 + 3 ^ 40 * 5843726 * 2
def baseEnd_5843726 : Nat := 333404472352878736538911

theorem tailTrace_5843726 : CollatzResearch.WordTrace tailWord_5843726 prefixEnd_5843726 333404472352878736538911 := by
  unfold tailWord_5843726
  simp only [CollatzResearch.WordTrace]
  refine ⟨26642274653398275723595879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142092131484790803859178021 26642274653398275723595879)
  ·
    refine ⟨39963411980097413585393819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26642274653398275723595879 39963411980097413585393819)
    ·
      refine ⟨59945117970146120378090729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39963411980097413585393819 59945117970146120378090729)
      ·
        refine ⟨44958838477609590283568047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59945117970146120378090729 44958838477609590283568047)
        ·
          refine ⟨67438257716414385425352071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44958838477609590283568047 67438257716414385425352071)
          ·
            refine ⟨101157386574621578138028107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67438257716414385425352071 101157386574621578138028107)
            ·
              refine ⟨151736079861932367207042161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101157386574621578138028107 151736079861932367207042161)
              ·
                refine ⟨113802059896449275405281621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151736079861932367207042161 113802059896449275405281621)
                ·
                  refine ⟨333404472352878736538911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 113802059896449275405281621 333404472352878736538911)
                  ·
                    rfl

theorem cell23_5843726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_5843726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843726 prefixEnd_5843726 := by exact prefixLift 5843726
  have htrace : WordTrace (prefixWord ++ tailWord_5843726) baseStart_5843726 baseEnd_5843726 := by
    simpa [prefixWord, tailWord_5843726, baseEnd_5843726] using wordTrace_append hprefix tailTrace_5843726
  have hstable : (prefixWord ++ tailWord_5843726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843726).length < 2 ^ (prefixWord ++ tailWord_5843726).sum := by decide
  have hdescent : baseEnd_5843726 < baseStart_5843726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843740 : List Nat := [2, 2, 3, 1, 1, 3, 3, 1, 2, 2, 3]
def baseStart_5843740 : Nat := 118140960795 + 5843740 * 2 ^ 59
def prefixEnd_5843740 : Nat := 4983230072969 + 3 ^ 40 * 5843740 * 2
def baseEnd_5843740 : Nat := 3000647439905071574075135

theorem tailTrace_5843740 : CollatzResearch.WordTrace tailWord_5843740 prefixEnd_5843740 3000647439905071574075135 := by
  unfold tailWord_5843740
  simp only [CollatzResearch.WordTrace]
  refine ⟨106569353924567743089888337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142092471899423657453184449 106569353924567743089888337)
  ·
    refine ⟨79927015443425807317416253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106569353924567743089888337 79927015443425807317416253)
    ·
      refine ⟨29972630791284677744031095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79927015443425807317416253 29972630791284677744031095)
      ·
        refine ⟨44958946186927016616046643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29972630791284677744031095 44958946186927016616046643)
        ·
          refine ⟨67438419280390524924069965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44958946186927016616046643 67438419280390524924069965)
          ·
            refine ⟨25289407230146446846526237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67438419280390524924069965 25289407230146446846526237)
            ·
              refine ⟨9483527711304917567447339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25289407230146446846526237 9483527711304917567447339)
              ·
                refine ⟨14225291566957376351171009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9483527711304917567447339 14225291566957376351171009)
                ·
                  refine ⟨10668968675218032263378257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14225291566957376351171009 10668968675218032263378257)
                  ·
                    refine ⟨8001726506413524197533693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10668968675218032263378257 8001726506413524197533693)
                    ·
                      refine ⟨3000647439905071574075135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8001726506413524197533693 3000647439905071574075135)
                      ·
                        rfl

theorem cell23_5843740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_5843740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843740 prefixEnd_5843740 := by exact prefixLift 5843740
  have htrace : WordTrace (prefixWord ++ tailWord_5843740) baseStart_5843740 baseEnd_5843740 := by
    simpa [prefixWord, tailWord_5843740, baseEnd_5843740] using wordTrace_append hprefix tailTrace_5843740
  have hstable : (prefixWord ++ tailWord_5843740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843740).length < 2 ^ (prefixWord ++ tailWord_5843740).sum := by decide
  have hdescent : baseEnd_5843740 < baseStart_5843740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843813 : List Nat := [1, 3, 1, 3, 1, 1, 3, 3, 1, 1, 5]
def baseStart_5843813 : Nat := 118140960795 + 5843813 * 2 ^ 59
def prefixEnd_5843813 : Nat := 4983230072969 + 3 ^ 40 * 5843813 * 2
def baseEnd_5843813 : Nat := 3000684923992849788462299

theorem tailTrace_5843813 : CollatzResearch.WordTrace tailWord_5843813 prefixEnd_5843813 3000684923992849788462299 := by
  unfold tailWord_5843813
  simp only [CollatzResearch.WordTrace]
  refine ⟨213141370377871019647184093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142094246918580679764789395 213141370377871019647184093)
  ·
    refine ⟨79928013891701632367694035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213141370377871019647184093 79928013891701632367694035)
    ·
      refine ⟨119892020837552448551541053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79928013891701632367694035 119892020837552448551541053)
      ·
        refine ⟨44959507814082168206827895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119892020837552448551541053 44959507814082168206827895)
        ·
          refine ⟨67439261721123252310241843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44959507814082168206827895 67439261721123252310241843)
          ·
            refine ⟨101158892581684878465362765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67439261721123252310241843 101158892581684878465362765)
            ·
              refine ⟨37934584718131829424511037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101158892581684878465362765 37934584718131829424511037)
              ·
                refine ⟨14225469269299436034191639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37934584718131829424511037 14225469269299436034191639)
                ·
                  refine ⟨21338203903949154051287459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14225469269299436034191639 21338203903949154051287459)
                  ·
                    refine ⟨32007305855923731076931189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21338203903949154051287459 32007305855923731076931189)
                    ·
                      refine ⟨3000684923992849788462299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32007305855923731076931189 3000684923992849788462299)
                      ·
                        rfl

theorem cell23_5843813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_5843813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843813 prefixEnd_5843813 := by exact prefixLift 5843813
  have htrace : WordTrace (prefixWord ++ tailWord_5843813) baseStart_5843813 baseEnd_5843813 := by
    simpa [prefixWord, tailWord_5843813, baseEnd_5843813] using wordTrace_append hprefix tailTrace_5843813
  have hstable : (prefixWord ++ tailWord_5843813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843813).length < 2 ^ (prefixWord ++ tailWord_5843813).sum := by decide
  have hdescent : baseEnd_5843813 < baseStart_5843813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843820 : List Nat := [2, 2, 1, 1, 4, 1, 2, 4, 2, 4]
def baseStart_5843820 : Nat := 118140960795 + 5843820 * 2 ^ 59
def prefixEnd_5843820 : Nat := 4983230072969 + 3 ^ 40 * 5843820 * 2
def baseEnd_5843820 : Nat := 1000229506119143753691589

theorem tailTrace_5843820 : CollatzResearch.WordTrace tailWord_5843820 prefixEnd_5843820 1000229506119143753691589 := by
  unfold tailWord_5843820
  simp only [CollatzResearch.WordTrace]
  refine ⟨106570812844422829921344457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142094417125897106561792609 106570812844422829921344457)
  ·
    refine ⟨79928109633317122441008343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106570812844422829921344457 79928109633317122441008343)
    ·
      refine ⟨119892164449975683661512515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79928109633317122441008343 119892164449975683661512515)
      ·
        refine ⟨179838246674963525492268773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119892164449975683661512515 179838246674963525492268773)
        ·
          refine ⟨33719671251555661029800395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179838246674963525492268773 33719671251555661029800395)
          ·
            refine ⟨50579506877333491544700593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33719671251555661029800395 50579506877333491544700593)
            ·
              refine ⟨37934630158000118658525445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50579506877333491544700593 37934630158000118658525445)
              ·
                refine ⟨7112743154625022248473521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37934630158000118658525445 7112743154625022248473521)
                ·
                  refine ⟨5334557365968766686355141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7112743154625022248473521 5334557365968766686355141)
                  ·
                    refine ⟨1000229506119143753691589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5334557365968766686355141 1000229506119143753691589)
                    ·
                      rfl

theorem cell23_5843820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 4].length) (baseStart_5843820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843820 prefixEnd_5843820 := by exact prefixLift 5843820
  have htrace : WordTrace (prefixWord ++ tailWord_5843820) baseStart_5843820 baseEnd_5843820 := by
    simpa [prefixWord, tailWord_5843820, baseEnd_5843820] using wordTrace_append hprefix tailTrace_5843820
  have hstable : (prefixWord ++ tailWord_5843820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843820).length < 2 ^ (prefixWord ++ tailWord_5843820).sum := by decide
  have hdescent : baseEnd_5843820 < baseStart_5843820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843827 : List Nat := [1, 1, 1, 2, 2, 1, 7, 1, 3, 2, 2]
def baseStart_5843827 : Nat := 118140960795 + 5843827 * 2 ^ 59
def prefixEnd_5843827 : Nat := 4983230072969 + 3 ^ 40 * 5843827 * 2
def baseEnd_5843827 : Nat := 3000692112722012733687235

theorem tailTrace_5843827 : CollatzResearch.WordTrace tailWord_5843827 prefixEnd_5843827 3000692112722012733687235 := by
  unfold tailWord_5843827
  simp only [CollatzResearch.WordTrace]
  refine ⟨213141880999820300038193735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142094587333213533358795823 213141880999820300038193735)
  ·
    refine ⟨319712821499730450057290603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213141880999820300038193735 319712821499730450057290603)
    ·
      refine ⟨479569232249595675085935905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319712821499730450057290603 479569232249595675085935905)
      ·
        refine ⟨359676924187196756314451929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479569232249595675085935905 359676924187196756314451929)
        ·
          refine ⟨269757693140397567235838947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359676924187196756314451929 269757693140397567235838947)
          ·
            refine ⟨404636539710596350853758421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269757693140397567235838947 404636539710596350853758421)
            ·
              refine ⟨9483668899467101973134963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 404636539710596350853758421 9483668899467101973134963)
              ·
                refine ⟨14225503349200652959702445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9483668899467101973134963 14225503349200652959702445)
                ·
                  refine ⟨5334563755950244859888417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14225503349200652959702445 5334563755950244859888417)
                  ·
                    refine ⟨4000922816962683644916313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5334563755950244859888417 4000922816962683644916313)
                    ·
                      refine ⟨3000692112722012733687235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4000922816962683644916313 3000692112722012733687235)
                      ·
                        rfl

theorem cell23_5843827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 2, 2].length) (baseStart_5843827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843827 prefixEnd_5843827 := by exact prefixLift 5843827
  have htrace : WordTrace (prefixWord ++ tailWord_5843827) baseStart_5843827 baseEnd_5843827 := by
    simpa [prefixWord, tailWord_5843827, baseEnd_5843827] using wordTrace_append hprefix tailTrace_5843827
  have hstable : (prefixWord ++ tailWord_5843827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843827).length < 2 ^ (prefixWord ++ tailWord_5843827).sum := by decide
  have hdescent : baseEnd_5843827 < baseStart_5843827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843833 : List Nat := [1, 2, 1, 3, 2, 4, 2, 8]
def baseStart_5843833 : Nat := 118140960795 + 5843833 * 2 ^ 59
def prefixEnd_5843833 : Nat := 4983230072969 + 3 ^ 40 * 5843833 * 2
def baseEnd_5843833 : Nat := 111136859022442211489341

theorem tailTrace_5843833 : CollatzResearch.WordTrace tailWord_5843833 prefixEnd_5843833 111136859022442211489341 := by
  unfold tailWord_5843833
  simp only [CollatzResearch.WordTrace]
  refine ⟨213142099837798563062912153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142094733225199042041941435 213142099837798563062912153)
  ·
    refine ⟨159856574878348922297184115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213142099837798563062912153 159856574878348922297184115)
    ·
      refine ⟨239784862317523383445776173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159856574878348922297184115 239784862317523383445776173)
      ·
        refine ⟨89919323369071268792166065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239784862317523383445776173 89919323369071268792166065)
        ·
          refine ⟨67439492526803451594124549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89919323369071268792166065 67439492526803451594124549)
          ·
            refine ⟨12644904848775647173898353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67439492526803451594124549 12644904848775647173898353)
            ·
              refine ⟨9483678636581735380423765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12644904848775647173898353 9483678636581735380423765)
              ·
                refine ⟨111136859022442211489341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9483678636581735380423765 111136859022442211489341)
                ·
                  rfl

theorem cell23_5843833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 8].length) (baseStart_5843833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843833 prefixEnd_5843833 := by exact prefixLift 5843833
  have htrace : WordTrace (prefixWord ++ tailWord_5843833) baseStart_5843833 baseEnd_5843833 := by
    simpa [prefixWord, tailWord_5843833, baseEnd_5843833] using wordTrace_append hprefix tailTrace_5843833
  have hstable : (prefixWord ++ tailWord_5843833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843833).length < 2 ^ (prefixWord ++ tailWord_5843833).sum := by decide
  have hdescent : baseEnd_5843833 < baseStart_5843833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843837 : List Nat := [1, 4, 1, 1, 2, 1, 6, 1, 2, 4]
def baseStart_5843837 : Nat := 118140960795 + 5843837 * 2 ^ 59
def prefixEnd_5843837 : Nat := 4983230072969 + 3 ^ 40 * 5843837 * 2
def baseEnd_5843837 : Nat := 1000232415842852564854063

theorem tailTrace_5843837 : CollatzResearch.WordTrace tailWord_5843837 prefixEnd_5843837 1000232415842852564854063 := by
  unfold tailWord_5843837
  simp only [CollatzResearch.WordTrace]
  refine ⟨213142245729784071746057765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142094830486522714497371843 213142245729784071746057765)
  ·
    refine ⟨39964171074334513452385831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213142245729784071746057765 39964171074334513452385831)
    ·
      refine ⟨59946256611501770178578747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39964171074334513452385831 59946256611501770178578747)
      ·
        refine ⟨89919384917252655267868121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59946256611501770178578747 89919384917252655267868121)
        ·
          refine ⟨67439538687939491450901091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89919384917252655267868121 67439538687939491450901091)
          ·
            refine ⟨101159308031909237176351637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67439538687939491450901091 101159308031909237176351637)
            ·
              refine ⟨4741842563995745492641483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101159308031909237176351637 4741842563995745492641483)
              ·
                refine ⟨7112763845993618238962225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4741842563995745492641483 7112763845993618238962225)
                ·
                  refine ⟨5334572884495213679221669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7112763845993618238962225 5334572884495213679221669)
                  ·
                    refine ⟨1000232415842852564854063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5334572884495213679221669 1000232415842852564854063)
                    ·
                      rfl

theorem cell23_5843837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_5843837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843837 prefixEnd_5843837 := by exact prefixLift 5843837
  have htrace : WordTrace (prefixWord ++ tailWord_5843837) baseStart_5843837 baseEnd_5843837 := by
    simpa [prefixWord, tailWord_5843837, baseEnd_5843837] using wordTrace_append hprefix tailTrace_5843837
  have hstable : (prefixWord ++ tailWord_5843837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843837).length < 2 ^ (prefixWord ++ tailWord_5843837).sum := by decide
  have hdescent : baseEnd_5843837 < baseStart_5843837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843847 : List Nat := [1, 1, 4, 2, 3, 1, 3, 2, 1, 2, 3]
def baseStart_5843847 : Nat := 118140960795 + 5843847 * 2 ^ 59
def prefixEnd_5843847 : Nat := 4983230072969 + 3 ^ 40 * 5843847 * 2
def baseEnd_5843847 : Nat := 3000702382335102655437143

theorem tailTrace_5843847 : CollatzResearch.WordTrace tailWord_5843847 prefixEnd_5843847 3000702382335102655437143 := by
  unfold tailWord_5843847
  simp only [CollatzResearch.WordTrace]
  refine ⟨213142610459747843453921795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142095073639831895635947863 213142610459747843453921795)
  ·
    refine ⟨319713915689621765180882693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213142610459747843453921795 319713915689621765180882693)
    ·
      refine ⟨59946359191804080971415505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319713915689621765180882693 59946359191804080971415505)
      ·
        refine ⟨44959769393853060728561629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59946359191804080971415505 44959769393853060728561629)
        ·
          refine ⟨16859913522694897773210611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44959769393853060728561629 16859913522694897773210611)
          ·
            refine ⟨25289870284042346659815917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16859913522694897773210611 25289870284042346659815917)
            ·
              refine ⟨9483701356515879997430969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25289870284042346659815917 9483701356515879997430969)
              ·
                refine ⟨7112776017386909998073227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9483701356515879997430969 7112776017386909998073227)
                ·
                  refine ⟨10669164026080364997109841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7112776017386909998073227 10669164026080364997109841)
                  ·
                    refine ⟨8001873019560273747832381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10669164026080364997109841 8001873019560273747832381)
                    ·
                      refine ⟨3000702382335102655437143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8001873019560273747832381 3000702382335102655437143)
                      ·
                        rfl

theorem cell23_5843847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_5843847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843847 prefixEnd_5843847 := by exact prefixLift 5843847
  have htrace : WordTrace (prefixWord ++ tailWord_5843847) baseStart_5843847 baseEnd_5843847 := by
    simpa [prefixWord, tailWord_5843847, baseEnd_5843847] using wordTrace_append hprefix tailTrace_5843847
  have hstable : (prefixWord ++ tailWord_5843847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843847).length < 2 ^ (prefixWord ++ tailWord_5843847).sum := by decide
  have hdescent : baseEnd_5843847 < baseStart_5843847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843903 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 5]
def baseStart_5843903 : Nat := 118140960795 + 5843903 * 2 ^ 59
def prefixEnd_5843903 : Nat := 4983230072969 + 3 ^ 40 * 5843903 * 2
def baseEnd_5843903 : Nat := 3000731137251754436336885

theorem tailTrace_5843903 : CollatzResearch.WordTrace tailWord_5843903 prefixEnd_5843903 3000731137251754436336885 := by
  unfold tailWord_5843903
  simp only [CollatzResearch.WordTrace]
  refine ⟨213144652947544965017960363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142096435298363310011973575 213144652947544965017960363)
  ·
    refine ⟨319716979421317447526940545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213144652947544965017960363 319716979421317447526940545)
    ·
      refine ⟨239787734565988085645205409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319716979421317447526940545 239787734565988085645205409)
      ·
        refine ⟨179840800924491064233904057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239787734565988085645205409 179840800924491064233904057)
        ·
          refine ⟨134880600693368298175428043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179840800924491064233904057 134880600693368298175428043)
          ·
            refine ⟨202320901040052447263142065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134880600693368298175428043 202320901040052447263142065)
            ·
              refine ⟨151740675780039335447356549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202320901040052447263142065 151740675780039335447356549)
              ·
                refine ⟨28451376708757375396379353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151740675780039335447356549 28451376708757375396379353)
                ·
                  refine ⟨21338532531568031547284515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28451376708757375396379353 21338532531568031547284515)
                  ·
                    refine ⟨32007798797352047320926773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21338532531568031547284515 32007798797352047320926773)
                    ·
                      refine ⟨3000731137251754436336885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32007798797352047320926773 3000731137251754436336885)
                      ·
                        rfl

theorem cell23_5843903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_5843903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843903 prefixEnd_5843903 := by exact prefixLift 5843903
  have htrace : WordTrace (prefixWord ++ tailWord_5843903) baseStart_5843903 baseEnd_5843903 := by
    simpa [prefixWord, tailWord_5843903, baseEnd_5843903] using wordTrace_append hprefix tailTrace_5843903
  have hstable : (prefixWord ++ tailWord_5843903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843903).length < 2 ^ (prefixWord ++ tailWord_5843903).sum := by decide
  have hdescent : baseEnd_5843903 < baseStart_5843903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843913 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 6, 2, 4]
def baseStart_5843913 : Nat := 118140960795 + 5843913 * 2 ^ 59
def prefixEnd_5843913 : Nat := 4983230072969 + 3 ^ 40 * 5843913 * 2
def baseEnd_5843913 : Nat := 3000736272058299397211839

theorem tailTrace_5843913 : CollatzResearch.WordTrace tailWord_5843913 prefixEnd_5843913 3000736272058299397211839 := by
  unfold tailWord_5843913
  simp only [CollatzResearch.WordTrace]
  refine ⟨213145017677508736725824393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142096678451672491150549595 213145017677508736725824393)
  ·
    refine ⟨159858763258131552544368295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213145017677508736725824393 159858763258131552544368295)
    ·
      refine ⟨239788144887197328816552443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159858763258131552544368295 239788144887197328816552443)
      ·
        refine ⟨359682217330795993224828665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239788144887197328816552443 359682217330795993224828665)
        ·
          refine ⟨269761662998096994918621499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359682217330795993224828665 269761662998096994918621499)
          ·
            refine ⟨404642494497145492377932249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269761662998096994918621499 404642494497145492377932249)
            ·
              refine ⟨303481870872859119283449187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404642494497145492377932249 303481870872859119283449187)
              ·
                refine ⟨455222806309288678925173781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303481870872859119283449187 455222806309288678925173781)
                ·
                  refine ⟨21338569045747906824617521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 455222806309288678925173781 21338569045747906824617521)
                  ·
                    refine ⟨16003926784310930118463141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21338569045747906824617521 16003926784310930118463141)
                    ·
                      refine ⟨3000736272058299397211839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16003926784310930118463141 3000736272058299397211839)
                      ·
                        rfl

theorem cell23_5843913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 2, 4].length) (baseStart_5843913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843913 prefixEnd_5843913 := by exact prefixLift 5843913
  have htrace : WordTrace (prefixWord ++ tailWord_5843913) baseStart_5843913 baseEnd_5843913 := by
    simpa [prefixWord, tailWord_5843913, baseEnd_5843913] using wordTrace_append hprefix tailTrace_5843913
  have hstable : (prefixWord ++ tailWord_5843913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843913).length < 2 ^ (prefixWord ++ tailWord_5843913).sum := by decide
  have hdescent : baseEnd_5843913 < baseStart_5843913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843930 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4]
def baseStart_5843930 : Nat := 118140960795 + 5843930 * 2 ^ 59
def prefixEnd_5843930 : Nat := 4983230072969 + 3 ^ 40 * 5843930 * 2
def baseEnd_5843930 : Nat := 3000745001229425830699261

theorem tailTrace_5843930 : CollatzResearch.WordTrace tailWord_5843930 prefixEnd_5843930 3000745001229425830699261 := by
  unfold tailWord_5843930
  simp only [CollatzResearch.WordTrace]
  refine ⟨53286409429611787157298311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142097091812298099086128829 53286409429611787157298311)
  ·
    refine ⟨79929614144417680735947467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53286409429611787157298311 79929614144417680735947467)
    ·
      refine ⟨119894421216626521103921201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79929614144417680735947467 119894421216626521103921201)
      ·
        refine ⟨89920815912469890827940901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119894421216626521103921201 89920815912469890827940901)
        ·
          refine ⟨16860152983588104530238919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89920815912469890827940901 16860152983588104530238919)
          ·
            refine ⟨25290229475382156795358379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16860152983588104530238919 25290229475382156795358379)
            ·
              refine ⟨37935344213073235193037569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25290229475382156795358379 37935344213073235193037569)
              ·
                refine ⟨28451508159804926394778177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37935344213073235193037569 28451508159804926394778177)
                ·
                  refine ⟨21338631119853694796083633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28451508159804926394778177 21338631119853694796083633)
                  ·
                    refine ⟨16003973339890271097062725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21338631119853694796083633 16003973339890271097062725)
                    ·
                      refine ⟨3000745001229425830699261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16003973339890271097062725 3000745001229425830699261)
                      ·
                        rfl

theorem cell23_5843930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_5843930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843930 prefixEnd_5843930 := by exact prefixLift 5843930
  have htrace : WordTrace (prefixWord ++ tailWord_5843930) baseStart_5843930 baseEnd_5843930 := by
    simpa [prefixWord, tailWord_5843930, baseEnd_5843930] using wordTrace_append hprefix tailTrace_5843930
  have hstable : (prefixWord ++ tailWord_5843930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843930).length < 2 ^ (prefixWord ++ tailWord_5843930).sum := by decide
  have hdescent : baseEnd_5843930 < baseStart_5843930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843951 : List Nat := [1, 1, 2, 1, 4, 4, 3, 1, 2, 2, 2]
def baseStart_5843951 : Nat := 118140960795 + 5843951 * 2 ^ 59
def prefixEnd_5843951 : Nat := 4983230072969 + 3 ^ 40 * 5843951 * 2
def baseEnd_5843951 : Nat := 3000755784323170248536665

theorem tailTrace_5843951 : CollatzResearch.WordTrace tailWord_5843951 prefixEnd_5843951 3000755784323170248536665 := by
  unfold tailWord_5843951
  simp only [CollatzResearch.WordTrace]
  refine ⟨213146403651371069215707707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142097602434247379477138471 213146403651371069215707707)
  ·
    refine ⟨319719605477056603823561561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213146403651371069215707707 319719605477056603823561561)
    ·
      refine ⟨239789704107792452867671171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319719605477056603823561561 239789704107792452867671171)
      ·
        refine ⟨359684556161688679301506757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239789704107792452867671171 359684556161688679301506757)
        ·
          refine ⟨67440854280316627369032517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 359684556161688679301506757 67440854280316627369032517)
          ·
            refine ⟨12645160177559367631693597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67440854280316627369032517 12645160177559367631693597)
            ·
              refine ⟨4741935066584762861885099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12645160177559367631693597 4741935066584762861885099)
              ·
                refine ⟨7112902599877144292827649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4741935066584762861885099 7112902599877144292827649)
                ·
                  refine ⟨5334676949907858219620737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7112902599877144292827649 5334676949907858219620737)
                  ·
                    refine ⟨4001007712430893664715553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5334676949907858219620737 4001007712430893664715553)
                    ·
                      refine ⟨3000755784323170248536665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4001007712430893664715553 3000755784323170248536665)
                      ·
                        rfl

theorem cell23_5843951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 2, 2, 2].length) (baseStart_5843951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843951 prefixEnd_5843951 := by exact prefixLift 5843951
  have htrace : WordTrace (prefixWord ++ tailWord_5843951) baseStart_5843951 baseEnd_5843951 := by
    simpa [prefixWord, tailWord_5843951, baseEnd_5843951] using wordTrace_append hprefix tailTrace_5843951
  have hstable : (prefixWord ++ tailWord_5843951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843951).length < 2 ^ (prefixWord ++ tailWord_5843951).sum := by decide
  have hdescent : baseEnd_5843951 < baseStart_5843951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843963 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 5]
def baseStart_5843963 : Nat := 118140960795 + 5843963 * 2 ^ 59
def prefixEnd_5843963 : Nat := 4983230072969 + 3 ^ 40 * 5843963 * 2
def baseEnd_5843963 : Nat := 3000761946091024201586609

theorem tailTrace_5843963 : CollatzResearch.WordTrace tailWord_5843963 prefixEnd_5843963 3000761946091024201586609 := by
  unfold tailWord_5843963
  simp only [CollatzResearch.WordTrace]
  refine ⟨213146841327327595265144543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142097894218218396843429695 213146841327327595265144543)
  ·
    refine ⟨319720261990991392897716815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213146841327327595265144543 319720261990991392897716815)
    ·
      refine ⟨479580392986487089346575223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319720261990991392897716815 479580392986487089346575223)
      ·
        refine ⟨719370589479730634019862835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479580392986487089346575223 719370589479730634019862835)
        ·
          refine ⟨1079055884219595951029794253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719370589479730634019862835 1079055884219595951029794253)
          ·
            refine ⟨404645956582348481636172845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1079055884219595951029794253 404645956582348481636172845)
            ·
              refine ⟨151742233718380680613564817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 404645956582348481636172845 151742233718380680613564817)
              ·
                refine ⟨113806675288785510460173613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151742233718380680613564817 113806675288785510460173613)
                ·
                  refine ⟨42677503233294566422565105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113806675288785510460173613 42677503233294566422565105)
                  ·
                    refine ⟨32008127424970924816923829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42677503233294566422565105 32008127424970924816923829)
                    ·
                      refine ⟨3000761946091024201586609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32008127424970924816923829 3000761946091024201586609)
                      ·
                        rfl

theorem cell23_5843963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 5].length) (baseStart_5843963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843963 prefixEnd_5843963 := by exact prefixLift 5843963
  have htrace : WordTrace (prefixWord ++ tailWord_5843963) baseStart_5843963 baseEnd_5843963 := by
    simpa [prefixWord, tailWord_5843963, baseEnd_5843963] using wordTrace_append hprefix tailTrace_5843963
  have hstable : (prefixWord ++ tailWord_5843963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843963).length < 2 ^ (prefixWord ++ tailWord_5843963).sum := by decide
  have hdescent : baseEnd_5843963 < baseStart_5843963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5843997 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 1, 2, 5]
def baseStart_5843997 : Nat := 118140960795 + 5843997 * 2 ^ 59
def prefixEnd_5843997 : Nat := 4983230072969 + 3 ^ 40 * 5843997 * 2
def baseEnd_5843997 : Nat := 3000779404433277068561453

theorem tailTrace_5843997 : CollatzResearch.WordTrace tailWord_5843997 prefixEnd_5843997 3000779404433277068561453 := by
  unfold tailWord_5843997
  simp only [CollatzResearch.WordTrace]
  refine ⟨213148081409204419071882245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142098720939469612714588163 213148081409204419071882245)
  ·
    refine ⟨39965265264225828575977921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213148081409204419071882245 39965265264225828575977921)
    ·
      refine ⟨29973948948169371431983441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39965265264225828575977921 29973948948169371431983441)
      ·
        refine ⟨22480461711127028573987581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29973948948169371431983441 22480461711127028573987581)
        ·
          refine ⟨8430173141672635715245343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22480461711127028573987581 8430173141672635715245343)
          ·
            refine ⟨12645259712508953572868015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8430173141672635715245343 12645259712508953572868015)
            ·
              refine ⟨18967889568763430359302023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12645259712508953572868015 18967889568763430359302023)
              ·
                refine ⟨28451834353145145538953035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18967889568763430359302023 28451834353145145538953035)
                ·
                  refine ⟨42677751529717718308429553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28451834353145145538953035 42677751529717718308429553)
                  ·
                    refine ⟨32008313647288288731322165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42677751529717718308429553 32008313647288288731322165)
                    ·
                      refine ⟨3000779404433277068561453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32008313647288288731322165 3000779404433277068561453)
                      ·
                        rfl

theorem cell23_5843997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_5843997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5843997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5843997 prefixEnd_5843997 := by exact prefixLift 5843997
  have htrace : WordTrace (prefixWord ++ tailWord_5843997) baseStart_5843997 baseEnd_5843997 := by
    simpa [prefixWord, tailWord_5843997, baseEnd_5843997] using wordTrace_append hprefix tailTrace_5843997
  have hstable : (prefixWord ++ tailWord_5843997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5843997).length < 2 ^ (prefixWord ++ tailWord_5843997).sum := by decide
  have hdescent : baseEnd_5843997 < baseStart_5843997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5843997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844067 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 1, 5, 2]
def baseStart_5844067 : Nat := 118140960795 + 5844067 * 2 ^ 59
def prefixEnd_5844067 : Nat := 4983230072969 + 3 ^ 40 * 5844067 * 2
def baseEnd_5844067 : Nat := 3000815348079091794686131

theorem tailTrace_5844067 : CollatzResearch.WordTrace tailWord_5844067 prefixEnd_5844067 3000815348079091794686131 := by
  unfold tailWord_5844067
  simp only [CollatzResearch.WordTrace]
  refine ⟨213150634518950821026930455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142100423012633880684620303 213150634518950821026930455)
  ·
    refine ⟨319725951778426231540395683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213150634518950821026930455 319725951778426231540395683)
    ·
      refine ⟨479588927667639347310593525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319725951778426231540395683 479588927667639347310593525)
      ·
        refine ⟨44961461968841188810368143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 479588927667639347310593525 44961461968841188810368143)
        ·
          refine ⟨67442192953261783215552215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44961461968841188810368143 67442192953261783215552215)
          ·
            refine ⟨101163289429892674823328323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67442192953261783215552215 101163289429892674823328323)
            ·
              refine ⟨151744934144839012234992485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101163289429892674823328323 151744934144839012234992485)
              ·
                refine ⟨28452175152157314794061091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151744934144839012234992485 28452175152157314794061091)
                ·
                  refine ⟨42678262728235972191091637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28452175152157314794061091 42678262728235972191091637)
                  ·
                    refine ⟨4001087130772122392914841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42678262728235972191091637 4001087130772122392914841)
                    ·
                      refine ⟨3000815348079091794686131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4001087130772122392914841 3000815348079091794686131)
                      ·
                        rfl

theorem cell23_5844067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_5844067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844067 prefixEnd_5844067 := by exact prefixLift 5844067
  have htrace : WordTrace (prefixWord ++ tailWord_5844067) baseStart_5844067 baseEnd_5844067 := by
    simpa [prefixWord, tailWord_5844067, baseEnd_5844067] using wordTrace_append hprefix tailTrace_5844067
  have hstable : (prefixWord ++ tailWord_5844067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844067).length < 2 ^ (prefixWord ++ tailWord_5844067).sum := by decide
  have hdescent : baseEnd_5844067 < baseStart_5844067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844074 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 5, 1, 3]
def baseStart_5844074 : Nat := 118140960795 + 5844074 * 2 ^ 59
def prefixEnd_5844074 : Nat := 4983230072969 + 3 ^ 40 * 5844074 * 2
def baseEnd_5844074 : Nat := 3000818942443673267298599

theorem tailTrace_5844074 : CollatzResearch.WordTrace tailWord_5844074 prefixEnd_5844074 3000818942443673267298599 := by
  unfold tailWord_5844074
  simp only [CollatzResearch.WordTrace]
  refine ⟨53287722457481365305608819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142100593219950307481623517 53287722457481365305608819)
  ·
    refine ⟨79931583686222047958413229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53287722457481365305608819 79931583686222047958413229)
    ·
      refine ⟨29974343882333267984404961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79931583686222047958413229 29974343882333267984404961)
      ·
        refine ⟨22480757911749950988303721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29974343882333267984404961 22480757911749950988303721)
        ·
          refine ⟨16860568433812463241227791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22480757911749950988303721 16860568433812463241227791)
          ·
            refine ⟨25290852650718694861841687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16860568433812463241227791 25290852650718694861841687)
            ·
              refine ⟨37936278976078042292762531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25290852650718694861841687 37936278976078042292762531)
              ·
                refine ⟨56904418464117063439143797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37936278976078042292762531 56904418464117063439143797)
                ·
                  refine ⟨5334789231010974697419731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56904418464117063439143797 5334789231010974697419731)
                  ·
                    refine ⟨8002183846516462046129597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5334789231010974697419731 8002183846516462046129597)
                    ·
                      refine ⟨3000818942443673267298599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8002183846516462046129597 3000818942443673267298599)
                      ·
                        rfl

theorem cell23_5844074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_5844074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844074 prefixEnd_5844074 := by exact prefixLift 5844074
  have htrace : WordTrace (prefixWord ++ tailWord_5844074) baseStart_5844074 baseEnd_5844074 := by
    simpa [prefixWord, tailWord_5844074, baseEnd_5844074] using wordTrace_append hprefix tailTrace_5844074
  have hstable : (prefixWord ++ tailWord_5844074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844074).length < 2 ^ (prefixWord ++ tailWord_5844074).sum := by decide
  have hdescent : baseEnd_5844074 < baseStart_5844074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844077 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_5844077 : Nat := 118140960795 + 5844077 * 2 ^ 59
def prefixEnd_5844077 : Nat := 4983230072969 + 3 ^ 40 * 5844077 * 2
def baseEnd_5844077 : Nat := 1000273494295212251853695

theorem tailTrace_5844077 : CollatzResearch.WordTrace tailWord_5844077 prefixEnd_5844077 1000273494295212251853695 := by
  unfold tailWord_5844077
  simp only [CollatzResearch.WordTrace]
  refine ⟨213150999248914592734794485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142100666165943061823196323 213150999248914592734794485)
  ·
    refine ⟨19982906179585743068886983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 213150999248914592734794485 19982906179585743068886983)
    ·
      refine ⟨29974359269378614603330475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19982906179585743068886983 29974359269378614603330475)
      ·
        refine ⟨44961538904067921904995713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29974359269378614603330475 44961538904067921904995713)
        ·
          refine ⟨33721154178050941428746785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44961538904067921904995713 33721154178050941428746785)
          ·
            refine ⟨25290865633538206071560089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33721154178050941428746785 25290865633538206071560089)
            ·
              refine ⟨18968149225153654553670067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25290865633538206071560089 18968149225153654553670067)
              ·
                refine ⟨28452223837730481830505101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18968149225153654553670067 28452223837730481830505101)
                ·
                  refine ⟨10669583939148930686439413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28452223837730481830505101 10669583939148930686439413)
                  ·
                    refine ⟨1000273494295212251853695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10669583939148930686439413 1000273494295212251853695)
                    ·
                      rfl

theorem cell23_5844077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_5844077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844077 prefixEnd_5844077 := by exact prefixLift 5844077
  have htrace : WordTrace (prefixWord ++ tailWord_5844077) baseStart_5844077 baseEnd_5844077 := by
    simpa [prefixWord, tailWord_5844077, baseEnd_5844077] using wordTrace_append hprefix tailTrace_5844077
  have hstable : (prefixWord ++ tailWord_5844077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844077).length < 2 ^ (prefixWord ++ tailWord_5844077).sum := by decide
  have hdescent : baseEnd_5844077 < baseStart_5844077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844117 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 3, 2, 3]
def baseStart_5844117 : Nat := 118140960795 + 5844117 * 2 ^ 59
def prefixEnd_5844117 : Nat := 4983230072969 + 3 ^ 40 * 5844117 * 2
def baseEnd_5844117 : Nat := 3000841022111816599060901

theorem tailTrace_5844117 : CollatzResearch.WordTrace tailWord_5844117 prefixEnd_5844117 3000841022111816599060901 := by
  unfold tailWord_5844117
  simp only [CollatzResearch.WordTrace]
  refine ⟨213152458168769679566250605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142101638779179786377500403 213152458168769679566250605)
  ·
    refine ⟨79932171813288629837343977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213152458168769679566250605 79932171813288629837343977)
    ·
      refine ⟨59949128859966472378007983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79932171813288629837343977 59949128859966472378007983)
      ·
        refine ⟨89923693289949708567011975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59949128859966472378007983 89923693289949708567011975)
        ·
          refine ⟨134885539934924562850517963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89923693289949708567011975 134885539934924562850517963)
          ·
            refine ⟨202328309902386844275776945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134885539934924562850517963 202328309902386844275776945)
            ·
              refine ⟨151746232426790133206832709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202328309902386844275776945 151746232426790133206832709)
              ·
                refine ⟨28452418580023149976281133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151746232426790133206832709 28452418580023149976281133)
                ·
                  refine ⟨10669656967508681241105425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28452418580023149976281133 10669656967508681241105425)
                  ·
                    refine ⟨8002242725631510930829069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10669656967508681241105425 8002242725631510930829069)
                    ·
                      refine ⟨3000841022111816599060901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8002242725631510930829069 3000841022111816599060901)
                      ·
                        rfl

theorem cell23_5844117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_5844117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844117 prefixEnd_5844117 := by exact prefixLift 5844117
  have htrace : WordTrace (prefixWord ++ tailWord_5844117) baseStart_5844117 baseEnd_5844117 := by
    simpa [prefixWord, tailWord_5844117, baseEnd_5844117] using wordTrace_append hprefix tailTrace_5844117
  have hstable : (prefixWord ++ tailWord_5844117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844117).length < 2 ^ (prefixWord ++ tailWord_5844117).sum := by decide
  have hdescent : baseEnd_5844117 < baseStart_5844117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844124 : List Nat := [2, 2, 3, 2, 1, 4, 1, 1, 1, 6]
def baseStart_5844124 : Nat := 118140960795 + 5844124 * 2 ^ 59
def prefixEnd_5844124 : Nat := 4983230072969 + 3 ^ 40 * 5844124 * 2
def baseEnd_5844124 : Nat := 1000281538825466023891123

theorem tailTrace_5844124 : CollatzResearch.WordTrace tailWord_5844124 prefixEnd_5844124 1000281538825466023891123 := by
  unfold tailWord_5844124
  simp only [CollatzResearch.WordTrace]
  refine ⟨106576356739872159880877713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142101808986496213174503617 106576356739872159880877713)
  ·
    refine ⟨79932267554904119910658285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106576356739872159880877713 79932267554904119910658285)
    ·
      refine ⟨29974600333089044966496857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79932267554904119910658285 29974600333089044966496857)
      ·
        refine ⟨22480950249816783724872643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29974600333089044966496857 22480950249816783724872643)
        ·
          refine ⟨33721425374725175587308965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22480950249816783724872643 33721425374725175587308965)
          ·
            refine ⟨6322767257760970422620431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33721425374725175587308965 6322767257760970422620431)
            ·
              refine ⟨9484150886641455633930647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6322767257760970422620431 9484150886641455633930647)
              ·
                refine ⟨14226226329962183450895971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9484150886641455633930647 14226226329962183450895971)
                ·
                  refine ⟨21339339494943275176343957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14226226329962183450895971 21339339494943275176343957)
                  ·
                    refine ⟨1000281538825466023891123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21339339494943275176343957 1000281538825466023891123)
                    ·
                      rfl

theorem cell23_5844124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_5844124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844124 prefixEnd_5844124 := by exact prefixLift 5844124
  have htrace : WordTrace (prefixWord ++ tailWord_5844124) baseStart_5844124 baseEnd_5844124 := by
    simpa [prefixWord, tailWord_5844124, baseEnd_5844124] using wordTrace_append hprefix tailTrace_5844124
  have hstable : (prefixWord ++ tailWord_5844124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844124).length < 2 ^ (prefixWord ++ tailWord_5844124).sum := by decide
  have hdescent : baseEnd_5844124 < baseStart_5844124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844147 : List Nat := [1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 3]
def baseStart_5844147 : Nat := 118140960795 + 5844147 * 2 ^ 59
def prefixEnd_5844147 : Nat := 4983230072969 + 3 ^ 40 * 5844147 * 2
def baseEnd_5844147 : Nat := 3000856426531451481685763

theorem tailTrace_5844147 : CollatzResearch.WordTrace tailWord_5844147 prefixEnd_5844147 3000856426531451481685763 := by
  unfold tailWord_5844147
  simp only [CollatzResearch.WordTrace]
  refine ⟨213153552358660994689842695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142102368239107329793228463 213153552358660994689842695)
  ·
    refine ⟨319730328537991492034764043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213153552358660994689842695 319730328537991492034764043)
    ·
      refine ⟨479595492806987238052146065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319730328537991492034764043 479595492806987238052146065)
      ·
        refine ⟨359696619605240428539109549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479595492806987238052146065 359696619605240428539109549)
        ·
          refine ⟨134886232351965160702166081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359696619605240428539109549 134886232351965160702166081)
          ·
            refine ⟨101164674263973870526624561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134886232351965160702166081 101164674263973870526624561)
            ·
              refine ⟨75873505697980402894968421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101164674263973870526624561 75873505697980402894968421)
              ·
                refine ⟨14226282318371325542806579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75873505697980402894968421 14226282318371325542806579)
                ·
                  refine ⟨21339423477556988314209869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14226282318371325542806579 21339423477556988314209869)
                  ·
                    refine ⟨8002283804083870617828701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21339423477556988314209869 8002283804083870617828701)
                    ·
                      refine ⟨3000856426531451481685763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8002283804083870617828701 3000856426531451481685763)
                      ·
                        rfl

theorem cell23_5844147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 3].length) (baseStart_5844147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844147 prefixEnd_5844147 := by exact prefixLift 5844147
  have htrace : WordTrace (prefixWord ++ tailWord_5844147) baseStart_5844147 baseEnd_5844147 := by
    simpa [prefixWord, tailWord_5844147, baseEnd_5844147] using wordTrace_append hprefix tailTrace_5844147
  have hstable : (prefixWord ++ tailWord_5844147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844147).length < 2 ^ (prefixWord ++ tailWord_5844147).sum := by decide
  have hdescent : baseEnd_5844147 < baseStart_5844147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844191 : List Nat := [1, 1, 2, 3, 2, 1, 5, 2, 1, 3, 2]
def baseStart_5844191 : Nat := 118140960795 + 5844191 * 2 ^ 59
def prefixEnd_5844191 : Nat := 4983230072969 + 3 ^ 40 * 5844191 * 2
def baseEnd_5844191 : Nat := 3000879019680249309535561

theorem tailTrace_5844191 : CollatzResearch.WordTrace tailWord_5844191 prefixEnd_5844191 3000879019680249309535561 := by
  unfold tailWord_5844191
  simp only [CollatzResearch.WordTrace]
  refine ⟨213155157170501590204444427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142103438113667726802962951 213155157170501590204444427)
  ·
    refine ⟨319732735755752385306666641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213155157170501590204444427 319732735755752385306666641)
    ·
      refine ⟨239799551816814288979999981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319732735755752385306666641 239799551816814288979999981)
      ·
        refine ⟨89924831931305358367499993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239799551816814288979999981 89924831931305358367499993)
        ·
          refine ⟨67443623948479018775624995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89924831931305358367499993 67443623948479018775624995)
          ·
            refine ⟨101165435922718528163437493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67443623948479018775624995 101165435922718528163437493)
            ·
              refine ⟨9484259617754862015322265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101165435922718528163437493 9484259617754862015322265)
              ·
                refine ⟨7113194713316146511491699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9484259617754862015322265 7113194713316146511491699)
                ·
                  refine ⟨10669792069974219767237549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7113194713316146511491699 10669792069974219767237549)
                  ·
                    refine ⟨4001172026240332412714081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10669792069974219767237549 4001172026240332412714081)
                    ·
                      refine ⟨3000879019680249309535561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4001172026240332412714081 3000879019680249309535561)
                      ·
                        rfl

theorem cell23_5844191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_5844191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844191 prefixEnd_5844191 := by exact prefixLift 5844191
  have htrace : WordTrace (prefixWord ++ tailWord_5844191) baseStart_5844191 baseEnd_5844191 := by
    simpa [prefixWord, tailWord_5844191, baseEnd_5844191] using wordTrace_append hprefix tailTrace_5844191
  have hstable : (prefixWord ++ tailWord_5844191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844191).length < 2 ^ (prefixWord ++ tailWord_5844191).sum := by decide
  have hdescent : baseEnd_5844191 < baseStart_5844191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844204 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 3, 4, 2]
def baseStart_5844204 : Nat := 118140960795 + 5844204 * 2 ^ 59
def prefixEnd_5844204 : Nat := 4983230072969 + 3 ^ 40 * 5844204 * 2
def baseEnd_5844204 : Nat := 3000885694928757758673001

theorem tailTrace_5844204 : CollatzResearch.WordTrace tailWord_5844204 prefixEnd_5844204 3000885694928757758673001 := by
  unfold tailWord_5844204
  simp only [CollatzResearch.WordTrace]
  refine ⟨106577815659727246712333833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142103754212969662283111777 106577815659727246712333833)
  ·
    refine ⟨79933361744795435034250375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106577815659727246712333833 79933361744795435034250375)
    ·
      refine ⟨119900042617193152551375563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79933361744795435034250375 119900042617193152551375563)
      ·
        refine ⟨179850063925789728827063345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119900042617193152551375563 179850063925789728827063345)
        ·
          refine ⟨134887547944342296620297509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179850063925789728827063345 134887547944342296620297509)
          ·
            refine ⟨25291415239564180616305783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134887547944342296620297509 25291415239564180616305783)
            ·
              refine ⟨37937122859346270924458675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25291415239564180616305783 37937122859346270924458675)
              ·
                refine ⟨56905684289019406386688013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37937122859346270924458675 56905684289019406386688013)
                ·
                  refine ⟨21339631608382277395008005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56905684289019406386688013 21339631608382277395008005)
                  ·
                    refine ⟨4001180926571677011564001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21339631608382277395008005 4001180926571677011564001)
                    ·
                      refine ⟨3000885694928757758673001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4001180926571677011564001 3000885694928757758673001)
                      ·
                        rfl

theorem cell23_5844204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 4, 2].length) (baseStart_5844204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844204 prefixEnd_5844204 := by exact prefixLift 5844204
  have htrace : WordTrace (prefixWord ++ tailWord_5844204) baseStart_5844204 baseEnd_5844204 := by
    simpa [prefixWord, tailWord_5844204, baseEnd_5844204] using wordTrace_append hprefix tailTrace_5844204
  have hstable : (prefixWord ++ tailWord_5844204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844204).length < 2 ^ (prefixWord ++ tailWord_5844204).sum := by decide
  have hdescent : baseEnd_5844204 < baseStart_5844204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844217 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 2, 2, 4]
def baseStart_5844217 : Nat := 118140960795 + 5844217 * 2 ^ 59
def prefixEnd_5844217 : Nat := 4983230072969 + 3 ^ 40 * 5844217 * 2
def baseEnd_5844217 : Nat := 3000892370177266207810441

theorem tailTrace_5844217 : CollatzResearch.WordTrace tailWord_5844217 prefixEnd_5844217 3000892370177266207810441 := by
  unfold tailWord_5844217
  simp only [CollatzResearch.WordTrace]
  refine ⟨213156105468407396644890905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142104070312271597763260603 213156105468407396644890905)
  ·
    refine ⟨159867079101305547483668179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213156105468407396644890905 159867079101305547483668179)
    ·
      refine ⟨239800618651958321225502269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159867079101305547483668179 239800618651958321225502269)
      ·
        refine ⟨89925231994484370459563351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239800618651958321225502269 89925231994484370459563351)
        ·
          refine ⟨134887847991726555689345027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89925231994484370459563351 134887847991726555689345027)
          ·
            refine ⟨202331771987589833534017541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134887847991726555689345027 202331771987589833534017541)
            ·
              refine ⟨37937207247673093787628289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202331771987589833534017541 37937207247673093787628289)
              ·
                refine ⟨28452905435754820340721217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37937207247673093787628289 28452905435754820340721217)
                ·
                  refine ⟨21339679076816115255540913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28452905435754820340721217 21339679076816115255540913)
                  ·
                    refine ⟨16004759307612086441655685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21339679076816115255540913 16004759307612086441655685)
                    ·
                      refine ⟨3000892370177266207810441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16004759307612086441655685 3000892370177266207810441)
                      ·
                        rfl

theorem cell23_5844217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_5844217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844217 prefixEnd_5844217 := by exact prefixLift 5844217
  have htrace : WordTrace (prefixWord ++ tailWord_5844217) baseStart_5844217 baseEnd_5844217 := by
    simpa [prefixWord, tailWord_5844217, baseEnd_5844217] using wordTrace_append hprefix tailTrace_5844217
  have hstable : (prefixWord ++ tailWord_5844217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844217).length < 2 ^ (prefixWord ++ tailWord_5844217).sum := by decide
  have hdescent : baseEnd_5844217 < baseStart_5844217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844238 : List Nat := [4, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2]
def baseStart_5844238 : Nat := 118140960795 + 5844238 * 2 ^ 59
def prefixEnd_5844238 : Nat := 4983230072969 + 3 ^ 40 * 5844238 * 2
def baseEnd_5844238 : Nat := 3000903153271010625647845

theorem tailTrace_5844238 : CollatzResearch.WordTrace tailWord_5844238 prefixEnd_5844238 3000903153271010625647845 := by
  unfold tailWord_5844238
  simp only [CollatzResearch.WordTrace]
  refine ⟨26644608925166414653925671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142104580934220878154270245 26644608925166414653925671)
  ·
    refine ⟨39966913387749621980888507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26644608925166414653925671 39966913387749621980888507)
    ·
      refine ⟨59950370081624432971332761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39966913387749621980888507 59950370081624432971332761)
      ·
        refine ⟨44962777561218324728499571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59950370081624432971332761 44962777561218324728499571)
        ·
          refine ⟨67444166341827487092749357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44962777561218324728499571 67444166341827487092749357)
          ·
            refine ⟨25291562378185307659781009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67444166341827487092749357 25291562378185307659781009)
            ·
              refine ⟨18968671783638980744835757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25291562378185307659781009 18968671783638980744835757)
              ·
                refine ⟨7113251918864617779313409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18968671783638980744835757 7113251918864617779313409)
                ·
                  refine ⟨5334938939148463334485057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7113251918864617779313409 5334938939148463334485057)
                  ·
                    refine ⟨4001204204361347500863793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5334938939148463334485057 4001204204361347500863793)
                    ·
                      refine ⟨3000903153271010625647845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4001204204361347500863793 3000903153271010625647845)
                      ·
                        rfl

theorem cell23_5844238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_5844238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844238 prefixEnd_5844238 := by exact prefixLift 5844238
  have htrace : WordTrace (prefixWord ++ tailWord_5844238) baseStart_5844238 baseEnd_5844238 := by
    simpa [prefixWord, tailWord_5844238, baseEnd_5844238] using wordTrace_append hprefix tailTrace_5844238
  have hstable : (prefixWord ++ tailWord_5844238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844238).length < 2 ^ (prefixWord ++ tailWord_5844238).sum := by decide
  have hdescent : baseEnd_5844238 < baseStart_5844238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844261 : List Nat := [1, 3, 1, 2, 4, 2, 2, 3, 5]
def baseStart_5844261 : Nat := 118140960795 + 5844261 * 2 ^ 59
def prefixEnd_5844261 : Nat := 4983230072969 + 3 ^ 40 * 5844261 * 2
def baseEnd_5844261 : Nat := 333434995925118226184471

theorem tailTrace_5844261 : CollatzResearch.WordTrace tailWord_5844261 prefixEnd_5844261 333434995925118226184471 := by
  unfold tailWord_5844261
  simp only [CollatzResearch.WordTrace]
  refine ⟨213157710280247992159492637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142105140186831994772995091 213157710280247992159492637)
  ·
    refine ⟨79934141355092997059809739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213157710280247992159492637 79934141355092997059809739)
    ·
      refine ⟨119901212032639495589714609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79934141355092997059809739 119901212032639495589714609)
      ·
        refine ⟨89925909024479621692285957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119901212032639495589714609 89925909024479621692285957)
        ·
          refine ⟨16861107942089929067303617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89925909024479621692285957 16861107942089929067303617)
          ·
            refine ⟨12645830956567446800477713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16861107942089929067303617 12645830956567446800477713)
            ·
              refine ⟨9484373217425585100358285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12645830956567446800477713 9484373217425585100358285)
              ·
                refine ⟨3556639956534594412634357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9484373217425585100358285 3556639956534594412634357)
                ·
                  refine ⟨333434995925118226184471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3556639956534594412634357 333434995925118226184471)
                  ·
                    rfl

theorem cell23_5844261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 5].length) (baseStart_5844261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844261 prefixEnd_5844261 := by exact prefixLift 5844261
  have htrace : WordTrace (prefixWord ++ tailWord_5844261) baseStart_5844261 baseEnd_5844261 := by
    simpa [prefixWord, tailWord_5844261, baseEnd_5844261] using wordTrace_append hprefix tailTrace_5844261
  have hstable : (prefixWord ++ tailWord_5844261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844261).length < 2 ^ (prefixWord ++ tailWord_5844261).sum := by decide
  have hdescent : baseEnd_5844261 < baseStart_5844261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844278 : List Nat := [5, 1, 2, 3, 1, 1, 2, 1, 7]
def baseStart_5844278 : Nat := 118140960795 + 5844278 * 2 ^ 59
def prefixEnd_5844278 : Nat := 4983230072969 + 3 ^ 40 * 5844278 * 2
def baseEnd_5844278 : Nat := 333435965833021163238629

theorem tailTrace_5844278 : CollatzResearch.WordTrace tailWord_5844278 prefixEnd_5844278 333435965833021163238629 := by
  unfold tailWord_5844278
  simp only [CollatzResearch.WordTrace]
  refine ⟨13322395645074150253928843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142105553547457602708574325 13322395645074150253928843)
  ·
    refine ⟨19983593467611225380893265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13322395645074150253928843 19983593467611225380893265)
    ·
      refine ⟨14987695100708419035669949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19983593467611225380893265 14987695100708419035669949)
      ·
        refine ⟨5620385662765657138376231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14987695100708419035669949 5620385662765657138376231)
        ·
          refine ⟨8430578494148485707564347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5620385662765657138376231 8430578494148485707564347)
          ·
            refine ⟨12645867741222728561346521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8430578494148485707564347 12645867741222728561346521)
            ·
              refine ⟨9484400805917046421009891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12645867741222728561346521 9484400805917046421009891)
              ·
                refine ⟨14226601208875569631514837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9484400805917046421009891 14226601208875569631514837)
                ·
                  refine ⟨333435965833021163238629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14226601208875569631514837 333435965833021163238629)
                  ·
                    rfl

theorem cell23_5844278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_5844278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844278 prefixEnd_5844278 := by exact prefixLift 5844278
  have htrace : WordTrace (prefixWord ++ tailWord_5844278) baseStart_5844278 baseEnd_5844278 := by
    simpa [prefixWord, tailWord_5844278, baseEnd_5844278] using wordTrace_append hprefix tailTrace_5844278
  have hstable : (prefixWord ++ tailWord_5844278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844278).length < 2 ^ (prefixWord ++ tailWord_5844278).sum := by decide
  have hdescent : baseEnd_5844278 < baseStart_5844278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844304 : List Nat := [2, 1, 1, 1, 1, 5, 1, 4, 3, 4]
def baseStart_5844304 : Nat := 118140960795 + 5844304 * 2 ^ 59
def prefixEnd_5844304 : Nat := 4983230072969 + 3 ^ 40 * 5844304 * 2
def baseEnd_5844304 : Nat := 1000312347664735789140847

theorem tailTrace_5844304 : CollatzResearch.WordTrace tailWord_5844304 prefixEnd_5844304 1000312347664735789140847 := by
  unfold tailWord_5844304
  simp only [CollatzResearch.WordTrace]
  refine ⟨106579639309546105251653983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142106185746061473668871977 106579639309546105251653983)
  ·
    refine ⟨159869458964319157877480975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106579639309546105251653983 159869458964319157877480975)
    ·
      refine ⟨239804188446478736816221463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159869458964319157877480975 239804188446478736816221463)
      ·
        refine ⟨359706282669718105224332195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239804188446478736816221463 359706282669718105224332195)
        ·
          refine ⟨539559424004577157836498293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359706282669718105224332195 539559424004577157836498293)
          ·
            refine ⟨50583696000429108547171715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 539559424004577157836498293 50583696000429108547171715)
            ·
              refine ⟨75875544000643662820757573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50583696000429108547171715 75875544000643662820757573)
              ·
                refine ⟨14226664500120686778892045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75875544000643662820757573 14226664500120686778892045)
                ·
                  refine ⟨5334999187545257542084517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14226664500120686778892045 5334999187545257542084517)
                  ·
                    refine ⟨1000312347664735789140847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5334999187545257542084517 1000312347664735789140847)
                    ·
                      rfl

theorem cell23_5844304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 3, 4].length) (baseStart_5844304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844304 prefixEnd_5844304 := by exact prefixLift 5844304
  have htrace : WordTrace (prefixWord ++ tailWord_5844304) baseStart_5844304 baseEnd_5844304 := by
    simpa [prefixWord, tailWord_5844304, baseEnd_5844304] using wordTrace_append hprefix tailTrace_5844304
  have hstable : (prefixWord ++ tailWord_5844304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844304).length < 2 ^ (prefixWord ++ tailWord_5844304).sum := by decide
  have hdescent : baseEnd_5844304 < baseStart_5844304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844307 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 4]
def baseStart_5844307 : Nat := 118140960795 + 5844307 * 2 ^ 59
def prefixEnd_5844307 : Nat := 4983230072969 + 3 ^ 40 * 5844307 * 2
def baseEnd_5844307 : Nat := 3000938583436170855685027

theorem tailTrace_5844307 : CollatzResearch.WordTrace tailWord_5844307 prefixEnd_5844307 3000938583436170855685027 := by
  unfold tailWord_5844307
  simp only [CollatzResearch.WordTrace]
  refine ⟨213159388038081342015667175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142106258692054228010444783 213159388038081342015667175)
  ·
    refine ⟨319739082057122013023500763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213159388038081342015667175 319739082057122013023500763)
    ·
      refine ⟨479608623085683019535251145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319739082057122013023500763 479608623085683019535251145)
      ·
        refine ⟨359706467314262264651438359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479608623085683019535251145 359706467314262264651438359)
        ·
          refine ⟨539559700971393396977157539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359706467314262264651438359 539559700971393396977157539)
          ·
            refine ⟨809339551457090095465736309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539559700971393396977157539 809339551457090095465736309)
            ·
              refine ⟨75875582949102196449912779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 809339551457090095465736309 75875582949102196449912779)
              ·
                refine ⟨113813374423653294674869169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75875582949102196449912779 113813374423653294674869169)
                ·
                  refine ⟨85360030817739971006151877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113813374423653294674869169 85360030817739971006151877)
                  ·
                    refine ⟨16005005778326244563653477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85360030817739971006151877 16005005778326244563653477)
                    ·
                      refine ⟨3000938583436170855685027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16005005778326244563653477 3000938583436170855685027)
                      ·
                        rfl

theorem cell23_5844307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 4].length) (baseStart_5844307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844307 prefixEnd_5844307 := by exact prefixLift 5844307
  have htrace : WordTrace (prefixWord ++ tailWord_5844307) baseStart_5844307 baseEnd_5844307 := by
    simpa [prefixWord, tailWord_5844307, baseEnd_5844307] using wordTrace_append hprefix tailTrace_5844307
  have hstable : (prefixWord ++ tailWord_5844307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844307).length < 2 ^ (prefixWord ++ tailWord_5844307).sum := by decide
  have hdescent : baseEnd_5844307 < baseStart_5844307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844314 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3]
def baseStart_5844314 : Nat := 118140960795 + 5844314 * 2 ^ 59
def prefixEnd_5844314 : Nat := 4983230072969 + 3 ^ 40 * 5844314 * 2
def baseEnd_5844314 : Nat := 3000942177800752328297495

theorem tailTrace_5844314 : CollatzResearch.WordTrace tailWord_5844314 prefixEnd_5844314 3000942177800752328297495 := by
  unfold tailWord_5844314
  simp only [CollatzResearch.WordTrace]
  refine ⟨53289910837263995552792999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142106428899370654807447997 53289910837263995552792999)
  ·
    refine ⟨79934866255895993329189499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53289910837263995552792999 79934866255895993329189499)
    ·
      refine ⟨119902299383843989993784249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79934866255895993329189499 119902299383843989993784249)
      ·
        refine ⟨89926724537882992495338187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119902299383843989993784249 89926724537882992495338187)
        ·
          refine ⟨134890086806824488743007281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89926724537882992495338187 134890086806824488743007281)
          ·
            refine ⟨101167565105118366557255461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134890086806824488743007281 101167565105118366557255461)
            ·
              refine ⟨18968918457209693729485399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101167565105118366557255461 18968918457209693729485399)
              ·
                refine ⟨28453377685814540594228099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18968918457209693729485399 28453377685814540594228099)
                ·
                  refine ⟨42680066528721810891342149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28453377685814540594228099 42680066528721810891342149)
                  ·
                    refine ⟨8002512474135339542126653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42680066528721810891342149 8002512474135339542126653)
                    ·
                      refine ⟨3000942177800752328297495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8002512474135339542126653 3000942177800752328297495)
                      ·
                        rfl

theorem cell23_5844314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_5844314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844314 prefixEnd_5844314 := by exact prefixLift 5844314
  have htrace : WordTrace (prefixWord ++ tailWord_5844314) baseStart_5844314 baseEnd_5844314 := by
    simpa [prefixWord, tailWord_5844314, baseEnd_5844314] using wordTrace_append hprefix tailTrace_5844314
  have hstable : (prefixWord ++ tailWord_5844314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844314).length < 2 ^ (prefixWord ++ tailWord_5844314).sum := by decide
  have hdescent : baseEnd_5844314 < baseStart_5844314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844337 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 8]
def baseStart_5844337 : Nat := 118140960795 + 5844337 * 2 ^ 59
def prefixEnd_5844337 : Nat := 4983230072969 + 3 ^ 40 * 5844337 * 2
def baseEnd_5844337 : Nat := 3000953987855805738309889

theorem tailTrace_5844337 : CollatzResearch.WordTrace tailWord_5844337 prefixEnd_5844337 3000953987855805738309889 := by
  unfold tailWord_5844337
  simp only [CollatzResearch.WordTrace]
  refine ⟨213160482227972657139259265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142106988151981771426172843 213160482227972657139259265)
  ·
    refine ⟨159870361670979492854444449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213160482227972657139259265 159870361670979492854444449)
    ·
      refine ⟨119902771253234619640833337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159870361670979492854444449 119902771253234619640833337)
      ·
        refine ⟨89927078439925964730625003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119902771253234619640833337 89927078439925964730625003)
        ·
          refine ⟨134890617659888947095937505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89927078439925964730625003 134890617659888947095937505)
          ·
            refine ⟨101167963244916710321953129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134890617659888947095937505 101167963244916710321953129)
            ·
              refine ⟨75875972433687532741464847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101167963244916710321953129 75875972433687532741464847)
              ·
                refine ⟨113813958650531299112197271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75875972433687532741464847 113813958650531299112197271)
                ·
                  refine ⟨170720937975796948668295907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113813958650531299112197271 170720937975796948668295907)
                  ·
                    refine ⟨256081406963695423002443861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 170720937975796948668295907 256081406963695423002443861)
                    ·
                      refine ⟨3000953987855805738309889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 256081406963695423002443861 3000953987855805738309889)
                      ·
                        rfl

theorem cell23_5844337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_5844337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844337 prefixEnd_5844337 := by exact prefixLift 5844337
  have htrace : WordTrace (prefixWord ++ tailWord_5844337) baseStart_5844337 baseEnd_5844337 := by
    simpa [prefixWord, tailWord_5844337, baseEnd_5844337] using wordTrace_append hprefix tailTrace_5844337
  have hstable : (prefixWord ++ tailWord_5844337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844337).length < 2 ^ (prefixWord ++ tailWord_5844337).sum := by decide
  have hdescent : baseEnd_5844337 < baseStart_5844337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844364 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 3, 5]
def baseStart_5844364 : Nat := 118140960795 + 5844364 * 2 ^ 59
def prefixEnd_5844364 : Nat := 4983230072969 + 3 ^ 40 * 5844364 * 2
def baseEnd_5844364 : Nat := 1000322617277825710890755

theorem tailTrace_5844364 : CollatzResearch.WordTrace tailWord_5844364 prefixEnd_5844364 1000322617277825710890755 := by
  unfold tailWord_5844364
  simp only [CollatzResearch.WordTrace]
  refine ⟨106580733499437420375246073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142107644665916560500328097 106580733499437420375246073)
  ·
    refine ⟨79935550124578065281434555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106580733499437420375246073 79935550124578065281434555)
    ·
      refine ⟨119903325186867097922151833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79935550124578065281434555 119903325186867097922151833)
      ·
        refine ⟨89927493890150323441613875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119903325186867097922151833 89927493890150323441613875)
        ·
          refine ⟨134891240835225485162420813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89927493890150323441613875 134891240835225485162420813)
          ·
            refine ⟨50584215313209556935907805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134891240835225485162420813 50584215313209556935907805)
            ·
              refine ⟨18969080742453583850965427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50584215313209556935907805 18969080742453583850965427)
              ·
                refine ⟨28453621113680375776448141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18969080742453583850965427 28453621113680375776448141)
                ·
                  refine ⟨10670107917630140916168053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28453621113680375776448141 10670107917630140916168053)
                  ·
                    refine ⟨1000322617277825710890755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10670107917630140916168053 1000322617277825710890755)
                    ·
                      rfl

theorem cell23_5844364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_5844364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844364 prefixEnd_5844364 := by exact prefixLift 5844364
  have htrace : WordTrace (prefixWord ++ tailWord_5844364) baseStart_5844364 baseEnd_5844364 := by
    simpa [prefixWord, tailWord_5844364, baseEnd_5844364] using wordTrace_append hprefix tailTrace_5844364
  have hstable : (prefixWord ++ tailWord_5844364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844364).length < 2 ^ (prefixWord ++ tailWord_5844364).sum := by decide
  have hdescent : baseEnd_5844364 < baseStart_5844364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844445 : List Nat := [1, 4, 3, 1, 1, 4, 1, 2, 2, 4]
def baseStart_5844445 : Nat := 118140960795 + 5844445 * 2 ^ 59
def prefixEnd_5844445 : Nat := 4983230072969 + 3 ^ 40 * 5844445 * 2
def baseEnd_5844445 : Nat := 1000336481255497105253131

theorem tailTrace_5844445 : CollatzResearch.WordTrace tailWord_5844445 prefixEnd_5844445 1000336481255497105253131 := by
  unfold tailWord_5844445
  simp only [CollatzResearch.WordTrace]
  refine ⟨213164421311581391584190789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142109614207720927722793859 213164421311581391584190789)
  ·
    refine ⟨39968328995921510922035773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213164421311581391584190789 39968328995921510922035773)
    ·
      refine ⟨14988123373470566595763415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39968328995921510922035773 14988123373470566595763415)
      ·
        refine ⟨22482185060205849893645123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14988123373470566595763415 22482185060205849893645123)
        ·
          refine ⟨33723277590308774840467685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22482185060205849893645123 33723277590308774840467685)
          ·
            refine ⟨6323114548182895282587691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33723277590308774840467685 6323114548182895282587691)
            ·
              refine ⟨9484671822274342923881537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6323114548182895282587691 9484671822274342923881537)
              ·
                refine ⟨7113503866705757192911153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9484671822274342923881537 7113503866705757192911153)
                ·
                  refine ⟨5335127900029317894683365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7113503866705757192911153 5335127900029317894683365)
                  ·
                    refine ⟨1000336481255497105253131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5335127900029317894683365 1000336481255497105253131)
                    ·
                      rfl

theorem cell23_5844445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_5844445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844445 prefixEnd_5844445 := by exact prefixLift 5844445
  have htrace : WordTrace (prefixWord ++ tailWord_5844445) baseStart_5844445 baseEnd_5844445 := by
    simpa [prefixWord, tailWord_5844445, baseEnd_5844445] using wordTrace_append hprefix tailTrace_5844445
  have hstable : (prefixWord ++ tailWord_5844445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844445).length < 2 ^ (prefixWord ++ tailWord_5844445).sum := by decide
  have hdescent : baseEnd_5844445 < baseStart_5844445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844561 : List Nat := [1, 2, 2, 1, 3, 2, 1, 4, 2, 5]
def baseStart_5844561 : Nat := 118140960795 + 5844561 * 2 ^ 59
def prefixEnd_5844561 : Nat := 4983230072969 + 3 ^ 40 * 5844561 * 2
def baseEnd_5844561 : Nat := 1000356335840804287302953

theorem tailTrace_5844561 : CollatzResearch.WordTrace tailWord_5844561 prefixEnd_5844561 1000356335840804287302953 := by
  unfold tailWord_5844561
  simp only [CollatzResearch.WordTrace]
  refine ⟨213168652179161143395413537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142112434786107428930275691 213168652179161143395413537)
  ·
    refine ⟨159876489134370857546560153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213168652179161143395413537 159876489134370857546560153)
    ·
      refine ⟨119907366850778143159920115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159876489134370857546560153 119907366850778143159920115)
      ·
        refine ⟨179861050276167214739880173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119907366850778143159920115 179861050276167214739880173)
        ·
          refine ⟨67447893853562705527455065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179861050276167214739880173 67447893853562705527455065)
          ·
            refine ⟨50585920390172029145591299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67447893853562705527455065 50585920390172029145591299)
            ·
              refine ⟨75878880585258043718386949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50585920390172029145591299 75878880585258043718386949)
              ·
                refine ⟨14227290109735883197197553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75878880585258043718386949 14227290109735883197197553)
                ·
                  refine ⟨10670467582301912397898165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14227290109735883197197553 10670467582301912397898165)
                  ·
                    refine ⟨1000356335840804287302953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10670467582301912397898165 1000356335840804287302953)
                    ·
                      rfl

theorem cell23_5844561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_5844561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844561 prefixEnd_5844561 := by exact prefixLift 5844561
  have htrace : WordTrace (prefixWord ++ tailWord_5844561) baseStart_5844561 baseEnd_5844561 := by
    simpa [prefixWord, tailWord_5844561, baseEnd_5844561] using wordTrace_append hprefix tailTrace_5844561
  have hstable : (prefixWord ++ tailWord_5844561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844561).length < 2 ^ (prefixWord ++ tailWord_5844561).sum := by decide
  have hdescent : baseEnd_5844561 < baseStart_5844561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844688 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 2, 6, 2]
def baseStart_5844688 : Nat := 118140960795 + 5844688 * 2 ^ 59
def prefixEnd_5844688 : Nat := 4983230072969 + 3 ^ 40 * 5844688 * 2
def baseEnd_5844688 : Nat := 3001134219565533865020775

theorem tailTrace_5844688 : CollatzResearch.WordTrace tailWord_5844688 prefixEnd_5844688 3001134219565533865020775 := by
  unfold tailWord_5844688
  simp only [CollatzResearch.WordTrace]
  refine ⟨106586642124850522042643359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142115522833134029390191145 106586642124850522042643359)
  ·
    refine ⟨159879963187275783063965039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106586642124850522042643359 159879963187275783063965039)
    ·
      refine ⟨239819944780913674595947559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159879963187275783063965039 239819944780913674595947559)
      ·
        refine ⟨359729917171370511893921339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239819944780913674595947559 359729917171370511893921339)
        ·
          refine ⟨539594875757055767840882009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359729917171370511893921339 539594875757055767840882009)
          ·
            refine ⟨404696156817791825880661507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 539594875757055767840882009 404696156817791825880661507)
            ·
              refine ⟨607044235226687738820992261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404696156817791825880661507 607044235226687738820992261)
              ·
                refine ⟨113820794105003951028936049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 607044235226687738820992261 113820794105003951028936049)
                ·
                  refine ⟨85365595578752963271702037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113820794105003951028936049 85365595578752963271702037)
                  ·
                    refine ⟨4001512292754045153361033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85365595578752963271702037 4001512292754045153361033)
                    ·
                      refine ⟨3001134219565533865020775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4001512292754045153361033 3001134219565533865020775)
                      ·
                        rfl

theorem cell23_5844688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 6, 2].length) (baseStart_5844688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844688 prefixEnd_5844688 := by exact prefixLift 5844688
  have htrace : WordTrace (prefixWord ++ tailWord_5844688) baseStart_5844688 baseEnd_5844688 := by
    simpa [prefixWord, tailWord_5844688, baseEnd_5844688] using wordTrace_append hprefix tailTrace_5844688
  have hstable : (prefixWord ++ tailWord_5844688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844688).length < 2 ^ (prefixWord ++ tailWord_5844688).sum := by decide
  have hdescent : baseEnd_5844688 < baseStart_5844688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844691 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 5]
def baseStart_5844691 : Nat := 118140960795 + 5844691 * 2 ^ 59
def prefixEnd_5844691 : Nat := 4983230072969 + 3 ^ 40 * 5844691 * 2
def baseEnd_5844691 : Nat := 3001135760007497353283261

theorem tailTrace_5844691 : CollatzResearch.WordTrace tailWord_5844691 prefixEnd_5844691 3001135760007497353283261 := by
  unfold tailWord_5844691
  simp only [CollatzResearch.WordTrace]
  refine ⟨213173393668690175597645927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142115595779126783731763951 213173393668690175597645927)
  ·
    refine ⟨319760090503035263396468891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213173393668690175597645927 319760090503035263396468891)
    ·
      refine ⟨479640135754552895094703337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319760090503035263396468891 479640135754552895094703337)
      ·
        refine ⟨359730101815914671321027503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479640135754552895094703337 359730101815914671321027503)
        ·
          refine ⟨539595152723872006981541255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359730101815914671321027503 539595152723872006981541255)
          ·
            refine ⟨809392729085808010472311883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539595152723872006981541255 809392729085808010472311883)
            ·
              refine ⟨1214089093628712015708467825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809392729085808010472311883 1214089093628712015708467825)
              ·
                refine ⟨910566820221534011781350869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1214089093628712015708467825 910566820221534011781350869)
                ·
                  refine ⟨21341409848942203401125411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 910566820221534011781350869 21341409848942203401125411)
                  ·
                    refine ⟨32012114773413305101688117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21341409848942203401125411 32012114773413305101688117)
                    ·
                      refine ⟨3001135760007497353283261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32012114773413305101688117 3001135760007497353283261)
                      ·
                        rfl

theorem cell23_5844691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 5].length) (baseStart_5844691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844691 prefixEnd_5844691 := by exact prefixLift 5844691
  have htrace : WordTrace (prefixWord ++ tailWord_5844691) baseStart_5844691 baseEnd_5844691 := by
    simpa [prefixWord, tailWord_5844691, baseEnd_5844691] using wordTrace_append hprefix tailTrace_5844691
  have hstable : (prefixWord ++ tailWord_5844691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844691).length < 2 ^ (prefixWord ++ tailWord_5844691).sum := by decide
  have hdescent : baseEnd_5844691 < baseStart_5844691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844705 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 3, 1, 4]
def baseStart_5844705 : Nat := 118140960795 + 5844705 * 2 ^ 59
def prefixEnd_5844705 : Nat := 4983230072969 + 3 ^ 40 * 5844705 * 2
def baseEnd_5844705 : Nat := 3001142948736660298508197

theorem tailTrace_5844705 : CollatzResearch.WordTrace tailWord_5844705 prefixEnd_5844705 3001142948736660298508197 := by
  unfold tailWord_5844705
  simp only [CollatzResearch.WordTrace]
  refine ⟨213173904290639455988655569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142115936193759637325770379 213173904290639455988655569)
  ·
    refine ⟨159880428217979591991491677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213173904290639455988655569 159880428217979591991491677)
    ·
      refine ⟨59955160581742346996809379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159880428217979591991491677 59955160581742346996809379)
      ·
        refine ⟨89932740872613520495214069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59955160581742346996809379 89932740872613520495214069)
        ·
          refine ⟨8431194456807517546426319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89932740872613520495214069 8431194456807517546426319)
          ·
            refine ⟨12646791685211276319639479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8431194456807517546426319 12646791685211276319639479)
            ·
              refine ⟨18970187527816914479459219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12646791685211276319639479 18970187527816914479459219)
              ·
                refine ⟨28455281291725371719188829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18970187527816914479459219 28455281291725371719188829)
                ·
                  refine ⟨10670730484397014394695811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28455281291725371719188829 10670730484397014394695811)
                  ·
                    refine ⟨16006095726595521592043717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10670730484397014394695811 16006095726595521592043717)
                    ·
                      refine ⟨3001142948736660298508197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16006095726595521592043717 3001142948736660298508197)
                      ·
                        rfl

theorem cell23_5844705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_5844705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844705 prefixEnd_5844705 := by exact prefixLift 5844705
  have htrace : WordTrace (prefixWord ++ tailWord_5844705) baseStart_5844705 baseEnd_5844705 := by
    simpa [prefixWord, tailWord_5844705, baseEnd_5844705] using wordTrace_append hprefix tailTrace_5844705
  have hstable : (prefixWord ++ tailWord_5844705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844705).length < 2 ^ (prefixWord ++ tailWord_5844705).sum := by decide
  have hdescent : baseEnd_5844705 < baseStart_5844705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844722 : List Nat := [3, 2, 1, 3, 1, 1, 5, 1, 1, 1, 4]
def baseStart_5844722 : Nat := 118140960795 + 5844722 * 2 ^ 59
def prefixEnd_5844722 : Nat := 4983230072969 + 3 ^ 40 * 5844722 * 2
def baseEnd_5844722 : Nat := 3001151677907786731995619

theorem tailTrace_5844722 : CollatzResearch.WordTrace tailWord_5844722 prefixEnd_5844722 3001151677907786731995619 := by
  unfold tailWord_5844722
  simp only [CollatzResearch.WordTrace]
  refine ⟨53293631082894466973006105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142116349554385245261349613 53293631082894466973006105)
  ·
    refine ⟨39970223312170850229754579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53293631082894466973006105 39970223312170850229754579)
    ·
      refine ⟨59955334968256275344631869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39970223312170850229754579 59955334968256275344631869)
      ·
        refine ⟨22483250613096103254236951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59955334968256275344631869 22483250613096103254236951)
        ·
          refine ⟨33724875919644154881355427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22483250613096103254236951 33724875919644154881355427)
          ·
            refine ⟨50587313879466232322033141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33724875919644154881355427 50587313879466232322033141)
            ·
              refine ⟨4742560676199959280190607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50587313879466232322033141 4742560676199959280190607)
              ·
                refine ⟨7113841014299938920285911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4742560676199959280190607 7113841014299938920285911)
                ·
                  refine ⟨10670761521449908380428867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7113841014299938920285911 10670761521449908380428867)
                  ·
                    refine ⟨16006142282174862570643301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10670761521449908380428867 16006142282174862570643301)
                    ·
                      refine ⟨3001151677907786731995619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16006142282174862570643301 3001151677907786731995619)
                      ·
                        rfl

theorem cell23_5844722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_5844722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844722 prefixEnd_5844722 := by exact prefixLift 5844722
  have htrace : WordTrace (prefixWord ++ tailWord_5844722) baseStart_5844722 baseEnd_5844722 := by
    simpa [prefixWord, tailWord_5844722, baseEnd_5844722] using wordTrace_append hprefix tailTrace_5844722
  have hstable : (prefixWord ++ tailWord_5844722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844722).length < 2 ^ (prefixWord ++ tailWord_5844722).sum := by decide
  have hdescent : baseEnd_5844722 < baseStart_5844722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844731 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 6]
def baseStart_5844731 : Nat := 118140960795 + 5844731 * 2 ^ 59
def prefixEnd_5844731 : Nat := 4983230072969 + 3 ^ 40 * 5844731 * 2
def baseEnd_5844731 : Nat := 3001156299233677196783077

theorem tailTrace_5844731 : CollatzResearch.WordTrace tailWord_5844731 prefixEnd_5844731 3001156299233677196783077 := by
  unfold tailWord_5844731
  simp only [CollatzResearch.WordTrace]
  refine ⟨213174852588545262429102047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142116568392363508286068031 213174852588545262429102047)
  ·
    refine ⟨319762278882817893643653071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213174852588545262429102047 319762278882817893643653071)
    ·
      refine ⟨479643418324226840465479607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319762278882817893643653071 479643418324226840465479607)
      ·
        refine ⟨719465127486340260698219411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479643418324226840465479607 719465127486340260698219411)
        ·
          refine ⟨1079197691229510391047329117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719465127486340260698219411 1079197691229510391047329117)
          ·
            refine ⟨404699134211066396642748419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1079197691229510391047329117 404699134211066396642748419)
            ·
              refine ⟨607048701316599594964122629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404699134211066396642748419 607048701316599594964122629)
              ·
                refine ⟨113821631496862424055772993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 607048701316599594964122629 113821631496862424055772993)
                ·
                  refine ⟨85366223622646818041829745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113821631496862424055772993 85366223622646818041829745)
                  ·
                    refine ⟨64024667716985113531372309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85366223622646818041829745 64024667716985113531372309)
                    ·
                      refine ⟨3001156299233677196783077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64024667716985113531372309 3001156299233677196783077)
                      ·
                        rfl

theorem cell23_5844731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 6].length) (baseStart_5844731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844731 prefixEnd_5844731 := by exact prefixLift 5844731
  have htrace : WordTrace (prefixWord ++ tailWord_5844731) baseStart_5844731 baseEnd_5844731 := by
    simpa [prefixWord, tailWord_5844731, baseEnd_5844731] using wordTrace_append hprefix tailTrace_5844731
  have hstable : (prefixWord ++ tailWord_5844731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844731).length < 2 ^ (prefixWord ++ tailWord_5844731).sum := by decide
  have hdescent : baseEnd_5844731 < baseStart_5844731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844768 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 5]
def baseStart_5844768 : Nat := 118140960795 + 5844768 * 2 ^ 59
def prefixEnd_5844768 : Nat := 4983230072969 + 3 ^ 40 * 5844768 * 2
def baseEnd_5844768 : Nat := 3001175298017893552020407

theorem tailTrace_5844768 : CollatzResearch.WordTrace tailWord_5844768 prefixEnd_5844768 3001175298017893552020407 := by
  unfold tailWord_5844768
  simp only [CollatzResearch.WordTrace]
  refine ⟨106588101044705608874099479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142117468059607478498799305 106588101044705608874099479)
  ·
    refine ⟨159882151567058413311149219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106588101044705608874099479 159882151567058413311149219)
    ·
      refine ⟨239823227350587619966723829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159882151567058413311149219 239823227350587619966723829)
      ·
        refine ⟨22483427564117589371880359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 239823227350587619966723829 22483427564117589371880359)
        ·
          refine ⟨33725141346176384057820539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22483427564117589371880359 33725141346176384057820539)
          ·
            refine ⟨50587712019264576086730809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33725141346176384057820539 50587712019264576086730809)
            ·
              refine ⟨37940784014448432065048107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50587712019264576086730809 37940784014448432065048107)
              ·
                refine ⟨56911176021672648097572161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37940784014448432065048107 56911176021672648097572161)
                ·
                  refine ⟨42683382016254486073179121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56911176021672648097572161 42683382016254486073179121)
                  ·
                    refine ⟨32012536512190864554884341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42683382016254486073179121 32012536512190864554884341)
                    ·
                      refine ⟨3001175298017893552020407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32012536512190864554884341 3001175298017893552020407)
                      ·
                        rfl

theorem cell23_5844768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_5844768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844768 prefixEnd_5844768 := by exact prefixLift 5844768
  have htrace : WordTrace (prefixWord ++ tailWord_5844768) baseStart_5844768 baseEnd_5844768 := by
    simpa [prefixWord, tailWord_5844768, baseEnd_5844768] using wordTrace_append hprefix tailTrace_5844768
  have hstable : (prefixWord ++ tailWord_5844768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844768).length < 2 ^ (prefixWord ++ tailWord_5844768).sum := by decide
  have hdescent : baseEnd_5844768 < baseStart_5844768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844806 : List Nat := [6, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_5844806 : Nat := 118140960795 + 5844806 * 2 ^ 59
def prefixEnd_5844806 : Nat := 4983230072969 + 3 ^ 40 * 5844806 * 2
def baseEnd_5844806 : Nat := 3001194810282764403345233

theorem tailTrace_5844806 : CollatzResearch.WordTrace tailWord_5844806 prefixEnd_5844806 3001194810282764403345233 := by
  unfold tailWord_5844806
  simp only [CollatzResearch.WordTrace]
  refine ⟨6661799626977298444940071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 142118392042182366825388181 6661799626977298444940071)
  ·
    refine ⟨9992699440465947667410107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6661799626977298444940071 9992699440465947667410107)
    ·
      refine ⟨14989049160698921501115161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9992699440465947667410107 14989049160698921501115161)
      ·
        refine ⟨11241786870524191125836371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14989049160698921501115161 11241786870524191125836371)
        ·
          refine ⟨16862680305786286688754557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11241786870524191125836371 16862680305786286688754557)
          ·
            refine ⟨6323505114669857508282959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16862680305786286688754557 6323505114669857508282959)
            ·
              refine ⟨9485257672004786262424439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6323505114669857508282959 9485257672004786262424439)
              ·
                refine ⟨14227886508007179393636659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9485257672004786262424439 14227886508007179393636659)
                ·
                  refine ⟨21341829762010769090454989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14227886508007179393636659 21341829762010769090454989)
                  ·
                    refine ⟨8003186160754038408920621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21341829762010769090454989 8003186160754038408920621)
                    ·
                      refine ⟨3001194810282764403345233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8003186160754038408920621 3001194810282764403345233)
                      ·
                        rfl

theorem cell23_5844806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_5844806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844806 prefixEnd_5844806 := by exact prefixLift 5844806
  have htrace : WordTrace (prefixWord ++ tailWord_5844806) baseStart_5844806 baseEnd_5844806 := by
    simpa [prefixWord, tailWord_5844806, baseEnd_5844806] using wordTrace_append hprefix tailTrace_5844806
  have hstable : (prefixWord ++ tailWord_5844806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844806).length < 2 ^ (prefixWord ++ tailWord_5844806).sum := by decide
  have hdescent : baseEnd_5844806 < baseStart_5844806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844845 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 4, 3, 3]
def baseStart_5844845 : Nat := 118140960795 + 5844845 * 2 ^ 59
def prefixEnd_5844845 : Nat := 4983230072969 + 3 ^ 40 * 5844845 * 2
def baseEnd_5844845 : Nat := 3001214836028289750757553

theorem tailTrace_5844845 : CollatzResearch.WordTrace tailWord_5844845 prefixEnd_5844845 3001214836028289750757553 := by
  unfold tailWord_5844845
  simp only [CollatzResearch.WordTrace]
  refine ⟨213179010510132259898751989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142119340340088173265834659 213179010510132259898751989)
  ·
    refine ⟨19985532235324899365507999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 213179010510132259898751989 19985532235324899365507999)
    ·
      refine ⟨29978298352987349048261999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19985532235324899365507999 29978298352987349048261999)
      ·
        refine ⟨44967447529481023572392999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29978298352987349048261999 44967447529481023572392999)
        ·
          refine ⟨67451171294221535358589499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44967447529481023572392999 67451171294221535358589499)
          ·
            refine ⟨101176756941332303037884249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67451171294221535358589499 101176756941332303037884249)
            ·
              refine ⟨75882567705999227278413187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101176756941332303037884249 75882567705999227278413187)
              ·
                refine ⟨113823851558998840917619781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75882567705999227278413187 113823851558998840917619781)
                ·
                  refine ⟨21341972167312282672053709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113823851558998840917619781 21341972167312282672053709)
                  ·
                    refine ⟨8003239562742106002020141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21341972167312282672053709 8003239562742106002020141)
                    ·
                      refine ⟨3001214836028289750757553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8003239562742106002020141 3001214836028289750757553)
                      ·
                        rfl

theorem cell23_5844845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_5844845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844845 prefixEnd_5844845 := by exact prefixLift 5844845
  have htrace : WordTrace (prefixWord ++ tailWord_5844845) baseStart_5844845 baseEnd_5844845 := by
    simpa [prefixWord, tailWord_5844845, baseEnd_5844845] using wordTrace_append hprefix tailTrace_5844845
  have hstable : (prefixWord ++ tailWord_5844845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844845).length < 2 ^ (prefixWord ++ tailWord_5844845).sum := by decide
  have hdescent : baseEnd_5844845 < baseStart_5844845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844858 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7]
def baseStart_5844858 : Nat := 118140960795 + 5844858 * 2 ^ 59
def prefixEnd_5844858 : Nat := 4983230072969 + 3 ^ 40 * 5844858 * 2
def baseEnd_5844858 : Nat := 3001221511276798199894993

theorem tailTrace_5844858 : CollatzResearch.WordTrace tailWord_5844858 prefixEnd_5844858 3001221511276798199894993 := by
  unfold tailWord_5844858
  simp only [CollatzResearch.WordTrace]
  refine ⟨53294871164771290779743807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142119656439390108745983485 53294871164771290779743807)
  ·
    refine ⟨79942306747156936169615711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53294871164771290779743807 79942306747156936169615711)
    ·
      refine ⟨119913460120735404254423567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79942306747156936169615711 119913460120735404254423567)
      ·
        refine ⟨179870190181103106381635351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119913460120735404254423567 179870190181103106381635351)
        ·
          refine ⟨269805285271654659572453027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179870190181103106381635351 269805285271654659572453027)
          ·
            refine ⟨404707927907481989358679541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269805285271654659572453027 404707927907481989358679541)
            ·
              refine ⟨37941368241326436502376207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 404707927907481989358679541 37941368241326436502376207)
              ·
                refine ⟨56912052361989654753564311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37941368241326436502376207 56912052361989654753564311)
                ·
                  refine ⟨85368078542984482130346467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56912052361989654753564311 85368078542984482130346467)
                  ·
                    refine ⟨128052117814476723195519701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85368078542984482130346467 128052117814476723195519701)
                    ·
                      refine ⟨3001221511276798199894993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128052117814476723195519701 3001221511276798199894993)
                      ·
                        rfl

theorem cell23_5844858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_5844858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844858 prefixEnd_5844858 := by exact prefixLift 5844858
  have htrace : WordTrace (prefixWord ++ tailWord_5844858) baseStart_5844858 baseEnd_5844858 := by
    simpa [prefixWord, tailWord_5844858, baseEnd_5844858] using wordTrace_append hprefix tailTrace_5844858
  have hstable : (prefixWord ++ tailWord_5844858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844858).length < 2 ^ (prefixWord ++ tailWord_5844858).sum := by decide
  have hdescent : baseEnd_5844858 < baseStart_5844858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844882 : List Nat := [3, 2, 3, 2, 1, 1, 1, 3, 2, 5]
def baseStart_5844882 : Nat := 118140960795 + 5844882 * 2 ^ 59
def prefixEnd_5844882 : Nat := 4983230072969 + 3 ^ 40 * 5844882 * 2
def baseEnd_5844882 : Nat := 1000411278270835368664961

theorem tailTrace_5844882 : CollatzResearch.WordTrace tailWord_5844882 prefixEnd_5844882 1000411278270835368664961 := by
  unfold tailWord_5844882
  simp only [CollatzResearch.WordTrace]
  refine ⟨53295090002749553804462225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142120240007332143478565933 53295090002749553804462225)
  ·
    refine ⟨39971317502062165353346669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53295090002749553804462225 39971317502062165353346669)
    ·
      refine ⟨14989244063273312007505001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39971317502062165353346669 14989244063273312007505001)
      ·
        refine ⟨11241933047454984005628751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14989244063273312007505001 11241933047454984005628751)
        ·
          refine ⟨16862899571182476008443127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11241933047454984005628751 16862899571182476008443127)
          ·
            refine ⟨25294349356773714012664691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16862899571182476008443127 25294349356773714012664691)
            ·
              refine ⟨37941524035160571018997037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25294349356773714012664691 37941524035160571018997037)
              ·
                refine ⟨14228071513185214132123889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37941524035160571018997037 14228071513185214132123889)
                ·
                  refine ⟨10671053634888910599092917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14228071513185214132123889 10671053634888910599092917)
                  ·
                    refine ⟨1000411278270835368664961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10671053634888910599092917 1000411278270835368664961)
                    ·
                      rfl

theorem cell23_5844882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_5844882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844882 prefixEnd_5844882 := by exact prefixLift 5844882
  have htrace : WordTrace (prefixWord ++ tailWord_5844882) baseStart_5844882 baseEnd_5844882 := by
    simpa [prefixWord, tailWord_5844882, baseEnd_5844882] using wordTrace_append hprefix tailTrace_5844882
  have hstable : (prefixWord ++ tailWord_5844882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844882).length < 2 ^ (prefixWord ++ tailWord_5844882).sum := by decide
  have hdescent : baseEnd_5844882 < baseStart_5844882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844905 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 4, 2, 3]
def baseStart_5844905 : Nat := 118140960795 + 5844905 * 2 ^ 59
def prefixEnd_5844905 : Nat := 4983230072969 + 3 ^ 40 * 5844905 * 2
def baseEnd_5844905 : Nat := 3001245644867559516007277

theorem tailTrace_5844905 : CollatzResearch.WordTrace tailWord_5844905 prefixEnd_5844905 3001245644867559516007277 := by
  unfold tailWord_5844905
  simp only [CollatzResearch.WordTrace]
  refine ⟨213181198889914890145936169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142120799259943260097290779 213181198889914890145936169)
  ·
    refine ⟨159885899167436167609452127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213181198889914890145936169 159885899167436167609452127)
    ·
      refine ⟨239828848751154251414178191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159885899167436167609452127 239828848751154251414178191)
      ·
        refine ⟨359743273126731377121267287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239828848751154251414178191 359743273126731377121267287)
        ·
          refine ⟨539614909690097065681900931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359743273126731377121267287 539614909690097065681900931)
          ·
            refine ⟨809422364535145598522851397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539614909690097065681900931 809422364535145598522851397)
            ·
              refine ⟨151766693350339799723034637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 809422364535145598522851397 151766693350339799723034637)
              ·
                refine ⟨56912510006377424896137989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151766693350339799723034637 56912510006377424896137989)
                ·
                  refine ⟨10671095626195767168025873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56912510006377424896137989 10671095626195767168025873)
                  ·
                    refine ⟨8003321719646825376019405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10671095626195767168025873 8003321719646825376019405)
                    ·
                      refine ⟨3001245644867559516007277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8003321719646825376019405 3001245644867559516007277)
                      ·
                        rfl

theorem cell23_5844905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 2, 3].length) (baseStart_5844905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844905 prefixEnd_5844905 := by exact prefixLift 5844905
  have htrace : WordTrace (prefixWord ++ tailWord_5844905) baseStart_5844905 baseEnd_5844905 := by
    simpa [prefixWord, tailWord_5844905, baseEnd_5844905] using wordTrace_append hprefix tailTrace_5844905
  have hstable : (prefixWord ++ tailWord_5844905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844905).length < 2 ^ (prefixWord ++ tailWord_5844905).sum := by decide
  have hdescent : baseEnd_5844905 < baseStart_5844905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844952 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 5, 1, 3]
def baseStart_5844952 : Nat := 118140960795 + 5844952 * 2 ^ 59
def prefixEnd_5844952 : Nat := 4983230072969 + 3 ^ 40 * 5844952 * 2
def baseEnd_5844952 : Nat := 3001269778458320832119561

theorem tailTrace_5844952 : CollatzResearch.WordTrace tailWord_5844952 prefixEnd_5844952 3001269778458320832119561 := by
  unfold tailWord_5844952
  simp only [CollatzResearch.WordTrace]
  refine ⟨106591456560372308586448555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142121942080496411448598073 106591456560372308586448555)
  ·
    refine ⟨159887184840558462879672833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106591456560372308586448555 159887184840558462879672833)
    ·
      refine ⟨119915388630418847159754625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159887184840558462879672833 119915388630418847159754625)
      ·
        refine ⟨89936541472814135369815969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119915388630418847159754625 89936541472814135369815969)
        ·
          refine ⟨67452406104610601527361977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89936541472814135369815969 67452406104610601527361977)
          ·
            refine ⟨50589304578457951145521483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67452406104610601527361977 50589304578457951145521483)
            ·
              refine ⟨75883956867686926718282225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50589304578457951145521483 75883956867686926718282225)
              ·
                refine ⟨56912967650765195038711669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75883956867686926718282225 56912967650765195038711669)
                ·
                  refine ⟨5335590717259237034879219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56912967650765195038711669 5335590717259237034879219)
                  ·
                    refine ⟨8003386075888855552318829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5335590717259237034879219 8003386075888855552318829)
                    ·
                      refine ⟨3001269778458320832119561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8003386075888855552318829 3001269778458320832119561)
                      ·
                        rfl

theorem cell23_5844952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_5844952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844952 prefixEnd_5844952 := by exact prefixLift 5844952
  have htrace : WordTrace (prefixWord ++ tailWord_5844952) baseStart_5844952 baseEnd_5844952 := by
    simpa [prefixWord, tailWord_5844952, baseEnd_5844952] using wordTrace_append hprefix tailTrace_5844952
  have hstable : (prefixWord ++ tailWord_5844952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844952).length < 2 ^ (prefixWord ++ tailWord_5844952).sum := by decide
  have hdescent : baseEnd_5844952 < baseStart_5844952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5844995 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 3]
def baseStart_5844995 : Nat := 118140960795 + 5844995 * 2 ^ 59
def prefixEnd_5844995 : Nat := 4983230072969 + 3 ^ 40 * 5844995 * 2
def baseEnd_5844995 : Nat := 3001291858126464163881863

theorem tailTrace_5844995 : CollatzResearch.WordTrace tailWord_5844995 prefixEnd_5844995 3001291858126464163881863 := by
  unfold tailWord_5844995
  simp only [CollatzResearch.WordTrace]
  refine ⟨213184481459588835516712439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142122987639725890344474959 213184481459588835516712439)
  ·
    refine ⟨319776722189383253275068659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213184481459588835516712439 319776722189383253275068659)
    ·
      refine ⟨479665083284074879912602989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319776722189383253275068659 479665083284074879912602989)
      ·
        refine ⟨179874406231528079967226121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 479665083284074879912602989 179874406231528079967226121)
        ·
          refine ⟨134905804673646059975419591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179874406231528079967226121 134905804673646059975419591)
          ·
            refine ⟨202358707010469089963129387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134905804673646059975419591 202358707010469089963129387)
            ·
              refine ⟨303538060515703634944694081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202358707010469089963129387 303538060515703634944694081)
              ·
                refine ⟨227653545386777726208520561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303538060515703634944694081 227653545386777726208520561)
                ·
                  refine ⟨170740159040083294656390421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227653545386777726208520561 170740159040083294656390421)
                  ·
                    refine ⟨8003444955003904437018301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 170740159040083294656390421 8003444955003904437018301)
                    ·
                      refine ⟨3001291858126464163881863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8003444955003904437018301 3001291858126464163881863)
                      ·
                        rfl

theorem cell23_5844995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_5844995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5844995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5844995 prefixEnd_5844995 := by exact prefixLift 5844995
  have htrace : WordTrace (prefixWord ++ tailWord_5844995) baseStart_5844995 baseEnd_5844995 := by
    simpa [prefixWord, tailWord_5844995, baseEnd_5844995] using wordTrace_append hprefix tailTrace_5844995
  have hstable : (prefixWord ++ tailWord_5844995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5844995).length < 2 ^ (prefixWord ++ tailWord_5844995).sum := by decide
  have hdescent : baseEnd_5844995 < baseStart_5844995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5844995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845055 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 5]
def baseStart_5845055 : Nat := 118140960795 + 5845055 * 2 ^ 59
def prefixEnd_5845055 : Nat := 4983230072969 + 3 ^ 40 * 5845055 * 2
def baseEnd_5845055 : Nat := 3001322666965733929131587

theorem tailTrace_5845055 : CollatzResearch.WordTrace tailWord_5845055 prefixEnd_5845055 3001322666965733929131587 := by
  unfold tailWord_5845055
  simp only [CollatzResearch.WordTrace]
  refine ⟨213186669839371465763896619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142124446559580977175931079 213186669839371465763896619)
  ·
    refine ⟨319780004759057198645844929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213186669839371465763896619 319780004759057198645844929)
    ·
      refine ⟨239835003569292898984383697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319780004759057198645844929 239835003569292898984383697)
      ·
        refine ⟨179876252676969674238287773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239835003569292898984383697 179876252676969674238287773)
        ·
          refine ⟨67453594753863627839357915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179876252676969674238287773 67453594753863627839357915)
          ·
            refine ⟨101180392130795441759036873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67453594753863627839357915 101180392130795441759036873)
            ·
              refine ⟨75885294098096581319277655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101180392130795441759036873 75885294098096581319277655)
              ·
                refine ⟨113827941147144871978916483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75885294098096581319277655 113827941147144871978916483)
                ·
                  refine ⟨170741911720717307968374725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113827941147144871978916483 170741911720717307968374725)
                  ·
                    refine ⟨32014108447634495244070261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 170741911720717307968374725 32014108447634495244070261)
                    ·
                      refine ⟨3001322666965733929131587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32014108447634495244070261 3001322666965733929131587)
                      ·
                        rfl

theorem cell23_5845055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_5845055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845055 prefixEnd_5845055 := by exact prefixLift 5845055
  have htrace : WordTrace (prefixWord ++ tailWord_5845055) baseStart_5845055 baseEnd_5845055 := by
    simpa [prefixWord, tailWord_5845055, baseEnd_5845055] using wordTrace_append hprefix tailTrace_5845055
  have hstable : (prefixWord ++ tailWord_5845055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845055).length < 2 ^ (prefixWord ++ tailWord_5845055).sum := by decide
  have hdescent : baseEnd_5845055 < baseStart_5845055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845115 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 7]
def baseStart_5845115 : Nat := 118140960795 + 5845115 * 2 ^ 59
def prefixEnd_5845115 : Nat := 4983230072969 + 3 ^ 40 * 5845115 * 2
def baseEnd_5845115 : Nat := 3001353475805003694381311

theorem tailTrace_5845115 : CollatzResearch.WordTrace tailWord_5845115 prefixEnd_5845115 3001353475805003694381311 := by
  unfold tailWord_5845115
  simp only [CollatzResearch.WordTrace]
  refine ⟨213188858219154096011080799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142125905479436064007387199 213188858219154096011080799)
  ·
    refine ⟨319783287328731144016621199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213188858219154096011080799 319783287328731144016621199)
    ·
      refine ⟨479674930993096716024931799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319783287328731144016621199 479674930993096716024931799)
      ·
        refine ⟨719512396489645074037397699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479674930993096716024931799 719512396489645074037397699)
        ·
          refine ⟨1079268594734467611056096549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719512396489645074037397699 1079268594734467611056096549)
          ·
            refine ⟨202362861512712677073018103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1079268594734467611056096549 202362861512712677073018103)
            ·
              refine ⟨303544292269069015609527155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202362861512712677073018103 303544292269069015609527155)
              ·
                refine ⟨455316438403603523414290733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303544292269069015609527155 455316438403603523414290733)
                ·
                  refine ⟨170743664401351321280359025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 455316438403603523414290733 170743664401351321280359025)
                  ·
                    refine ⟨128057748301013490960269269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 170743664401351321280359025 128057748301013490960269269)
                    ·
                      refine ⟨3001353475805003694381311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128057748301013490960269269 3001353475805003694381311)
                      ·
                        rfl

theorem cell23_5845115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 7].length) (baseStart_5845115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845115 prefixEnd_5845115 := by exact prefixLift 5845115
  have htrace : WordTrace (prefixWord ++ tailWord_5845115) baseStart_5845115 baseEnd_5845115 := by
    simpa [prefixWord, tailWord_5845115, baseEnd_5845115] using wordTrace_append hprefix tailTrace_5845115
  have hstable : (prefixWord ++ tailWord_5845115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845115).length < 2 ^ (prefixWord ++ tailWord_5845115).sum := by decide
  have hdescent : baseEnd_5845115 < baseStart_5845115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845149 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 2, 3, 3]
def baseStart_5845149 : Nat := 118140960795 + 5845149 * 2 ^ 59
def prefixEnd_5845149 : Nat := 4983230072969 + 3 ^ 40 * 5845149 * 2
def baseEnd_5845149 : Nat := 3001370934147256561356155

theorem tailTrace_5845149 : CollatzResearch.WordTrace tailWord_5845149 prefixEnd_5845149 3001370934147256561356155 := by
  unfold tailWord_5845149
  simp only [CollatzResearch.WordTrace]
  refine ⟨213190098301030919817818501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142126732200687279878545667 213190098301030919817818501)
  ·
    refine ⟨39973143431443297465840969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213190098301030919817818501 39973143431443297465840969)
    ·
      refine ⟨29979857573582473099380727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39973143431443297465840969 29979857573582473099380727)
      ·
        refine ⟨44969786360373709649071091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29979857573582473099380727 44969786360373709649071091)
        ·
          refine ⟨67454679540560564473606637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44969786360373709649071091 67454679540560564473606637)
          ·
            refine ⟨25295504827710211677602489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67454679540560564473606637 25295504827710211677602489)
            ·
              refine ⟨18971628620782658758201867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25295504827710211677602489 18971628620782658758201867)
              ·
                refine ⟨28457442931173988137302801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18971628620782658758201867 28457442931173988137302801)
                ·
                  refine ⟨21343082198380491102977101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28457442931173988137302801 21343082198380491102977101)
                  ·
                    refine ⟨8003655824392684163616413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21343082198380491102977101 8003655824392684163616413)
                    ·
                      refine ⟨3001370934147256561356155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8003655824392684163616413 3001370934147256561356155)
                      ·
                        rfl

theorem cell23_5845149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_5845149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845149 prefixEnd_5845149 := by exact prefixLift 5845149
  have htrace : WordTrace (prefixWord ++ tailWord_5845149) baseStart_5845149 baseEnd_5845149 := by
    simpa [prefixWord, tailWord_5845149, baseEnd_5845149] using wordTrace_append hprefix tailTrace_5845149
  have hstable : (prefixWord ++ tailWord_5845149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845149).length < 2 ^ (prefixWord ++ tailWord_5845149).sum := by decide
  have hdescent : baseEnd_5845149 < baseStart_5845149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845150 : List Nat := [4, 3, 1, 1, 3, 2, 1, 1, 1, 4, 2]
def baseStart_5845150 : Nat := 118140960795 + 5845150 * 2 ^ 59
def prefixEnd_5845150 : Nat := 4983230072969 + 3 ^ 40 * 5845150 * 2
def baseEnd_5845150 : Nat := 3001371447627911057443651

theorem tailTrace_5845150 : CollatzResearch.WordTrace tailWord_5845150 prefixEnd_5845150 3001371447627911057443651 := by
  unfold tailWord_5845150
  simp only [CollatzResearch.WordTrace]
  refine ⟨26648766846753412123575613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142126756516018197992403269 26648766846753412123575613)
  ·
    refine ⟨9993287567532529546340855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26648766846753412123575613 9993287567532529546340855)
    ·
      refine ⟨14989931351298794319511283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9993287567532529546340855 14989931351298794319511283)
      ·
        refine ⟨22484897026948191479266925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14989931351298794319511283 22484897026948191479266925)
        ·
          refine ⟨8431836385105571804725097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22484897026948191479266925 8431836385105571804725097)
          ·
            refine ⟨6323877288829178853543823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8431836385105571804725097 6323877288829178853543823)
            ·
              refine ⟨9485815933243768280315735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6323877288829178853543823 9485815933243768280315735)
              ·
                refine ⟨14228723899865652420473603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9485815933243768280315735 14228723899865652420473603)
                ·
                  refine ⟨21343085849798478630710405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14228723899865652420473603 21343085849798478630710405)
                  ·
                    refine ⟨4001828596837214743258201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21343085849798478630710405 4001828596837214743258201)
                    ·
                      refine ⟨3001371447627911057443651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4001828596837214743258201 3001371447627911057443651)
                      ·
                        rfl

theorem cell23_5845150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_5845150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845150 prefixEnd_5845150 := by exact prefixLift 5845150
  have htrace : WordTrace (prefixWord ++ tailWord_5845150) baseStart_5845150 baseEnd_5845150 := by
    simpa [prefixWord, tailWord_5845150, baseEnd_5845150] using wordTrace_append hprefix tailTrace_5845150
  have hstable : (prefixWord ++ tailWord_5845150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845150).length < 2 ^ (prefixWord ++ tailWord_5845150).sum := by decide
  have hdescent : baseEnd_5845150 < baseStart_5845150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845152 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 1, 7]
def baseStart_5845152 : Nat := 118140960795 + 5845152 * 2 ^ 59
def prefixEnd_5845152 : Nat := 4983230072969 + 3 ^ 40 * 5845152 * 2
def baseEnd_5845152 : Nat := 1000457491529740016539547

theorem tailTrace_5845152 : CollatzResearch.WordTrace tailWord_5845152 prefixEnd_5845152 1000457491529740016539547 := by
  unfold tailWord_5845152
  simp only [CollatzResearch.WordTrace]
  refine ⟨106595103860010025665088855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142126805146680034220118473 106595103860010025665088855)
  ·
    refine ⟨159892655790015038497633283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106595103860010025665088855 159892655790015038497633283)
    ·
      refine ⟨239838983685022557746449925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159892655790015038497633283 239838983685022557746449925)
      ·
        refine ⟨44969809440941729577459361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239838983685022557746449925 44969809440941729577459361)
        ·
          refine ⟨33727357080706297183094521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44969809440941729577459361 33727357080706297183094521)
          ·
            refine ⟨25295517810529722887320891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33727357080706297183094521 25295517810529722887320891)
            ·
              refine ⟨37943276715794584330981337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25295517810529722887320891 37943276715794584330981337)
              ·
                refine ⟨28457457536845938248236003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37943276715794584330981337 28457457536845938248236003)
                ·
                  refine ⟨42686186305268907372354005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28457457536845938248236003 42686186305268907372354005)
                  ·
                    refine ⟨1000457491529740016539547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42686186305268907372354005 1000457491529740016539547)
                    ·
                      rfl

theorem cell23_5845152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 1, 7].length) (baseStart_5845152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845152 prefixEnd_5845152 := by exact prefixLift 5845152
  have htrace : WordTrace (prefixWord ++ tailWord_5845152) baseStart_5845152 baseEnd_5845152 := by
    simpa [prefixWord, tailWord_5845152, baseEnd_5845152] using wordTrace_append hprefix tailTrace_5845152
  have hstable : (prefixWord ++ tailWord_5845152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845152).length < 2 ^ (prefixWord ++ tailWord_5845152).sum := by decide
  have hdescent : baseEnd_5845152 < baseStart_5845152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845189 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 4, 4, 2]
def baseStart_5845189 : Nat := 118140960795 + 5845189 * 2 ^ 59
def prefixEnd_5845189 : Nat := 4983230072969 + 3 ^ 40 * 5845189 * 2
def baseEnd_5845189 : Nat := 3001391473373436404855971

theorem tailTrace_5845189 : CollatzResearch.WordTrace tailWord_5845189 prefixEnd_5845189 3001391473373436404855971 := by
  unfold tailWord_5845189
  simp only [CollatzResearch.WordTrace]
  refine ⟨213191557220886006649274621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142127704813924004432849747 213191557220886006649274621)
  ·
    refine ⟨79946833957832252493477983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213191557220886006649274621 79946833957832252493477983)
    ·
      refine ⟨119920250936748378740216975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79946833957832252493477983 119920250936748378740216975)
      ·
        refine ⟨179880376405122568110325463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119920250936748378740216975 179880376405122568110325463)
        ·
          refine ⟨269820564607683852165488195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179880376405122568110325463 269820564607683852165488195)
          ·
            refine ⟨404730846911525778248232293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269820564607683852165488195 404730846911525778248232293)
            ·
              refine ⟨75887033795911083421543555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 404730846911525778248232293 75887033795911083421543555)
              ·
                refine ⟨113830550693866625132315333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75887033795911083421543555 113830550693866625132315333)
                ·
                  refine ⟨21343228255099992212309125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113830550693866625132315333 21343228255099992212309125)
                  ·
                    refine ⟨4001855297831248539807961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21343228255099992212309125 4001855297831248539807961)
                    ·
                      refine ⟨3001391473373436404855971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4001855297831248539807961 3001391473373436404855971)
                      ·
                        rfl

theorem cell23_5845189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 4, 2].length) (baseStart_5845189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845189 prefixEnd_5845189 := by exact prefixLift 5845189
  have htrace : WordTrace (prefixWord ++ tailWord_5845189) baseStart_5845189 baseEnd_5845189 := by
    simpa [prefixWord, tailWord_5845189, baseEnd_5845189] using wordTrace_append hprefix tailTrace_5845189
  have hstable : (prefixWord ++ tailWord_5845189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845189).length < 2 ^ (prefixWord ++ tailWord_5845189).sum := by decide
  have hdescent : baseEnd_5845189 < baseStart_5845189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845196 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 1, 2, 5]
def baseStart_5845196 : Nat := 118140960795 + 5845196 * 2 ^ 59
def prefixEnd_5845196 : Nat := 4983230072969 + 3 ^ 40 * 5845196 * 2
def baseEnd_5845196 : Nat := 3001395067738017877468439

theorem tailTrace_5845196 : CollatzResearch.WordTrace tailWord_5845196 prefixEnd_5845196 3001395067738017877468439 := by
  unfold tailWord_5845196
  simp only [CollatzResearch.WordTrace]
  refine ⟨106595906265930323422389721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142127875021240431229852961 106595906265930323422389721)
  ·
    refine ⟨79946929699447742566792291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106595906265930323422389721 79946929699447742566792291)
    ·
      refine ⟨119920394549171613850188437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79946929699447742566792291 119920394549171613850188437)
      ·
        refine ⟨5621268494492419399227583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 119920394549171613850188437 5621268494492419399227583)
        ·
          refine ⟨8431902741738629098841375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5621268494492419399227583 8431902741738629098841375)
          ·
            refine ⟨12647854112607943648262063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8431902741738629098841375 12647854112607943648262063)
            ·
              refine ⟨18971781168911915472393095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12647854112607943648262063 18971781168911915472393095)
              ·
                refine ⟨28457671753367873208589643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18971781168911915472393095 28457671753367873208589643)
                ·
                  refine ⟨42686507630051809812884465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28457671753367873208589643 42686507630051809812884465)
                  ·
                    refine ⟨32014880722538857359663349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42686507630051809812884465 32014880722538857359663349)
                    ·
                      refine ⟨3001395067738017877468439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32014880722538857359663349 3001395067738017877468439)
                      ·
                        rfl

theorem cell23_5845196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_5845196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845196 prefixEnd_5845196 := by exact prefixLift 5845196
  have htrace : WordTrace (prefixWord ++ tailWord_5845196) baseStart_5845196 baseEnd_5845196 := by
    simpa [prefixWord, tailWord_5845196, baseEnd_5845196] using wordTrace_append hprefix tailTrace_5845196
  have hstable : (prefixWord ++ tailWord_5845196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845196).length < 2 ^ (prefixWord ++ tailWord_5845196).sum := by decide
  have hdescent : baseEnd_5845196 < baseStart_5845196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845226 : List Nat := [3, 1, 3, 1, 1, 2, 4, 1, 2, 2, 3]
def baseStart_5845226 : Nat := 118140960795 + 5845226 * 2 ^ 59
def prefixEnd_5845226 : Nat := 4983230072969 + 3 ^ 40 * 5845226 * 2
def baseEnd_5845226 : Nat := 3001410472157652760093301

theorem tailTrace_5845226 : CollatzResearch.WordTrace tailWord_5845226 prefixEnd_5845226 3001410472157652760093301 := by
  unfold tailWord_5845226
  simp only [CollatzResearch.WordTrace]
  refine ⟨53298226680437990492092883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142128604481167974645581021 53298226680437990492092883)
  ·
    refine ⟨79947340020656985738139325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53298226680437990492092883 79947340020656985738139325)
    ·
      refine ⟨29980252507746369651802247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79947340020656985738139325 29980252507746369651802247)
      ·
        refine ⟨44970378761619554477703371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29980252507746369651802247 44970378761619554477703371)
        ·
          refine ⟨67455568142429331716555057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44970378761619554477703371 67455568142429331716555057)
          ·
            refine ⟨50591676106821998787416293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67455568142429331716555057 50591676106821998787416293)
            ·
              refine ⟨9485939270029124772640555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50591676106821998787416293 9485939270029124772640555)
              ·
                refine ⟨14228908905043687158960833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9485939270029124772640555 14228908905043687158960833)
                ·
                  refine ⟨10671681678782765369220625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14228908905043687158960833 10671681678782765369220625)
                  ·
                    refine ⟨8003761259087074026915469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10671681678782765369220625 8003761259087074026915469)
                    ·
                      refine ⟨3001410472157652760093301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8003761259087074026915469 3001410472157652760093301)
                      ·
                        rfl

theorem cell23_5845226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_5845226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845226 prefixEnd_5845226 := by exact prefixLift 5845226
  have htrace : WordTrace (prefixWord ++ tailWord_5845226) baseStart_5845226 baseEnd_5845226 := by
    simpa [prefixWord, tailWord_5845226, baseEnd_5845226] using wordTrace_append hprefix tailTrace_5845226
  have hstable : (prefixWord ++ tailWord_5845226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845226).length < 2 ^ (prefixWord ++ tailWord_5845226).sum := by decide
  have hdescent : baseEnd_5845226 < baseStart_5845226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845246 : List Nat := [4, 2, 2, 1, 1, 1, 4, 2, 6]
def baseStart_5845246 : Nat := 118140960795 + 5845246 * 2 ^ 59
def prefixEnd_5845246 : Nat := 4983230072969 + 3 ^ 40 * 5845246 * 2
def baseEnd_5845246 : Nat := 333491193530082520204801

theorem tailTrace_5845246 : CollatzResearch.WordTrace tailWord_5845246 prefixEnd_5845246 333491193530082520204801 := by
  unfold tailWord_5845246
  simp only [CollatzResearch.WordTrace]
  refine ⟨26649204522709938173012449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142129090787786336922733061 26649204522709938173012449)
  ·
    refine ⟨19986903392032453629759337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26649204522709938173012449 19986903392032453629759337)
    ·
      refine ⟨14990177544024340222319503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19986903392032453629759337 14990177544024340222319503)
      ·
        refine ⟨22485266316036510333479255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14990177544024340222319503 22485266316036510333479255)
        ·
          refine ⟨33727899474054765500218883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22485266316036510333479255 33727899474054765500218883)
          ·
            refine ⟨50591849211082148250328325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33727899474054765500218883 50591849211082148250328325)
            ·
              refine ⟨9485971727077902796936561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50591849211082148250328325 9485971727077902796936561)
              ·
                refine ⟨7114478795308427097702421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9485971727077902796936561 7114478795308427097702421)
                ·
                  refine ⟨333491193530082520204801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7114478795308427097702421 333491193530082520204801)
                  ·
                    rfl

theorem cell23_5845246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_5845246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845246 prefixEnd_5845246 := by exact prefixLift 5845246
  have htrace : WordTrace (prefixWord ++ tailWord_5845246) baseStart_5845246 baseEnd_5845246 := by
    simpa [prefixWord, tailWord_5845246, baseEnd_5845246] using wordTrace_append hprefix tailTrace_5845246
  have hstable : (prefixWord ++ tailWord_5845246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845246).length < 2 ^ (prefixWord ++ tailWord_5845246).sum := by decide
  have hdescent : baseEnd_5845246 < baseStart_5845246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845250 : List Nat := [3, 4, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_5845250 : Nat := 118140960795 + 5845250 * 2 ^ 59
def prefixEnd_5845250 : Nat := 4983230072969 + 3 ^ 40 * 5845250 * 2
def baseEnd_5845250 : Nat := 1000474265231120222064397

theorem tailTrace_5845250 : CollatzResearch.WordTrace tailWord_5845250 prefixEnd_5845250 1000474265231120222064397 := by
  unfold tailWord_5845250
  simp only [CollatzResearch.WordTrace]
  refine ⟨53298445518416253516811301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142129188049110009378163469 53298445518416253516811301)
  ·
    refine ⟨9993458534703047534402119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53298445518416253516811301 9993458534703047534402119)
    ·
      refine ⟨14990187802054571301603179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9993458534703047534402119 14990187802054571301603179)
      ·
        refine ⟨22485281703081856952404769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14990187802054571301603179 22485281703081856952404769)
        ·
          refine ⟨16863961277311392714303577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22485281703081856952404769 16863961277311392714303577)
          ·
            refine ⟨12647970957983544535727683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16863961277311392714303577 12647970957983544535727683)
            ·
              refine ⟨18971956436975316803591525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12647970957983544535727683 18971956436975316803591525)
              ·
                refine ⟨3557241831932871900673411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18971956436975316803591525 3557241831932871900673411)
                ·
                  refine ⟨5335862747899307851010117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3557241831932871900673411 5335862747899307851010117)
                  ·
                    refine ⟨1000474265231120222064397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5335862747899307851010117 1000474265231120222064397)
                    ·
                      rfl

theorem cell23_5845250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_5845250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845250 prefixEnd_5845250 := by exact prefixLift 5845250
  have htrace : WordTrace (prefixWord ++ tailWord_5845250) baseStart_5845250 baseEnd_5845250 := by
    simpa [prefixWord, tailWord_5845250, baseEnd_5845250] using wordTrace_append hprefix tailTrace_5845250
  have hstable : (prefixWord ++ tailWord_5845250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845250).length < 2 ^ (prefixWord ++ tailWord_5845250).sum := by decide
  have hdescent : baseEnd_5845250 < baseStart_5845250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845299 : List Nat := [1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 5]
def baseStart_5845299 : Nat := 118140960795 + 5845299 * 2 ^ 59
def prefixEnd_5845299 : Nat := 4983230072969 + 3 ^ 40 * 5845299 * 2
def baseEnd_5845299 : Nat := 3001447956245430974480465

theorem tailTrace_5845299 : CollatzResearch.WordTrace tailWord_5845299 prefixEnd_5845299 3001447956245430974480465 := by
  unfold tailWord_5845299
  simp only [CollatzResearch.WordTrace]
  refine ⟨213195569250487495435778951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142130379500324996957185967 213195569250487495435778951)
  ·
    refine ⟨319793353875731243153668427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213195569250487495435778951 319793353875731243153668427)
    ·
      refine ⟨479690030813596864730502641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319793353875731243153668427 479690030813596864730502641)
      ·
        refine ⟨359767523110197648547876981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479690030813596864730502641 359767523110197648547876981)
        ·
          refine ⟨33728205291581029551363467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 359767523110197648547876981 33728205291581029551363467)
          ·
            refine ⟨50592307937371544327045201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33728205291581029551363467 50592307937371544327045201)
            ·
              refine ⟨37944230953028658245283901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50592307937371544327045201 37944230953028658245283901)
              ·
                refine ⟨14229086607385746841981463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37944230953028658245283901 14229086607385746841981463)
                ·
                  refine ⟨21343629911078620262972195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14229086607385746841981463 21343629911078620262972195)
                  ·
                    refine ⟨32015444866617930394458293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21343629911078620262972195 32015444866617930394458293)
                    ·
                      refine ⟨3001447956245430974480465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32015444866617930394458293 3001447956245430974480465)
                      ·
                        rfl

theorem cell23_5845299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 5].length) (baseStart_5845299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845299 prefixEnd_5845299 := by exact prefixLift 5845299
  have htrace : WordTrace (prefixWord ++ tailWord_5845299) baseStart_5845299 baseEnd_5845299 := by
    simpa [prefixWord, tailWord_5845299, baseEnd_5845299] using wordTrace_append hprefix tailTrace_5845299
  have hstable : (prefixWord ++ tailWord_5845299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845299).length < 2 ^ (prefixWord ++ tailWord_5845299).sum := by decide
  have hdescent : baseEnd_5845299 < baseStart_5845299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845306 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 4, 4]
def baseStart_5845306 : Nat := 118140960795 + 5845306 * 2 ^ 59
def prefixEnd_5845306 : Nat := 4983230072969 + 3 ^ 40 * 5845306 * 2
def baseEnd_5845306 : Nat := 1000483850203337482364311

theorem tailTrace_5845306 : CollatzResearch.WordTrace tailWord_5845306 prefixEnd_5845306 1000483850203337482364311 := by
  unfold tailWord_5845306
  simp only [CollatzResearch.WordTrace]
  refine ⟨53298956140365533907820943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142130549707641423754189181 53298956140365533907820943)
  ·
    refine ⟨79948434210548300861731415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53298956140365533907820943 79948434210548300861731415)
    ·
      refine ⟨119922651315822451292597123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79948434210548300861731415 119922651315822451292597123)
      ·
        refine ⟨179883976973733676938895685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119922651315822451292597123 179883976973733676938895685)
        ·
          refine ⟨33728245682575064426042941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179883976973733676938895685 33728245682575064426042941)
          ·
            refine ⟨12648092130965649159766103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33728245682575064426042941 12648092130965649159766103)
            ·
              refine ⟨18972138196448473739649155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12648092130965649159766103 18972138196448473739649155)
              ·
                refine ⟨28458207294672710609473733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18972138196448473739649155 28458207294672710609473733)
                ·
                  refine ⟨5335913867751133239276325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28458207294672710609473733 5335913867751133239276325)
                  ·
                    refine ⟨1000483850203337482364311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5335913867751133239276325 1000483850203337482364311)
                    ·
                      rfl

theorem cell23_5845306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 4, 4].length) (baseStart_5845306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845306 prefixEnd_5845306 := by exact prefixLift 5845306
  have htrace : WordTrace (prefixWord ++ tailWord_5845306) baseStart_5845306 baseEnd_5845306 := by
    simpa [prefixWord, tailWord_5845306, baseEnd_5845306] using wordTrace_append hprefix tailTrace_5845306
  have hstable : (prefixWord ++ tailWord_5845306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845306).length < 2 ^ (prefixWord ++ tailWord_5845306).sum := by decide
  have hdescent : baseEnd_5845306 < baseStart_5845306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845369 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 2, 3, 4]
def baseStart_5845369 : Nat := 118140960795 + 5845369 * 2 ^ 59
def prefixEnd_5845369 : Nat := 4983230072969 + 3 ^ 40 * 5845369 * 2
def baseEnd_5845369 : Nat := 3001483899891245700605143

theorem tailTrace_5845369 : CollatzResearch.WordTrace tailWord_5845369 prefixEnd_5845369 3001483899891245700605143 := by
  unfold tailWord_5845369
  simp only [CollatzResearch.WordTrace]
  refine ⟨213198122360233897390827161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142132081573489264927218107 213198122360233897390827161)
  ·
    refine ⟨159898591770175423043120371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213198122360233897390827161 159898591770175423043120371)
    ·
      refine ⟨239847887655263134564680557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159898591770175423043120371 239847887655263134564680557)
      ·
        refine ⟨89942957870723675461755209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239847887655263134564680557 89942957870723675461755209)
        ·
          refine ⟨67457218403042756596316407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89942957870723675461755209 67457218403042756596316407)
          ·
            refine ⟨101185827604564134894474611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67457218403042756596316407 101185827604564134894474611)
            ·
              refine ⟨151778741406846202341711917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101185827604564134894474611 151778741406846202341711917)
              ·
                refine ⟨56917028027567325878141969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151778741406846202341711917 56917028027567325878141969)
                ·
                  refine ⟨42687771020675494408606477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56917028027567325878141969 42687771020675494408606477)
                  ·
                    refine ⟨16007914132753310403227429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42687771020675494408606477 16007914132753310403227429)
                    ·
                      refine ⟨3001483899891245700605143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16007914132753310403227429 3001483899891245700605143)
                      ·
                        rfl

theorem cell23_5845369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_5845369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845369 prefixEnd_5845369 := by exact prefixLift 5845369
  have htrace : WordTrace (prefixWord ++ tailWord_5845369) baseStart_5845369 baseEnd_5845369 := by
    simpa [prefixWord, tailWord_5845369, baseEnd_5845369] using wordTrace_append hprefix tailTrace_5845369
  have hstable : (prefixWord ++ tailWord_5845369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845369).length < 2 ^ (prefixWord ++ tailWord_5845369).sum := by decide
  have hdescent : baseEnd_5845369 < baseStart_5845369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845390 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2]
def baseStart_5845390 : Nat := 118140960795 + 5845390 * 2 ^ 59
def prefixEnd_5845390 : Nat := 4983230072969 + 3 ^ 40 * 5845390 * 2
def baseEnd_5845390 : Nat := 3001494682984990118442547

theorem tailTrace_5845390 : CollatzResearch.WordTrace tailWord_5845390 prefixEnd_5845390 3001494682984990118442547 := by
  unfold tailWord_5845390
  simp only [CollatzResearch.WordTrace]
  refine ⟨26649861036644727247167703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142132592195438545318227749 26649861036644727247167703)
  ·
    refine ⟨39974791554967090870751555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26649861036644727247167703 39974791554967090870751555)
    ·
      refine ⟨59962187332450636306127333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39974791554967090870751555 59962187332450636306127333)
      ·
        refine ⟨11242910124834494307398875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59962187332450636306127333 11242910124834494307398875)
        ·
          refine ⟨16864365187251741461098313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11242910124834494307398875 16864365187251741461098313)
          ·
            refine ⟨12648273890438806095823735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16864365187251741461098313 12648273890438806095823735)
            ·
              refine ⟨18972410835658209143735603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12648273890438806095823735 18972410835658209143735603)
              ·
                refine ⟨28458616253487313715603405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18972410835658209143735603 28458616253487313715603405)
                ·
                  refine ⟨10671981095057742643351277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28458616253487313715603405 10671981095057742643351277)
                  ·
                    refine ⟨4001992910646653491256729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10671981095057742643351277 4001992910646653491256729)
                    ·
                      refine ⟨3001494682984990118442547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4001992910646653491256729 3001494682984990118442547)
                      ·
                        rfl

theorem cell23_5845390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_5845390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845390 prefixEnd_5845390 := by exact prefixLift 5845390
  have htrace : WordTrace (prefixWord ++ tailWord_5845390) baseStart_5845390 baseEnd_5845390 := by
    simpa [prefixWord, tailWord_5845390, baseEnd_5845390] using wordTrace_append hprefix tailTrace_5845390
  have hstable : (prefixWord ++ tailWord_5845390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845390).length < 2 ^ (prefixWord ++ tailWord_5845390).sum := by decide
  have hdescent : baseEnd_5845390 < baseStart_5845390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845449 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 1, 1, 7]
def baseStart_5845449 : Nat := 118140960795 + 5845449 * 2 ^ 59
def prefixEnd_5845449 : Nat := 4983230072969 + 3 ^ 40 * 5845449 * 2
def baseEnd_5845449 : Nat := 3001524978343605387604775

theorem tailTrace_5845449 : CollatzResearch.WordTrace tailWord_5845449 prefixEnd_5845449 3001524978343605387604775 := by
  unfold tailWord_5845449
  simp only [CollatzResearch.WordTrace]
  refine ⟨213201040199944071053739401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142134026799962714035826267 213201040199944071053739401)
  ·
    refine ⟨159900780149958053290304551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213201040199944071053739401 159900780149958053290304551)
    ·
      refine ⟨239851170224937079935456827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159900780149958053290304551 239851170224937079935456827)
      ·
        refine ⟨359776755337405619903185241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239851170224937079935456827 359776755337405619903185241)
        ·
          refine ⟨269832566503054214927388931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359776755337405619903185241 269832566503054214927388931)
          ·
            refine ⟨404748849754581322391083397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269832566503054214927388931 404748849754581322391083397)
            ·
              refine ⟨75890409328983997948328137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 404748849754581322391083397 75890409328983997948328137)
              ·
                refine ⟨56917806996737998461246103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75890409328983997948328137 56917806996737998461246103)
                ·
                  refine ⟨85376710495106997691869155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56917806996737998461246103 85376710495106997691869155)
                  ·
                    refine ⟨128065065742660496537803733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85376710495106997691869155 128065065742660496537803733)
                    ·
                      refine ⟨3001524978343605387604775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128065065742660496537803733 3001524978343605387604775)
                      ·
                        rfl

theorem cell23_5845449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_5845449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845449 prefixEnd_5845449 := by exact prefixLift 5845449
  have htrace : WordTrace (prefixWord ++ tailWord_5845449) baseStart_5845449 baseEnd_5845449 := by
    simpa [prefixWord, tailWord_5845449, baseEnd_5845449] using wordTrace_append hprefix tailTrace_5845449
  have hstable : (prefixWord ++ tailWord_5845449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845449).length < 2 ^ (prefixWord ++ tailWord_5845449).sum := by decide
  have hdescent : baseEnd_5845449 < baseStart_5845449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845460 : List Nat := [2, 4, 1, 2, 2, 2, 2, 3, 5]
def baseStart_5845460 : Nat := 118140960795 + 5845460 * 2 ^ 59
def prefixEnd_5845460 : Nat := 4983230072969 + 3 ^ 40 * 5845460 * 2
def baseEnd_5845460 : Nat := 333503402958978316063025

theorem tailTrace_5845460 : CollatzResearch.WordTrace tailWord_5845460 prefixEnd_5845460 333503402958978316063025 := by
  unfold tailWord_5845460
  simp only [CollatzResearch.WordTrace]
  refine ⟨106600720701452109966194917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142134294268602813288259889 106600720701452109966194917)
  ·
    refine ⟨19987635131522270618661547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106600720701452109966194917 19987635131522270618661547)
    ·
      refine ⟨29981452697283405927992321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19987635131522270618661547 29981452697283405927992321)
      ·
        refine ⟨22486089522962554445994241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29981452697283405927992321 22486089522962554445994241)
        ·
          refine ⟨16864567142221915834495681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22486089522962554445994241 16864567142221915834495681)
          ·
            refine ⟨12648425356666436875871761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16864567142221915834495681 12648425356666436875871761)
            ·
              refine ⟨9486319017499827656903821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12648425356666436875871761 9486319017499827656903821)
              ·
                refine ⟨3557369631562435371338933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9486319017499827656903821 3557369631562435371338933)
                ·
                  refine ⟨333503402958978316063025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3557369631562435371338933 333503402958978316063025)
                  ·
                    rfl

theorem cell23_5845460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_5845460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845460 prefixEnd_5845460 := by exact prefixLift 5845460
  have htrace : WordTrace (prefixWord ++ tailWord_5845460) baseStart_5845460 baseEnd_5845460 := by
    simpa [prefixWord, tailWord_5845460, baseEnd_5845460] using wordTrace_append hprefix tailTrace_5845460
  have hstable : (prefixWord ++ tailWord_5845460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845460).length < 2 ^ (prefixWord ++ tailWord_5845460).sum := by decide
  have hdescent : baseEnd_5845460 < baseStart_5845460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845496 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 3, 4, 3]
def baseStart_5845496 : Nat := 118140960795 + 5845496 * 2 ^ 59
def prefixEnd_5845496 : Nat := 4983230072969 + 3 ^ 40 * 5845496 * 2
def baseEnd_5845496 : Nat := 3001549111934366703717059

theorem tailTrace_5845496 : CollatzResearch.WordTrace tailWord_5845496 prefixEnd_5845496 3001549111934366703717059 := by
  unfold tailWord_5845496
  simp only [CollatzResearch.WordTrace]
  refine ⟨106601377215386899040350171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142135169620515865387133561 106601377215386899040350171)
  ·
    refine ⟨159902065823080348560525257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106601377215386899040350171 159902065823080348560525257)
    ·
      refine ⟨119926549367310261420393943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159902065823080348560525257 119926549367310261420393943)
      ·
        refine ⟨179889824050965392130590915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119926549367310261420393943 179889824050965392130590915)
        ·
          refine ⟨269834736076448088195886373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179889824050965392130590915 269834736076448088195886373)
          ·
            refine ⟨50594013014334016536728695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 269834736076448088195886373 50594013014334016536728695)
            ·
              refine ⟨75891019521501024805093043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50594013014334016536728695 75891019521501024805093043)
              ·
                refine ⟨113836529282251537207639565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75891019521501024805093043 113836529282251537207639565)
                ·
                  refine ⟨42688698480844326452864837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113836529282251537207639565 42688698480844326452864837)
                  ·
                    refine ⟨8004130965158311209912157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42688698480844326452864837 8004130965158311209912157)
                    ·
                      refine ⟨3001549111934366703717059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8004130965158311209912157 3001549111934366703717059)
                      ·
                        rfl

theorem cell23_5845496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 3, 4, 3].length) (baseStart_5845496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845496 prefixEnd_5845496 := by exact prefixLift 5845496
  have htrace : WordTrace (prefixWord ++ tailWord_5845496) baseStart_5845496 baseEnd_5845496 := by
    simpa [prefixWord, tailWord_5845496, baseEnd_5845496] using wordTrace_append hprefix tailTrace_5845496
  have hstable : (prefixWord ++ tailWord_5845496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845496).length < 2 ^ (prefixWord ++ tailWord_5845496).sum := by decide
  have hdescent : baseEnd_5845496 < baseStart_5845496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845499 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 12]
def baseStart_5845499 : Nat := 118140960795 + 5845499 * 2 ^ 59
def prefixEnd_5845499 : Nat := 4983230072969 + 3 ^ 40 * 5845499 * 2
def baseEnd_5845499 : Nat := 333505628041814465775505

theorem tailTrace_5845499 : CollatzResearch.WordTrace tailWord_5845499 prefixEnd_5845499 333505628041814465775505 := by
  unfold tailWord_5845499
  simp only [CollatzResearch.WordTrace]
  refine ⟨213202863849762929593059551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142135242566508619728706367 213202863849762929593059551)
  ·
    refine ⟨319804295774644394389589327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213202863849762929593059551 319804295774644394389589327)
    ·
      refine ⟨479706443661966591584383991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319804295774644394389589327 479706443661966591584383991)
      ·
        refine ⟨719559665492949887376575987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479706443661966591584383991 719559665492949887376575987)
        ·
          refine ⟨1079339498239424831064863981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719559665492949887376575987 1079339498239424831064863981)
          ·
            refine ⟨404752311839784311649323993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1079339498239424831064863981 404752311839784311649323993)
            ·
              refine ⟨303564233879838233736992995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404752311839784311649323993 303564233879838233736992995)
              ·
                refine ⟨455346350819757350605489493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303564233879838233736992995 455346350819757350605489493)
                ·
                  refine ⟨333505628041814465775505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 455346350819757350605489493 333505628041814465775505)
                  ·
                    rfl

theorem cell23_5845499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 12].length) (baseStart_5845499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845499 prefixEnd_5845499 := by exact prefixLift 5845499
  have htrace : WordTrace (prefixWord ++ tailWord_5845499) baseStart_5845499 baseEnd_5845499 := by
    simpa [prefixWord, tailWord_5845499, baseEnd_5845499] using wordTrace_append hprefix tailTrace_5845499
  have hstable : (prefixWord ++ tailWord_5845499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845499).length < 2 ^ (prefixWord ++ tailWord_5845499).sum := by decide
  have hdescent : baseEnd_5845499 < baseStart_5845499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845516 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 8]
def baseStart_5845516 : Nat := 118140960795 + 5845516 * 2 ^ 59
def prefixEnd_5845516 : Nat := 4983230072969 + 3 ^ 40 * 5845516 * 2
def baseEnd_5845516 : Nat := 333506597949717402829663

theorem tailTrace_5845516 : CollatzResearch.WordTrace tailWord_5845516 prefixEnd_5845516 333506597949717402829663 := by
  unfold tailWord_5845516
  simp only [CollatzResearch.WordTrace]
  refine ⟨106601741945350670748214201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142135655927134227664285601 106601741945350670748214201)
  ·
    refine ⟨79951306459013003061160651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106601741945350670748214201 79951306459013003061160651)
    ·
      refine ⟨119926959688519504591740977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79951306459013003061160651 119926959688519504591740977)
      ·
        refine ⟨89945219766389628443805733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119926959688519504591740977 89945219766389628443805733)
        ·
          refine ⟨16864728706198055333213575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89945219766389628443805733 16864728706198055333213575)
          ·
            refine ⟨25297093059297082999820363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16864728706198055333213575 25297093059297082999820363)
            ·
              refine ⟨37945639588945624499730545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25297093059297082999820363 37945639588945624499730545)
              ·
                refine ⟨28459229691709218374797909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37945639588945624499730545 28459229691709218374797909)
                ·
                  refine ⟨333506597949717402829663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28459229691709218374797909 333506597949717402829663)
                  ·
                    rfl

theorem cell23_5845516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 8].length) (baseStart_5845516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845516 prefixEnd_5845516 := by exact prefixLift 5845516
  have htrace : WordTrace (prefixWord ++ tailWord_5845516) baseStart_5845516 baseEnd_5845516 := by
    simpa [prefixWord, tailWord_5845516, baseEnd_5845516] using wordTrace_append hprefix tailTrace_5845516
  have hstable : (prefixWord ++ tailWord_5845516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845516).length < 2 ^ (prefixWord ++ tailWord_5845516).sum := by decide
  have hdescent : baseEnd_5845516 < baseStart_5845516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845537 : List Nat := [1, 2, 3, 2, 2, 1, 5, 2, 1, 4]
def baseStart_5845537 : Nat := 118140960795 + 5845537 * 2 ^ 59
def prefixEnd_5845537 : Nat := 4983230072969 + 3 ^ 40 * 5845537 * 2
def baseEnd_5845537 : Nat := 1000523388213733681101457

theorem tailTrace_5845537 : CollatzResearch.WordTrace tailWord_5845537 prefixEnd_5845537 1000523388213733681101457 := by
  unfold tailWord_5845537
  simp only [CollatzResearch.WordTrace]
  refine ⟨213204249823625262082942865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142136166549083508055295243 213204249823625262082942865)
  ·
    refine ⟨159903187367718946562207149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213204249823625262082942865 159903187367718946562207149)
    ·
      refine ⟨59963695262894604960827681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159903187367718946562207149 59963695262894604960827681)
      ·
        refine ⟨44972771447170953720620761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59963695262894604960827681 44972771447170953720620761)
        ·
          refine ⟨33729578585378215290465571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44972771447170953720620761 33729578585378215290465571)
          ·
            refine ⟨50594367878067322935698357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33729578585378215290465571 50594367878067322935698357)
            ·
              refine ⟨4743221988568811525221721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50594367878067322935698357 4743221988568811525221721)
              ·
                refine ⟨3557416491426608643916291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4743221988568811525221721 3557416491426608643916291)
                ·
                  refine ⟨5336124737139912965874437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3557416491426608643916291 5336124737139912965874437)
                  ·
                    refine ⟨1000523388213733681101457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5336124737139912965874437 1000523388213733681101457)
                    ·
                      rfl

theorem cell23_5845537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_5845537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845537 prefixEnd_5845537 := by exact prefixLift 5845537
  have htrace : WordTrace (prefixWord ++ tailWord_5845537) baseStart_5845537 baseEnd_5845537 := by
    simpa [prefixWord, tailWord_5845537, baseEnd_5845537] using wordTrace_append hprefix tailTrace_5845537
  have hstable : (prefixWord ++ tailWord_5845537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845537).length < 2 ^ (prefixWord ++ tailWord_5845537).sum := by decide
  have hdescent : baseEnd_5845537 < baseStart_5845537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845550 : List Nat := [4, 1, 3, 1, 3, 1, 1, 3, 6]
def baseStart_5845550 : Nat := 118140960795 + 5845550 * 2 ^ 59
def prefixEnd_5845550 : Nat := 4983230072969 + 3 ^ 40 * 5845550 * 2
def baseEnd_5845550 : Nat := 333508537765523276937979

theorem tailTrace_5845550 : CollatzResearch.WordTrace tailWord_5845550 prefixEnd_5845550 333508537765523276937979 := by
  unfold tailWord_5845550
  simp only [CollatzResearch.WordTrace]
  refine ⟨26650590496572270662895763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142136482648385443535444069 26650590496572270662895763)
  ·
    refine ⟨39975885744858405994343645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26650590496572270662895763 39975885744858405994343645)
    ·
      refine ⟨14990957154321902247878867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39975885744858405994343645 14990957154321902247878867)
      ·
        refine ⟨22486435731482853371818301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14990957154321902247878867 22486435731482853371818301)
        ·
          refine ⟨8432413399306070014431863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22486435731482853371818301 8432413399306070014431863)
          ·
            refine ⟨12648620098959105021647795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8432413399306070014431863 12648620098959105021647795)
            ·
              refine ⟨18972930148438657532471693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12648620098959105021647795 18972930148438657532471693)
              ·
                refine ⟨7114848805664496574676885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18972930148438657532471693 7114848805664496574676885)
                ·
                  refine ⟨333508537765523276937979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7114848805664496574676885 333508537765523276937979)
                  ·
                    rfl

theorem cell23_5845550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_5845550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845550 prefixEnd_5845550 := by exact prefixLift 5845550
  have htrace : WordTrace (prefixWord ++ tailWord_5845550) baseStart_5845550 baseEnd_5845550 := by
    simpa [prefixWord, tailWord_5845550, baseEnd_5845550] using wordTrace_append hprefix tailTrace_5845550
  have hstable : (prefixWord ++ tailWord_5845550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845550).length < 2 ^ (prefixWord ++ tailWord_5845550).sum := by decide
  have hdescent : baseEnd_5845550 < baseStart_5845550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845553 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 3, 5, 2]
def baseStart_5845553 : Nat := 118140960795 + 5845553 * 2 ^ 59
def prefixEnd_5845553 : Nat := 4983230072969 + 3 ^ 40 * 5845553 * 2
def baseEnd_5845553 : Nat := 3001578380331672980704297

theorem tailTrace_5845553 : CollatzResearch.WordTrace tailWord_5845553 prefixEnd_5845553 3001578380331672980704297 := by
  unfold tailWord_5845553
  simp only [CollatzResearch.WordTrace]
  refine ⟨213204833391567296815525313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142136555594378197877016875 213204833391567296815525313)
  ·
    refine ⟨159903625043675472611643985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213204833391567296815525313 159903625043675472611643985)
    ·
      refine ⟨119927718782756604458732989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159903625043675472611643985 119927718782756604458732989)
      ·
        refine ⟨44972894543533726672024871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119927718782756604458732989 44972894543533726672024871)
        ·
          refine ⟨67459341815300590008037307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44972894543533726672024871 67459341815300590008037307)
          ·
            refine ⟨101189012722950885012055961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67459341815300590008037307 101189012722950885012055961)
            ·
              refine ⟨75891759542213163759041971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101189012722950885012055961 75891759542213163759041971)
              ·
                refine ⟨113837639313319745638562957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75891759542213163759041971 113837639313319745638562957)
                ·
                  refine ⟨42689114742494904614461109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113837639313319745638562957 42689114742494904614461109)
                  ·
                    refine ⟨4002104507108897307605729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42689114742494904614461109 4002104507108897307605729)
                    ·
                      refine ⟨3001578380331672980704297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4002104507108897307605729 3001578380331672980704297)
                      ·
                        rfl

theorem cell23_5845553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_5845553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845553 prefixEnd_5845553 := by exact prefixLift 5845553
  have htrace : WordTrace (prefixWord ++ tailWord_5845553) baseStart_5845553 baseEnd_5845553 := by
    simpa [prefixWord, tailWord_5845553, baseEnd_5845553] using wordTrace_append hprefix tailTrace_5845553
  have hstable : (prefixWord ++ tailWord_5845553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845553).length < 2 ^ (prefixWord ++ tailWord_5845553).sum := by decide
  have hdescent : baseEnd_5845553 < baseStart_5845553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845580 : List Nat := [2, 2, 1, 3, 1, 2, 5, 1, 1, 5]
def baseStart_5845580 : Nat := 118140960795 + 5845580 * 2 ^ 59
def prefixEnd_5845580 : Nat := 4983230072969 + 3 ^ 40 * 5845580 * 2
def baseEnd_5845580 : Nat := 1000530748103114791688891

theorem tailTrace_5845580 : CollatzResearch.WordTrace tailWord_5845580 prefixEnd_5845580 1000530748103114791688891 := by
  unfold tailWord_5845580
  simp only [CollatzResearch.WordTrace]
  refine ⟨106602909081234740213379097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142137212108312986951172129 106602909081234740213379097)
  ·
    refine ⟨79952181810926055160034323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106602909081234740213379097 79952181810926055160034323)
    ·
      refine ⟨119928272716389082740051485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79952181810926055160034323 119928272716389082740051485)
      ·
        refine ⟨44973102268645906027519307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119928272716389082740051485 44973102268645906027519307)
        ·
          refine ⟨67459653402968859041278961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44973102268645906027519307 67459653402968859041278961)
          ·
            refine ⟨50594740052226644280959221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67459653402968859041278961 50594740052226644280959221)
            ·
              refine ⟨4743256879896247901339927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50594740052226644280959221 4743256879896247901339927)
              ·
                refine ⟨7114885319844371852009891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4743256879896247901339927 7114885319844371852009891)
                ·
                  refine ⟨10672327979766557778014837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7114885319844371852009891 10672327979766557778014837)
                  ·
                    refine ⟨1000530748103114791688891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10672327979766557778014837 1000530748103114791688891)
                    ·
                      rfl

theorem cell23_5845580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 1, 5].length) (baseStart_5845580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845580 prefixEnd_5845580 := by exact prefixLift 5845580
  have htrace : WordTrace (prefixWord ++ tailWord_5845580) baseStart_5845580 baseEnd_5845580 := by
    simpa [prefixWord, tailWord_5845580, baseEnd_5845580] using wordTrace_append hprefix tailTrace_5845580
  have hstable : (prefixWord ++ tailWord_5845580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845580).length < 2 ^ (prefixWord ++ tailWord_5845580).sum := by decide
  have hdescent : baseEnd_5845580 < baseStart_5845580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845583 : List Nat := [1, 1, 2, 1, 1, 2, 4, 5, 1, 1, 4]
def baseStart_5845583 : Nat := 118140960795 + 5845583 * 2 ^ 59
def prefixEnd_5845583 : Nat := 4983230072969 + 3 ^ 40 * 5845583 * 2
def baseEnd_5845583 : Nat := 3001593784751307863329159

theorem tailTrace_5845583 : CollatzResearch.WordTrace tailWord_5845583 prefixEnd_5845583 3001593784751307863329159 := by
  unfold tailWord_5845583
  simp only [CollatzResearch.WordTrace]
  refine ⟨213205927581458611939117403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142137285054305741292744935 213205927581458611939117403)
  ·
    refine ⟨319808891372187917908676105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213205927581458611939117403 319808891372187917908676105)
    ·
      refine ⟨239856668529140938431507079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319808891372187917908676105 239856668529140938431507079)
      ·
        refine ⟨359785002793711407647260619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239856668529140938431507079 359785002793711407647260619)
        ·
          refine ⟨539677504190567111470890929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359785002793711407647260619 539677504190567111470890929)
          ·
            refine ⟨404758128142925333603168197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 539677504190567111470890929 404758128142925333603168197)
            ·
              refine ⟨75892149026798500050594037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 404758128142925333603168197 75892149026798500050594037)
              ·
                refine ⟨7114888971262359379743191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75892149026798500050594037 7114888971262359379743191)
                ·
                  refine ⟨10672333456893539069614787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7114888971262359379743191 10672333456893539069614787)
                  ·
                    refine ⟨16008500185340308604422181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10672333456893539069614787 16008500185340308604422181)
                    ·
                      refine ⟨3001593784751307863329159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16008500185340308604422181 3001593784751307863329159)
                      ·
                        rfl

theorem cell23_5845583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 1, 4].length) (baseStart_5845583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845583 prefixEnd_5845583 := by exact prefixLift 5845583
  have htrace : WordTrace (prefixWord ++ tailWord_5845583) baseStart_5845583 baseEnd_5845583 := by
    simpa [prefixWord, tailWord_5845583, baseEnd_5845583] using wordTrace_append hprefix tailTrace_5845583
  have hstable : (prefixWord ++ tailWord_5845583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845583).length < 2 ^ (prefixWord ++ tailWord_5845583).sum := by decide
  have hdescent : baseEnd_5845583 < baseStart_5845583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845603 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 3]
def baseStart_5845603 : Nat := 118140960795 + 5845603 * 2 ^ 59
def prefixEnd_5845603 : Nat := 4983230072969 + 3 ^ 40 * 5845603 * 2
def baseEnd_5845603 : Nat := 3001604054364397785079067

theorem tailTrace_5845603 : CollatzResearch.WordTrace tailWord_5845603 prefixEnd_5845603 3001604054364397785079067 := by
  unfold tailWord_5845603
  simp only [CollatzResearch.WordTrace]
  refine ⟨213206657041386155354845463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142137771360924103569896975 213206657041386155354845463)
  ·
    refine ⟨319809985562079233032268195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213206657041386155354845463 319809985562079233032268195)
    ·
      refine ⟨479714978343118849548402293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319809985562079233032268195 479714978343118849548402293)
      ·
        refine ⟨44973279219667392145162715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 479714978343118849548402293 44973279219667392145162715)
        ·
          refine ⟨67459918829501088217744073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44973279219667392145162715 67459918829501088217744073)
          ·
            refine ⟨50594939122125816163308055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67459918829501088217744073 50594939122125816163308055)
            ·
              refine ⟨75892408683188724244962083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50594939122125816163308055 75892408683188724244962083)
              ·
                refine ⟨113838613024783086367443125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75892408683188724244962083 113838613024783086367443125)
                ·
                  refine ⟨10672369971073414346947793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113838613024783086367443125 10672369971073414346947793)
                  ·
                    refine ⟨8004277478305060760210845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10672369971073414346947793 8004277478305060760210845)
                    ·
                      refine ⟨3001604054364397785079067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8004277478305060760210845 3001604054364397785079067)
                      ·
                        rfl

theorem cell23_5845603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_5845603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845603 prefixEnd_5845603 := by exact prefixLift 5845603
  have htrace : WordTrace (prefixWord ++ tailWord_5845603) baseStart_5845603 baseEnd_5845603 := by
    simpa [prefixWord, tailWord_5845603, baseEnd_5845603] using wordTrace_append hprefix tailTrace_5845603
  have hstable : (prefixWord ++ tailWord_5845603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845603).length < 2 ^ (prefixWord ++ tailWord_5845603).sum := by decide
  have hdescent : baseEnd_5845603 < baseStart_5845603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845610 : List Nat := [3, 1, 3, 2, 1, 1, 1, 5, 2, 4]
def baseStart_5845610 : Nat := 118140960795 + 5845610 * 2 ^ 59
def prefixEnd_5845610 : Nat := 4983230072969 + 3 ^ 40 * 5845610 * 2
def baseEnd_5845610 : Nat := 1000535882909659752563845

theorem tailTrace_5845610 : CollatzResearch.WordTrace tailWord_5845610 prefixEnd_5845610 1000535882909659752563845 := by
  unfold tailWord_5845610
  simp only [CollatzResearch.WordTrace]
  refine ⟨53301728088090198887587571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142137941568240530366900189 53301728088090198887587571)
  ·
    refine ⟨79952592132135298331381357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53301728088090198887587571 79952592132135298331381357)
    ·
      refine ⟨29982222049550736874268009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79952592132135298331381357 29982222049550736874268009)
      ·
        refine ⟨22486666537163052655701007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29982222049550736874268009 22486666537163052655701007)
        ·
          refine ⟨33729999805744578983551511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22486666537163052655701007 33729999805744578983551511)
          ·
            refine ⟨50594999708616868475327267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33729999805744578983551511 50594999708616868475327267)
            ·
              refine ⟨75892499562925302712990901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50594999708616868475327267 75892499562925302712990901)
              ·
                refine ⟨7114921834024247129342897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75892499562925302712990901 7114921834024247129342897)
                ·
                  refine ⟨5336191375518185347007173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7114921834024247129342897 5336191375518185347007173)
                  ·
                    refine ⟨1000535882909659752563845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5336191375518185347007173 1000535882909659752563845)
                    ·
                      rfl

theorem cell23_5845610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_5845610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845610 prefixEnd_5845610 := by exact prefixLift 5845610
  have htrace : WordTrace (prefixWord ++ tailWord_5845610) baseStart_5845610 baseEnd_5845610 := by
    simpa [prefixWord, tailWord_5845610, baseEnd_5845610] using wordTrace_append hprefix tailTrace_5845610
  have hstable : (prefixWord ++ tailWord_5845610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845610).length < 2 ^ (prefixWord ++ tailWord_5845610).sum := by decide
  have hdescent : baseEnd_5845610 < baseStart_5845610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845621 : List Nat := [1, 3, 4, 2, 3, 1, 1, 1, 2, 3, 2]
def baseStart_5845621 : Nat := 118140960795 + 5845621 * 2 ^ 59
def prefixEnd_5845621 : Nat := 4983230072969 + 3 ^ 40 * 5845621 * 2
def baseEnd_5845621 : Nat := 3001613297016178714653985

theorem tailTrace_5845621 : CollatzResearch.WordTrace tailWord_5845621 prefixEnd_5845621 3001613297016178714653985 := by
  unfold tailWord_5845621
  simp only [CollatzResearch.WordTrace]
  refine ⟨213207313555320944429000717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142138209036880629619333811 213207313555320944429000717)
  ·
    refine ⟨79952742583245354160875269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213207313555320944429000717 79952742583245354160875269)
    ·
      refine ⟨14991139234358503905164113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79952742583245354160875269 14991139234358503905164113)
      ·
        refine ⟨11243354425768877928873085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14991139234358503905164113 11243354425768877928873085)
        ·
          refine ⟨4216257909663329223327407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11243354425768877928873085 4216257909663329223327407)
          ·
            refine ⟨6324386864494993834991111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4216257909663329223327407 6324386864494993834991111)
            ·
              refine ⟨9486580296742490752486667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6324386864494993834991111 9486580296742490752486667)
              ·
                refine ⟨14229870445113736128730001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9486580296742490752486667 14229870445113736128730001)
                ·
                  refine ⟨10672402833835302096547501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14229870445113736128730001 10672402833835302096547501)
                  ·
                    refine ⟨4002151062688238286205313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10672402833835302096547501 4002151062688238286205313)
                    ·
                      refine ⟨3001613297016178714653985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4002151062688238286205313 3001613297016178714653985)
                      ·
                        rfl

theorem cell23_5845621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_5845621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845621 prefixEnd_5845621 := by exact prefixLift 5845621
  have htrace : WordTrace (prefixWord ++ tailWord_5845621) baseStart_5845621 baseEnd_5845621 := by
    simpa [prefixWord, tailWord_5845621, baseEnd_5845621] using wordTrace_append hprefix tailTrace_5845621
  have hstable : (prefixWord ++ tailWord_5845621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845621).length < 2 ^ (prefixWord ++ tailWord_5845621).sum := by decide
  have hdescent : baseEnd_5845621 < baseStart_5845621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845626 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6]
def baseStart_5845626 : Nat := 118140960795 + 5845626 * 2 ^ 59
def prefixEnd_5845626 : Nat := 4983230072969 + 3 ^ 40 * 5845626 * 2
def baseEnd_5845626 : Nat := 3001615864419451195091461

theorem tailTrace_5845626 : CollatzResearch.WordTrace tailWord_5845626 prefixEnd_5845626 3001615864419451195091461 := by
  unfold tailWord_5845626
  simp only [CollatzResearch.WordTrace]
  refine ⟨53301873980075707570733183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142138330613535220188621821 53301873980075707570733183)
  ·
    refine ⟨79952810970113561356099775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53301873980075707570733183 79952810970113561356099775)
    ·
      refine ⟨119929216455170342034149663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79952810970113561356099775 119929216455170342034149663)
      ·
        refine ⟨179893824682755513051224495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119929216455170342034149663 179893824682755513051224495)
        ·
          refine ⟨269840737024133269576836743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179893824682755513051224495 269840737024133269576836743)
          ·
            refine ⟨404761105536199904365255115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269840737024133269576836743 404761105536199904365255115)
            ·
              refine ⟨607141658304299856547882673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404761105536199904365255115 607141658304299856547882673)
              ·
                refine ⟨455356243728224892410912005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 607141658304299856547882673 455356243728224892410912005)
                ·
                  refine ⟨85379295699042167327046001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 455356243728224892410912005 85379295699042167327046001)
                  ·
                    refine ⟨64034471774281625495284501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85379295699042167327046001 64034471774281625495284501)
                    ·
                      refine ⟨3001615864419451195091461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64034471774281625495284501 3001615864419451195091461)
                      ·
                        rfl

theorem cell23_5845626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_5845626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845626 prefixEnd_5845626 := by exact prefixLift 5845626
  have htrace : WordTrace (prefixWord ++ tailWord_5845626) baseStart_5845626 baseEnd_5845626 := by
    simpa [prefixWord, tailWord_5845626, baseEnd_5845626] using wordTrace_append hprefix tailTrace_5845626
  have hstable : (prefixWord ++ tailWord_5845626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845626).length < 2 ^ (prefixWord ++ tailWord_5845626).sum := by decide
  have hdescent : baseEnd_5845626 < baseStart_5845626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845637 : List Nat := [1, 3, 1, 1, 4, 2, 4, 1, 1, 2, 3]
def baseStart_5845637 : Nat := 118140960795 + 5845637 * 2 ^ 59
def prefixEnd_5845637 : Nat := 4983230072969 + 3 ^ 40 * 5845637 * 2
def baseEnd_5845637 : Nat := 3001621512706650652053911

theorem tailTrace_5845637 : CollatzResearch.WordTrace tailWord_5845637 prefixEnd_5845637 3001621512706650652053911 := by
  unfold tailWord_5845637
  simp only [CollatzResearch.WordTrace]
  refine ⟨213207897123262979161583165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142138598082175319441055443 213207897123262979161583165)
  ·
    refine ⟨79952961421223617185593687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213207897123262979161583165 79952961421223617185593687)
    ·
      refine ⟨119929442131835425778390531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79952961421223617185593687 119929442131835425778390531)
      ·
        refine ⟨179894163197753138667585797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119929442131835425778390531 179894163197753138667585797)
        ·
          refine ⟨33730155599578713500172337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179894163197753138667585797 33730155599578713500172337)
          ·
            refine ⟨25297616699684035125129253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33730155599578713500172337 25297616699684035125129253)
            ·
              refine ⟨4743303131190756585961735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25297616699684035125129253 4743303131190756585961735)
              ·
                refine ⟨7114954696786134878942603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4743303131190756585961735 7114954696786134878942603)
                ·
                  refine ⟨10672432045179202318413905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7114954696786134878942603 10672432045179202318413905)
                  ·
                    refine ⟨8004324033884401738810429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10672432045179202318413905 8004324033884401738810429)
                    ·
                      refine ⟨3001621512706650652053911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8004324033884401738810429 3001621512706650652053911)
                      ·
                        rfl

theorem cell23_5845637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 1, 2, 3].length) (baseStart_5845637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845637 prefixEnd_5845637 := by exact prefixLift 5845637
  have htrace : WordTrace (prefixWord ++ tailWord_5845637) baseStart_5845637 baseEnd_5845637 := by
    simpa [prefixWord, tailWord_5845637, baseEnd_5845637] using wordTrace_append hprefix tailTrace_5845637
  have hstable : (prefixWord ++ tailWord_5845637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845637).length < 2 ^ (prefixWord ++ tailWord_5845637).sum := by decide
  have hdescent : baseEnd_5845637 < baseStart_5845637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845674 : List Nat := [3, 1, 5, 2, 1, 2, 2, 7]
def baseStart_5845674 : Nat := 118140960795 + 5845674 * 2 ^ 59
def prefixEnd_5845674 : Nat := 4983230072969 + 3 ^ 40 * 5845674 * 2
def baseEnd_5845674 : Nat := 111171870795958037307083

theorem tailTrace_5845674 : CollatzResearch.WordTrace tailWord_5845674 prefixEnd_5845674 111171870795958037307083 := by
  unfold tailWord_5845674
  simp only [CollatzResearch.WordTrace]
  refine ⟨53302311656032233620170019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142139497749419289653786717 53302311656032233620170019)
  ·
    refine ⟨79953467484048350430255029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53302311656032233620170019 79953467484048350430255029)
    ·
      refine ⟨7495637576629532852836409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79953467484048350430255029 7495637576629532852836409)
      ·
        refine ⟨5621728182472149639627307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7495637576629532852836409 5621728182472149639627307)
        ·
          refine ⟨8432592273708224459440961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5621728182472149639627307 8432592273708224459440961)
          ·
            refine ⟨6324444205281168344580721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8432592273708224459440961 6324444205281168344580721)
            ·
              refine ⟨4743333153960876258435541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6324444205281168344580721 4743333153960876258435541)
              ·
                refine ⟨111171870795958037307083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4743333153960876258435541 111171870795958037307083)
                ·
                  rfl

theorem cell23_5845674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 7].length) (baseStart_5845674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845674 prefixEnd_5845674 := by exact prefixLift 5845674
  have htrace : WordTrace (prefixWord ++ tailWord_5845674) baseStart_5845674 baseEnd_5845674 := by
    simpa [prefixWord, tailWord_5845674, baseEnd_5845674] using wordTrace_append hprefix tailTrace_5845674
  have hstable : (prefixWord ++ tailWord_5845674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845674).length < 2 ^ (prefixWord ++ tailWord_5845674).sum := by decide
  have hdescent : baseEnd_5845674 < baseStart_5845674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845690 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2]
def baseStart_5845690 : Nat := 118140960795 + 5845690 * 2 ^ 59
def prefixEnd_5845690 : Nat := 4983230072969 + 3 ^ 40 * 5845690 * 2
def baseEnd_5845690 : Nat := 3001648727181338944691167

theorem tailTrace_5845690 : CollatzResearch.WordTrace tailWord_5845690 prefixEnd_5845690 3001648727181338944691167 := by
  unfold tailWord_5845690
  simp only [CollatzResearch.WordTrace]
  refine ⟨53302457548017742303315631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142139886794713979475508349 53302457548017742303315631)
  ·
    refine ⟨79953686322026613454973447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53302457548017742303315631 79953686322026613454973447)
    ·
      refine ⟨119930529483039920182460171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79953686322026613454973447 119930529483039920182460171)
      ·
        refine ⟨179895794224559880273690257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119930529483039920182460171 179895794224559880273690257)
        ·
          refine ⟨134921845668419910205267693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179895794224559880273690257 134921845668419910205267693)
          ·
            refine ⟨50595692125657466326975385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134921845668419910205267693 50595692125657466326975385)
            ·
              refine ⟨37946769094243099745231539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50595692125657466326975385 37946769094243099745231539)
              ·
                refine ⟨56920153641364649617847309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37946769094243099745231539 56920153641364649617847309)
                ·
                  refine ⟨21345057615511743606692741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56920153641364649617847309 21345057615511743606692741)
                  ·
                    refine ⟨4002198302908451926254889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21345057615511743606692741 4002198302908451926254889)
                    ·
                      refine ⟨3001648727181338944691167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4002198302908451926254889 3001648727181338944691167)
                      ·
                        rfl

theorem cell23_5845690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2].length) (baseStart_5845690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845690 prefixEnd_5845690 := by exact prefixLift 5845690
  have htrace : WordTrace (prefixWord ++ tailWord_5845690) baseStart_5845690 baseEnd_5845690 := by
    simpa [prefixWord, tailWord_5845690, baseEnd_5845690] using wordTrace_append hprefix tailTrace_5845690
  have hstable : (prefixWord ++ tailWord_5845690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845690).length < 2 ^ (prefixWord ++ tailWord_5845690).sum := by decide
  have hdescent : baseEnd_5845690 < baseStart_5845690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845693 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 1, 3, 5]
def baseStart_5845693 : Nat := 118140960795 + 5845693 * 2 ^ 59
def prefixEnd_5845693 : Nat := 4983230072969 + 3 ^ 40 * 5845693 * 2
def baseEnd_5845693 : Nat := 3001650267623302432953653

theorem tailTrace_5845693 : CollatzResearch.WordTrace tailWord_5845693 prefixEnd_5845693 3001650267623302432953653 := by
  unfold tailWord_5845693
  simp only [CollatzResearch.WordTrace]
  refine ⟨213209939611060100725621733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142139959740706733817081155 213209939611060100725621733)
  ·
    refine ⟨39976863677073768886054075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213209939611060100725621733 39976863677073768886054075)
    ·
      refine ⟨59965295515610653329081113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39976863677073768886054075 59965295515610653329081113)
      ·
        refine ⟨44973971636707989996810835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59965295515610653329081113 44973971636707989996810835)
        ·
          refine ⟨67460957455061984995216253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44973971636707989996810835 67460957455061984995216253)
          ·
            refine ⟨25297859045648244373206095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67460957455061984995216253 25297859045648244373206095)
            ·
              refine ⟨37946788568472366559809143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25297859045648244373206095 37946788568472366559809143)
              ·
                refine ⟨56920182852708549839713715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37946788568472366559809143 56920182852708549839713715)
                ·
                  refine ⟨85380274279062824759570573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56920182852708549839713715 85380274279062824759570573)
                  ·
                    refine ⟨32017602854648559284838965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85380274279062824759570573 32017602854648559284838965)
                    ·
                      refine ⟨3001650267623302432953653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32017602854648559284838965 3001650267623302432953653)
                      ·
                        rfl

theorem cell23_5845693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_5845693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845693 prefixEnd_5845693 := by exact prefixLift 5845693
  have htrace : WordTrace (prefixWord ++ tailWord_5845693) baseStart_5845693 baseEnd_5845693 := by
    simpa [prefixWord, tailWord_5845693, baseEnd_5845693] using wordTrace_append hprefix tailTrace_5845693
  have hstable : (prefixWord ++ tailWord_5845693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845693).length < 2 ^ (prefixWord ++ tailWord_5845693).sum := by decide
  have hdescent : baseEnd_5845693 < baseStart_5845693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845702 : List Nat := [6, 1, 2, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_5845702 : Nat := 118140960795 + 5845702 * 2 ^ 59
def prefixEnd_5845702 : Nat := 4983230072969 + 3 ^ 40 * 5845702 * 2
def baseEnd_5845702 : Nat := 3001654888949192897741113

theorem tailTrace_5845702 : CollatzResearch.WordTrace tailWord_5845702 prefixEnd_5845702 3001654888949192897741113 := by
  unfold tailWord_5845702
  simp only [CollatzResearch.WordTrace]
  refine ⟨6662820870875859226959355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 142140178578684996841799573 6662820870875859226959355)
  ·
    refine ⟨9994231306313788840439033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6662820870875859226959355 9994231306313788840439033)
    ·
      refine ⟨7495673479735341630329275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9994231306313788840439033 7495673479735341630329275)
      ·
        refine ⟨11243510219603012445493913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7495673479735341630329275 11243510219603012445493913)
        ·
          refine ⟨8432632664702259334120435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11243510219603012445493913 8432632664702259334120435)
          ·
            refine ⟨12648948997053389001180653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8432632664702259334120435 12648948997053389001180653)
            ·
              refine ⟨4743355873895020875442745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12648948997053389001180653 4743355873895020875442745)
              ·
                refine ⟨3557516905421265656582059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4743355873895020875442745 3557516905421265656582059)
                ·
                  refine ⟨5336275358131898484873089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3557516905421265656582059 5336275358131898484873089)
                  ·
                    refine ⟨4002206518598923863654817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5336275358131898484873089 4002206518598923863654817)
                    ·
                      refine ⟨3001654888949192897741113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4002206518598923863654817 3001654888949192897741113)
                      ·
                        rfl

theorem cell23_5845702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_5845702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845702 prefixEnd_5845702 := by exact prefixLift 5845702
  have htrace : WordTrace (prefixWord ++ tailWord_5845702) baseStart_5845702 baseEnd_5845702 := by
    simpa [prefixWord, tailWord_5845702, baseEnd_5845702] using wordTrace_append hprefix tailTrace_5845702
  have hstable : (prefixWord ++ tailWord_5845702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845702).length < 2 ^ (prefixWord ++ tailWord_5845702).sum := by decide
  have hdescent : baseEnd_5845702 < baseStart_5845702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845703 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 4]
def baseStart_5845703 : Nat := 118140960795 + 5845703 * 2 ^ 59
def prefixEnd_5845703 : Nat := 4983230072969 + 3 ^ 40 * 5845703 * 2
def baseEnd_5845703 : Nat := 3001655402429847393828607

theorem tailTrace_5845703 : CollatzResearch.WordTrace tailWord_5845703 prefixEnd_5845703 3001655402429847393828607 := by
  unfold tailWord_5845703
  simp only [CollatzResearch.WordTrace]
  refine ⟨213210304341023872433485763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142140202894015914955657175 213210304341023872433485763)
  ·
    refine ⟨319815456511535808650228645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213210304341023872433485763 319815456511535808650228645)
    ·
      refine ⟨59965398095912964121917871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319815456511535808650228645 59965398095912964121917871)
      ·
        refine ⟨89948097143869446182876807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59965398095912964121917871 89948097143869446182876807)
        ·
          refine ⟨134922145715804169274315211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89948097143869446182876807 134922145715804169274315211)
          ·
            refine ⟨202383218573706253911472817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134922145715804169274315211 202383218573706253911472817)
            ·
              refine ⟨151787413930279690433604613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202383218573706253911472817 151787413930279690433604613)
              ·
                refine ⟨28460140111927441956300865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151787413930279690433604613 28460140111927441956300865)
                ·
                  refine ⟨21345105083945581467225649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28460140111927441956300865 21345105083945581467225649)
                  ·
                    refine ⟨16008828812959186100419237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21345105083945581467225649 16008828812959186100419237)
                    ·
                      refine ⟨3001655402429847393828607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16008828812959186100419237 3001655402429847393828607)
                      ·
                        rfl

theorem cell23_5845703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_5845703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845703 prefixEnd_5845703 := by exact prefixLift 5845703
  have htrace : WordTrace (prefixWord ++ tailWord_5845703) baseStart_5845703 baseEnd_5845703 := by
    simpa [prefixWord, tailWord_5845703, baseEnd_5845703] using wordTrace_append hprefix tailTrace_5845703
  have hstable : (prefixWord ++ tailWord_5845703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845703).length < 2 ^ (prefixWord ++ tailWord_5845703).sum := by decide
  have hdescent : baseEnd_5845703 < baseStart_5845703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845763 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 4]
def baseStart_5845763 : Nat := 118140960795 + 5845763 * 2 ^ 59
def prefixEnd_5845763 : Nat := 4983230072969 + 3 ^ 40 * 5845763 * 2
def baseEnd_5845763 : Nat := 3001686211269117159078331

theorem tailTrace_5845763 : CollatzResearch.WordTrace tailWord_5845763 prefixEnd_5845763 3001686211269117159078331 := by
  unfold tailWord_5845763
  simp only [CollatzResearch.WordTrace]
  refine ⟨213212492720806502680669943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142141661813871001787113295 213212492720806502680669943)
  ·
    refine ⟨319818739081209754021004915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213212492720806502680669943 319818739081209754021004915)
    ·
      refine ⟨479728108621814631031507373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319818739081209754021004915 479728108621814631031507373)
      ·
        refine ⟨179898040733180486636815265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 479728108621814631031507373 179898040733180486636815265)
        ·
          refine ⟨134923530549885364977611449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179898040733180486636815265 134923530549885364977611449)
          ·
            refine ⟨101192647912414023733208587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134923530549885364977611449 101192647912414023733208587)
            ·
              refine ⟨151788971868621035599812881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101192647912414023733208587 151788971868621035599812881)
              ·
                refine ⟨113841728901465776699859661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151788971868621035599812881 113841728901465776699859661)
                ·
                  refine ⟨42690648338049666262447373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113841728901465776699859661 42690648338049666262447373)
                  ·
                    refine ⟨16008993126768624848417765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42690648338049666262447373 16008993126768624848417765)
                    ·
                      refine ⟨3001686211269117159078331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16008993126768624848417765 3001686211269117159078331)
                      ·
                        rfl

theorem cell23_5845763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_5845763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845763 prefixEnd_5845763 := by exact prefixLift 5845763
  have htrace : WordTrace (prefixWord ++ tailWord_5845763) baseStart_5845763 baseEnd_5845763 := by
    simpa [prefixWord, tailWord_5845763, baseEnd_5845763] using wordTrace_append hprefix tailTrace_5845763
  have hstable : (prefixWord ++ tailWord_5845763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845763).length < 2 ^ (prefixWord ++ tailWord_5845763).sum := by decide
  have hdescent : baseEnd_5845763 < baseStart_5845763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845767 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 2, 5, 2]
def baseStart_5845767 : Nat := 118140960795 + 5845767 * 2 ^ 59
def prefixEnd_5845767 : Nat := 4983230072969 + 3 ^ 40 * 5845767 * 2
def baseEnd_5845767 : Nat := 3001688265191735143428313

theorem tailTrace_5845767 : CollatzResearch.WordTrace tailWord_5845767 prefixEnd_5845767 3001688265191735143428313 := by
  unfold tailWord_5845767
  simp only [CollatzResearch.WordTrace]
  refine ⟨213212638612792011363815555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142141759075194674242543703 213212638612792011363815555)
  ·
    refine ⟨319818957919188017045723333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213212638612792011363815555 319818957919188017045723333)
    ·
      refine ⟨59966054609847753196073125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319818957919188017045723333 59966054609847753196073125)
      ·
        refine ⟨11243635239346453724263711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59966054609847753196073125 11243635239346453724263711)
        ·
          refine ⟨16865452859019680586395567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11243635239346453724263711 16865452859019680586395567)
          ·
            refine ⟨25298179288529520879593351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16865452859019680586395567 25298179288529520879593351)
            ·
              refine ⟨37947268932794281319390027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25298179288529520879593351 37947268932794281319390027)
              ·
                refine ⟨56920903399191421979085041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37947268932794281319390027 56920903399191421979085041)
                ·
                  refine ⟨42690677549393566484313781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56920903399191421979085041 42690677549393566484313781)
                  ·
                    refine ⟨4002251020255646857904417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42690677549393566484313781 4002251020255646857904417)
                    ·
                      refine ⟨3001688265191735143428313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4002251020255646857904417 3001688265191735143428313)
                      ·
                        rfl

theorem cell23_5845767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_5845767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845767 prefixEnd_5845767 := by exact prefixLift 5845767
  have htrace : WordTrace (prefixWord ++ tailWord_5845767) baseStart_5845767 baseEnd_5845767 := by
    simpa [prefixWord, tailWord_5845767, baseEnd_5845767] using wordTrace_append hprefix tailTrace_5845767
  have hstable : (prefixWord ++ tailWord_5845767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845767).length < 2 ^ (prefixWord ++ tailWord_5845767).sum := by decide
  have hdescent : baseEnd_5845767 < baseStart_5845767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845843 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 7]
def baseStart_5845843 : Nat := 118140960795 + 5845843 * 2 ^ 59
def prefixEnd_5845843 : Nat := 4983230072969 + 3 ^ 40 * 5845843 * 2
def baseEnd_5845843 : Nat := 3001727289721476846077963

theorem tailTrace_5845843 : CollatzResearch.WordTrace tailWord_5845843 prefixEnd_5845843 3001727289721476846077963 := by
  unfold tailWord_5845843
  simp only [CollatzResearch.WordTrace]
  refine ⟨213215410560516676343582183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142143607040344450895721455 213215410560516676343582183)
  ·
    refine ⟨319823115840775014515373275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213215410560516676343582183 319823115840775014515373275)
    ·
      refine ⟨479734673761162521773059913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319823115840775014515373275 479734673761162521773059913)
      ·
        refine ⟨359801005320871891329794935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479734673761162521773059913 359801005320871891329794935)
        ·
          refine ⟨539701507981307836994692403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359801005320871891329794935 539701507981307836994692403)
          ·
            refine ⟨809552261971961755492038605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539701507981307836994692403 809552261971961755492038605)
            ·
              refine ⟨303582098239485658309514477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 809552261971961755492038605 303582098239485658309514477)
              ·
                refine ⟨113843286839807121866067929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303582098239485658309514477 113843286839807121866067929)
                ·
                  refine ⟨85382465129855341399550947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113843286839807121866067929 85382465129855341399550947)
                  ·
                    refine ⟨128073697694783012099326421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85382465129855341399550947 128073697694783012099326421)
                    ·
                      refine ⟨3001727289721476846077963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128073697694783012099326421 3001727289721476846077963)
                      ·
                        rfl

theorem cell23_5845843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_5845843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845843 prefixEnd_5845843 := by exact prefixLift 5845843
  have htrace : WordTrace (prefixWord ++ tailWord_5845843) baseStart_5845843 baseEnd_5845843 := by
    simpa [prefixWord, tailWord_5845843, baseEnd_5845843] using wordTrace_append hprefix tailTrace_5845843
  have hstable : (prefixWord ++ tailWord_5845843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845843).length < 2 ^ (prefixWord ++ tailWord_5845843).sum := by decide
  have hdescent : baseEnd_5845843 < baseStart_5845843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845858 : List Nat := [3, 3, 2, 1, 3, 2, 1, 3, 1, 4]
def baseStart_5845858 : Nat := 118140960795 + 5845858 * 2 ^ 59
def prefixEnd_5845858 : Nat := 4983230072969 + 3 ^ 40 * 5845858 * 2
def baseEnd_5845858 : Nat := 1000578330643764762463465

theorem tailTrace_5845858 : CollatzResearch.WordTrace tailWord_5845858 prefixEnd_5845858 1000578330643764762463465 := by
  unfold tailWord_5845858
  simp only [CollatzResearch.WordTrace]
  refine ⟨53303989413865583476344557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142143971770308222603585485 53303989413865583476344557)
  ·
    refine ⟨19988996030199593803629209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53303989413865583476344557 19988996030199593803629209)
    ·
      refine ⟨14991747022649695352721907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19988996030199593803629209 14991747022649695352721907)
      ·
        refine ⟨22487620533974543029082861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14991747022649695352721907 22487620533974543029082861)
        ·
          refine ⟨8432857700240453635906073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22487620533974543029082861 8432857700240453635906073)
          ·
            refine ⟨6324643275180340226929555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8432857700240453635906073 6324643275180340226929555)
            ·
              refine ⟨9486964912770510340394333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6324643275180340226929555 9486964912770510340394333)
              ·
                refine ⟨3557611842288941377647875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9486964912770510340394333 3557611842288941377647875)
                ·
                  refine ⟨5336417763433412066471813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3557611842288941377647875 5336417763433412066471813)
                  ·
                    refine ⟨1000578330643764762463465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5336417763433412066471813 1000578330643764762463465)
                    ·
                      rfl

theorem cell23_5845858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_5845858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845858 prefixEnd_5845858 := by exact prefixLift 5845858
  have htrace : WordTrace (prefixWord ++ tailWord_5845858) baseStart_5845858 baseEnd_5845858 := by
    simpa [prefixWord, tailWord_5845858, baseEnd_5845858] using wordTrace_append hprefix tailTrace_5845858
  have hstable : (prefixWord ++ tailWord_5845858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845858).length < 2 ^ (prefixWord ++ tailWord_5845858).sum := by decide
  have hdescent : baseEnd_5845858 < baseStart_5845858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845900 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 1, 1, 6]
def baseStart_5845900 : Nat := 118140960795 + 5845900 * 2 ^ 59
def prefixEnd_5845900 : Nat := 4983230072969 + 3 ^ 40 * 5845900 * 2
def baseEnd_5845900 : Nat := 3001756558118783123065201

theorem tailTrace_5845900 : CollatzResearch.WordTrace tailWord_5845900 prefixEnd_5845900 3001756558118783123065201 := by
  unfold tailWord_5845900
  simp only [CollatzResearch.WordTrace]
  refine ⟨106608744760655087539203577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142144993014206783385604769 106608744760655087539203577)
  ·
    refine ⟨79956558570491315654402683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106608744760655087539203577 79956558570491315654402683)
    ·
      refine ⟨119934837855736973481604025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79956558570491315654402683 119934837855736973481604025)
      ·
        refine ⟨89951128391802730111203019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119934837855736973481604025 89951128391802730111203019)
        ·
          refine ⟨134926692587704095166804529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89951128391802730111203019 134926692587704095166804529)
          ·
            refine ⟨101195019440778071375103397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134926692587704095166804529 101195019440778071375103397)
            ·
              refine ⟨18974066145145888382831887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101195019440778071375103397 18974066145145888382831887)
              ·
                refine ⟨28461099217718832574247831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18974066145145888382831887 28461099217718832574247831)
                ·
                  refine ⟨42691648826578248861371747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28461099217718832574247831 42691648826578248861371747)
                  ·
                    refine ⟨64037473239867373292057621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42691648826578248861371747 64037473239867373292057621)
                    ·
                      refine ⟨3001756558118783123065201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64037473239867373292057621 3001756558118783123065201)
                      ·
                        rfl

theorem cell23_5845900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_5845900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845900 prefixEnd_5845900 := by exact prefixLift 5845900
  have htrace : WordTrace (prefixWord ++ tailWord_5845900) baseStart_5845900 baseEnd_5845900 := by
    simpa [prefixWord, tailWord_5845900, baseEnd_5845900] using wordTrace_append hprefix tailTrace_5845900
  have hstable : (prefixWord ++ tailWord_5845900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845900).length < 2 ^ (prefixWord ++ tailWord_5845900).sum := by decide
  have hdescent : baseEnd_5845900 < baseStart_5845900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845907 : List Nat := [1, 1, 1, 2, 1, 2, 1, 8, 1, 2, 3]
def baseStart_5845907 : Nat := 118140960795 + 5845907 * 2 ^ 59
def prefixEnd_5845907 : Nat := 4983230072969 + 3 ^ 40 * 5845907 * 2
def baseEnd_5845907 : Nat := 3001760152483364595677669

theorem tailTrace_5845907 : CollatzResearch.WordTrace tailWord_5845907 prefixEnd_5845907 3001760152483364595677669 := by
  unfold tailWord_5845907
  simp only [CollatzResearch.WordTrace]
  refine ⟨213217744832284815273911975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142145163221523210182607983 213217744832284815273911975)
  ·
    refine ⟨319826617248427222910867963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213217744832284815273911975 319826617248427222910867963)
    ·
      refine ⟨479739925872640834366301945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319826617248427222910867963 479739925872640834366301945)
      ·
        refine ⟨359804944404480625774726459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479739925872640834366301945 359804944404480625774726459)
        ·
          refine ⟨539707416606720938662089689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359804944404480625774726459 539707416606720938662089689)
          ·
            refine ⟨404780562455040703996567267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 539707416606720938662089689 404780562455040703996567267)
            ·
              refine ⟨607170843682561055994850901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404780562455040703996567267 607170843682561055994850901)
              ·
                refine ⟨7115283324405012374939659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 607170843682561055994850901 7115283324405012374939659)
                ·
                  refine ⟨10672924986607518562409489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7115283324405012374939659 10672924986607518562409489)
                  ·
                    refine ⟨8004693739955638921807117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10672924986607518562409489 8004693739955638921807117)
                    ·
                      refine ⟨3001760152483364595677669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8004693739955638921807117 3001760152483364595677669)
                      ·
                        rfl

theorem cell23_5845907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 2, 3].length) (baseStart_5845907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845907 prefixEnd_5845907 := by exact prefixLift 5845907
  have htrace : WordTrace (prefixWord ++ tailWord_5845907) baseStart_5845907 baseEnd_5845907 := by
    simpa [prefixWord, tailWord_5845907, baseEnd_5845907] using wordTrace_append hprefix tailTrace_5845907
  have hstable : (prefixWord ++ tailWord_5845907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845907).length < 2 ^ (prefixWord ++ tailWord_5845907).sum := by decide
  have hdescent : baseEnd_5845907 < baseStart_5845907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845917 : List Nat := [1, 4, 2, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_5845917 : Nat := 118140960795 + 5845917 * 2 ^ 59
def prefixEnd_5845917 : Nat := 4983230072969 + 3 ^ 40 * 5845917 * 2
def baseEnd_5845917 : Nat := 3001765287289909556552623

theorem tailTrace_5845917 : CollatzResearch.WordTrace tailWord_5845917 prefixEnd_5845917 3001765287289909556552623 := by
  unfold tailWord_5845917
  simp only [CollatzResearch.WordTrace]
  refine ⟨213218109562248586981776005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142145406374832391321184003 213218109562248586981776005)
  ·
    refine ⟨39978395542921610059083001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213218109562248586981776005 39978395542921610059083001)
    ·
      refine ⟨29983796657191207544312251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39978395542921610059083001 29983796657191207544312251)
      ·
        refine ⟨44975694985786811316468377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29983796657191207544312251 44975694985786811316468377)
        ·
          refine ⟨33731771239340108487351283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44975694985786811316468377 33731771239340108487351283)
          ·
            refine ⟨50597656859010162731026925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33731771239340108487351283 50597656859010162731026925)
            ·
              refine ⟨18974121322128811024135097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50597656859010162731026925 18974121322128811024135097)
              ·
                refine ⟨14230590991596608268101323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18974121322128811024135097 14230590991596608268101323)
                ·
                  refine ⟨21345886487394912402151985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14230590991596608268101323 21345886487394912402151985)
                  ·
                    refine ⟨16009414865546184301613989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21345886487394912402151985 16009414865546184301613989)
                    ·
                      refine ⟨3001765287289909556552623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16009414865546184301613989 3001765287289909556552623)
                      ·
                        rfl

theorem cell23_5845917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_5845917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845917 prefixEnd_5845917 := by exact prefixLift 5845917
  have htrace : WordTrace (prefixWord ++ tailWord_5845917) baseStart_5845917 baseEnd_5845917 := by
    simpa [prefixWord, tailWord_5845917, baseEnd_5845917] using wordTrace_append hprefix tailTrace_5845917
  have hstable : (prefixWord ++ tailWord_5845917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845917).length < 2 ^ (prefixWord ++ tailWord_5845917).sum := by decide
  have hdescent : baseEnd_5845917 < baseStart_5845917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845921 : List Nat := [1, 2, 3, 4, 1, 2, 3, 1, 1, 1, 4]
def baseStart_5845921 : Nat := 118140960795 + 5845921 * 2 ^ 59
def prefixEnd_5845921 : Nat := 4983230072969 + 3 ^ 40 * 5845921 * 2
def baseEnd_5845921 : Nat := 3001767341212527540902605

theorem tailTrace_5845921 : CollatzResearch.WordTrace tailWord_5845921 prefixEnd_5845921 3001767341212527540902605 := by
  unfold tailWord_5845921
  simp only [CollatzResearch.WordTrace]
  refine ⟨213218255454234095664921617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142145503636156063776614411 213218255454234095664921617)
  ·
    refine ⟨159913691590675571748691213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213218255454234095664921617 159913691590675571748691213)
    ·
      refine ⟨59967634346503339405759205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159913691590675571748691213 59967634346503339405759205)
      ·
        refine ⟨11243931439969376138579851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59967634346503339405759205 11243931439969376138579851)
        ·
          refine ⟨16865897159954064207869777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11243931439969376138579851 16865897159954064207869777)
          ·
            refine ⟨12649422869965548155902333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16865897159954064207869777 12649422869965548155902333)
            ·
              refine ⟨4743533576237080558463375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12649422869965548155902333 4743533576237080558463375)
              ·
                refine ⟨7115300364355620837695063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4743533576237080558463375 7115300364355620837695063)
                ·
                  refine ⟨10672950546533431256542595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7115300364355620837695063 10672950546533431256542595)
                  ·
                    refine ⟨16009425819800146884813893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10672950546533431256542595 16009425819800146884813893)
                    ·
                      refine ⟨3001767341212527540902605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16009425819800146884813893 3001767341212527540902605)
                      ·
                        rfl

theorem cell23_5845921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_5845921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845921 prefixEnd_5845921 := by exact prefixLift 5845921
  have htrace : WordTrace (prefixWord ++ tailWord_5845921) baseStart_5845921 baseEnd_5845921 := by
    simpa [prefixWord, tailWord_5845921, baseEnd_5845921] using wordTrace_append hprefix tailTrace_5845921
  have hstable : (prefixWord ++ tailWord_5845921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845921).length < 2 ^ (prefixWord ++ tailWord_5845921).sum := by decide
  have hdescent : baseEnd_5845921 < baseStart_5845921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845927 : List Nat := [1, 1, 6, 1, 4, 10]
def baseStart_5845927 : Nat := 118140960795 + 5845927 * 2 ^ 59
def prefixEnd_5845927 : Nat := 4983230072969 + 3 ^ 40 * 5845927 * 2
def baseEnd_5845927 : Nat := 12352964699985409536739

theorem tailTrace_5845927 : CollatzResearch.WordTrace tailWord_5845927 prefixEnd_5845927 12352964699985409536739 := by
  unfold tailWord_5845927
  simp only [CollatzResearch.WordTrace]
  refine ⟨213218474292212358689640035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142145649528141572459760023 213218474292212358689640035)
  ·
    refine ⟨319827711438318538034460053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213218474292212358689640035 319827711438318538034460053)
    ·
      refine ⟨14991923973671181470365315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 319827711438318538034460053 14991923973671181470365315)
      ·
        refine ⟨22487885960506772205547973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14991923973671181470365315 22487885960506772205547973)
        ·
          refine ⟨4216478617595019788540245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22487885960506772205547973 4216478617595019788540245)
          ·
            refine ⟨12352964699985409536739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4216478617595019788540245 12352964699985409536739)
            ·
              rfl

theorem cell23_5845927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 10].length) (baseStart_5845927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845927 prefixEnd_5845927 := by exact prefixLift 5845927
  have htrace : WordTrace (prefixWord ++ tailWord_5845927) baseStart_5845927 baseEnd_5845927 := by
    simpa [prefixWord, tailWord_5845927, baseEnd_5845927] using wordTrace_append hprefix tailTrace_5845927
  have hstable : (prefixWord ++ tailWord_5845927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845927).length < 2 ^ (prefixWord ++ tailWord_5845927).sum := by decide
  have hdescent : baseEnd_5845927 < baseStart_5845927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5845964 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 3, 3, 2]
def baseStart_5845964 : Nat := 118140960795 + 5845964 * 2 ^ 59
def prefixEnd_5845964 : Nat := 4983230072969 + 3 ^ 40 * 5845964 * 2
def baseEnd_5845964 : Nat := 3001789420880670872664907

theorem tailTrace_5845964 : CollatzResearch.WordTrace tailWord_5845964 prefixEnd_5845964 3001789420880670872664907 := by
  unfold tailWord_5845964
  simp only [CollatzResearch.WordTrace]
  refine ⟨106609911896539157004368473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142146549195385542672491297 106609911896539157004368473)
  ·
    refine ⟨79957433922404367753276355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106609911896539157004368473 79957433922404367753276355)
    ·
      refine ⟨119936150883606551629914533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79957433922404367753276355 119936150883606551629914533)
      ·
        refine ⟨22488028290676228430608975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119936150883606551629914533 22488028290676228430608975)
        ·
          refine ⟨33732042436014342645913463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22488028290676228430608975 33732042436014342645913463)
          ·
            refine ⟨50598063654021513968870195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33732042436014342645913463 50598063654021513968870195)
            ·
              refine ⟨75897095481032270953305293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50598063654021513968870195 75897095481032270953305293)
              ·
                refine ⟨28461410805387101607489485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75897095481032270953305293 28461410805387101607489485)
                ·
                  refine ⟨10673029052020163102808557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28461410805387101607489485 10673029052020163102808557)
                  ·
                    refine ⟨4002385894507561163553209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10673029052020163102808557 4002385894507561163553209)
                    ·
                      refine ⟨3001789420880670872664907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4002385894507561163553209 3001789420880670872664907)
                      ·
                        rfl

theorem cell23_5845964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_5845964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5845964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5845964 prefixEnd_5845964 := by exact prefixLift 5845964
  have htrace : WordTrace (prefixWord ++ tailWord_5845964) baseStart_5845964 baseEnd_5845964 := by
    simpa [prefixWord, tailWord_5845964, baseEnd_5845964] using wordTrace_append hprefix tailTrace_5845964
  have hstable : (prefixWord ++ tailWord_5845964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5845964).length < 2 ^ (prefixWord ++ tailWord_5845964).sum := by decide
  have hdescent : baseEnd_5845964 < baseStart_5845964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5845964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846005 : List Nat := [1, 3, 5, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_5846005 : Nat := 118140960795 + 5846005 * 2 ^ 59
def prefixEnd_5846005 : Nat := 4983230072969 + 3 ^ 40 * 5846005 * 2
def baseEnd_5846005 : Nat := 3001810473587505212252219

theorem tailTrace_5846005 : CollatzResearch.WordTrace tailWord_5846005 prefixEnd_5846005 3001810473587505212252219 := by
  unfold tailWord_5846005
  simp only [CollatzResearch.WordTrace]
  refine ⟨213221319185929778010979469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142147546123953185340652979 213221319185929778010979469)
  ·
    refine ⟨79957994694723666754117301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213221319185929778010979469 79957994694723666754117301)
    ·
      refine ⟨7496062002630343758198497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79957994694723666754117301 7496062002630343758198497)
      ·
        refine ⟨5622046501972757818648873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7496062002630343758198497 5622046501972757818648873)
        ·
          refine ⟨4216534876479568363986655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5622046501972757818648873 4216534876479568363986655)
          ·
            refine ⟨6324802314719352545979983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4216534876479568363986655 6324802314719352545979983)
            ·
              refine ⟨9487203472079028818969975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6324802314719352545979983 9487203472079028818969975)
              ·
                refine ⟨14230805208118543228454963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9487203472079028818969975 14230805208118543228454963)
                ·
                  refine ⟨21346207812177814842682445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14230805208118543228454963 21346207812177814842682445)
                  ·
                    refine ⟨8004827929566680566005917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21346207812177814842682445 8004827929566680566005917)
                    ·
                      refine ⟨3001810473587505212252219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8004827929566680566005917 3001810473587505212252219)
                      ·
                        rfl

theorem cell23_5846005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_5846005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846005 prefixEnd_5846005 := by exact prefixLift 5846005
  have htrace : WordTrace (prefixWord ++ tailWord_5846005) baseStart_5846005 baseEnd_5846005 := by
    simpa [prefixWord, tailWord_5846005, baseEnd_5846005] using wordTrace_append hprefix tailTrace_5846005
  have hstable : (prefixWord ++ tailWord_5846005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846005).length < 2 ^ (prefixWord ++ tailWord_5846005).sum := by decide
  have hdescent : baseEnd_5846005 < baseStart_5846005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846010 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9]
def baseStart_5846010 : Nat := 118140960795 + 5846010 * 2 ^ 59
def prefixEnd_5846010 : Nat := 4983230072969 + 3 ^ 40 * 5846010 * 2
def baseEnd_5846010 : Nat := 3001813040990777692689695

theorem tailTrace_5846010 : CollatzResearch.WordTrace tailWord_5846010 prefixEnd_5846010 3001813040990777692689695 := by
  unfold tailWord_5846010
  simp only [CollatzResearch.WordTrace]
  refine ⟨53305375387727915966227871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142147667700607775909940989 53305375387727915966227871)
  ·
    refine ⟨79958063081591873949341807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53305375387727915966227871 79958063081591873949341807)
    ·
      refine ⟨119937094622387810924012711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79958063081591873949341807 119937094622387810924012711)
      ·
        refine ⟨179905641933581716386019067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119937094622387810924012711 179905641933581716386019067)
        ·
          refine ⟨269858462900372574579028601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179905641933581716386019067 269858462900372574579028601)
          ·
            refine ⟨202393847175279430934271451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269858462900372574579028601 202393847175279430934271451)
            ·
              refine ⟨303590770762919146401407177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202393847175279430934271451 303590770762919146401407177)
              ·
                refine ⟨227693078072189359801055383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303590770762919146401407177 227693078072189359801055383)
                ·
                  refine ⟨341539617108284039701583075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227693078072189359801055383 341539617108284039701583075)
                  ·
                    refine ⟨512309425662426059552374613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 341539617108284039701583075 512309425662426059552374613)
                    ·
                      refine ⟨3001813040990777692689695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 512309425662426059552374613 3001813040990777692689695)
                      ·
                        rfl

theorem cell23_5846010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_5846010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846010 prefixEnd_5846010 := by exact prefixLift 5846010
  have htrace : WordTrace (prefixWord ++ tailWord_5846010) baseStart_5846010 baseEnd_5846010 := by
    simpa [prefixWord, tailWord_5846010, baseEnd_5846010] using wordTrace_append hprefix tailTrace_5846010
  have hstable : (prefixWord ++ tailWord_5846010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846010).length < 2 ^ (prefixWord ++ tailWord_5846010).sum := by decide
  have hdescent : baseEnd_5846010 < baseStart_5846010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846017 : List Nat := [1, 2, 4, 1, 2, 2, 2, 2, 7]
def baseStart_5846017 : Nat := 118140960795 + 5846017 * 2 ^ 59
def prefixEnd_5846017 : Nat := 4983230072969 + 3 ^ 40 * 5846017 * 2
def baseEnd_5846017 : Nat := 333535181706151018366907

theorem tailTrace_5846017 : CollatzResearch.WordTrace tailWord_5846017 prefixEnd_5846017 333535181706151018366907 := by
  unfold tailWord_5846017
  simp only [CollatzResearch.WordTrace]
  refine ⟨213221756861886304060416305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142147837907924202706944203 213221756861886304060416305)
  ·
    refine ⟨159916317646414728045312229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213221756861886304060416305 159916317646414728045312229)
    ·
      refine ⟨29984309558702761508496043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159916317646414728045312229 29984309558702761508496043)
      ·
        refine ⟨44976464338054142262744065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29984309558702761508496043 44976464338054142262744065)
        ·
          refine ⟨33732348253540606697058049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44976464338054142262744065 33732348253540606697058049)
          ·
            refine ⟨25299261190155455022793537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33732348253540606697058049 25299261190155455022793537)
            ·
              refine ⟨18974445892616591267095153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25299261190155455022793537 18974445892616591267095153)
              ·
                refine ⟨14230834419462443450321365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18974445892616591267095153 14230834419462443450321365)
                ·
                  refine ⟨333535181706151018366907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14230834419462443450321365 333535181706151018366907)
                  ·
                    rfl

theorem cell23_5846017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 7].length) (baseStart_5846017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846017 prefixEnd_5846017 := by exact prefixLift 5846017
  have htrace : WordTrace (prefixWord ++ tailWord_5846017) baseStart_5846017 baseEnd_5846017 := by
    simpa [prefixWord, tailWord_5846017, baseEnd_5846017] using wordTrace_append hprefix tailTrace_5846017
  have hstable : (prefixWord ++ tailWord_5846017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846017).length < 2 ^ (prefixWord ++ tailWord_5846017).sum := by decide
  have hdescent : baseEnd_5846017 < baseStart_5846017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846047 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 4, 5]
def baseStart_5846047 : Nat := 118140960795 + 5846047 * 2 ^ 59
def prefixEnd_5846047 : Nat := 4983230072969 + 3 ^ 40 * 5846047 * 2
def baseEnd_5846047 : Nat := 1000610679924998015975675

theorem tailTrace_5846047 : CollatzResearch.WordTrace tailWord_5846047 prefixEnd_5846047 1000610679924998015975675 := by
  unfold tailWord_5846047
  simp only [CollatzResearch.WordTrace]
  refine ⟨213222851051777619184008395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142148567367851746122672263 213222851051777619184008395)
  ·
    refine ⟨319834276577666428776012593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213222851051777619184008395 319834276577666428776012593)
    ·
      refine ⟨239875707433249821582009445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319834276577666428776012593 239875707433249821582009445)
      ·
        refine ⟨44976695143734341546626771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239875707433249821582009445 44976695143734341546626771)
        ·
          refine ⟨67465042715601512319940157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44976695143734341546626771 67465042715601512319940157)
          ·
            refine ⟨25299391018350567119977559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67465042715601512319940157 25299391018350567119977559)
            ·
              refine ⟨37949086527525850679966339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25299391018350567119977559 37949086527525850679966339)
              ·
                refine ⟨56923629791288776019949509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37949086527525850679966339 56923629791288776019949509)
                ·
                  refine ⟨10673180585866645503740533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56923629791288776019949509 10673180585866645503740533)
                  ·
                    refine ⟨1000610679924998015975675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10673180585866645503740533 1000610679924998015975675)
                    ·
                      rfl

theorem cell23_5846047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 5].length) (baseStart_5846047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846047 prefixEnd_5846047 := by exact prefixLift 5846047
  have htrace : WordTrace (prefixWord ++ tailWord_5846047) baseStart_5846047 baseEnd_5846047 := by
    simpa [prefixWord, tailWord_5846047, baseEnd_5846047] using wordTrace_append hprefix tailTrace_5846047
  have hstable : (prefixWord ++ tailWord_5846047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846047).length < 2 ^ (prefixWord ++ tailWord_5846047).sum := by decide
  have hdescent : baseEnd_5846047 < baseStart_5846047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846051 : List Nat := [1, 1, 1, 4, 3, 3, 3, 2, 5]
def baseStart_5846051 : Nat := 118140960795 + 5846051 * 2 ^ 59
def prefixEnd_5846051 : Nat := 4983230072969 + 3 ^ 40 * 5846051 * 2
def baseEnd_5846051 : Nat := 333537121521956892475223

theorem tailTrace_5846051 : CollatzResearch.WordTrace tailWord_5846051 prefixEnd_5846051 333537121521956892475223 := by
  unfold tailWord_5846051
  simp only [CollatzResearch.WordTrace]
  refine ⟨213222996943763127867154007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142148664629175418578102671 213222996943763127867154007)
  ·
    refine ⟨319834495415644691800731011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213222996943763127867154007 319834495415644691800731011)
    ·
      refine ⟨479751743123467037701096517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319834495415644691800731011 479751743123467037701096517)
      ·
        refine ⟨89953451835650069568955597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 479751743123467037701096517 89953451835650069568955597)
        ·
          refine ⟨33732544438368776088358349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89953451835650069568955597 33732544438368776088358349)
          ·
            refine ⟨12649704164388291033134381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33732544438368776088358349 12649704164388291033134381)
            ·
              refine ⟨4743639061645609137425393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12649704164388291033134381 4743639061645609137425393)
              ·
                refine ⟨3557729296234206853069045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4743639061645609137425393 3557729296234206853069045)
                ·
                  refine ⟨333537121521956892475223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3557729296234206853069045 333537121521956892475223)
                  ·
                    rfl

theorem cell23_5846051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 5].length) (baseStart_5846051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846051 prefixEnd_5846051 := by exact prefixLift 5846051
  have htrace : WordTrace (prefixWord ++ tailWord_5846051) baseStart_5846051 baseEnd_5846051 := by
    simpa [prefixWord, tailWord_5846051, baseEnd_5846051] using wordTrace_append hprefix tailTrace_5846051
  have hstable : (prefixWord ++ tailWord_5846051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846051).length < 2 ^ (prefixWord ++ tailWord_5846051).sum := by decide
  have hdescent : baseEnd_5846051 < baseStart_5846051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846067 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 4]
def baseStart_5846067 : Nat := 118140960795 + 5846067 * 2 ^ 59
def prefixEnd_5846067 : Nat := 4983230072969 + 3 ^ 40 * 5846067 * 2
def baseEnd_5846067 : Nat := 3001842309388083969676933

theorem tailTrace_5846067 : CollatzResearch.WordTrace tailWord_5846067 prefixEnd_5846067 3001842309388083969676933 := by
  unfold tailWord_5846067
  simp only [CollatzResearch.WordTrace]
  refine ⟨213223580511705162599736455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142149053674470108399824303 213223580511705162599736455)
  ·
    refine ⟨319835370767557743899604683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213223580511705162599736455 319835370767557743899604683)
    ·
      refine ⟨479753056151336615849407025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319835370767557743899604683 479753056151336615849407025)
      ·
        refine ⟨359814792113502461887055269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479753056151336615849407025 359814792113502461887055269)
        ·
          refine ⟨67465273521281711603822863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 359814792113502461887055269 67465273521281711603822863)
          ·
            refine ⟨101197910281922567405734295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67465273521281711603822863 101197910281922567405734295)
            ·
              refine ⟨151796865422883851108601443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101197910281922567405734295 151796865422883851108601443)
              ·
                refine ⟨227695298134325776662902165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151796865422883851108601443 227695298134325776662902165)
                ·
                  refine ⟨10673217100046520781073539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 227695298134325776662902165 10673217100046520781073539)
                  ·
                    refine ⟨16009825650069781171610309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10673217100046520781073539 16009825650069781171610309)
                    ·
                      refine ⟨3001842309388083969676933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16009825650069781171610309 3001842309388083969676933)
                      ·
                        rfl

theorem cell23_5846067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 4].length) (baseStart_5846067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846067 prefixEnd_5846067 := by exact prefixLift 5846067
  have htrace : WordTrace (prefixWord ++ tailWord_5846067) baseStart_5846067 baseEnd_5846067 := by
    simpa [prefixWord, tailWord_5846067, baseEnd_5846067] using wordTrace_append hprefix tailTrace_5846067
  have hstable : (prefixWord ++ tailWord_5846067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846067).length < 2 ^ (prefixWord ++ tailWord_5846067).sum := by decide
  have hdescent : baseEnd_5846067 < baseStart_5846067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846081 : List Nat := [1, 2, 5, 1, 3, 1, 2, 1, 2, 5]
def baseStart_5846081 : Nat := 118140960795 + 5846081 * 2 ^ 59
def prefixEnd_5846081 : Nat := 4983230072969 + 3 ^ 40 * 5846081 * 2
def baseEnd_5846081 : Nat := 1000616499372415638300623

theorem tailTrace_5846081 : CollatzResearch.WordTrace tailWord_5846081 prefixEnd_5846081 1000616499372415638300623 := by
  unfold tailWord_5846081
  simp only [CollatzResearch.WordTrace]
  refine ⟨213224091133654442990746097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142149394089102961993830731 213224091133654442990746097)
  ·
    refine ⟨159918068350240832243059573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213224091133654442990746097 159918068350240832243059573)
    ·
      refine ⟨14992318907835078022786835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159918068350240832243059573 14992318907835078022786835)
      ·
        refine ⟨22488478361752617034180253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14992318907835078022786835 22488478361752617034180253)
        ·
          refine ⟨8433179385657231387817595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22488478361752617034180253 8433179385657231387817595)
          ·
            refine ⟨12649769078485847081726393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8433179385657231387817595 12649769078485847081726393)
            ·
              refine ⟨9487326808864385311294795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12649769078485847081726393 9487326808864385311294795)
              ·
                refine ⟨14230990213296577966942193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9487326808864385311294795 14230990213296577966942193)
                ·
                  refine ⟨10673242659972433475206645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14230990213296577966942193 10673242659972433475206645)
                  ·
                    refine ⟨1000616499372415638300623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10673242659972433475206645 1000616499372415638300623)
                    ·
                      rfl

theorem cell23_5846081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_5846081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846081 prefixEnd_5846081 := by exact prefixLift 5846081
  have htrace : WordTrace (prefixWord ++ tailWord_5846081) baseStart_5846081 baseEnd_5846081 := by
    simpa [prefixWord, tailWord_5846081, baseEnd_5846081] using wordTrace_append hprefix tailTrace_5846081
  have hstable : (prefixWord ++ tailWord_5846081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846081).length < 2 ^ (prefixWord ++ tailWord_5846081).sum := by decide
  have hdescent : baseEnd_5846081 < baseStart_5846081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846102 : List Nat := [5, 2, 2, 1, 2, 2, 2, 2, 5]
def baseStart_5846102 : Nat := 118140960795 + 5846102 * 2 ^ 59
def prefixEnd_5846102 : Nat := 4983230072969 + 3 ^ 40 * 5846102 * 2
def baseEnd_5846102 : Nat := 333540031245665703637697

theorem tailTrace_5846102 : CollatzResearch.WordTrace tailWord_5846102 prefixEnd_5846102 333540031245665703637697 := by
  unfold tailWord_5846102
  simp only [CollatzResearch.WordTrace]
  refine ⟨13326553566661147723578785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142149904711052242384840373 13326553566661147723578785)
  ·
    refine ⟨9994915174995860792684089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13326553566661147723578785 9994915174995860792684089)
    ·
      refine ⟨7496186381246895594513067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9994915174995860792684089 7496186381246895594513067)
      ·
        refine ⟨11244279571870343391769601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7496186381246895594513067 11244279571870343391769601)
        ·
          refine ⟨8433209678902757543827201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11244279571870343391769601 8433209678902757543827201)
          ·
            refine ⟨6324907259177068157870401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8433209678902757543827201 6324907259177068157870401)
            ·
              refine ⟨4743680444382801118402801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6324907259177068157870401 4743680444382801118402801)
              ·
                refine ⟨3557760333287100838802101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4743680444382801118402801 3557760333287100838802101)
                ·
                  refine ⟨333540031245665703637697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3557760333287100838802101 333540031245665703637697)
                  ·
                    rfl

theorem cell23_5846102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_5846102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846102 prefixEnd_5846102 := by exact prefixLift 5846102
  have htrace : WordTrace (prefixWord ++ tailWord_5846102) baseStart_5846102 baseEnd_5846102 := by
    simpa [prefixWord, tailWord_5846102, baseEnd_5846102] using wordTrace_append hprefix tailTrace_5846102
  have hstable : (prefixWord ++ tailWord_5846102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846102).length < 2 ^ (prefixWord ++ tailWord_5846102).sum := by decide
  have hdescent : baseEnd_5846102 < baseStart_5846102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846104 : List Nat := [2, 1, 2, 2, 1, 3, 1, 4, 2, 2, 3]
def baseStart_5846104 : Nat := 118140960795 + 5846104 * 2 ^ 59
def prefixEnd_5846104 : Nat := 4983230072969 + 3 ^ 40 * 5846104 * 2
def baseEnd_5846104 : Nat := 3001861308172300324914263

theorem tailTrace_5846104 : CollatzResearch.WordTrace tailWord_5846104 prefixEnd_5846104 3001861308172300324914263 := by
  unfold tailWord_5846104
  simp only [CollatzResearch.WordTrace]
  refine ⟨106612465006285558959416683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142149953341714078612555577 106612465006285558959416683)
  ·
    refine ⟨159918697509428338439125025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106612465006285558959416683 159918697509428338439125025)
    ·
      refine ⟨119939023132071253829343769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159918697509428338439125025 119939023132071253829343769)
      ·
        refine ⟨89954267349053440372007827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119939023132071253829343769 89954267349053440372007827)
        ·
          refine ⟨134931401023580160558011741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89954267349053440372007827 134931401023580160558011741)
          ·
            refine ⟨50599275383842560209254403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134931401023580160558011741 50599275383842560209254403)
            ·
              refine ⟨75898913075763840313881605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50599275383842560209254403 75898913075763840313881605)
              ·
                refine ⟨14231046201705720058852801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75898913075763840313881605 14231046201705720058852801)
                ·
                  refine ⟨10673284651279290044139601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14231046201705720058852801 10673284651279290044139601)
                  ·
                    refine ⟨8004963488459467533104701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10673284651279290044139601 8004963488459467533104701)
                    ·
                      refine ⟨3001861308172300324914263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8004963488459467533104701 3001861308172300324914263)
                      ·
                        rfl

theorem cell23_5846104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_5846104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846104 prefixEnd_5846104 := by exact prefixLift 5846104
  have htrace : WordTrace (prefixWord ++ tailWord_5846104) baseStart_5846104 baseEnd_5846104 := by
    simpa [prefixWord, tailWord_5846104, baseEnd_5846104] using wordTrace_append hprefix tailTrace_5846104
  have hstable : (prefixWord ++ tailWord_5846104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846104).length < 2 ^ (prefixWord ++ tailWord_5846104).sum := by decide
  have hdescent : baseEnd_5846104 < baseStart_5846104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846111 : List Nat := [1, 1, 2, 3, 1, 1, 5, 4, 1, 4]
def baseStart_5846111 : Nat := 118140960795 + 5846111 * 2 ^ 59
def prefixEnd_5846111 : Nat := 4983230072969 + 3 ^ 40 * 5846111 * 2
def baseEnd_5846111 : Nat := 1000621634178960599175577

theorem tailTrace_5846111 : CollatzResearch.WordTrace tailWord_5846111 prefixEnd_5846111 1000621634178960599175577 := by
  unfold tailWord_5846111
  simp only [CollatzResearch.WordTrace]
  refine ⟨213225185323545758114338187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142150123549030505409558791 213225185323545758114338187)
  ·
    refine ⟨319837777985318637171507281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213225185323545758114338187 319837777985318637171507281)
    ·
      refine ⟨239878333488988977878630461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319837777985318637171507281 239878333488988977878630461)
      ·
        refine ⟨89954375058370866704486423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239878333488988977878630461 89954375058370866704486423)
        ·
          refine ⟨134931562587556300056729635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89954375058370866704486423 134931562587556300056729635)
          ·
            refine ⟨202397343881334450085094453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134931562587556300056729635 202397343881334450085094453)
            ·
              refine ⟨18974750988875104695477605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 202397343881334450085094453 18974750988875104695477605)
              ·
                refine ⟨3557765810414082130402051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18974750988875104695477605 3557765810414082130402051)
                ·
                  refine ⟨5336648715621123195603077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3557765810414082130402051 5336648715621123195603077)
                  ·
                    refine ⟨1000621634178960599175577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5336648715621123195603077 1000621634178960599175577)
                    ·
                      rfl

theorem cell23_5846111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 1, 4].length) (baseStart_5846111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846111 prefixEnd_5846111 := by exact prefixLift 5846111
  have htrace : WordTrace (prefixWord ++ tailWord_5846111) baseStart_5846111 baseEnd_5846111 := by
    simpa [prefixWord, tailWord_5846111, baseEnd_5846111] using wordTrace_append hprefix tailTrace_5846111
  have hstable : (prefixWord ++ tailWord_5846111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846111).length < 2 ^ (prefixWord ++ tailWord_5846111).sum := by decide
  have hdescent : baseEnd_5846111 < baseStart_5846111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846168 : List Nat := [2, 1, 2, 4, 2, 2, 2, 1, 3, 1, 3]
def baseStart_5846168 : Nat := 118140960795 + 5846168 * 2 ^ 59
def prefixEnd_5846168 : Nat := 4983230072969 + 3 ^ 40 * 5846168 * 2
def baseEnd_5846168 : Nat := 3001894170934188074513969

theorem tailTrace_5846168 : CollatzResearch.WordTrace tailWord_5846168 prefixEnd_5846168 3001894170934188074513969 := by
  unfold tailWord_5846168
  simp only [CollatzResearch.WordTrace]
  refine ⟨106613632142169628424581579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142151509522892837899442105 106613632142169628424581579)
  ·
    refine ⟨159920448213254442636872369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106613632142169628424581579 159920448213254442636872369)
    ·
      refine ⟨119940336159940831977654277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159920448213254442636872369 119940336159940831977654277)
      ·
        refine ⟨22488813029988905995810177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119940336159940831977654277 22488813029988905995810177)
        ·
          refine ⟨16866609772491679496857633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22488813029988905995810177 16866609772491679496857633)
          ·
            refine ⟨12649957329368759622643225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16866609772491679496857633 12649957329368759622643225)
            ·
              refine ⟨9487467997026569716982419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12649957329368759622643225 9487467997026569716982419)
              ·
                refine ⟨14231201995539854575473629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9487467997026569716982419 14231201995539854575473629)
                ·
                  refine ⟨5336700748327445465802611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14231201995539854575473629 5336700748327445465802611)
                  ·
                    refine ⟨8005051122491168198703917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5336700748327445465802611 8005051122491168198703917)
                    ·
                      refine ⟨3001894170934188074513969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8005051122491168198703917 3001894170934188074513969)
                      ·
                        rfl

theorem cell23_5846168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_5846168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846168 prefixEnd_5846168 := by exact prefixLift 5846168
  have htrace : WordTrace (prefixWord ++ tailWord_5846168) baseStart_5846168 baseEnd_5846168 := by
    simpa [prefixWord, tailWord_5846168, baseEnd_5846168] using wordTrace_append hprefix tailTrace_5846168
  have hstable : (prefixWord ++ tailWord_5846168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846168).length < 2 ^ (prefixWord ++ tailWord_5846168).sum := by decide
  have hdescent : baseEnd_5846168 < baseStart_5846168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846227 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 1, 9]
def baseStart_5846227 : Nat := 118140960795 + 5846227 * 2 ^ 59
def prefixEnd_5846227 : Nat := 4983230072969 + 3 ^ 40 * 5846227 * 2
def baseEnd_5846227 : Nat := 1000641488764267781225399

theorem tailTrace_5846227 : CollatzResearch.WordTrace tailWord_5846227 prefixEnd_5846227 1000641488764267781225399 := by
  unfold tailWord_5846227
  simp only [CollatzResearch.WordTrace]
  refine ⟨213229416191125509925560935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142152944127417006617040623 213229416191125509925560935)
  ·
    refine ⟨319844124286688264888341403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213229416191125509925560935 319844124286688264888341403)
    ·
      refine ⟨479766186430032397332512105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319844124286688264888341403 479766186430032397332512105)
      ·
        refine ⟨359824639822524297999384079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479766186430032397332512105 359824639822524297999384079)
        ·
          refine ⟨539736959733786446999076119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359824639822524297999384079 539736959733786446999076119)
          ·
            refine ⟨809605439600679670498614179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539736959733786446999076119 809605439600679670498614179)
            ·
              refine ⟨1214408159401019505747921269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809605439600679670498614179 1214408159401019505747921269)
              ·
                refine ⟨113850764943845578663867619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1214408159401019505747921269 113850764943845578663867619)
                ·
                  refine ⟨170776147415768367995801429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113850764943845578663867619 170776147415768367995801429)
                  ·
                    refine ⟨1000641488764267781225399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 170776147415768367995801429 1000641488764267781225399)
                    ·
                      rfl

theorem cell23_5846227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 9].length) (baseStart_5846227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846227 prefixEnd_5846227 := by exact prefixLift 5846227
  have htrace : WordTrace (prefixWord ++ tailWord_5846227) baseStart_5846227 baseEnd_5846227 := by
    simpa [prefixWord, tailWord_5846227, baseEnd_5846227] using wordTrace_append hprefix tailTrace_5846227
  have hstable : (prefixWord ++ tailWord_5846227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846227).length < 2 ^ (prefixWord ++ tailWord_5846227).sum := by decide
  have hdescent : baseEnd_5846227 < baseStart_5846227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846245 : List Nat := [1, 3, 1, 4, 3, 2, 1, 2, 1, 2, 3]
def baseStart_5846245 : Nat := 118140960795 + 5846245 * 2 ^ 59
def prefixEnd_5846245 : Nat := 4983230072969 + 3 ^ 40 * 5846245 * 2
def baseEnd_5846245 : Nat := 3001933708944584273251115

theorem tailTrace_5846245 : CollatzResearch.WordTrace tailWord_5846245 prefixEnd_5846245 3001933708944584273251115 := by
  unfold tailWord_5846245
  simp only [CollatzResearch.WordTrace]
  refine ⟨213230072705060298999716189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142153381803373532666477459 213230072705060298999716189)
  ·
    refine ⟨79961277264397612124893571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213230072705060298999716189 79961277264397612124893571)
    ·
      refine ⟨119941915896596418187340357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79961277264397612124893571 119941915896596418187340357)
      ·
        refine ⟨22489109230611828410126317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119941915896596418187340357 22489109230611828410126317)
        ·
          refine ⟨8433415961479435653797369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22489109230611828410126317 8433415961479435653797369)
          ·
            refine ⟨6325061971109576740348027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8433415961479435653797369 6325061971109576740348027)
            ·
              refine ⟨9487592956664365110522041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6325061971109576740348027 9487592956664365110522041)
              ·
                refine ⟨7115694717498273832891531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9487592956664365110522041 7115694717498273832891531)
                ·
                  refine ⟨10673542076247410749337297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7115694717498273832891531 10673542076247410749337297)
                  ·
                    refine ⟨8005156557185558062002973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10673542076247410749337297 8005156557185558062002973)
                    ·
                      refine ⟨3001933708944584273251115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8005156557185558062002973 3001933708944584273251115)
                      ·
                        rfl

theorem cell23_5846245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_5846245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846245 prefixEnd_5846245 := by exact prefixLift 5846245
  have htrace : WordTrace (prefixWord ++ tailWord_5846245) baseStart_5846245 baseEnd_5846245 := by
    simpa [prefixWord, tailWord_5846245, baseEnd_5846245] using wordTrace_append hprefix tailTrace_5846245
  have hstable : (prefixWord ++ tailWord_5846245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846245).length < 2 ^ (prefixWord ++ tailWord_5846245).sum := by decide
  have hdescent : baseEnd_5846245 < baseStart_5846245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846254 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_5846254 : Nat := 118140960795 + 5846254 * 2 ^ 59
def prefixEnd_5846254 : Nat := 4983230072969 + 3 ^ 40 * 5846254 * 2
def baseEnd_5846254 : Nat := 3001938330270474738038573

theorem tailTrace_5846254 : CollatzResearch.WordTrace tailWord_5846254 prefixEnd_5846254 3001938330270474738038573 := by
  unfold tailWord_5846254
  simp only [CollatzResearch.WordTrace]
  refine ⟨26653800120253461692099227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142153600641351795691195877 26653800120253461692099227)
  ·
    refine ⟨39980700180380192538148841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26653800120253461692099227 39980700180380192538148841)
    ·
      refine ⟨29985525135285144403611631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39980700180380192538148841 29985525135285144403611631)
      ·
        refine ⟨44978287702927716605417447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29985525135285144403611631 44978287702927716605417447)
        ·
          refine ⟨67467431554391574908126171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44978287702927716605417447 67467431554391574908126171)
          ·
            refine ⟨101201147331587362362189257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67467431554391574908126171 101201147331587362362189257)
            ·
              refine ⟨75900860498690521771641943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101201147331587362362189257 75900860498690521771641943)
              ·
                refine ⟨113851290748035782657462915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75900860498690521771641943 113851290748035782657462915)
                ·
                  refine ⟨170776936122053673986194373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113851290748035782657462915 170776936122053673986194373)
                  ·
                    refine ⟨32020675522885063872411445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 170776936122053673986194373 32020675522885063872411445)
                    ·
                      refine ⟨3001938330270474738038573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32020675522885063872411445 3001938330270474738038573)
                      ·
                        rfl

theorem cell23_5846254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_5846254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846254 prefixEnd_5846254 := by exact prefixLift 5846254
  have htrace : WordTrace (prefixWord ++ tailWord_5846254) baseStart_5846254 baseEnd_5846254 := by
    simpa [prefixWord, tailWord_5846254, baseEnd_5846254] using wordTrace_append hprefix tailTrace_5846254
  have hstable : (prefixWord ++ tailWord_5846254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846254).length < 2 ^ (prefixWord ++ tailWord_5846254).sum := by decide
  have hdescent : baseEnd_5846254 < baseStart_5846254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846258 : List Nat := [3, 2, 1, 3, 3, 1, 1, 2, 1, 3, 3]
def baseStart_5846258 : Nat := 118140960795 + 5846258 * 2 ^ 59
def prefixEnd_5846258 : Nat := 4983230072969 + 3 ^ 40 * 5846258 * 2
def baseEnd_5846258 : Nat := 3001940384193092722388555

theorem tailTrace_5846258 : CollatzResearch.WordTrace tailWord_5846258 prefixEnd_5846258 3001940384193092722388555 := by
  unfold tailWord_5846258
  simp only [CollatzResearch.WordTrace]
  refine ⟨53307636713503300554984857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142153697902675468146626285 53307636713503300554984857)
  ·
    refine ⟨39980727535127475416238643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53307636713503300554984857 39980727535127475416238643)
    ·
      refine ⟨59971091302691213124357965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39980727535127475416238643 59971091302691213124357965)
      ·
        refine ⟨22489159238509204921634237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59971091302691213124357965 22489159238509204921634237)
        ·
          refine ⟨8433434714440951845612839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22489159238509204921634237 8433434714440951845612839)
          ·
            refine ⟨12650152071661427768419259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8433434714440951845612839 12650152071661427768419259)
            ·
              refine ⟨18975228107492141652628889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12650152071661427768419259 18975228107492141652628889)
              ·
                refine ⟨14231421080619106239471667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18975228107492141652628889 14231421080619106239471667)
                ·
                  refine ⟨21347131620928659359207501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14231421080619106239471667 21347131620928659359207501)
                  ·
                    refine ⟨8005174357848247259702813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21347131620928659359207501 8005174357848247259702813)
                    ·
                      refine ⟨3001940384193092722388555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8005174357848247259702813 3001940384193092722388555)
                      ·
                        rfl

theorem cell23_5846258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_5846258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846258 prefixEnd_5846258 := by exact prefixLift 5846258
  have htrace : WordTrace (prefixWord ++ tailWord_5846258) baseStart_5846258 baseEnd_5846258 := by
    simpa [prefixWord, tailWord_5846258, baseEnd_5846258] using wordTrace_append hprefix tailTrace_5846258
  have hstable : (prefixWord ++ tailWord_5846258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846258).length < 2 ^ (prefixWord ++ tailWord_5846258).sum := by decide
  have hdescent : baseEnd_5846258 < baseStart_5846258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846281 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 3, 4, 2]
def baseStart_5846281 : Nat := 118140960795 + 5846281 * 2 ^ 59
def prefixEnd_5846281 : Nat := 4983230072969 + 3 ^ 40 * 5846281 * 2
def baseEnd_5846281 : Nat := 3001952194248146132400949

theorem tailTrace_5846281 : CollatzResearch.WordTrace tailWord_5846281 prefixEnd_5846281 3001952194248146132400949 := by
  unfold tailWord_5846281
  simp only [CollatzResearch.WordTrace]
  refine ⟨213231385732929877148026697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142154257155286584765351131 213231385732929877148026697)
  ·
    refine ⟨159923539299697407861020023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213231385732929877148026697 159923539299697407861020023)
    ·
      refine ⟨239885308949546111791530035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159923539299697407861020023 239885308949546111791530035)
      ·
        refine ⟨359827963424319167687295053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239885308949546111791530035 359827963424319167687295053)
        ·
          refine ⟨134935486284119687882735645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359827963424319167687295053 134935486284119687882735645)
          ·
            refine ⟨50600807356544882956025867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134935486284119687882735645 50600807356544882956025867)
            ·
              refine ⟨75901211034817324434038801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50600807356544882956025867 75901211034817324434038801)
              ·
                refine ⟨56925908276112993325529101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75901211034817324434038801 56925908276112993325529101)
                ·
                  refine ⟨21347215603542372497073413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56925908276112993325529101 21347215603542372497073413)
                  ·
                    refine ⟨4002602925664194843201265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21347215603542372497073413 4002602925664194843201265)
                    ·
                      refine ⟨3001952194248146132400949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4002602925664194843201265 3001952194248146132400949)
                      ·
                        rfl

theorem cell23_5846281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 4, 2].length) (baseStart_5846281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846281 prefixEnd_5846281 := by exact prefixLift 5846281
  have htrace : WordTrace (prefixWord ++ tailWord_5846281) baseStart_5846281 baseEnd_5846281 := by
    simpa [prefixWord, tailWord_5846281, baseEnd_5846281] using wordTrace_append hprefix tailTrace_5846281
  have hstable : (prefixWord ++ tailWord_5846281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846281).length < 2 ^ (prefixWord ++ tailWord_5846281).sum := by decide
  have hdescent : baseEnd_5846281 < baseStart_5846281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846298 : List Nat := [3, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2]
def baseStart_5846298 : Nat := 118140960795 + 5846298 * 2 ^ 59
def prefixEnd_5846298 : Nat := 4983230072969 + 3 ^ 40 * 5846298 * 2
def baseEnd_5846298 : Nat := 3001960923419272565888371

theorem tailTrace_5846298 : CollatzResearch.WordTrace tailWord_5846298 prefixEnd_5846298 3001960923419272565888371 := by
  unfold tailWord_5846298
  simp only [CollatzResearch.WordTrace]
  refine ⟨53308001443467072262848887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142154670515912192700930365 53308001443467072262848887)
  ·
    refine ⟨79962002165200608394273331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53308001443467072262848887 79962002165200608394273331)
    ·
      refine ⟨119943003247800912591409997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79962002165200608394273331 119943003247800912591409997)
      ·
        refine ⟨44978626217925342221778749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119943003247800912591409997 44978626217925342221778749)
        ·
          refine ⟨16866984831722003333167031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44978626217925342221778749 16866984831722003333167031)
          ·
            refine ⟨25300477247583004999750547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16866984831722003333167031 25300477247583004999750547)
            ·
              refine ⟨37950715871374507499625821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25300477247583004999750547 37950715871374507499625821)
              ·
                refine ⟨14231518451765440312359683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37950715871374507499625821 14231518451765440312359683)
                ·
                  refine ⟨21347277677648160468539525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14231518451765440312359683 21347277677648160468539525)
                  ·
                    refine ⟨4002614564559030087851161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21347277677648160468539525 4002614564559030087851161)
                    ·
                      refine ⟨3001960923419272565888371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4002614564559030087851161 3001960923419272565888371)
                      ·
                        rfl

theorem cell23_5846298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_5846298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846298 prefixEnd_5846298 := by exact prefixLift 5846298
  have htrace : WordTrace (prefixWord ++ tailWord_5846298) baseStart_5846298 baseEnd_5846298 := by
    simpa [prefixWord, tailWord_5846298, baseEnd_5846298] using wordTrace_append hprefix tailTrace_5846298
  have hstable : (prefixWord ++ tailWord_5846298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846298).length < 2 ^ (prefixWord ++ tailWord_5846298).sum := by decide
  have hdescent : baseEnd_5846298 < baseStart_5846298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846326 : List Nat := [5, 1, 2, 3, 2, 1, 1, 2, 2, 1, 3]
def baseStart_5846326 : Nat := 118140960795 + 5846326 * 2 ^ 59
def prefixEnd_5846326 : Nat := 4983230072969 + 3 ^ 40 * 5846326 * 2
def baseEnd_5846326 : Nat := 3001975300877598456338243

theorem tailTrace_5846326 : CollatzResearch.WordTrace tailWord_5846326 prefixEnd_5846326 3001975300877598456338243 := by
  unfold tailWord_5846326
  simp only [CollatzResearch.WordTrace]
  refine ⟨13327064188610428114588427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142155351345177899888943221 13327064188610428114588427)
  ·
    refine ⟨19990596282915642171882641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13327064188610428114588427 19990596282915642171882641)
    ·
      refine ⟨14992947212186731628911981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19990596282915642171882641 14992947212186731628911981)
      ·
        refine ⟨5622355204570024360841993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14992947212186731628911981 5622355204570024360841993)
        ·
          refine ⟨4216766403427518270631495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5622355204570024360841993 4216766403427518270631495)
          ·
            refine ⟨6325149605141277405947243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4216766403427518270631495 6325149605141277405947243)
            ·
              refine ⟨9487724407711916108920865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6325149605141277405947243 9487724407711916108920865)
              ·
                refine ⟨7115793305783937081690649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9487724407711916108920865 7115793305783937081690649)
                ·
                  refine ⟨5336844979337952811267987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7115793305783937081690649 5336844979337952811267987)
                  ·
                    refine ⟨8005267469006929216901981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5336844979337952811267987 8005267469006929216901981)
                    ·
                      refine ⟨3001975300877598456338243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8005267469006929216901981 3001975300877598456338243)
                      ·
                        rfl

theorem cell23_5846326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_5846326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846326 prefixEnd_5846326 := by exact prefixLift 5846326
  have htrace : WordTrace (prefixWord ++ tailWord_5846326) baseStart_5846326 baseEnd_5846326 := by
    simpa [prefixWord, tailWord_5846326, baseEnd_5846326] using wordTrace_append hprefix tailTrace_5846326
  have hstable : (prefixWord ++ tailWord_5846326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846326).length < 2 ^ (prefixWord ++ tailWord_5846326).sum := by decide
  have hdescent : baseEnd_5846326 < baseStart_5846326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846332 : List Nat := [2, 2, 2, 2, 1, 5, 1, 2, 2, 2, 2]
def baseStart_5846332 : Nat := 118140960795 + 5846332 * 2 ^ 59
def prefixEnd_5846332 : Nat := 4983230072969 + 3 ^ 40 * 5846332 * 2
def baseEnd_5846332 : Nat := 3001978381761525432863215

theorem tailTrace_5846332 : CollatzResearch.WordTrace tailWord_5846332 prefixEnd_5846332 3001978381761525432863215 := by
  unfold tailWord_5846332
  simp only [CollatzResearch.WordTrace]
  refine ⟨106616622927872556429066625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142155497237163408572088833 106616622927872556429066625)
  ·
    refine ⟨79962467195904417321799969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106616622927872556429066625 79962467195904417321799969)
    ·
      refine ⟨59971850396928312991349977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79962467195904417321799969 59971850396928312991349977)
      ·
        refine ⟨44978887797696234743512483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59971850396928312991349977 44978887797696234743512483)
        ·
          refine ⟨67468331696544352115268725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44978887797696234743512483 67468331696544352115268725)
          ·
            refine ⟨6325156096551033010806443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67468331696544352115268725 6325156096551033010806443)
            ·
              refine ⟨9487734144826549516209665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6325156096551033010806443 9487734144826549516209665)
              ·
                refine ⟨7115800608619912137157249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9487734144826549516209665 7115800608619912137157249)
                ·
                  refine ⟨5336850456464934102867937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7115800608619912137157249 5336850456464934102867937)
                  ·
                    refine ⟨4002637842348700577150953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5336850456464934102867937 4002637842348700577150953)
                    ·
                      refine ⟨3001978381761525432863215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4002637842348700577150953 3001978381761525432863215)
                      ·
                        rfl

theorem cell23_5846332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_5846332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846332 prefixEnd_5846332 := by exact prefixLift 5846332
  have htrace : WordTrace (prefixWord ++ tailWord_5846332) baseStart_5846332 baseEnd_5846332 := by
    simpa [prefixWord, tailWord_5846332, baseEnd_5846332] using wordTrace_append hprefix tailTrace_5846332
  have hstable : (prefixWord ++ tailWord_5846332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846332).length < 2 ^ (prefixWord ++ tailWord_5846332).sum := by decide
  have hdescent : baseEnd_5846332 < baseStart_5846332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846341 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 1, 7, 2]
def baseStart_5846341 : Nat := 118140960795 + 5846341 * 2 ^ 59
def prefixEnd_5846341 : Nat := 4983230072969 + 3 ^ 40 * 5846341 * 2
def baseEnd_5846341 : Nat := 3001983003087415897650673

theorem tailTrace_5846341 : CollatzResearch.WordTrace tailWord_5846341 prefixEnd_5846341 3001983003087415897650673 := by
  unfold tailWord_5846341
  simp only [CollatzResearch.WordTrace]
  refine ⟨213233574112712507395210877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142155716075141671596807251 213233574112712507395210877)
  ·
    refine ⟨79962590292267190273204079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213233574112712507395210877 79962590292267190273204079)
    ·
      refine ⟨119943885438400785409806119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79962590292267190273204079 119943885438400785409806119)
      ·
        refine ⟨179915828157601178114709179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119943885438400785409806119 179915828157601178114709179)
        ·
          refine ⟨269873742236401767172063769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179915828157601178114709179 269873742236401767172063769)
          ·
            refine ⟨202405306677301325379047827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269873742236401767172063769 202405306677301325379047827)
            ·
              refine ⟨303607960015951988068571741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202405306677301325379047827 303607960015951988068571741)
              ·
                refine ⟨113852985005981995525714403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303607960015951988068571741 113852985005981995525714403)
                ·
                  refine ⟨170779477508972993288571605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113852985005981995525714403 170779477508972993288571605)
                  ·
                    refine ⟨4002644004116554530200897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 170779477508972993288571605 4002644004116554530200897)
                    ·
                      refine ⟨3001983003087415897650673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4002644004116554530200897 3001983003087415897650673)
                      ·
                        rfl

theorem cell23_5846341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 7, 2].length) (baseStart_5846341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846341 prefixEnd_5846341 := by exact prefixLift 5846341
  have htrace : WordTrace (prefixWord ++ tailWord_5846341) baseStart_5846341 baseEnd_5846341 := by
    simpa [prefixWord, tailWord_5846341, baseEnd_5846341] using wordTrace_append hprefix tailTrace_5846341
  have hstable : (prefixWord ++ tailWord_5846341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846341).length < 2 ^ (prefixWord ++ tailWord_5846341).sum := by decide
  have hdescent : baseEnd_5846341 < baseStart_5846341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846344 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_5846344 : Nat := 118140960795 + 5846344 * 2 ^ 59
def prefixEnd_5846344 : Nat := 4983230072969 + 3 ^ 40 * 5846344 * 2
def baseEnd_5846344 : Nat := 3001984543529379385913159

theorem tailTrace_5846344 : CollatzResearch.WordTrace tailWord_5846344 prefixEnd_5846344 3001984543529379385913159 := by
  unfold tailWord_5846344
  simp only [CollatzResearch.WordTrace]
  refine ⟨106616841765850819453785043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142155789021134425938380057 106616841765850819453785043)
  ·
    refine ⟨159925262648776229180677565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106616841765850819453785043 159925262648776229180677565)
    ·
      refine ⟨59971973493291085942754087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159925262648776229180677565 59971973493291085942754087)
      ·
        refine ⟨89957960239936628914131131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59971973493291085942754087 89957960239936628914131131)
        ·
          refine ⟨134936940359904943371196697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89957960239936628914131131 134936940359904943371196697)
          ·
            refine ⟨101202705269928707528397523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134936940359904943371196697 101202705269928707528397523)
            ·
              refine ⟨151804057904893061292596285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101202705269928707528397523 151804057904893061292596285)
              ·
                refine ⟨56926521714334897984723607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151804057904893061292596285 56926521714334897984723607)
                ·
                  refine ⟨85389782571502346977085411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56926521714334897984723607 85389782571502346977085411)
                  ·
                    refine ⟨128084673857253520465628117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85389782571502346977085411 128084673857253520465628117)
                    ·
                      refine ⟨3001984543529379385913159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128084673857253520465628117 3001984543529379385913159)
                      ·
                        rfl

theorem cell23_5846344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_5846344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846344 prefixEnd_5846344 := by exact prefixLift 5846344
  have htrace : WordTrace (prefixWord ++ tailWord_5846344) baseStart_5846344 baseEnd_5846344 := by
    simpa [prefixWord, tailWord_5846344, baseEnd_5846344] using wordTrace_append hprefix tailTrace_5846344
  have hstable : (prefixWord ++ tailWord_5846344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846344).length < 2 ^ (prefixWord ++ tailWord_5846344).sum := by decide
  have hdescent : baseEnd_5846344 < baseStart_5846344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846349 : List Nat := [1, 6, 1, 3, 1, 2, 1, 1, 1, 4, 2]
def baseStart_5846349 : Nat := 118140960795 + 5846349 * 2 ^ 59
def prefixEnd_5846349 : Nat := 4983230072969 + 3 ^ 40 * 5846349 * 2
def baseEnd_5846349 : Nat := 3001987110932651866350637

theorem tailTrace_5846349 : CollatzResearch.WordTrace tailWord_5846349 prefixEnd_5846349 3001987110932651866350637 := by
  unfold tailWord_5846349
  simp only [CollatzResearch.WordTrace]
  refine ⟨213233865896683524761502101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142155910597789016507668067 213233865896683524761502101)
  ·
    refine ⟨9995337463907040223195411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 213233865896683524761502101 9995337463907040223195411)
    ·
      refine ⟨14993006195860560334793117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9995337463907040223195411 14993006195860560334793117)
      ·
        refine ⟨5622377323447710125547419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14993006195860560334793117 5622377323447710125547419)
        ·
          refine ⟨8433565985171565188321129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5622377323447710125547419 8433565985171565188321129)
          ·
            refine ⟨6325174488878673891240847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8433565985171565188321129 6325174488878673891240847)
            ·
              refine ⟨9487761733318010836861271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6325174488878673891240847 9487761733318010836861271)
              ·
                refine ⟨14231642599977016255291907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9487761733318010836861271 14231642599977016255291907)
                ·
                  refine ⟨21347463899965524382937861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14231642599977016255291907 21347463899965524382937861)
                  ·
                    refine ⟨4002649481243535821800849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21347463899965524382937861 4002649481243535821800849)
                    ·
                      refine ⟨3001987110932651866350637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4002649481243535821800849 3001987110932651866350637)
                      ·
                        rfl

theorem cell23_5846349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_5846349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846349 prefixEnd_5846349 := by exact prefixLift 5846349
  have htrace : WordTrace (prefixWord ++ tailWord_5846349) baseStart_5846349 baseEnd_5846349 := by
    simpa [prefixWord, tailWord_5846349, baseEnd_5846349] using wordTrace_append hprefix tailTrace_5846349
  have hstable : (prefixWord ++ tailWord_5846349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846349).length < 2 ^ (prefixWord ++ tailWord_5846349).sum := by decide
  have hdescent : baseEnd_5846349 < baseStart_5846349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846371 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 4]
def baseStart_5846371 : Nat := 118140960795 + 5846371 * 2 ^ 59
def prefixEnd_5846371 : Nat := 4983230072969 + 3 ^ 40 * 5846371 * 2
def baseEnd_5846371 : Nat := 3001998407507050780275535

theorem tailTrace_5846371 : CollatzResearch.WordTrace tailWord_5846371 prefixEnd_5846371 3001998407507050780275535 := by
  unfold tailWord_5846371
  simp only [CollatzResearch.WordTrace]
  refine ⟨213234668302603822518802967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142156445535069215012535311 213234668302603822518802967)
  ·
    refine ⟨319852002453905733778204451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213234668302603822518802967 319852002453905733778204451)
    ·
      refine ⟨479778003680858600667306677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319852002453905733778204451 479778003680858600667306677)
      ·
        refine ⟨44979187845080493812560001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 479778003680858600667306677 44979187845080493812560001)
        ·
          refine ⟨33734390883810370359420001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44979187845080493812560001 33734390883810370359420001)
          ·
            refine ⟨25300793162857777769565001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33734390883810370359420001 25300793162857777769565001)
            ·
              refine ⟨18975594872143333327173751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25300793162857777769565001 18975594872143333327173751)
              ·
                refine ⟨28463392308214999990760627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18975594872143333327173751 28463392308214999990760627)
                ·
                  refine ⟨42695088462322499986140941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28463392308214999990760627 42695088462322499986140941)
                  ·
                    refine ⟨16010658173370937494802853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42695088462322499986140941 16010658173370937494802853)
                    ·
                      refine ⟨3001998407507050780275535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16010658173370937494802853 3001998407507050780275535)
                      ·
                        rfl

theorem cell23_5846371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_5846371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846371 prefixEnd_5846371 := by exact prefixLift 5846371
  have htrace : WordTrace (prefixWord ++ tailWord_5846371) baseStart_5846371 baseEnd_5846371 := by
    simpa [prefixWord, tailWord_5846371, baseEnd_5846371] using wordTrace_append hprefix tailTrace_5846371
  have hstable : (prefixWord ++ tailWord_5846371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846371).length < 2 ^ (prefixWord ++ tailWord_5846371).sum := by decide
  have hdescent : baseEnd_5846371 < baseStart_5846371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846411 : List Nat := [1, 1, 1, 1, 4, 3, 3, 3, 6]
def baseStart_5846411 : Nat := 118140960795 + 5846411 * 2 ^ 59
def prefixEnd_5846411 : Nat := 4983230072969 + 3 ^ 40 * 5846411 * 2
def baseEnd_5846411 : Nat := 333557660748136735975039

theorem tailTrace_5846411 : CollatzResearch.WordTrace tailWord_5846411 prefixEnd_5846411 333557660748136735975039 := by
  unfold tailWord_5846411
  simp only [CollatzResearch.WordTrace]
  refine ⟨213236127222458909350259087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142157418148305939566839391 213236127222458909350259087)
  ·
    refine ⟨319854190833688364025388631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213236127222458909350259087 319854190833688364025388631)
    ·
      refine ⟨479781286250532546038082947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319854190833688364025388631 479781286250532546038082947)
      ·
        refine ⟨719671929375798819057124421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479781286250532546038082947 719671929375798819057124421)
        ·
          refine ⟨134938486757962278573210829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 719671929375798819057124421 134938486757962278573210829)
          ·
            refine ⟨50601932534235854464954061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134938486757962278573210829 50601932534235854464954061)
            ·
              refine ⟨18975724700338445424357773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50601932534235854464954061 18975724700338445424357773)
              ·
                refine ⟨7115896762626917034134165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18975724700338445424357773 7115896762626917034134165)
                ·
                  refine ⟨333557660748136735975039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7115896762626917034134165 333557660748136735975039)
                  ·
                    rfl

theorem cell23_5846411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 6].length) (baseStart_5846411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846411 prefixEnd_5846411 := by exact prefixLift 5846411
  have htrace : WordTrace (prefixWord ++ tailWord_5846411) baseStart_5846411 baseEnd_5846411 := by
    simpa [prefixWord, tailWord_5846411, baseEnd_5846411] using wordTrace_append hprefix tailTrace_5846411
  have hstable : (prefixWord ++ tailWord_5846411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846411).length < 2 ^ (prefixWord ++ tailWord_5846411).sum := by decide
  have hdescent : baseEnd_5846411 < baseStart_5846411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846421 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 2, 5, 3]
def baseStart_5846421 : Nat := 118140960795 + 5846421 * 2 ^ 59
def prefixEnd_5846421 : Nat := 4983230072969 + 3 ^ 40 * 5846421 * 2
def baseEnd_5846421 : Nat := 3002024081539775584650305

theorem tailTrace_5846421 : CollatzResearch.WordTrace tailWord_5846421 prefixEnd_5846421 3002024081539775584650305 := by
  unfold tailWord_5846421
  simp only [CollatzResearch.WordTrace]
  refine ⟨213236491952422681058123117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142157661301615120705415411 213236491952422681058123117)
  ·
    refine ⟨79963684482158505396796169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213236491952422681058123117 79963684482158505396796169)
    ·
      refine ⟨59972763361618879047597127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79963684482158505396796169 59972763361618879047597127)
      ·
        refine ⟨89959145042428318571395691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59972763361618879047597127 89959145042428318571395691)
        ·
          refine ⟨134938717563642477857093537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89959145042428318571395691 134938717563642477857093537)
          ·
            refine ⟨101204038172731858392820153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134938717563642477857093537 101204038172731858392820153)
            ·
              refine ⟨75903028629548893794615115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101204038172731858392820153 75903028629548893794615115)
              ·
                refine ⟨113854542944323340691922673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75903028629548893794615115 113854542944323340691922673)
                ·
                  refine ⟨85390907208242505518942005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113854542944323340691922673 85390907208242505518942005)
                  ·
                    refine ⟨8005397550772734892400813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85390907208242505518942005 8005397550772734892400813)
                    ·
                      refine ⟨3002024081539775584650305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8005397550772734892400813 3002024081539775584650305)
                      ·
                        rfl

theorem cell23_5846421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_5846421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846421 prefixEnd_5846421 := by exact prefixLift 5846421
  have htrace : WordTrace (prefixWord ++ tailWord_5846421) baseStart_5846421 baseEnd_5846421 := by
    simpa [prefixWord, tailWord_5846421, baseEnd_5846421] using wordTrace_append hprefix tailTrace_5846421
  have hstable : (prefixWord ++ tailWord_5846421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846421).length < 2 ^ (prefixWord ++ tailWord_5846421).sum := by decide
  have hdescent : baseEnd_5846421 < baseStart_5846421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846445 : List Nat := [1, 5, 2, 2, 1, 2, 2, 2, 6]
def baseStart_5846445 : Nat := 118140960795 + 5846445 * 2 ^ 59
def prefixEnd_5846445 : Nat := 4983230072969 + 3 ^ 40 * 5846445 * 2
def baseEnd_5846445 : Nat := 333559600563942610083355

theorem tailTrace_5846445 : CollatzResearch.WordTrace tailWord_5846445 prefixEnd_5846445 333559600563942610083355 := by
  unfold tailWord_5846445
  simp only [CollatzResearch.WordTrace]
  refine ⟨213237367304335733156996789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142158244869557155437997859 213237367304335733156996789)
  ·
    refine ⟨19991003184781474983468449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 213237367304335733156996789 19991003184781474983468449)
    ·
      refine ⟨14993252388586106237601337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19991003184781474983468449 14993252388586106237601337)
      ·
        refine ⟨11244939291439579678201003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14993252388586106237601337 11244939291439579678201003)
        ·
          refine ⟨16867408937159369517301505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11244939291439579678201003 16867408937159369517301505)
          ·
            refine ⟨12650556702869527137976129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16867408937159369517301505 12650556702869527137976129)
            ·
              refine ⟨9487917527152145353482097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12650556702869527137976129 9487917527152145353482097)
              ·
                refine ⟨7115938145364109015111573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9487917527152145353482097 7115938145364109015111573)
                ·
                  refine ⟨333559600563942610083355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7115938145364109015111573 333559600563942610083355)
                  ·
                    rfl

theorem cell23_5846445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_5846445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846445 prefixEnd_5846445 := by exact prefixLift 5846445
  have htrace : WordTrace (prefixWord ++ tailWord_5846445) baseStart_5846445 baseEnd_5846445 := by
    simpa [prefixWord, tailWord_5846445, baseEnd_5846445] using wordTrace_append hprefix tailTrace_5846445
  have hstable : (prefixWord ++ tailWord_5846445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846445).length < 2 ^ (prefixWord ++ tailWord_5846445).sum := by decide
  have hdescent : baseEnd_5846445 < baseStart_5846445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846448 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 4, 3, 2]
def baseStart_5846448 : Nat := 118140960795 + 5846448 * 2 ^ 59
def prefixEnd_5846448 : Nat := 4983230072969 + 3 ^ 40 * 5846448 * 2
def baseEnd_5846448 : Nat := 3002037945517446979012681

theorem tailTrace_5846448 : CollatzResearch.WordTrace tailWord_5846448 prefixEnd_5846448 3002037945517446979012681 := by
  unfold tailWord_5846448
  simp only [CollatzResearch.WordTrace]
  refine ⟨106618738361662432334677999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142158317815549909779570665 106618738361662432334677999)
  ·
    refine ⟨159928107542493648502016999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106618738361662432334677999 159928107542493648502016999)
    ·
      refine ⟨239892161313740472753025499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159928107542493648502016999 239892161313740472753025499)
      ·
        refine ⟨359838241970610709129538249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239892161313740472753025499 359838241970610709129538249)
        ·
          refine ⟨269878681477958031847153687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359838241970610709129538249 269878681477958031847153687)
          ·
            refine ⟨404818022216937047770730531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269878681477958031847153687 404818022216937047770730531)
            ·
              refine ⟨607227033325405571656095797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404818022216937047770730531 607227033325405571656095797)
              ·
                refine ⟨56927534374256772342758981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 607227033325405571656095797 56927534374256772342758981)
                ·
                  refine ⟨10673912695173144814267309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56927534374256772342758981 10673912695173144814267309)
                  ·
                    refine ⟨4002717260689929305350241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10673912695173144814267309 4002717260689929305350241)
                    ·
                      refine ⟨3002037945517446979012681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4002717260689929305350241 3002037945517446979012681)
                      ·
                        rfl

theorem cell23_5846448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 4, 3, 2].length) (baseStart_5846448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846448 prefixEnd_5846448 := by exact prefixLift 5846448
  have htrace : WordTrace (prefixWord ++ tailWord_5846448) baseStart_5846448 baseEnd_5846448 := by
    simpa [prefixWord, tailWord_5846448, baseEnd_5846448] using wordTrace_append hprefix tailTrace_5846448
  have hstable : (prefixWord ++ tailWord_5846448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846448).length < 2 ^ (prefixWord ++ tailWord_5846448).sum := by decide
  have hdescent : baseEnd_5846448 < baseStart_5846448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846466 : List Nat := [3, 5, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_5846466 : Nat := 118140960795 + 5846466 * 2 ^ 59
def prefixEnd_5846466 : Nat := 4983230072969 + 3 ^ 40 * 5846466 * 2
def baseEnd_5846466 : Nat := 1000682396056409302862533

theorem tailTrace_5846466 : CollatzResearch.WordTrace tailWord_5846466 prefixEnd_5846466 1000682396056409302862533 := by
  unfold tailWord_5846466
  simp only [CollatzResearch.WordTrace]
  refine ⟨53309533309314913435877813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142158755491506435829007501 53309533309314913435877813)
  ·
    refine ⟨4997768747748273134613545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53309533309314913435877813 4997768747748273134613545)
    ·
      refine ⟨3748326560811204850960159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4997768747748273134613545 3748326560811204850960159)
      ·
        refine ⟨5622489841216807276440239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3748326560811204850960159 5622489841216807276440239)
        ·
          refine ⟨8433734761825210914660359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5622489841216807276440239 8433734761825210914660359)
          ·
            refine ⟨12650602142737816371990539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8433734761825210914660359 12650602142737816371990539)
            ·
              refine ⟨18975903214106724557985809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12650602142737816371990539 18975903214106724557985809)
              ·
                refine ⟨14231927410580043418489357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18975903214106724557985809 14231927410580043418489357)
                ·
                  refine ⟨5336972778967516281933509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14231927410580043418489357 5336972778967516281933509)
                  ·
                    refine ⟨1000682396056409302862533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5336972778967516281933509 1000682396056409302862533)
                    ·
                      rfl

theorem cell23_5846466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_5846466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846466 prefixEnd_5846466 := by exact prefixLift 5846466
  have htrace : WordTrace (prefixWord ++ tailWord_5846466) baseStart_5846466 baseEnd_5846466 := by
    simpa [prefixWord, tailWord_5846466, baseEnd_5846466] using wordTrace_append hprefix tailTrace_5846466
  have hstable : (prefixWord ++ tailWord_5846466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846466).length < 2 ^ (prefixWord ++ tailWord_5846466).sum := by decide
  have hdescent : baseEnd_5846466 < baseStart_5846466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846478 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4]
def baseStart_5846478 : Nat := 118140960795 + 5846478 * 2 ^ 59
def prefixEnd_5846478 : Nat := 4983230072969 + 3 ^ 40 * 5846478 * 2
def baseEnd_5846478 : Nat := 3002053349937081861637543

theorem tailTrace_5846478 : CollatzResearch.WordTrace tailWord_5846478 prefixEnd_5846478 3002053349937081861637543 := by
  unfold tailWord_5846478
  simp only [CollatzResearch.WordTrace]
  refine ⟨26654821364152022474118511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142159047275477453195298725 26654821364152022474118511)
  ·
    refine ⟨39982232046228033711177767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26654821364152022474118511 39982232046228033711177767)
    ·
      refine ⟨59973348069342050566766651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39982232046228033711177767 59973348069342050566766651)
      ·
        refine ⟨89960022104013075850149977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59973348069342050566766651 89960022104013075850149977)
        ·
          refine ⟨67470016578009806887612483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89960022104013075850149977 67470016578009806887612483)
          ·
            refine ⟨101205024867014710331418725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67470016578009806887612483 101205024867014710331418725)
            ·
              refine ⟨18975942162565258187141011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101205024867014710331418725 18975942162565258187141011)
              ·
                refine ⟨28463913243847887280711517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18975942162565258187141011 28463913243847887280711517)
                ·
                  refine ⟨10673967466442957730266819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28463913243847887280711517 10673967466442957730266819)
                  ·
                    refine ⟨16010951199664436595400229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10673967466442957730266819 16010951199664436595400229)
                    ·
                      refine ⟨3002053349937081861637543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16010951199664436595400229 3002053349937081861637543)
                      ·
                        rfl

theorem cell23_5846478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_5846478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846478 prefixEnd_5846478 := by exact prefixLift 5846478
  have htrace : WordTrace (prefixWord ++ tailWord_5846478) baseStart_5846478 baseEnd_5846478 := by
    simpa [prefixWord, tailWord_5846478, baseEnd_5846478] using wordTrace_append hprefix tailTrace_5846478
  have hstable : (prefixWord ++ tailWord_5846478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846478).length < 2 ^ (prefixWord ++ tailWord_5846478).sum := by decide
  have hdescent : baseEnd_5846478 < baseStart_5846478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846495 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 5, 2, 2]
def baseStart_5846495 : Nat := 118140960795 + 5846495 * 2 ^ 59
def prefixEnd_5846495 : Nat := 4983230072969 + 3 ^ 40 * 5846495 * 2
def baseEnd_5846495 : Nat := 3002062079108208295124965

theorem tailTrace_5846495 : CollatzResearch.WordTrace tailWord_5846495 prefixEnd_5846495 3002062079108208295124965 := by
  unfold tailWord_5846495
  simp only [CollatzResearch.WordTrace]
  refine ⟨213239190954154591696316939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142159460636103061130877959 213239190954154591696316939)
  ·
    refine ⟨319858786431231887544475409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213239190954154591696316939 319858786431231887544475409)
    ·
      refine ⟨239894089823423915658356557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319858786431231887544475409 239894089823423915658356557)
      ·
        refine ⟨89960283683783968371883709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239894089823423915658356557 89960283683783968371883709)
        ·
          refine ⟨33735106381418988139456391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89960283683783968371883709 33735106381418988139456391)
          ·
            refine ⟨50602659572128482209184587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33735106381418988139456391 50602659572128482209184587)
            ·
              refine ⟨75903989358192723313776881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50602659572128482209184587 75903989358192723313776881)
              ·
                refine ⟨56927992018644542485332661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75903989358192723313776881 56927992018644542485332661)
                ·
                  refine ⟨5336999251747925857999937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56927992018644542485332661 5336999251747925857999937)
                  ·
                    refine ⟨4002749438810944393499953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5336999251747925857999937 4002749438810944393499953)
                    ·
                      refine ⟨3002062079108208295124965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4002749438810944393499953 3002062079108208295124965)
                      ·
                        rfl

theorem cell23_5846495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_5846495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846495 prefixEnd_5846495 := by exact prefixLift 5846495
  have htrace : WordTrace (prefixWord ++ tailWord_5846495) baseStart_5846495 baseEnd_5846495 := by
    simpa [prefixWord, tailWord_5846495, baseEnd_5846495] using wordTrace_append hprefix tailTrace_5846495
  have hstable : (prefixWord ++ tailWord_5846495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846495).length < 2 ^ (prefixWord ++ tailWord_5846495).sum := by decide
  have hdescent : baseEnd_5846495 < baseStart_5846495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846512 : List Nat := [2, 1, 1, 1, 3, 5, 2, 1, 3, 2, 2]
def baseStart_5846512 : Nat := 118140960795 + 5846512 * 2 ^ 59
def prefixEnd_5846512 : Nat := 4983230072969 + 3 ^ 40 * 5846512 * 2
def baseEnd_5846512 : Nat := 3002070808279334728612387

theorem tailTrace_5846512 : CollatzResearch.WordTrace tailWord_5846512 prefixEnd_5846512 3002070808279334728612387 := by
  unfold tailWord_5846512
  simp only [CollatzResearch.WordTrace]
  refine ⟨106619905497546501799842895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142159873996728669066457193 106619905497546501799842895)
  ·
    refine ⟨159929858246319752699764343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106619905497546501799842895 159929858246319752699764343)
    ·
      refine ⟨239894787369479629049646515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159929858246319752699764343 239894787369479629049646515)
      ·
        refine ⟨359842181054219443574469773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239894787369479629049646515 359842181054219443574469773)
        ·
          refine ⟨134940817895332291340426165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359842181054219443574469773 134940817895332291340426165)
          ·
            refine ⟨12650701677687402313164953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134940817895332291340426165 12650701677687402313164953)
            ·
              refine ⟨9488026258265551734873715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12650701677687402313164953 9488026258265551734873715)
              ·
                refine ⟨14232039387398327602310573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9488026258265551734873715 14232039387398327602310573)
                ·
                  refine ⟨5337014770274372850866465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14232039387398327602310573 5337014770274372850866465)
                  ·
                    refine ⟨4002761077705779638149849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5337014770274372850866465 4002761077705779638149849)
                    ·
                      refine ⟨3002070808279334728612387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4002761077705779638149849 3002070808279334728612387)
                      ·
                        rfl

theorem cell23_5846512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 3, 2, 2].length) (baseStart_5846512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846512 prefixEnd_5846512 := by exact prefixLift 5846512
  have htrace : WordTrace (prefixWord ++ tailWord_5846512) baseStart_5846512 baseEnd_5846512 := by
    simpa [prefixWord, tailWord_5846512, baseEnd_5846512] using wordTrace_append hprefix tailTrace_5846512
  have hstable : (prefixWord ++ tailWord_5846512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846512).length < 2 ^ (prefixWord ++ tailWord_5846512).sum := by decide
  have hdescent : baseEnd_5846512 < baseStart_5846512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846525 : List Nat := [1, 4, 1, 1, 1, 6, 1, 1, 1, 2, 4]
def baseStart_5846525 : Nat := 118140960795 + 5846525 * 2 ^ 59
def prefixEnd_5846525 : Nat := 4983230072969 + 3 ^ 40 * 5846525 * 2
def baseEnd_5846525 : Nat := 3002077483527843177749827

theorem tailTrace_5846525 : CollatzResearch.WordTrace tailWord_5846525 prefixEnd_5846525 3002077483527843177749827 := by
  unfold tailWord_5846525
  simp only [CollatzResearch.WordTrace]
  refine ⟨213240285144045906819909029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142160190096030604546606019 213240285144045906819909029)
  ·
    refine ⟨39982553464508607528732943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213240285144045906819909029 39982553464508607528732943)
    ·
      refine ⟨59973830196762911293099415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39982553464508607528732943 59973830196762911293099415)
      ·
        refine ⟨89960745295144366939649123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59973830196762911293099415 89960745295144366939649123)
        ·
          refine ⟨134941117942716550409473685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89960745295144366939649123 134941117942716550409473685)
          ·
            refine ⟨6325364903564838300444079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 134941117942716550409473685 6325364903564838300444079)
            ·
              refine ⟨9488047355347257450666119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6325364903564838300444079 9488047355347257450666119)
              ·
                refine ⟨14232071033020886175999179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9488047355347257450666119 14232071033020886175999179)
                ·
                  refine ⟨21348106549531329263998769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14232071033020886175999179 21348106549531329263998769)
                  ·
                    refine ⟨16011079912148496947999077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21348106549531329263998769 16011079912148496947999077)
                    ·
                      refine ⟨3002077483527843177749827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16011079912148496947999077 3002077483527843177749827)
                      ·
                        rfl

theorem cell23_5846525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_5846525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846525 prefixEnd_5846525 := by exact prefixLift 5846525
  have htrace : WordTrace (prefixWord ++ tailWord_5846525) baseStart_5846525 baseEnd_5846525 := by
    simpa [prefixWord, tailWord_5846525, baseEnd_5846525] using wordTrace_append hprefix tailTrace_5846525
  have hstable : (prefixWord ++ tailWord_5846525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846525).length < 2 ^ (prefixWord ++ tailWord_5846525).sum := by decide
  have hdescent : baseEnd_5846525 < baseStart_5846525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846535 : List Nat := [1, 1, 4, 3, 2, 3, 2, 7]
def baseStart_5846535 : Nat := 118140960795 + 5846535 * 2 ^ 59
def prefixEnd_5846535 : Nat := 4983230072969 + 3 ^ 40 * 5846535 * 2
def baseEnd_5846535 : Nat := 111188245123495856986103

theorem tailTrace_5846535 : CollatzResearch.WordTrace tailWord_5846535 prefixEnd_5846535 111188245123495856986103 := by
  unfold tailWord_5846535
  simp only [CollatzResearch.WordTrace]
  refine ⟨213240649874009678527773059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142160433249339785685182039 213240649874009678527773059)
  ·
    refine ⟨319860974811014517791659589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213240649874009678527773059 319860974811014517791659589)
    ·
      refine ⟨59973932777065222085936173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319860974811014517791659589 59973932777065222085936173)
      ·
        refine ⟨22490224791399458282226065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59973932777065222085936173 22490224791399458282226065)
        ·
          refine ⟨16867668593549593711669549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22490224791399458282226065 16867668593549593711669549)
          ·
            refine ⟨6325375722581097641876081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16867668593549593711669549 6325375722581097641876081)
            ·
              refine ⟨4744031791935823231407061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6325375722581097641876081 4744031791935823231407061)
              ·
                refine ⟨111188245123495856986103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4744031791935823231407061 111188245123495856986103)
                ·
                  rfl

theorem cell23_5846535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 7].length) (baseStart_5846535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846535 prefixEnd_5846535 := by exact prefixLift 5846535
  have htrace : WordTrace (prefixWord ++ tailWord_5846535) baseStart_5846535 baseEnd_5846535 := by
    simpa [prefixWord, tailWord_5846535, baseEnd_5846535] using wordTrace_append hprefix tailTrace_5846535
  have hstable : (prefixWord ++ tailWord_5846535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846535).length < 2 ^ (prefixWord ++ tailWord_5846535).sum := by decide
  have hdescent : baseEnd_5846535 < baseStart_5846535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846579 : List Nat := [1, 1, 1, 2, 4, 5, 2, 1, 2, 1, 3]
def baseStart_5846579 : Nat := 118140960795 + 5846579 * 2 ^ 59
def prefixEnd_5846579 : Nat := 4983230072969 + 3 ^ 40 * 5846579 * 2
def baseEnd_5846579 : Nat := 3002105211483185966474579

theorem tailTrace_5846579 : CollatzResearch.WordTrace tailWord_5846579 prefixEnd_5846579 3002105211483185966474579 := by
  unfold tailWord_5846579
  simp only [CollatzResearch.WordTrace]
  refine ⟨213242254685850274042374791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142161503123900182694916527 213242254685850274042374791)
  ·
    refine ⟨319863382028775411063562187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213242254685850274042374791 319863382028775411063562187)
    ·
      refine ⟨479795073043163116595343281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319863382028775411063562187 479795073043163116595343281)
      ·
        refine ⟨359846304782372337446507461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479795073043163116595343281 359846304782372337446507461)
        ·
          refine ⟨67471182146694813271220149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 359846304782372337446507461 67471182146694813271220149)
          ·
            refine ⟨6325423326252638744176889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67471182146694813271220149 6325423326252638744176889)
            ·
              refine ⟨4744067494689479058132667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6325423326252638744176889 4744067494689479058132667)
              ·
                refine ⟨7116101242034218587199001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4744067494689479058132667 7116101242034218587199001)
                ·
                  refine ⟨5337075931525663940399251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7116101242034218587199001 5337075931525663940399251)
                  ·
                    refine ⟨8005613897288495910598877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5337075931525663940399251 8005613897288495910598877)
                    ·
                      refine ⟨3002105211483185966474579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8005613897288495910598877 3002105211483185966474579)
                      ·
                        rfl

theorem cell23_5846579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 2, 1, 3].length) (baseStart_5846579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846579 prefixEnd_5846579 := by exact prefixLift 5846579
  have htrace : WordTrace (prefixWord ++ tailWord_5846579) baseStart_5846579 baseEnd_5846579 := by
    simpa [prefixWord, tailWord_5846579, baseEnd_5846579] using wordTrace_append hprefix tailTrace_5846579
  have hstable : (prefixWord ++ tailWord_5846579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846579).length < 2 ^ (prefixWord ++ tailWord_5846579).sum := by decide
  have hdescent : baseEnd_5846579 < baseStart_5846579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846614 : List Nat := [5, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_5846614 : Nat := 118140960795 + 5846614 * 2 ^ 59
def prefixEnd_5846614 : Nat := 4983230072969 + 3 ^ 40 * 5846614 * 2
def baseEnd_5846614 : Nat := 3002123183306093329536919

theorem tailTrace_5846614 : CollatzResearch.WordTrace tailWord_5846614 prefixEnd_5846614 3002123183306093329536919 := by
  unfold tailWord_5846614
  simp only [CollatzResearch.WordTrace]
  refine ⟨13327720702545217188743681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142162354160482316679932597 13327720702545217188743681)
  ·
    refine ⟨9995790526908912891557761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13327720702545217188743681 9995790526908912891557761)
    ·
      refine ⟨7496842895181684668668321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9995790526908912891557761 7496842895181684668668321)
      ·
        refine ⟨5622632171386263501501241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7496842895181684668668321 5622632171386263501501241)
        ·
          refine ⟨4216974128539697626125931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5622632171386263501501241 4216974128539697626125931)
          ·
            refine ⟨6325461192809546439188897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4216974128539697626125931 6325461192809546439188897)
            ·
              refine ⟨4744095894607159829391673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6325461192809546439188897 4744095894607159829391673)
              ·
                refine ⟨3558071920955369872043755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4744095894607159829391673 3558071920955369872043755)
                ·
                  refine ⟨5337107881433054808065633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3558071920955369872043755 5337107881433054808065633)
                  ·
                    refine ⟨4002830911074791106049225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5337107881433054808065633 4002830911074791106049225)
                    ·
                      refine ⟨3002123183306093329536919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4002830911074791106049225 3002123183306093329536919)
                      ·
                        rfl

theorem cell23_5846614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_5846614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846614 prefixEnd_5846614 := by exact prefixLift 5846614
  have htrace : WordTrace (prefixWord ++ tailWord_5846614) baseStart_5846614 baseEnd_5846614 := by
    simpa [prefixWord, tailWord_5846614, baseEnd_5846614] using wordTrace_append hprefix tailTrace_5846614
  have hstable : (prefixWord ++ tailWord_5846614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846614).length < 2 ^ (prefixWord ++ tailWord_5846614).sum := by decide
  have hdescent : baseEnd_5846614 < baseStart_5846614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846618 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3]
def baseStart_5846618 : Nat := 118140960795 + 5846618 * 2 ^ 59
def prefixEnd_5846618 : Nat := 4983230072969 + 3 ^ 40 * 5846618 * 2
def baseEnd_5846618 : Nat := 3002125237228711313886899

theorem tailTrace_5846618 : CollatzResearch.WordTrace tailWord_5846618 prefixEnd_5846618 3002125237228711313886899 := by
  unfold tailWord_5846618
  simp only [CollatzResearch.WordTrace]
  refine ⟨53310919283177245925761127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142162451421805989135363005 53310919283177245925761127)
  ·
    refine ⟨79966378924765868888641691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53310919283177245925761127 79966378924765868888641691)
    ·
      refine ⟨119949568387148803332962537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79966378924765868888641691 119949568387148803332962537)
      ·
        refine ⟨89962176290361602499721903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119949568387148803332962537 89962176290361602499721903)
        ·
          refine ⟨134943264435542403749582855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89962176290361602499721903 134943264435542403749582855)
          ·
            refine ⟨202414896653313605624374283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134943264435542403749582855 202414896653313605624374283)
            ·
              refine ⟨303622344979970408436561425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202414896653313605624374283 303622344979970408436561425)
              ·
                refine ⟨227716758734977806327421069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303622344979970408436561425 227716758734977806327421069)
                ·
                  refine ⟨85393784525616677372782901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227716758734977806327421069 85393784525616677372782901)
                  ·
                    refine ⟨8005667299276563503698397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85393784525616677372782901 8005667299276563503698397)
                    ·
                      refine ⟨3002125237228711313886899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8005667299276563503698397 3002125237228711313886899)
                      ·
                        rfl

theorem cell23_5846618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_5846618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846618 prefixEnd_5846618 := by exact prefixLift 5846618
  have htrace : WordTrace (prefixWord ++ tailWord_5846618) baseStart_5846618 baseEnd_5846618 := by
    simpa [prefixWord, tailWord_5846618, baseEnd_5846618] using wordTrace_append hprefix tailTrace_5846618
  have hstable : (prefixWord ++ tailWord_5846618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846618).length < 2 ^ (prefixWord ++ tailWord_5846618).sum := by decide
  have hdescent : baseEnd_5846618 < baseStart_5846618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846625 : List Nat := [1, 2, 3, 1, 1, 3, 3, 4, 5]
def baseStart_5846625 : Nat := 118140960795 + 5846625 * 2 ^ 59
def prefixEnd_5846625 : Nat := 4983230072969 + 3 ^ 40 * 5846625 * 2
def baseEnd_5846625 : Nat := 333569870177032531833263

theorem tailTrace_5846625 : CollatzResearch.WordTrace tailWord_5846625 prefixEnd_5846625 333569870177032531833263 := by
  unfold tailWord_5846625
  simp only [CollatzResearch.WordTrace]
  refine ⟨213243932443683623898549329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142162621629122415932366219 213243932443683623898549329)
  ·
    refine ⟨159932949332762717923911997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213243932443683623898549329 159932949332762717923911997)
    ·
      refine ⟨59974855999786019221466999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159932949332762717923911997 59974855999786019221466999)
      ·
        refine ⟨89962283999679028832200499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59974855999786019221466999 89962283999679028832200499)
        ·
          refine ⟨134943425999518543248300749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89962283999679028832200499 134943425999518543248300749)
          ·
            refine ⟨50603784749819453718112781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134943425999518543248300749 50603784749819453718112781)
            ·
              refine ⟨18976419281182295144292293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50603784749819453718112781 18976419281182295144292293)
              ·
                refine ⟨3558078615221680339554805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18976419281182295144292293 3558078615221680339554805)
                ·
                  refine ⟨333569870177032531833263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3558078615221680339554805 333569870177032531833263)
                  ·
                    rfl

theorem cell23_5846625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 5].length) (baseStart_5846625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846625 prefixEnd_5846625 := by exact prefixLift 5846625
  have htrace : WordTrace (prefixWord ++ tailWord_5846625) baseStart_5846625 baseEnd_5846625 := by
    simpa [prefixWord, tailWord_5846625, baseEnd_5846625] using wordTrace_append hprefix tailTrace_5846625
  have hstable : (prefixWord ++ tailWord_5846625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846625).length < 2 ^ (prefixWord ++ tailWord_5846625).sum := by decide
  have hdescent : baseEnd_5846625 < baseStart_5846625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846692 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 2, 4, 2]
def baseStart_5846692 : Nat := 118140960795 + 5846692 * 2 ^ 59
def prefixEnd_5846692 : Nat := 4983230072969 + 3 ^ 40 * 5846692 * 2
def baseEnd_5846692 : Nat := 3002163234797144024361559

theorem tailTrace_5846692 : CollatzResearch.WordTrace tailWord_5846692 prefixEnd_5846692 3002163234797144024361559 := by
  unfold tailWord_5846692
  simp only [CollatzResearch.WordTrace]
  refine ⟨106623188067220447170619165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142164250756293929560825553 106623188067220447170619165)
  ·
    refine ⟨39983695525207667688982187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106623188067220447170619165 39983695525207667688982187)
    ·
      refine ⟨59975543287811501533473281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39983695525207667688982187 59975543287811501533473281)
      ·
        refine ⟨44981657465858626150104961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59975543287811501533473281 44981657465858626150104961)
        ·
          refine ⟨33736243099393969612578721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44981657465858626150104961 33736243099393969612578721)
          ·
            refine ⟨25302182324545477209434041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33736243099393969612578721 25302182324545477209434041)
            ·
              refine ⟨18976636743409107907075531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25302182324545477209434041 18976636743409107907075531)
              ·
                refine ⟨28464955115113661860613297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18976636743409107907075531 28464955115113661860613297)
                ·
                  refine ⟨21348716336335246395459973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28464955115113661860613297 21348716336335246395459973)
                  ·
                    refine ⟨4002884313062858699148745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21348716336335246395459973 4002884313062858699148745)
                    ·
                      refine ⟨3002163234797144024361559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4002884313062858699148745 3002163234797144024361559)
                      ·
                        rfl

theorem cell23_5846692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_5846692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846692 prefixEnd_5846692 := by exact prefixLift 5846692
  have htrace : WordTrace (prefixWord ++ tailWord_5846692) baseStart_5846692 baseEnd_5846692 := by
    simpa [prefixWord, tailWord_5846692, baseEnd_5846692] using wordTrace_append hprefix tailTrace_5846692
  have hstable : (prefixWord ++ tailWord_5846692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846692).length < 2 ^ (prefixWord ++ tailWord_5846692).sum := by decide
  have hdescent : baseEnd_5846692 < baseStart_5846692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846726 : List Nat := [6, 1, 2, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_5846726 : Nat := 118140960795 + 5846726 * 2 ^ 59
def prefixEnd_5846726 : Nat := 4983230072969 + 3 ^ 40 * 5846726 * 2
def baseEnd_5846726 : Nat := 3002180693139396891336403

theorem tailTrace_5846726 : CollatzResearch.WordTrace tailWord_5846726 prefixEnd_5846726 3002180693139396891336403 := by
  unfold tailWord_5846726
  simp only [CollatzResearch.WordTrace]
  refine ⟨6663988006759928692124251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 142165077477545145431984021 6663988006759928692124251)
  ·
    refine ⟨9995982010139893038186377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6663988006759928692124251 9995982010139893038186377)
    ·
      refine ⟨7496986507604919778639783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9995982010139893038186377 7496986507604919778639783)
      ·
        refine ⟨11245479761407379667959675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7496986507604919778639783 11245479761407379667959675)
        ·
          refine ⟨16868219642111069501939513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11245479761407379667959675 16868219642111069501939513)
          ·
            refine ⟨12651164731583302126454635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16868219642111069501939513 12651164731583302126454635)
            ·
              refine ⟨18976747097374953189681953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12651164731583302126454635 18976747097374953189681953)
              ·
                refine ⟨14232560323031214892261465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18976747097374953189681953 14232560323031214892261465)
                ·
                  refine ⟨10674420242273411169196099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14232560323031214892261465 10674420242273411169196099)
                  ·
                    refine ⟨16011630363410116753794149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10674420242273411169196099 16011630363410116753794149)
                    ·
                      refine ⟨3002180693139396891336403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16011630363410116753794149 3002180693139396891336403)
                      ·
                        rfl

theorem cell23_5846726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_5846726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846726 prefixEnd_5846726 := by exact prefixLift 5846726
  have htrace : WordTrace (prefixWord ++ tailWord_5846726) baseStart_5846726 baseEnd_5846726 := by
    simpa [prefixWord, tailWord_5846726, baseEnd_5846726] using wordTrace_append hprefix tailTrace_5846726
  have hstable : (prefixWord ++ tailWord_5846726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846726).length < 2 ^ (prefixWord ++ tailWord_5846726).sum := by decide
  have hdescent : baseEnd_5846726 < baseStart_5846726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846749 : List Nat := [1, 4, 3, 3, 1, 1, 1, 3, 6]
def baseStart_5846749 : Nat := 118140960795 + 5846749 * 2 ^ 59
def prefixEnd_5846749 : Nat := 4983230072969 + 3 ^ 40 * 5846749 * 2
def baseEnd_5846749 : Nat := 333576944799383366816533

theorem tailTrace_5846749 : CollatzResearch.WordTrace tailWord_5846749 prefixEnd_5846749 333576944799383366816533 := by
  unfold tailWord_5846749
  simp only [CollatzResearch.WordTrace]
  refine ⟨213248455095234393076063301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142165636730156262050708867 213248455095234393076063301)
  ·
    refine ⟨39984085330356448701761869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213248455095234393076063301 39984085330356448701761869)
    ·
      refine ⟨14994031998883668263160701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39984085330356448701761869 14994031998883668263160701)
      ·
        refine ⟨5622761999581375598685263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14994031998883668263160701 5622761999581375598685263)
        ·
          refine ⟨8434142999372063398027895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5622761999581375598685263 8434142999372063398027895)
          ·
            refine ⟨12651214499058095097041843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8434142999372063398027895 12651214499058095097041843)
            ·
              refine ⟨18976821748587142645562765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12651214499058095097041843 18976821748587142645562765)
              ·
                refine ⟨7116308155720178492086037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18976821748587142645562765 7116308155720178492086037)
                ·
                  refine ⟨333576944799383366816533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7116308155720178492086037 333576944799383366816533)
                  ·
                    rfl

theorem cell23_5846749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_5846749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846749 prefixEnd_5846749 := by exact prefixLift 5846749
  have htrace : WordTrace (prefixWord ++ tailWord_5846749) baseStart_5846749 baseEnd_5846749 := by
    simpa [prefixWord, tailWord_5846749, baseEnd_5846749] using wordTrace_append hprefix tailTrace_5846749
  have hstable : (prefixWord ++ tailWord_5846749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846749).length < 2 ^ (prefixWord ++ tailWord_5846749).sum := by decide
  have hdescent : baseEnd_5846749 < baseStart_5846749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846762 : List Nat := [3, 1, 3, 1, 1, 1, 5, 2, 1, 5]
def baseStart_5846762 : Nat := 118140960795 + 5846762 * 2 ^ 59
def prefixEnd_5846762 : Nat := 4983230072969 + 3 ^ 40 * 5846762 * 2
def baseEnd_5846762 : Nat := 1000733059480986250162079

theorem tailTrace_5846762 : CollatzResearch.WordTrace tailWord_5846762 prefixEnd_5846762 1000733059480986250162079 := by
  unfold tailWord_5846762
  simp only [CollatzResearch.WordTrace]
  refine ⟨53312232311046824074071635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142165952829458197530857693 53312232311046824074071635)
  ·
    refine ⟨79968348466570236111107453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53312232311046824074071635 79968348466570236111107453)
    ·
      refine ⟨29988130674963838541665295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79968348466570236111107453 29988130674963838541665295)
      ·
        refine ⟨44982196012445757812497943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29988130674963838541665295 44982196012445757812497943)
        ·
          refine ⟨67473294018668636718746915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44982196012445757812497943 67473294018668636718746915)
          ·
            refine ⟨101209941028002955078120373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67473294018668636718746915 101209941028002955078120373)
            ·
              refine ⟨9488431971375277038573785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101209941028002955078120373 9488431971375277038573785)
              ·
                refine ⟨7116323978531457778930339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9488431971375277038573785 7116323978531457778930339)
                ·
                  refine ⟨10674485967797186668395509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7116323978531457778930339 10674485967797186668395509)
                  ·
                    refine ⟨1000733059480986250162079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10674485967797186668395509 1000733059480986250162079)
                    ·
                      rfl

theorem cell23_5846762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_5846762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846762 prefixEnd_5846762 := by exact prefixLift 5846762
  have htrace : WordTrace (prefixWord ++ tailWord_5846762) baseStart_5846762 baseEnd_5846762 := by
    simpa [prefixWord, tailWord_5846762, baseEnd_5846762] using wordTrace_append hprefix tailTrace_5846762
  have hstable : (prefixWord ++ tailWord_5846762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846762).length < 2 ^ (prefixWord ++ tailWord_5846762).sum := by decide
  have hdescent : baseEnd_5846762 < baseStart_5846762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846769 : List Nat := [1, 2, 2, 2, 2, 4, 2, 1, 2, 3, 2]
def baseStart_5846769 : Nat := 118140960795 + 5846769 * 2 ^ 59
def prefixEnd_5846769 : Nat := 4983230072969 + 3 ^ 40 * 5846769 * 2
def baseEnd_5846769 : Nat := 3002202772807540223098705

theorem tailTrace_5846769 : CollatzResearch.WordTrace tailWord_5846769 prefixEnd_5846769 3002202772807540223098705 := by
  unfold tailWord_5846769
  simp only [CollatzResearch.WordTrace]
  refine ⟨213249184555161936491791361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142166123036774624327860907 213249184555161936491791361)
  ·
    refine ⟨159936888416371452368843521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213249184555161936491791361 159936888416371452368843521)
    ·
      refine ⟨119952666312278589276632641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159936888416371452368843521 119952666312278589276632641)
      ·
        refine ⟨89964499734208941957474481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119952666312278589276632641 89964499734208941957474481)
        ·
          refine ⟨67473374800656706468105861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89964499734208941957474481 67473374800656706468105861)
          ·
            refine ⟨12651257775123132462769849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67473374800656706468105861 12651257775123132462769849)
            ·
              refine ⟨9488443331342349347077387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12651257775123132462769849 9488443331342349347077387)
              ·
                refine ⟨14232664997013524020616081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9488443331342349347077387 14232664997013524020616081)
                ·
                  refine ⟨10674498747760143015462061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14232664997013524020616081 10674498747760143015462061)
                  ·
                    refine ⟨4002937030410053630798273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10674498747760143015462061 4002937030410053630798273)
                    ·
                      refine ⟨3002202772807540223098705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4002937030410053630798273 3002202772807540223098705)
                      ·
                        rfl

theorem cell23_5846769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_5846769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846769 prefixEnd_5846769 := by exact prefixLift 5846769
  have htrace : WordTrace (prefixWord ++ tailWord_5846769) baseStart_5846769 baseEnd_5846769 := by
    simpa [prefixWord, tailWord_5846769, baseEnd_5846769] using wordTrace_append hprefix tailTrace_5846769
  have hstable : (prefixWord ++ tailWord_5846769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846769).length < 2 ^ (prefixWord ++ tailWord_5846769).sum := by decide
  have hdescent : baseEnd_5846769 < baseStart_5846769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846775 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 6, 4]
def baseStart_5846775 : Nat := 118140960795 + 5846775 * 2 ^ 59
def prefixEnd_5846775 : Nat := 4983230072969 + 3 ^ 40 * 5846775 * 2
def baseEnd_5846775 : Nat := 1000735284563822399874559

theorem tailTrace_5846775 : CollatzResearch.WordTrace tailWord_5846775 prefixEnd_5846775 1000735284563822399874559 := by
  unfold tailWord_5846775
  simp only [CollatzResearch.WordTrace]
  refine ⟨213249403393140199516509779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142166268928760133011006519 213249403393140199516509779)
  ·
    refine ⟨319874105089710299274764669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213249403393140199516509779 319874105089710299274764669)
    ·
      refine ⟨119952789408641362228036751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319874105089710299274764669 119952789408641362228036751)
      ·
        refine ⟨179929184112962043342055127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119952789408641362228036751 179929184112962043342055127)
        ·
          refine ⟨269893776169443065013082691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179929184112962043342055127 269893776169443065013082691)
          ·
            refine ⟨404840664254164597519624037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269893776169443065013082691 404840664254164597519624037)
            ·
              refine ⟨75907624547655862034929507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 404840664254164597519624037 75907624547655862034929507)
              ·
                refine ⟨113861436821483793052394261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75907624547655862034929507 113861436821483793052394261)
                ·
                  refine ⟨5337254851007052799330981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 113861436821483793052394261 5337254851007052799330981)
                  ·
                    refine ⟨1000735284563822399874559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5337254851007052799330981 1000735284563822399874559)
                    ·
                      rfl

theorem cell23_5846775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 4].length) (baseStart_5846775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846775 prefixEnd_5846775 := by exact prefixLift 5846775
  have htrace : WordTrace (prefixWord ++ tailWord_5846775) baseStart_5846775 baseEnd_5846775 := by
    simpa [prefixWord, tailWord_5846775, baseEnd_5846775] using wordTrace_append hprefix tailTrace_5846775
  have hstable : (prefixWord ++ tailWord_5846775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846775).length < 2 ^ (prefixWord ++ tailWord_5846775).sum := by decide
  have hdescent : baseEnd_5846775 < baseStart_5846775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846805 : List Nat := [1, 3, 2, 1, 2, 3, 3, 8]
def baseStart_5846805 : Nat := 118140960795 + 5846805 * 2 ^ 59
def prefixEnd_5846805 : Nat := 4983230072969 + 3 ^ 40 * 5846805 * 2
def baseEnd_5846805 : Nat := 111193379930040817861057

theorem tailTrace_5846805 : CollatzResearch.WordTrace tailWord_5846805 prefixEnd_5846805 111193379930040817861057 := by
  unfold tailWord_5846805
  simp only [CollatzResearch.WordTrace]
  refine ⟨213250497583031514640101869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142166998388687676426734579 213250497583031514640101869)
  ·
    refine ⟨79968936593636817990038201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213250497583031514640101869 79968936593636817990038201)
    ·
      refine ⟨59976702445227613492528651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79968936593636817990038201 59976702445227613492528651)
      ·
        refine ⟨89965053667841420238792977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59976702445227613492528651 89965053667841420238792977)
        ·
          refine ⟨67473790250881065179094733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89965053667841420238792977 67473790250881065179094733)
          ·
            refine ⟨25302671344080399442160525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67473790250881065179094733 25302671344080399442160525)
            ·
              refine ⟨9488501754030149790810197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25302671344080399442160525 9488501754030149790810197)
              ·
                refine ⟨111193379930040817861057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9488501754030149790810197 111193379930040817861057)
                ·
                  rfl

theorem cell23_5846805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 8].length) (baseStart_5846805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846805 prefixEnd_5846805 := by exact prefixLift 5846805
  have htrace : WordTrace (prefixWord ++ tailWord_5846805) baseStart_5846805 baseEnd_5846805 := by
    simpa [prefixWord, tailWord_5846805, baseEnd_5846805] using wordTrace_append hprefix tailTrace_5846805
  have hstable : (prefixWord ++ tailWord_5846805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846805).length < 2 ^ (prefixWord ++ tailWord_5846805).sum := by decide
  have hdescent : baseEnd_5846805 < baseStart_5846805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846812 : List Nat := [2, 2, 3, 1, 1, 2, 4, 1, 1, 2, 4]
def baseStart_5846812 : Nat := 118140960795 + 5846812 * 2 ^ 59
def prefixEnd_5846812 : Nat := 4983230072969 + 3 ^ 40 * 5846812 * 2
def baseEnd_5846812 : Nat := 3002224852475683554861007

theorem tailTrace_5846812 : CollatzResearch.WordTrace tailWord_5846812 prefixEnd_5846812 3002224852475683554861007 := by
  unfold tailWord_5846812
  simp only [CollatzResearch.WordTrace]
  refine ⟨106625376447003077417803345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142167168596004103223737793 106625376447003077417803345)
  ·
    refine ⟨79969032335252308063352509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106625376447003077417803345 79969032335252308063352509)
    ·
      refine ⟨29988387125719615523757191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79969032335252308063352509 29988387125719615523757191)
      ·
        refine ⟨44982580688579423285635787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29988387125719615523757191 44982580688579423285635787)
        ·
          refine ⟨67473871032869134928453681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44982580688579423285635787 67473871032869134928453681)
          ·
            refine ⟨50605403274651851196340261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67473871032869134928453681 50605403274651851196340261)
            ·
              refine ⟨9488513113997222099313799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50605403274651851196340261 9488513113997222099313799)
              ·
                refine ⟨14232769670995833148970699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9488513113997222099313799 14232769670995833148970699)
                ·
                  refine ⟨21349154506493749723456049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14232769670995833148970699 21349154506493749723456049)
                  ·
                    refine ⟨16011865879870312292592037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21349154506493749723456049 16011865879870312292592037)
                    ·
                      refine ⟨3002224852475683554861007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16011865879870312292592037 3002224852475683554861007)
                      ·
                        rfl

theorem cell23_5846812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_5846812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846812 prefixEnd_5846812 := by exact prefixLift 5846812
  have htrace : WordTrace (prefixWord ++ tailWord_5846812) baseStart_5846812 baseEnd_5846812 := by
    simpa [prefixWord, tailWord_5846812, baseEnd_5846812] using wordTrace_append hprefix tailTrace_5846812
  have hstable : (prefixWord ++ tailWord_5846812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846812).length < 2 ^ (prefixWord ++ tailWord_5846812).sum := by decide
  have hdescent : baseEnd_5846812 < baseStart_5846812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846833 : List Nat := [1, 2, 2, 3, 2, 3, 2, 3, 1, 2, 2]
def baseStart_5846833 : Nat := 118140960795 + 5846833 * 2 ^ 59
def prefixEnd_5846833 : Nat := 4983230072969 + 3 ^ 40 * 5846833 * 2
def baseEnd_5846833 : Nat := 3002235635569427972698411

theorem tailTrace_5846833 : CollatzResearch.WordTrace tailWord_5846833 prefixEnd_5846833 3002235635569427972698411 := by
  unfold tailWord_5846833
  simp only [CollatzResearch.WordTrace]
  refine ⟨213251518826930075422121153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142167679217953383614747435 213251518826930075422121153)
  ·
    refine ⟨159938639120197556566590865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213251518826930075422121153 159938639120197556566590865)
    ·
      refine ⟨119953979340148167424943149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159938639120197556566590865 119953979340148167424943149)
      ·
        refine ⟨44982742252555562784353681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119953979340148167424943149 44982742252555562784353681)
        ·
          refine ⟨33737056689416672088265261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44982742252555562784353681 33737056689416672088265261)
          ·
            refine ⟨12651396258531252033099473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33737056689416672088265261 12651396258531252033099473)
            ·
              refine ⟨9488547193898439024824605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12651396258531252033099473 9488547193898439024824605)
              ·
                refine ⟨3558205197711914634309227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9488547193898439024824605 3558205197711914634309227)
                ·
                  refine ⟨5337307796567871951463841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3558205197711914634309227 5337307796567871951463841)
                  ·
                    refine ⟨4002980847425903963597881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5337307796567871951463841 4002980847425903963597881)
                    ·
                      refine ⟨3002235635569427972698411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4002980847425903963597881 3002235635569427972698411)
                      ·
                        rfl

theorem cell23_5846833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_5846833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846833 prefixEnd_5846833 := by exact prefixLift 5846833
  have htrace : WordTrace (prefixWord ++ tailWord_5846833) baseStart_5846833 baseEnd_5846833 := by
    simpa [prefixWord, tailWord_5846833, baseEnd_5846833] using wordTrace_append hprefix tailTrace_5846833
  have hstable : (prefixWord ++ tailWord_5846833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846833).length < 2 ^ (prefixWord ++ tailWord_5846833).sum := by decide
  have hdescent : baseEnd_5846833 < baseStart_5846833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846836 : List Nat := [2, 5, 1, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_5846836 : Nat := 118140960795 + 5846836 * 2 ^ 59
def prefixEnd_5846836 : Nat := 4983230072969 + 3 ^ 40 * 5846836 * 2
def baseEnd_5846836 : Nat := 3002237176011391460960897

theorem tailTrace_5846836 : CollatzResearch.WordTrace tailWord_5846836 prefixEnd_5846836 3002237176011391460960897 := by
  unfold tailWord_5846836
  simp only [CollatzResearch.WordTrace]
  refine ⟨106625814122959603467240181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142167752163946137956320241 106625814122959603467240181)
  ·
    refine ⟨9996170074027462825053767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106625814122959603467240181 9996170074027462825053767)
    ·
      refine ⟨14994255111041194237580651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9996170074027462825053767 14994255111041194237580651)
      ·
        refine ⟨22491382666561791356370977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14994255111041194237580651 22491382666561791356370977)
        ·
          refine ⟨16868536999921343517278233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22491382666561791356370977 16868536999921343517278233)
          ·
            refine ⟨12651402749941007637958675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16868536999921343517278233 12651402749941007637958675)
            ·
              refine ⟨18977104124911511456938013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12651402749941007637958675 18977104124911511456938013)
              ·
                refine ⟨7116414046841816796351755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18977104124911511456938013 7116414046841816796351755)
                ·
                  refine ⟨10674621070262725194527633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7116414046841816796351755 10674621070262725194527633)
                  ·
                    refine ⟨8005965802697043895895725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10674621070262725194527633 8005965802697043895895725)
                    ·
                      refine ⟨3002237176011391460960897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8005965802697043895895725 3002237176011391460960897)
                      ·
                        rfl

theorem cell23_5846836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_5846836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846836 prefixEnd_5846836 := by exact prefixLift 5846836
  have htrace : WordTrace (prefixWord ++ tailWord_5846836) baseStart_5846836 baseEnd_5846836 := by
    simpa [prefixWord, tailWord_5846836, baseEnd_5846836] using wordTrace_append hprefix tailTrace_5846836
  have hstable : (prefixWord ++ tailWord_5846836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846836).length < 2 ^ (prefixWord ++ tailWord_5846836).sum := by decide
  have hdescent : baseEnd_5846836 < baseStart_5846836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846855 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 4]
def baseStart_5846855 : Nat := 118140960795 + 5846855 * 2 ^ 59
def prefixEnd_5846855 : Nat := 4983230072969 + 3 ^ 40 * 5846855 * 2
def baseEnd_5846855 : Nat := 3002246932143826886623309

theorem tailTrace_5846855 : CollatzResearch.WordTrace tailWord_5846855 prefixEnd_5846855 3002246932143826886623309 := by
  unfold tailWord_5846855
  simp only [CollatzResearch.WordTrace]
  refine ⟨213252321232850373179422019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142168214155233582119614679 213252321232850373179422019)
  ·
    refine ⟨319878481849275559769133029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213252321232850373179422019 319878481849275559769133029)
    ·
      refine ⟨59977215346739167456712443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319878481849275559769133029 59977215346739167456712443)
      ·
        refine ⟨89965823020108751185068665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59977215346739167456712443 89965823020108751185068665)
        ·
          refine ⟨67474367265081563388801499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89965823020108751185068665 67474367265081563388801499)
          ·
            refine ⟨101211550897622345083202249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67474367265081563388801499 101211550897622345083202249)
            ·
              refine ⟨75908663173216758812401687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101211550897622345083202249 75908663173216758812401687)
              ·
                refine ⟨113862994759825138218602531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75908663173216758812401687 113862994759825138218602531)
                ·
                  refine ⟨170794492139737707327903797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113862994759825138218602531 170794492139737707327903797)
                  ·
                    refine ⟨16011983638100410061990981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 170794492139737707327903797 16011983638100410061990981)
                    ·
                      refine ⟨3002246932143826886623309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16011983638100410061990981 3002246932143826886623309)
                      ·
                        rfl

theorem cell23_5846855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_5846855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846855 prefixEnd_5846855 := by exact prefixLift 5846855
  have htrace : WordTrace (prefixWord ++ tailWord_5846855) baseStart_5846855 baseEnd_5846855 := by
    simpa [prefixWord, tailWord_5846855, baseEnd_5846855] using wordTrace_append hprefix tailTrace_5846855
  have hstable : (prefixWord ++ tailWord_5846855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846855).length < 2 ^ (prefixWord ++ tailWord_5846855).sum := by decide
  have hdescent : baseEnd_5846855 < baseStart_5846855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846892 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 5]
def baseStart_5846892 : Nat := 118140960795 + 5846892 * 2 ^ 59
def prefixEnd_5846892 : Nat := 4983230072969 + 3 ^ 40 * 5846892 * 2
def baseEnd_5846892 : Nat := 3002265930928043241860639

theorem tailTrace_5846892 : CollatzResearch.WordTrace tailWord_5846892 prefixEnd_5846892 3002265930928043241860639 := by
  unfold tailWord_5846892
  simp only [CollatzResearch.WordTrace]
  refine ⟨106626835366858164249259465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142169113822477552332345953 106626835366858164249259465)
  ·
    refine ⟨79970126525143623186944599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106626835366858164249259465 79970126525143623186944599)
    ·
      refine ⟨119955189787715434780416899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79970126525143623186944599 119955189787715434780416899)
      ·
        refine ⟨179932784681573152170625349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119955189787715434780416899 179932784681573152170625349)
        ·
          refine ⟨33737397127794966031992253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179932784681573152170625349 33737397127794966031992253)
          ·
            refine ⟨12651523922923112261997095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33737397127794966031992253 12651523922923112261997095)
            ·
              refine ⟨18977285884384668392995643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12651523922923112261997095 18977285884384668392995643)
              ·
                refine ⟨28465928826577002589493465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18977285884384668392995643 28465928826577002589493465)
                ·
                  refine ⟨21349446619932751942120099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28465928826577002589493465 21349446619932751942120099)
                  ·
                    refine ⟨32024169929899127913180149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21349446619932751942120099 32024169929899127913180149)
                    ·
                      refine ⟨3002265930928043241860639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32024169929899127913180149 3002265930928043241860639)
                      ·
                        rfl

theorem cell23_5846892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_5846892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846892 prefixEnd_5846892 := by exact prefixLift 5846892
  have htrace : WordTrace (prefixWord ++ tailWord_5846892) baseStart_5846892 baseEnd_5846892 := by
    simpa [prefixWord, tailWord_5846892, baseEnd_5846892] using wordTrace_append hprefix tailTrace_5846892
  have hstable : (prefixWord ++ tailWord_5846892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846892).length < 2 ^ (prefixWord ++ tailWord_5846892).sum := by decide
  have hdescent : baseEnd_5846892 < baseStart_5846892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5846905 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 1, 2, 7]
def baseStart_5846905 : Nat := 118140960795 + 5846905 * 2 ^ 59
def prefixEnd_5846905 : Nat := 4983230072969 + 3 ^ 40 * 5846905 * 2
def baseEnd_5846905 : Nat := 3002272606176551690998079

theorem tailTrace_5846905 : CollatzResearch.WordTrace tailWord_5846905 prefixEnd_5846905 3002272606176551690998079 := by
  unfold tailWord_5846905
  simp only [CollatzResearch.WordTrace]
  refine ⟨213254144882669231718742169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142169429921779487812494779 213254144882669231718742169)
  ·
    refine ⟨159940608662001923789056627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213254144882669231718742169 159940608662001923789056627)
    ·
      refine ⟨239910912993002885683584941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159940608662001923789056627 239910912993002885683584941)
      ·
        refine ⟨89966592372376082131344353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239910912993002885683584941 89966592372376082131344353)
        ·
          refine ⟨67474944279282061598508265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89966592372376082131344353 67474944279282061598508265)
          ·
            refine ⟨50606208209461546198881199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67474944279282061598508265 50606208209461546198881199)
            ·
              refine ⟨75909312314192319298321799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50606208209461546198881199 75909312314192319298321799)
              ·
                refine ⟨113863968471288478947482699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75909312314192319298321799 113863968471288478947482699)
                ·
                  refine ⟨170795952706932718421224049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113863968471288478947482699 170795952706932718421224049)
                  ·
                    refine ⟨128096964530199538815918037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 170795952706932718421224049 128096964530199538815918037)
                    ·
                      refine ⟨3002272606176551690998079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128096964530199538815918037 3002272606176551690998079)
                      ·
                        rfl

theorem cell23_5846905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_5846905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5846905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5846905 prefixEnd_5846905 := by exact prefixLift 5846905
  have htrace : WordTrace (prefixWord ++ tailWord_5846905) baseStart_5846905 baseEnd_5846905 := by
    simpa [prefixWord, tailWord_5846905, baseEnd_5846905] using wordTrace_append hprefix tailTrace_5846905
  have hstable : (prefixWord ++ tailWord_5846905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5846905).length < 2 ^ (prefixWord ++ tailWord_5846905).sum := by decide
  have hdescent : baseEnd_5846905 < baseStart_5846905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5846905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847032 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 5, 5]
def baseStart_5847032 : Nat := 118140960795 + 5847032 * 2 ^ 59
def prefixEnd_5847032 : Nat := 4983230072969 + 3 ^ 40 * 5847032 * 2
def baseEnd_5847032 : Nat := 1000779272739890898036665

theorem tailTrace_5847032 : CollatzResearch.WordTrace tailWord_5847032 prefixEnd_5847032 1000779272739890898036665 := by
  unfold tailWord_5847032
  simp only [CollatzResearch.WordTrace]
  refine ⟨106629388476604566204307675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142172517968806088272410233 106629388476604566204307675)
  ·
    refine ⟨159944082714906849306461513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106629388476604566204307675 159944082714906849306461513)
    ·
      refine ⟨119958062036180136979846135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159944082714906849306461513 119958062036180136979846135)
      ·
        refine ⟨179937093054270205469769203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119958062036180136979846135 179937093054270205469769203)
        ·
          refine ⟨269905639581405308204653805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179937093054270205469769203 269905639581405308204653805)
          ·
            refine ⟨101214614843026990576745177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 269905639581405308204653805 101214614843026990576745177)
            ·
              refine ⟨75910961132270242932558883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101214614843026990576745177 75910961132270242932558883)
              ·
                refine ⟨113866441698405364398838325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75910961132270242932558883 113866441698405364398838325)
                ·
                  refine ⟨10674978909225502912391093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113866441698405364398838325 10674978909225502912391093)
                  ·
                    refine ⟨1000779272739890898036665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10674978909225502912391093 1000779272739890898036665)
                    ·
                      rfl

theorem cell23_5847032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_5847032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847032 prefixEnd_5847032 := by exact prefixLift 5847032
  have htrace : WordTrace (prefixWord ++ tailWord_5847032) baseStart_5847032 baseEnd_5847032 := by
    simpa [prefixWord, tailWord_5847032, baseEnd_5847032] using wordTrace_append hprefix tailTrace_5847032
  have hstable : (prefixWord ++ tailWord_5847032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847032).length < 2 ^ (prefixWord ++ tailWord_5847032).sum := by decide
  have hdescent : baseEnd_5847032 < baseStart_5847032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847073 : List Nat := [1, 2, 3, 2, 4, 1, 1, 2, 2, 3, 2]
def baseStart_5847073 : Nat := 118140960795 + 5847073 * 2 ^ 59
def prefixEnd_5847073 : Nat := 4983230072969 + 3 ^ 40 * 5847073 * 2
def baseEnd_5847073 : Nat := 3002358870926507033697307

theorem tailTrace_5847073 : CollatzResearch.WordTrace tailWord_5847073 prefixEnd_5847073 3002358870926507033697307 := by
  unfold tailWord_5847073
  simp only [CollatzResearch.WordTrace]
  refine ⟨213260272346060596410857873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142173514897373730940571915 213260272346060596410857873)
  ·
    refine ⟨159945204259545447308143405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213260272346060596410857873 159945204259545447308143405)
    ·
      refine ⟨59979451597329542740553777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159945204259545447308143405 59979451597329542740553777)
      ·
        refine ⟨44984588697997157055415333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59979451597329542740553777 44984588697997157055415333)
        ·
          refine ⟨8434610380874466947890375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44984588697997157055415333 8434610380874466947890375)
          ·
            refine ⟨12651915571311700421835563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8434610380874466947890375 12651915571311700421835563)
            ·
              refine ⟨18977873356967550632753345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12651915571311700421835563 18977873356967550632753345)
              ·
                refine ⟨14233405017725662974565009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18977873356967550632753345 14233405017725662974565009)
                ·
                  refine ⟨10675053763294247230923757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14233405017725662974565009 10675053763294247230923757)
                  ·
                    refine ⟨4003145161235342711596409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10675053763294247230923757 4003145161235342711596409)
                    ·
                      refine ⟨3002358870926507033697307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4003145161235342711596409 3002358870926507033697307)
                      ·
                        rfl

theorem cell23_5847073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_5847073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847073 prefixEnd_5847073 := by exact prefixLift 5847073
  have htrace : WordTrace (prefixWord ++ tailWord_5847073) baseStart_5847073 baseEnd_5847073 := by
    simpa [prefixWord, tailWord_5847073, baseEnd_5847073] using wordTrace_append hprefix tailTrace_5847073
  have hstable : (prefixWord ++ tailWord_5847073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847073).length < 2 ^ (prefixWord ++ tailWord_5847073).sum := by decide
  have hdescent : baseEnd_5847073 < baseStart_5847073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847089 : List Nat := [1, 2, 2, 3, 1, 3, 2, 2, 1, 1, 5]
def baseStart_5847089 : Nat := 118140960795 + 5847089 * 2 ^ 59
def prefixEnd_5847089 : Nat := 4983230072969 + 3 ^ 40 * 5847089 * 2
def baseEnd_5847089 : Nat := 3002367086616978971097233

theorem tailTrace_5847089 : CollatzResearch.WordTrace tailWord_5847089 prefixEnd_5847089 3002367086616978971097233 := by
  unfold tailWord_5847089
  simp only [CollatzResearch.WordTrace]
  refine ⟨213260855914002631143440321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142173903942668420762293547 213260855914002631143440321)
  ·
    refine ⟨159945641935501973357580241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213260855914002631143440321 159945641935501973357580241)
    ·
      refine ⟨119959231451626480018185181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159945641935501973357580241 119959231451626480018185181)
      ·
        refine ⟨44984711794359930006819443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119959231451626480018185181 44984711794359930006819443)
        ·
          refine ⟨67477067691539895010229165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44984711794359930006819443 67477067691539895010229165)
          ·
            refine ⟨25303900384327460628835937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67477067691539895010229165 25303900384327460628835937)
            ·
              refine ⟨18977925288245595471626953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25303900384327460628835937 18977925288245595471626953)
              ·
                refine ⟨14233443966184196603720215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18977925288245595471626953 14233443966184196603720215)
                ·
                  refine ⟨21350165949276294905580323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14233443966184196603720215 21350165949276294905580323)
                  ·
                    refine ⟨32025248923914442358370485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21350165949276294905580323 32025248923914442358370485)
                    ·
                      refine ⟨3002367086616978971097233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32025248923914442358370485 3002367086616978971097233)
                      ·
                        rfl

theorem cell23_5847089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_5847089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847089 prefixEnd_5847089 := by exact prefixLift 5847089
  have htrace : WordTrace (prefixWord ++ tailWord_5847089) baseStart_5847089 baseEnd_5847089 := by
    simpa [prefixWord, tailWord_5847089, baseEnd_5847089] using wordTrace_append hprefix tailTrace_5847089
  have hstable : (prefixWord ++ tailWord_5847089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847089).length < 2 ^ (prefixWord ++ tailWord_5847089).sum := by decide
  have hdescent : baseEnd_5847089 < baseStart_5847089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847119 : List Nat := [1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 3]
def baseStart_5847119 : Nat := 118140960795 + 5847119 * 2 ^ 59
def prefixEnd_5847119 : Nat := 4983230072969 + 3 ^ 40 * 5847119 * 2
def baseEnd_5847119 : Nat := 3002382491036613853722095

theorem tailTrace_5847119 : CollatzResearch.WordTrace tailWord_5847119 prefixEnd_5847119 3002382491036613853722095 := by
  unfold tailWord_5847119
  simp only [CollatzResearch.WordTrace]
  refine ⟨213261950103893946267032411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142174633402595964178021607 213261950103893946267032411)
  ·
    refine ⟨319892925155840919400548617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213261950103893946267032411 319892925155840919400548617)
    ·
      refine ⟨239919693866880689550411463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319892925155840919400548617 239919693866880689550411463)
      ·
        refine ⟨359879540800321034325617195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239919693866880689550411463 359879540800321034325617195)
        ·
          refine ⟨539819311200481551488425793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359879540800321034325617195 539819311200481551488425793)
          ·
            refine ⟨404864483400361163616319345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 539819311200481551488425793 404864483400361163616319345)
            ·
              refine ⟨303648362550270872712239509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404864483400361163616319345 303648362550270872712239509)
              ·
                refine ⟨14233516994543947158386227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 303648362550270872712239509 14233516994543947158386227)
                ·
                  refine ⟨21350275491815920737579341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14233516994543947158386227 21350275491815920737579341)
                  ·
                    refine ⟨8006353309430970276592253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21350275491815920737579341 8006353309430970276592253)
                    ·
                      refine ⟨3002382491036613853722095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8006353309430970276592253 3002382491036613853722095)
                      ·
                        rfl

theorem cell23_5847119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 3].length) (baseStart_5847119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847119 prefixEnd_5847119 := by exact prefixLift 5847119
  have htrace : WordTrace (prefixWord ++ tailWord_5847119) baseStart_5847119 baseEnd_5847119 := by
    simpa [prefixWord, tailWord_5847119, baseEnd_5847119] using wordTrace_append hprefix tailTrace_5847119
  have hstable : (prefixWord ++ tailWord_5847119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847119).length < 2 ^ (prefixWord ++ tailWord_5847119).sum := by decide
  have hdescent : baseEnd_5847119 < baseStart_5847119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847126 : List Nat := [5, 2, 2, 1, 1, 12]
def baseStart_5847126 : Nat := 118140960795 + 5847126 * 2 ^ 59
def prefixEnd_5847126 : Nat := 4983230072969 + 3 ^ 40 * 5847126 * 2
def baseEnd_5847126 : Nat := 12355498293832079532241

theorem tailTrace_5847126 : CollatzResearch.WordTrace tailWord_5847126 prefixEnd_5847126 12355498293832079532241 := by
  unfold tailWord_5847126
  simp only [CollatzResearch.WordTrace]
  refine ⟨13328887838429286653908577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142174803609912390975024821 13328887838429286653908577)
  ·
    refine ⟨9996665878821964990431433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13328887838429286653908577 9996665878821964990431433)
    ·
      refine ⟨7497499409116473742823575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9996665878821964990431433 7497499409116473742823575)
      ·
        refine ⟨11246249113674710614235363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7497499409116473742823575 11246249113674710614235363)
        ·
          refine ⟨16869373670512065921353045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11246249113674710614235363 16869373670512065921353045)
          ·
            refine ⟨12355498293832079532241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 16869373670512065921353045 12355498293832079532241)
            ·
              rfl

theorem cell23_5847126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 12].length) (baseStart_5847126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847126 prefixEnd_5847126 := by exact prefixLift 5847126
  have htrace : WordTrace (prefixWord ++ tailWord_5847126) baseStart_5847126 baseEnd_5847126 := by
    simpa [prefixWord, tailWord_5847126, baseEnd_5847126] using wordTrace_append hprefix tailTrace_5847126
  have hstable : (prefixWord ++ tailWord_5847126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847126).length < 2 ^ (prefixWord ++ tailWord_5847126).sum := by decide
  have hdescent : baseEnd_5847126 < baseStart_5847126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847189 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 4, 2, 4]
def baseStart_5847189 : Nat := 118140960795 + 5847189 * 2 ^ 59
def prefixEnd_5847189 : Nat := 4983230072969 + 3 ^ 40 * 5847189 * 2
def baseEnd_5847189 : Nat := 3002418434682428579846773

theorem tailTrace_5847189 : CollatzResearch.WordTrace tailWord_5847189 prefixEnd_5847189 3002418434682428579846773 := by
  unfold tailWord_5847189
  simp only [CollatzResearch.WordTrace]
  refine ⟨213264503213640348222080621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142176335475760232148053747 213264503213640348222080621)
  ·
    refine ⟨79974188705115130583280233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213264503213640348222080621 79974188705115130583280233)
    ·
      refine ⟨59980641528836347937460175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79974188705115130583280233 59980641528836347937460175)
      ·
        refine ⟨89970962293254521906190263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59980641528836347937460175 89970962293254521906190263)
        ·
          refine ⟨134956443439881782859285395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89970962293254521906190263 134956443439881782859285395)
          ·
            refine ⟨202434665159822674288928093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134956443439881782859285395 202434665159822674288928093)
            ·
              refine ⟨75912999434933502858348035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202434665159822674288928093 75912999434933502858348035)
              ·
                refine ⟨113869499152400254287522053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75912999434933502858348035 113869499152400254287522053)
                ·
                  refine ⟨21350531091075047678910385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113869499152400254287522053 21350531091075047678910385)
                  ·
                    refine ⟨16012898318306285759182789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21350531091075047678910385 16012898318306285759182789)
                    ·
                      refine ⟨3002418434682428579846773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16012898318306285759182789 3002418434682428579846773)
                      ·
                        rfl

theorem cell23_5847189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_5847189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847189 prefixEnd_5847189 := by exact prefixLift 5847189
  have htrace : WordTrace (prefixWord ++ tailWord_5847189) baseStart_5847189 baseEnd_5847189 := by
    simpa [prefixWord, tailWord_5847189, baseEnd_5847189] using wordTrace_append hprefix tailTrace_5847189
  have hstable : (prefixWord ++ tailWord_5847189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847189).length < 2 ^ (prefixWord ++ tailWord_5847189).sum := by decide
  have hdescent : baseEnd_5847189 < baseStart_5847189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847214 : List Nat := [4, 1, 4, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_5847214 : Nat := 118140960795 + 5847214 * 2 ^ 59
def prefixEnd_5847214 : Nat := 4983230072969 + 3 ^ 40 * 5847214 * 2
def baseEnd_5847214 : Nat := 3002431271698790982034159

theorem tailTrace_5847214 : CollatzResearch.WordTrace tailWord_5847214 prefixEnd_5847214 3002431271698790982034159 := by
  unfold tailWord_5847214
  simp only [CollatzResearch.WordTrace]
  refine ⟨26658176879818722186467587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142176943359033184994493797 26658176879818722186467587)
  ·
    refine ⟨39987265319728083279701381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26658176879818722186467587 39987265319728083279701381)
    ·
      refine ⟨7497612247449015614944009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39987265319728083279701381 7497612247449015614944009)
      ·
        refine ⟨5623209185586761711208007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7497612247449015614944009 5623209185586761711208007)
        ·
          refine ⟨8434813778380142566812011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5623209185586761711208007 8434813778380142566812011)
          ·
            refine ⟨12652220667570213850218017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8434813778380142566812011 12652220667570213850218017)
            ·
              refine ⟨9489165500677660387663513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12652220667570213850218017 9489165500677660387663513)
              ·
                refine ⟨7116874125508245290747635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9489165500677660387663513 7116874125508245290747635)
                ·
                  refine ⟨10675311188262367936121453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7116874125508245290747635 10675311188262367936121453)
                  ·
                    refine ⟨4003241695598387976045545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10675311188262367936121453 4003241695598387976045545)
                    ·
                      refine ⟨3002431271698790982034159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4003241695598387976045545 3002431271698790982034159)
                      ·
                        rfl

theorem cell23_5847214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_5847214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847214 prefixEnd_5847214 := by exact prefixLift 5847214
  have htrace : WordTrace (prefixWord ++ tailWord_5847214) baseStart_5847214 baseEnd_5847214 := by
    simpa [prefixWord, tailWord_5847214, baseEnd_5847214] using wordTrace_append hprefix tailTrace_5847214
  have hstable : (prefixWord ++ tailWord_5847214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847214).length < 2 ^ (prefixWord ++ tailWord_5847214).sum := by decide
  have hdescent : baseEnd_5847214 < baseStart_5847214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847246 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 4, 5]
def baseStart_5847246 : Nat := 118140960795 + 5847246 * 2 ^ 59
def prefixEnd_5847246 : Nat := 4983230072969 + 3 ^ 40 * 5847246 * 2
def baseEnd_5847246 : Nat := 1000815901026578285611337

theorem tailTrace_5847246 : CollatzResearch.WordTrace tailWord_5847246 prefixEnd_5847246 1000815901026578285611337 := by
  unfold tailWord_5847246
  simp only [CollatzResearch.WordTrace]
  refine ⟨26658322771804230869613199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142177721449622564637937061 26658322771804230869613199)
  ·
    refine ⟨39987484157706346304419799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26658322771804230869613199 39987484157706346304419799)
    ·
      refine ⟨59981226236559519456629699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39987484157706346304419799 59981226236559519456629699)
      ·
        refine ⟨89971839354839279184944549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59981226236559519456629699 89971839354839279184944549)
        ·
          refine ⟨16869719879032364847177103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89971839354839279184944549 16869719879032364847177103)
          ·
            refine ⟨25304579818548547270765655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16869719879032364847177103 25304579818548547270765655)
            ·
              refine ⟨37956869727822820906148483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25304579818548547270765655 37956869727822820906148483)
              ·
                refine ⟨56935304591734231359222725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37956869727822820906148483 56935304591734231359222725)
                ·
                  refine ⟨10675369610950168379854261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56935304591734231359222725 10675369610950168379854261)
                  ·
                    refine ⟨1000815901026578285611337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10675369610950168379854261 1000815901026578285611337)
                    ·
                      rfl

theorem cell23_5847246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_5847246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847246 prefixEnd_5847246 := by exact prefixLift 5847246
  have htrace : WordTrace (prefixWord ++ tailWord_5847246) baseStart_5847246 baseEnd_5847246 := by
    simpa [prefixWord, tailWord_5847246, baseEnd_5847246] using wordTrace_append hprefix tailTrace_5847246
  have hstable : (prefixWord ++ tailWord_5847246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847246).length < 2 ^ (prefixWord ++ tailWord_5847246).sum := by decide
  have hdescent : baseEnd_5847246 < baseStart_5847246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847250 : List Nat := [3, 2, 2, 2, 1, 3, 3, 2, 5]
def baseStart_5847250 : Nat := 118140960795 + 5847250 * 2 ^ 59
def prefixEnd_5847250 : Nat := 4983230072969 + 3 ^ 40 * 5847250 * 2
def baseEnd_5847250 : Nat := 333605528555816982353777

theorem tailTrace_5847250 : CollatzResearch.WordTrace tailWord_5847250 prefixEnd_5847250 333605528555816982353777 := by
  unfold tailWord_5847250
  simp only [CollatzResearch.WordTrace]
  refine ⟨53316682016604838910012801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142177818710946237093367469 53316682016604838910012801)
  ·
    refine ⟨39987511512453629182509601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53316682016604838910012801 39987511512453629182509601)
    ·
      refine ⟨29990633634340221886882201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39987511512453629182509601 29990633634340221886882201)
      ·
        refine ⟨22492975225755166415161651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29990633634340221886882201 22492975225755166415161651)
        ·
          refine ⟨33739462838632749622742477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22492975225755166415161651 33739462838632749622742477)
          ·
            refine ⟨12652298564487281108528429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33739462838632749622742477 12652298564487281108528429)
            ·
              refine ⟨4744611961682730415698161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12652298564487281108528429 4744611961682730415698161)
              ·
                refine ⟨3558458971262047811773621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4744611961682730415698161 3558458971262047811773621)
                ·
                  refine ⟨333605528555816982353777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3558458971262047811773621 333605528555816982353777)
                  ·
                    rfl

theorem cell23_5847250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_5847250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847250 prefixEnd_5847250 := by exact prefixLift 5847250
  have htrace : WordTrace (prefixWord ++ tailWord_5847250) baseStart_5847250 baseEnd_5847250 := by
    simpa [prefixWord, tailWord_5847250, baseEnd_5847250] using wordTrace_append hprefix tailTrace_5847250
  have hstable : (prefixWord ++ tailWord_5847250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847250).length < 2 ^ (prefixWord ++ tailWord_5847250).sum := by decide
  have hdescent : baseEnd_5847250 < baseStart_5847250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847256 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 1, 2, 5]
def baseStart_5847256 : Nat := 118140960795 + 5847256 * 2 ^ 59
def prefixEnd_5847256 : Nat := 4983230072969 + 3 ^ 40 * 5847256 * 2
def baseEnd_5847256 : Nat := 3002452837886279817708965

theorem tailTrace_5847256 : CollatzResearch.WordTrace tailWord_5847256 prefixEnd_5847256 3002452837886279817708965 := by
  unfold tailWord_5847256
  simp only [CollatzResearch.WordTrace]
  refine ⟨106633473452198809332384811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142177964602931745776513081 106633473452198809332384811)
  ·
    refine ⟨159950210178298213998577217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106633473452198809332384811 159950210178298213998577217)
    ·
      refine ⟨119962657633723660498932913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159950210178298213998577217 119962657633723660498932913)
      ·
        refine ⟨89971993225292745374199685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119962657633723660498932913 89971993225292745374199685)
        ·
          refine ⟨16869748729742389757662441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89971993225292745374199685 16869748729742389757662441)
          ·
            refine ⟨12652311547306792318246831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16869748729742389757662441 12652311547306792318246831)
            ·
              refine ⟨18978467320960188477370247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12652311547306792318246831 18978467320960188477370247)
              ·
                refine ⟨28467700981440282716055371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18978467320960188477370247 28467700981440282716055371)
                ·
                  refine ⟨42701551472160424074083057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28467700981440282716055371 42701551472160424074083057)
                  ·
                    refine ⟨32026163604120318055562293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42701551472160424074083057 32026163604120318055562293)
                    ·
                      refine ⟨3002452837886279817708965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32026163604120318055562293 3002452837886279817708965)
                      ·
                        rfl

theorem cell23_5847256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_5847256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847256 prefixEnd_5847256 := by exact prefixLift 5847256
  have htrace : WordTrace (prefixWord ++ tailWord_5847256) baseStart_5847256 baseEnd_5847256 := by
    simpa [prefixWord, tailWord_5847256, baseEnd_5847256] using wordTrace_append hprefix tailTrace_5847256
  have hstable : (prefixWord ++ tailWord_5847256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847256).length < 2 ^ (prefixWord ++ tailWord_5847256).sum := by decide
  have hdescent : baseEnd_5847256 < baseStart_5847256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847276 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 5, 4]
def baseStart_5847276 : Nat := 118140960795 + 5847276 * 2 ^ 59
def prefixEnd_5847276 : Nat := 4983230072969 + 3 ^ 40 * 5847276 * 2
def baseEnd_5847276 : Nat := 1000821035833123246486291

theorem tailTrace_5847276 : CollatzResearch.WordTrace tailWord_5847276 prefixEnd_5847276 1000821035833123246486291 := by
  unfold tailWord_5847276
  simp only [CollatzResearch.WordTrace]
  refine ⟨106633838182162581040248841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142178450909550108053665121 106633838182162581040248841)
  ·
    refine ⟨79975378636621935780186631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106633838182162581040248841 79975378636621935780186631)
    ·
      refine ⟨119963067954932903670279947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79975378636621935780186631 119963067954932903670279947)
      ·
        refine ⟨179944601932399355505419921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119963067954932903670279947 179944601932399355505419921)
        ·
          refine ⟨134958451449299516629064941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179944601932399355505419921 134958451449299516629064941)
          ·
            refine ⟨50609419293487318735899353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134958451449299516629064941 50609419293487318735899353)
            ·
              refine ⟨37957064470115489051924515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50609419293487318735899353 37957064470115489051924515)
              ·
                refine ⟨56935596705173233577886773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37957064470115489051924515 56935596705173233577886773)
                ·
                  refine ⟨5337712191109990647926885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56935596705173233577886773 5337712191109990647926885)
                  ·
                    refine ⟨1000821035833123246486291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5337712191109990647926885 1000821035833123246486291)
                    ·
                      rfl

theorem cell23_5847276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 4].length) (baseStart_5847276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847276 prefixEnd_5847276 := by exact prefixLift 5847276
  have htrace : WordTrace (prefixWord ++ tailWord_5847276) baseStart_5847276 baseEnd_5847276 := by
    simpa [prefixWord, tailWord_5847276, baseEnd_5847276] using wordTrace_append hprefix tailTrace_5847276
  have hstable : (prefixWord ++ tailWord_5847276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847276).length < 2 ^ (prefixWord ++ tailWord_5847276).sum := by decide
  have hdescent : baseEnd_5847276 < baseStart_5847276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847289 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 8]
def baseStart_5847289 : Nat := 118140960795 + 5847289 * 2 ^ 59
def prefixEnd_5847289 : Nat := 4983230072969 + 3 ^ 40 * 5847289 * 2
def baseEnd_5847289 : Nat := 333607753638653132066257

theorem tailTrace_5847289 : CollatzResearch.WordTrace tailWord_5847289 prefixEnd_5847289 333607753638653132066257 := by
  unfold tailWord_5847289
  simp only [CollatzResearch.WordTrace]
  refine ⟨213268150513278065300720921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142178767008852043533813947 213268150513278065300720921)
  ·
    refine ⟨159951112884958548975540691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213268150513278065300720921 159951112884958548975540691)
    ·
      refine ⟨239926669327437823463311037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159951112884958548975540691 239926669327437823463311037)
      ·
        refine ⟨89972500997789183798741639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239926669327437823463311037 89972500997789183798741639)
        ·
          refine ⟨134958751496683775698112459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89972500997789183798741639 134958751496683775698112459)
          ·
            refine ⟨202438127245025663547168689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134958751496683775698112459 202438127245025663547168689)
            ·
              refine ⟨151828595433769247660376517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202438127245025663547168689 151828595433769247660376517)
              ·
                refine ⟨28467861643831733936320597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151828595433769247660376517 28467861643831733936320597)
                ·
                  refine ⟨333607753638653132066257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28467861643831733936320597 333607753638653132066257)
                  ·
                    rfl

theorem cell23_5847289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 8].length) (baseStart_5847289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847289 prefixEnd_5847289 := by exact prefixLift 5847289
  have htrace : WordTrace (prefixWord ++ tailWord_5847289) baseStart_5847289 baseEnd_5847289 := by
    simpa [prefixWord, tailWord_5847289, baseEnd_5847289] using wordTrace_append hprefix tailTrace_5847289
  have hstable : (prefixWord ++ tailWord_5847289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847289).length < 2 ^ (prefixWord ++ tailWord_5847289).sum := by decide
  have hdescent : baseEnd_5847289 < baseStart_5847289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847306 : List Nat := [3, 1, 2, 2, 1, 1, 3, 4, 6]
def baseStart_5847306 : Nat := 118140960795 + 5847306 * 2 ^ 59
def prefixEnd_5847306 : Nat := 4983230072969 + 3 ^ 40 * 5847306 * 2
def baseEnd_5847306 : Nat := 333608723546556069120415

theorem tailTrace_5847306 : CollatzResearch.WordTrace tailWord_5847306 prefixEnd_5847306 333608723546556069120415 := by
  unfold tailWord_5847306
  simp only [CollatzResearch.WordTrace]
  refine ⟨53317192638554119301022443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142179180369477651469393181 53317192638554119301022443)
  ·
    refine ⟨79975788957831178951533665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53317192638554119301022443 79975788957831178951533665)
    ·
      refine ⟨59981841718373384213650249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79975788957831178951533665 59981841718373384213650249)
      ·
        refine ⟨44986381288780038160237687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59981841718373384213650249 44986381288780038160237687)
        ·
          refine ⟨67479571933170057240356531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44986381288780038160237687 67479571933170057240356531)
          ·
            refine ⟨101219357899755085860534797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67479571933170057240356531 101219357899755085860534797)
            ·
              refine ⟨37957259212408157197700549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101219357899755085860534797 37957259212408157197700549)
              ·
                refine ⟨7116986102326529474568853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37957259212408157197700549 7116986102326529474568853)
                ·
                  refine ⟨333608723546556069120415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7116986102326529474568853 333608723546556069120415)
                  ·
                    rfl

theorem cell23_5847306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 6].length) (baseStart_5847306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847306 prefixEnd_5847306 := by exact prefixLift 5847306
  have htrace : WordTrace (prefixWord ++ tailWord_5847306) baseStart_5847306 baseEnd_5847306 := by
    simpa [prefixWord, tailWord_5847306, baseEnd_5847306] using wordTrace_append hprefix tailTrace_5847306
  have hstable : (prefixWord ++ tailWord_5847306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847306).length < 2 ^ (prefixWord ++ tailWord_5847306).sum := by decide
  have hdescent : baseEnd_5847306 < baseStart_5847306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847310 : List Nat := [4, 1, 1, 2, 1, 2, 3, 4, 1, 4]
def baseStart_5847310 : Nat := 118140960795 + 5847310 * 2 ^ 59
def prefixEnd_5847310 : Nat := 4983230072969 + 3 ^ 40 * 5847310 * 2
def baseEnd_5847310 : Nat := 1000826855280540868811239

theorem tailTrace_5847310 : CollatzResearch.WordTrace tailWord_5847310 prefixEnd_5847310 1000826855280540868811239 := by
  unfold tailWord_5847310
  simp only [CollatzResearch.WordTrace]
  refine ⟨26658614555775248235904423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142179277630801323924823589 26658614555775248235904423)
  ·
    refine ⟨39987921833662872353856635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26658614555775248235904423 39987921833662872353856635)
    ·
      refine ⟨59981882750494308530784953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39987921833662872353856635 59981882750494308530784953)
      ·
        refine ⟨44986412062870731398088715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59981882750494308530784953 44986412062870731398088715)
        ·
          refine ⟨67479618094306097097133073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44986412062870731398088715 67479618094306097097133073)
          ·
            refine ⟨50609713570729572822849805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67479618094306097097133073 50609713570729572822849805)
            ·
              refine ⟨18978642589023589808568677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50609713570729572822849805 18978642589023589808568677)
              ·
                refine ⟨3558495485441923089106627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18978642589023589808568677 3558495485441923089106627)
                ·
                  refine ⟨5337743228162884633659941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3558495485441923089106627 5337743228162884633659941)
                  ·
                    refine ⟨1000826855280540868811239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5337743228162884633659941 1000826855280540868811239)
                    ·
                      rfl

theorem cell23_5847310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_5847310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847310 prefixEnd_5847310 := by exact prefixLift 5847310
  have htrace : WordTrace (prefixWord ++ tailWord_5847310) baseStart_5847310 baseEnd_5847310 := by
    simpa [prefixWord, tailWord_5847310, baseEnd_5847310] using wordTrace_append hprefix tailTrace_5847310
  have hstable : (prefixWord ++ tailWord_5847310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847310).length < 2 ^ (prefixWord ++ tailWord_5847310).sum := by decide
  have hdescent : baseEnd_5847310 < baseStart_5847310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847376 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 5]
def baseStart_5847376 : Nat := 118140960795 + 5847376 * 2 ^ 59
def prefixEnd_5847376 : Nat := 4983230072969 + 3 ^ 40 * 5847376 * 2
def baseEnd_5847376 : Nat := 3002514455564819348208413

theorem tailTrace_5847376 : CollatzResearch.WordTrace tailWord_5847376 prefixEnd_5847376 3002514455564819348208413 := by
  unfold tailWord_5847376
  simp only [CollatzResearch.WordTrace]
  refine ⟨106635661831981439579568991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142180882442641919439425321 106635661831981439579568991)
  ·
    refine ⟨159953492747972159369353487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106635661831981439579568991 159953492747972159369353487)
    ·
      refine ⟨239930239121958239054030231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159953492747972159369353487 239930239121958239054030231)
      ·
        refine ⟨359895358682937358581045347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239930239121958239054030231 359895358682937358581045347)
        ·
          refine ⟨539843038024406037871568021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359895358682937358581045347 539843038024406037871568021)
          ·
            refine ⟨25305142407394033025229751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 539843038024406037871568021 25305142407394033025229751)
            ·
              refine ⟨37957713611091049537844627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25305142407394033025229751 37957713611091049537844627)
              ·
                refine ⟨56936570416636574306766941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37957713611091049537844627 56936570416636574306766941)
                ·
                  refine ⟨21351213906238715365037603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56936570416636574306766941 21351213906238715365037603)
                  ·
                    refine ⟨32026820859358073047556405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21351213906238715365037603 32026820859358073047556405)
                    ·
                      refine ⟨3002514455564819348208413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32026820859358073047556405 3002514455564819348208413)
                      ·
                        rfl

theorem cell23_5847376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 5].length) (baseStart_5847376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847376 prefixEnd_5847376 := by exact prefixLift 5847376
  have htrace : WordTrace (prefixWord ++ tailWord_5847376) baseStart_5847376 baseEnd_5847376 := by
    simpa [prefixWord, tailWord_5847376, baseEnd_5847376] using wordTrace_append hprefix tailTrace_5847376
  have hstable : (prefixWord ++ tailWord_5847376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847376).length < 2 ^ (prefixWord ++ tailWord_5847376).sum := by decide
  have hdescent : baseEnd_5847376 < baseStart_5847376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847396 : List Nat := [2, 3, 1, 1, 3, 1, 3, 9]
def baseStart_5847396 : Nat := 118140960795 + 5847396 * 2 ^ 59
def prefixEnd_5847396 : Nat := 4983230072969 + 3 ^ 40 * 5847396 * 2
def baseEnd_5847396 : Nat := 111204619451033676665123

theorem tailTrace_5847396 : CollatzResearch.WordTrace tailWord_5847396 prefixEnd_5847396 111204619451033676665123 := by
  unfold tailWord_5847396
  simp only [CollatzResearch.WordTrace]
  refine ⟨106636026561945211287433021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142181368749260281716577361 106636026561945211287433021)
  ·
    refine ⟨39988509960729454232787383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106636026561945211287433021 39988509960729454232787383)
    ·
      refine ⟨59982764941094181349181075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39988509960729454232787383 59982764941094181349181075)
      ·
        refine ⟨89974147411641272023771613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59982764941094181349181075 89974147411641272023771613)
        ·
          refine ⟨33740305279365477008914355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89974147411641272023771613 33740305279365477008914355)
          ·
            refine ⟨50610457919048215513371533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33740305279365477008914355 50610457919048215513371533)
            ·
              refine ⟨18978921719643080817514325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50610457919048215513371533 18978921719643080817514325)
              ·
                refine ⟨111204619451033676665123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18978921719643080817514325 111204619451033676665123)
                ·
                  rfl

theorem cell23_5847396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 9].length) (baseStart_5847396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847396 prefixEnd_5847396 := by exact prefixLift 5847396
  have htrace : WordTrace (prefixWord ++ tailWord_5847396) baseStart_5847396 baseEnd_5847396 := by
    simpa [prefixWord, tailWord_5847396, baseEnd_5847396] using wordTrace_append hprefix tailTrace_5847396
  have hstable : (prefixWord ++ tailWord_5847396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847396).length < 2 ^ (prefixWord ++ tailWord_5847396).sum := by decide
  have hdescent : baseEnd_5847396 < baseStart_5847396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847407 : List Nat := [1, 1, 2, 1, 3, 1, 2, 7, 1, 2, 2]
def baseStart_5847407 : Nat := 118140960795 + 5847407 * 2 ^ 59
def prefixEnd_5847407 : Nat := 4983230072969 + 3 ^ 40 * 5847407 * 2
def baseEnd_5847407 : Nat := 3002530373465108726920771

theorem tailTrace_5847407 : CollatzResearch.WordTrace tailWord_5847407 prefixEnd_5847407 3002530373465108726920771 := by
  unfold tailWord_5847407
  simp only [CollatzResearch.WordTrace]
  refine ⟨213272454326850571453516475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142181636217900380969010983 213272454326850571453516475)
  ·
    refine ⟨319908681490275857180274713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213272454326850571453516475 319908681490275857180274713)
    ·
      refine ⟨239931511117706892885206035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319908681490275857180274713 239931511117706892885206035)
      ·
        refine ⟨359897266676560339327809053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239931511117706892885206035 359897266676560339327809053)
        ·
          refine ⟨134961475003710127247928395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359897266676560339327809053 134961475003710127247928395)
          ·
            refine ⟨202442212505565190871892593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134961475003710127247928395 202442212505565190871892593)
            ·
              refine ⟨151831659379173893153919445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202442212505565190871892593 151831659379173893153919445)
              ·
                refine ⟨3558554516699388120794987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 151831659379173893153919445 3558554516699388120794987)
                ·
                  refine ⟨5337831775049082181192481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3558554516699388120794987 5337831775049082181192481)
                  ·
                    refine ⟨4003373831286811635894361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5337831775049082181192481 4003373831286811635894361)
                    ·
                      refine ⟨3002530373465108726920771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4003373831286811635894361 3002530373465108726920771)
                      ·
                        rfl

theorem cell23_5847407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 1, 2, 2].length) (baseStart_5847407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847407 prefixEnd_5847407 := by exact prefixLift 5847407
  have htrace : WordTrace (prefixWord ++ tailWord_5847407) baseStart_5847407 baseEnd_5847407 := by
    simpa [prefixWord, tailWord_5847407, baseEnd_5847407] using wordTrace_append hprefix tailTrace_5847407
  have hstable : (prefixWord ++ tailWord_5847407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847407).length < 2 ^ (prefixWord ++ tailWord_5847407).sum := by decide
  have hdescent : baseEnd_5847407 < baseStart_5847407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847410 : List Nat := [3, 2, 1, 2, 1, 3, 2, 3, 1, 2, 3]
def baseStart_5847410 : Nat := 118140960795 + 5847410 * 2 ^ 59
def prefixEnd_5847410 : Nat := 4983230072969 + 3 ^ 40 * 5847410 * 2
def baseEnd_5847410 : Nat := 3002531913907072215183257

theorem tailTrace_5847410 : CollatzResearch.WordTrace tailWord_5847410 prefixEnd_5847410 3002531913907072215183257 := by
  unfold tailWord_5847410
  simp only [CollatzResearch.WordTrace]
  refine ⟨53318140936459925741468921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142181709163893135310583789 53318140936459925741468921)
  ·
    refine ⟨39988605702344944306101691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53318140936459925741468921 39988605702344944306101691)
    ·
      refine ⟨59982908553517416459152537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39988605702344944306101691 59982908553517416459152537)
      ·
        refine ⟨44987181415138062344364403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59982908553517416459152537 44987181415138062344364403)
        ·
          refine ⟨67480772122707093516546605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44987181415138062344364403 67480772122707093516546605)
          ·
            refine ⟨25305289546015160068704977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67480772122707093516546605 25305289546015160068704977)
            ·
              refine ⟨18978967159511370051528733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25305289546015160068704977 18978967159511370051528733)
              ·
                refine ⟨7117112684816763769323275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18978967159511370051528733 7117112684816763769323275)
                ·
                  refine ⟨10675669027225145653984913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7117112684816763769323275 10675669027225145653984913)
                  ·
                    refine ⟨8006751770418859240488685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10675669027225145653984913 8006751770418859240488685)
                    ·
                      refine ⟨3002531913907072215183257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8006751770418859240488685 3002531913907072215183257)
                      ·
                        rfl

theorem cell23_5847410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_5847410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847410 prefixEnd_5847410 := by exact prefixLift 5847410
  have htrace : WordTrace (prefixWord ++ tailWord_5847410) baseStart_5847410 baseEnd_5847410 := by
    simpa [prefixWord, tailWord_5847410, baseEnd_5847410] using wordTrace_append hprefix tailTrace_5847410
  have hstable : (prefixWord ++ tailWord_5847410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847410).length < 2 ^ (prefixWord ++ tailWord_5847410).sum := by decide
  have hdescent : baseEnd_5847410 < baseStart_5847410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847413 : List Nat := [1, 3, 4, 1, 2, 3, 9]
def baseStart_5847413 : Nat := 118140960795 + 5847413 * 2 ^ 59
def prefixEnd_5847413 : Nat := 4983230072969 + 3 ^ 40 * 5847413 * 2
def baseEnd_5847413 : Nat := 37068314251222663005503

theorem tailTrace_5847413 : CollatzResearch.WordTrace tailWord_5847413 prefixEnd_5847413 37068314251222663005503 := by
  unfold tailWord_5847413
  simp only [CollatzResearch.WordTrace]
  refine ⟨213272673164828834478234893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142181782109885889652156595 213272673164828834478234893)
  ·
    refine ⟨79977252436810812929338085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213272673164828834478234893 79977252436810812929338085)
    ·
      refine ⟨14995734831902027424250891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79977252436810812929338085 14995734831902027424250891)
      ·
        refine ⟨22493602247853041136376337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14995734831902027424250891 22493602247853041136376337)
        ·
          refine ⟨16870201685889780852282253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22493602247853041136376337 16870201685889780852282253)
          ·
            refine ⟨6326325632208667819605845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16870201685889780852282253 6326325632208667819605845)
            ·
              refine ⟨37068314251222663005503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6326325632208667819605845 37068314251222663005503)
              ·
                rfl

theorem cell23_5847413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 9].length) (baseStart_5847413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847413 prefixEnd_5847413 := by exact prefixLift 5847413
  have htrace : WordTrace (prefixWord ++ tailWord_5847413) baseStart_5847413 baseEnd_5847413 := by
    simpa [prefixWord, tailWord_5847413, baseEnd_5847413] using wordTrace_append hprefix tailTrace_5847413
  have hstable : (prefixWord ++ tailWord_5847413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847413).length < 2 ^ (prefixWord ++ tailWord_5847413).sum := by decide
  have hdescent : baseEnd_5847413 < baseStart_5847413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847444 : List Nat := [2, 4, 2, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_5847444 : Nat := 118140960795 + 5847444 * 2 ^ 59
def prefixEnd_5847444 : Nat := 4983230072969 + 3 ^ 40 * 5847444 * 2
def baseEnd_5847444 : Nat := 3002549372249325082158101

theorem tailTrace_5847444 : CollatzResearch.WordTrace tailWord_5847444 prefixEnd_5847444 3002549372249325082158101 := by
  unfold tailWord_5847444
  simp only [CollatzResearch.WordTrace]
  refine ⟨106636901913858263386306693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142182535885144351181742257 106636901913858263386306693)
  ·
    refine ⟨19994419108848424384932505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106636901913858263386306693 19994419108848424384932505)
    ·
      refine ⟨14995814331636318288699379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19994419108848424384932505 14995814331636318288699379)
      ·
        refine ⟨22493721497454477433049069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14995814331636318288699379 22493721497454477433049069)
        ·
          refine ⟨8435145561545429037393401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22493721497454477433049069 8435145561545429037393401)
          ·
            refine ⟨6326359171159071778045051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8435145561545429037393401 6326359171159071778045051)
            ·
              refine ⟨9489538756738607667067577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6326359171159071778045051 9489538756738607667067577)
              ·
                refine ⟨7117154067553955750300683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9489538756738607667067577 7117154067553955750300683)
                ·
                  refine ⟨10675731101330933625451025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7117154067553955750300683 10675731101330933625451025)
                  ·
                    refine ⟨8006798325998200219088269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10675731101330933625451025 8006798325998200219088269)
                    ·
                      refine ⟨3002549372249325082158101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8006798325998200219088269 3002549372249325082158101)
                      ·
                        rfl

theorem cell23_5847444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_5847444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847444 prefixEnd_5847444 := by exact prefixLift 5847444
  have htrace : WordTrace (prefixWord ++ tailWord_5847444) baseStart_5847444 baseEnd_5847444 := by
    simpa [prefixWord, tailWord_5847444, baseEnd_5847444] using wordTrace_append hprefix tailTrace_5847444
  have hstable : (prefixWord ++ tailWord_5847444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847444).length < 2 ^ (prefixWord ++ tailWord_5847444).sum := by decide
  have hdescent : baseEnd_5847444 < baseStart_5847444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847457 : List Nat := [1, 2, 3, 5, 1, 1, 1, 2, 1, 3, 3]
def baseStart_5847457 : Nat := 118140960795 + 5847457 * 2 ^ 59
def prefixEnd_5847457 : Nat := 4983230072969 + 3 ^ 40 * 5847457 * 2
def baseEnd_5847457 : Nat := 3002556047497833531295541

theorem tailTrace_5847457 : CollatzResearch.WordTrace tailWord_5847457 prefixEnd_5847457 3002556047497833531295541 := by
  unfold tailWord_5847457
  simp only [CollatzResearch.WordTrace]
  refine ⟨213274277976669429992836625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142182851984446286661891083 213274277976669429992836625)
  ·
    refine ⟨159955708482502072494627469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213274277976669429992836625 159955708482502072494627469)
    ·
      refine ⟨59983390680938277185485301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159955708482502072494627469 59983390680938277185485301)
      ·
        refine ⟨5623442876337963486139247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59983390680938277185485301 5623442876337963486139247)
        ·
          refine ⟨8435164314506945229208871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5623442876337963486139247 8435164314506945229208871)
          ·
            refine ⟨12652746471760417843813307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8435164314506945229208871 12652746471760417843813307)
            ·
              refine ⟨18979119707640626765719961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12652746471760417843813307 18979119707640626765719961)
              ·
                refine ⟨14234339780730470074289971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18979119707640626765719961 14234339780730470074289971)
                ·
                  refine ⟨21351509671095705111434957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14234339780730470074289971 21351509671095705111434957)
                  ·
                    refine ⟨8006816126660889416788109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21351509671095705111434957 8006816126660889416788109)
                    ·
                      refine ⟨3002556047497833531295541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8006816126660889416788109 3002556047497833531295541)
                      ·
                        rfl

theorem cell23_5847457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_5847457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847457 prefixEnd_5847457 := by exact prefixLift 5847457
  have htrace : WordTrace (prefixWord ++ tailWord_5847457) baseStart_5847457 baseEnd_5847457 := by
    simpa [prefixWord, tailWord_5847457, baseEnd_5847457] using wordTrace_append hprefix tailTrace_5847457
  have hstable : (prefixWord ++ tailWord_5847457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847457).length < 2 ^ (prefixWord ++ tailWord_5847457).sum := by decide
  have hdescent : baseEnd_5847457 < baseStart_5847457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847497 : List Nat := [1, 2, 1, 1, 2, 1, 6, 3, 2, 2, 2]
def baseStart_5847497 : Nat := 118140960795 + 5847497 * 2 ^ 59
def prefixEnd_5847497 : Nat := 4983230072969 + 3 ^ 40 * 5847497 * 2
def baseEnd_5847497 : Nat := 3002576586724013374795357

theorem tailTrace_5847497 : CollatzResearch.WordTrace tailWord_5847497 prefixEnd_5847497 3002576586724013374795357 := by
  unfold tailWord_5847497
  simp only [CollatzResearch.WordTrace]
  refine ⟨213275736896524516824292745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142183824597683011216195163 213275736896524516824292745)
  ·
    refine ⟨159956802672393387618219559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213275736896524516824292745 159956802672393387618219559)
    ·
      refine ⟨239935204008590081427329339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159956802672393387618219559 239935204008590081427329339)
      ·
        refine ⟨359902806012885122140994009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239935204008590081427329339 359902806012885122140994009)
        ·
          refine ⟨269927104509663841605745507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359902806012885122140994009 269927104509663841605745507)
          ·
            refine ⟨404890656764495762408618261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269927104509663841605745507 404890656764495762408618261)
            ·
              refine ⟨18979249535835738862903981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 404890656764495762408618261 18979249535835738862903981)
              ·
                refine ⟨7117218575938402073588993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18979249535835738862903981 7117218575938402073588993)
                ·
                  refine ⟨5337913931953801555191745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7117218575938402073588993 5337913931953801555191745)
                  ·
                    refine ⟨4003435448965351166393809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5337913931953801555191745 4003435448965351166393809)
                    ·
                      refine ⟨3002576586724013374795357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4003435448965351166393809 3002576586724013374795357)
                      ·
                        rfl

theorem cell23_5847497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 2, 2].length) (baseStart_5847497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847497 prefixEnd_5847497 := by exact prefixLift 5847497
  have htrace : WordTrace (prefixWord ++ tailWord_5847497) baseStart_5847497 baseEnd_5847497 := by
    simpa [prefixWord, tailWord_5847497, baseEnd_5847497] using wordTrace_append hprefix tailTrace_5847497
  have hstable : (prefixWord ++ tailWord_5847497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847497).length < 2 ^ (prefixWord ++ tailWord_5847497).sum := by decide
  have hdescent : baseEnd_5847497 < baseStart_5847497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847510 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_5847510 : Nat := 118140960795 + 5847510 * 2 ^ 59
def prefixEnd_5847510 : Nat := 4983230072969 + 3 ^ 40 * 5847510 * 2
def baseEnd_5847510 : Nat := 3002583261972521823932797

theorem tailTrace_5847510 : CollatzResearch.WordTrace tailWord_5847510 prefixEnd_5847510 3002583261972521823932797 := by
  unfold tailWord_5847510
  simp only [CollatzResearch.WordTrace]
  refine ⟨13329763190342338752782249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142184140696984946696343989 13329763190342338752782249)
  ·
    refine ⟨9997322392756754064586687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13329763190342338752782249 9997322392756754064586687)
    ·
      refine ⟨14995983589135131096880031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9997322392756754064586687 14995983589135131096880031)
      ·
        refine ⟨22493975383702696645320047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14995983589135131096880031 22493975383702696645320047)
        ·
          refine ⟨33740963075554044967980071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22493975383702696645320047 33740963075554044967980071)
          ·
            refine ⟨50611444613331067451970107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33740963075554044967980071 50611444613331067451970107)
            ·
              refine ⟨75917166919996601177955161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50611444613331067451970107 75917166919996601177955161)
              ·
                refine ⟨56937875189997450883466371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75917166919996601177955161 56937875189997450883466371)
                ·
                  refine ⟨85406812784996176325199557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56937875189997450883466371 85406812784996176325199557)
                  ·
                    refine ⟨16013777397186783060974917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85406812784996176325199557 16013777397186783060974917)
                    ·
                      refine ⟨3002583261972521823932797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16013777397186783060974917 3002583261972521823932797)
                      ·
                        rfl

theorem cell23_5847510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_5847510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847510 prefixEnd_5847510 := by exact prefixLift 5847510
  have htrace : WordTrace (prefixWord ++ tailWord_5847510) baseStart_5847510 baseEnd_5847510 := by
    simpa [prefixWord, tailWord_5847510, baseEnd_5847510] using wordTrace_append hprefix tailTrace_5847510
  have hstable : (prefixWord ++ tailWord_5847510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847510).length < 2 ^ (prefixWord ++ tailWord_5847510).sum := by decide
  have hdescent : baseEnd_5847510 < baseStart_5847510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847513 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 1, 5, 3]
def baseStart_5847513 : Nat := 118140960795 + 5847513 * 2 ^ 59
def prefixEnd_5847513 : Nat := 4983230072969 + 3 ^ 40 * 5847513 * 2
def baseEnd_5847513 : Nat := 3002584802414485312195283

theorem tailTrace_5847513 : CollatzResearch.WordTrace tailWord_5847513 prefixEnd_5847513 3002584802414485312195283 := by
  unfold tailWord_5847513
  simp only [CollatzResearch.WordTrace]
  refine ⟨213276320464466551556875193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142184213642977701037916795 213276320464466551556875193)
  ·
    refine ⟨159957240348349913667656395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213276320464466551556875193 159957240348349913667656395)
    ·
      refine ⟨239935860522524870501484593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159957240348349913667656395 239935860522524870501484593)
      ·
        refine ⟨179951895391893652876113445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239935860522524870501484593 179951895391893652876113445)
        ·
          refine ⟨33740980385980059914271271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179951895391893652876113445 33740980385980059914271271)
          ·
            refine ⟨50611470578970089871406907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33740980385980059914271271 50611470578970089871406907)
            ·
              refine ⟨75917205868455134807110361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50611470578970089871406907 75917205868455134807110361)
              ·
                refine ⟨56937904401341351105332771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75917205868455134807110361 56937904401341351105332771)
                ·
                  refine ⟨85406856602012026657999157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56937904401341351105332771 85406856602012026657999157)
                  ·
                    refine ⟨8006892806438627499187421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85406856602012026657999157 8006892806438627499187421)
                    ·
                      refine ⟨3002584802414485312195283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8006892806438627499187421 3002584802414485312195283)
                      ·
                        rfl

theorem cell23_5847513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 5, 3].length) (baseStart_5847513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847513 prefixEnd_5847513 := by exact prefixLift 5847513
  have htrace : WordTrace (prefixWord ++ tailWord_5847513) baseStart_5847513 baseEnd_5847513 := by
    simpa [prefixWord, tailWord_5847513, baseEnd_5847513] using wordTrace_append hprefix tailTrace_5847513
  have hstable : (prefixWord ++ tailWord_5847513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847513).length < 2 ^ (prefixWord ++ tailWord_5847513).sum := by decide
  have hdescent : baseEnd_5847513 < baseStart_5847513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847520 : List Nat := [2, 1, 1, 3, 1, 1, 6, 3, 5]
def baseStart_5847520 : Nat := 118140960795 + 5847520 * 2 ^ 59
def prefixEnd_5847520 : Nat := 4983230072969 + 3 ^ 40 * 5847520 * 2
def baseEnd_5847520 : Nat := 333620932975451864978639

theorem tailTrace_5847520 : CollatzResearch.WordTrace tailWord_5847520 prefixEnd_5847520 333620932975451864978639 := by
  unfold tailWord_5847520
  simp only [CollatzResearch.WordTrace]
  refine ⟨106638287887720595876190007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142184383850294127834920009 106638287887720595876190007)
  ·
    refine ⟨159957431831580893814285011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106638287887720595876190007 159957431831580893814285011)
    ·
      refine ⟨239936147747371340721427517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159957431831580893814285011 239936147747371340721427517)
      ·
        refine ⟨89976055405264252770535319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239936147747371340721427517 89976055405264252770535319)
        ·
          refine ⟨134964083107896379155802979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89976055405264252770535319 134964083107896379155802979)
          ·
            refine ⟨202446124661844568733704469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134964083107896379155802979 202446124661844568733704469)
            ·
              refine ⟨9489662093523964159392397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 202446124661844568733704469 9489662093523964159392397)
              ·
                refine ⟨3558623285071486559772149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9489662093523964159392397 3558623285071486559772149)
                ·
                  refine ⟨333620932975451864978639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3558623285071486559772149 333620932975451864978639)
                  ·
                    rfl

theorem cell23_5847520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 5].length) (baseStart_5847520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847520 prefixEnd_5847520 := by exact prefixLift 5847520
  have htrace : WordTrace (prefixWord ++ tailWord_5847520) baseStart_5847520 baseEnd_5847520 := by
    simpa [prefixWord, tailWord_5847520, baseEnd_5847520] using wordTrace_append hprefix tailTrace_5847520
  have hstable : (prefixWord ++ tailWord_5847520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847520).length < 2 ^ (prefixWord ++ tailWord_5847520).sum := by decide
  have hdescent : baseEnd_5847520 < baseStart_5847520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847530 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 2, 3, 3]
def baseStart_5847530 : Nat := 118140960795 + 5847530 * 2 ^ 59
def prefixEnd_5847530 : Nat := 4983230072969 + 3 ^ 40 * 5847530 * 2
def baseEnd_5847530 : Nat := 3002593531585611745682705

theorem tailTrace_5847530 : CollatzResearch.WordTrace tailWord_5847530 prefixEnd_5847530 3002593531585611745682705 := by
  unfold tailWord_5847530
  simp only [CollatzResearch.WordTrace]
  refine ⟨53319235126351240865061011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142184627003603308973496029 53319235126351240865061011)
  ·
    refine ⟨79978852689526861297591517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53319235126351240865061011 79978852689526861297591517)
    ·
      refine ⟨29992069758572572986596819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79978852689526861297591517 29992069758572572986596819)
      ·
        refine ⟨44988104637858859479895229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29992069758572572986596819 44988104637858859479895229)
        ·
          refine ⟨16870539239197072304960711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44988104637858859479895229 16870539239197072304960711)
          ·
            refine ⟨25305808858795608457441067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16870539239197072304960711 25305808858795608457441067)
            ·
              refine ⟨37958713288193412686161601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25305808858795608457441067 37958713288193412686161601)
              ·
                refine ⟨28469034966145059514621201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37958713288193412686161601 28469034966145059514621201)
                ·
                  refine ⟨21351776224608794635965901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28469034966145059514621201 21351776224608794635965901)
                  ·
                    refine ⟨8006916084228297988487213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21351776224608794635965901 8006916084228297988487213)
                    ·
                      refine ⟨3002593531585611745682705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8006916084228297988487213 3002593531585611745682705)
                      ·
                        rfl

theorem cell23_5847530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_5847530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847530 prefixEnd_5847530 := by exact prefixLift 5847530
  have htrace : WordTrace (prefixWord ++ tailWord_5847530) baseStart_5847530 baseEnd_5847530 := by
    simpa [prefixWord, tailWord_5847530, baseEnd_5847530] using wordTrace_append hprefix tailTrace_5847530
  have hstable : (prefixWord ++ tailWord_5847530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847530).length < 2 ^ (prefixWord ++ tailWord_5847530).sum := by decide
  have hdescent : baseEnd_5847530 < baseStart_5847530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847610 : List Nat := [3, 1, 1, 1, 3, 4, 1, 3, 6]
def baseStart_5847610 : Nat := 118140960795 + 5847610 * 2 ^ 59
def prefixEnd_5847610 : Nat := 4983230072969 + 3 ^ 40 * 5847610 * 2
def baseEnd_5847610 : Nat := 333626067781996825853593

theorem tailTrace_5847610 : CollatzResearch.WordTrace tailWord_5847610 prefixEnd_5847610 333626067781996825853593 := by
  unfold tailWord_5847610
  simp only [CollatzResearch.WordTrace]
  refine ⟨53319964586278784280789071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142186572230076758082104189 53319964586278784280789071)
  ·
    refine ⟨79979946879418176421183607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53319964586278784280789071 79979946879418176421183607)
    ·
      refine ⟨119969920319127264631775411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79979946879418176421183607 119969920319127264631775411)
      ·
        refine ⟨179954880478690896947663117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119969920319127264631775411 179954880478690896947663117)
        ·
          refine ⟨67483080179509086355373669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179954880478690896947663117 67483080179509086355373669)
          ·
            refine ⟨12653077533657953691632563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67483080179509086355373669 12653077533657953691632563)
            ·
              refine ⟨18979616300486930537448845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12653077533657953691632563 18979616300486930537448845)
              ·
                refine ⟨7117356112682598951543317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18979616300486930537448845 7117356112682598951543317)
                ·
                  refine ⟨333626067781996825853593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7117356112682598951543317 333626067781996825853593)
                  ·
                    rfl

theorem cell23_5847610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 6].length) (baseStart_5847610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847610 prefixEnd_5847610 := by exact prefixLift 5847610
  have htrace : WordTrace (prefixWord ++ tailWord_5847610) baseStart_5847610 baseEnd_5847610 := by
    simpa [prefixWord, tailWord_5847610, baseEnd_5847610] using wordTrace_append hprefix tailTrace_5847610
  have hstable : (prefixWord ++ tailWord_5847610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847610).length < 2 ^ (prefixWord ++ tailWord_5847610).sum := by decide
  have hdescent : baseEnd_5847610 < baseStart_5847610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847640 : List Nat := [2, 1, 2, 2, 1, 2, 2, 5, 1, 5]
def baseStart_5847640 : Nat := 118140960795 + 5847640 * 2 ^ 59
def prefixEnd_5847640 : Nat := 4983230072969 + 3 ^ 40 * 5847640 * 2
def baseEnd_5847640 : Nat := 1000883338152535438435733

theorem tailTrace_5847640 : CollatzResearch.WordTrace tailWord_5847640 prefixEnd_5847640 1000883338152535438435733 := by
  unfold tailWord_5847640
  simp only [CollatzResearch.WordTrace]
  refine ⟨106640476267503226123374187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142187301690004301497832249 106640476267503226123374187)
  ·
    refine ⟨159960714401254839185061281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106640476267503226123374187 159960714401254839185061281)
    ·
      refine ⟨119970535800941129388795961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159960714401254839185061281 119970535800941129388795961)
      ·
        refine ⟨89977901850705847041596971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119970535800941129388795961 89977901850705847041596971)
        ·
          refine ⟨134966852776058770562395457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89977901850705847041596971 134966852776058770562395457)
          ·
            refine ⟨101225139582044077921796593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134966852776058770562395457 101225139582044077921796593)
            ·
              refine ⟨75918854686533058441347445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101225139582044077921796593 75918854686533058441347445)
              ·
                refine ⟨7117392626862474228876323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75918854686533058441347445 7117392626862474228876323)
                ·
                  refine ⟨10676088940293711343314485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7117392626862474228876323 10676088940293711343314485)
                  ·
                    refine ⟨1000883338152535438435733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10676088940293711343314485 1000883338152535438435733)
                    ·
                      rfl

theorem cell23_5847640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 1, 5].length) (baseStart_5847640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847640 prefixEnd_5847640 := by exact prefixLift 5847640
  have htrace : WordTrace (prefixWord ++ tailWord_5847640) baseStart_5847640 baseEnd_5847640 := by
    simpa [prefixWord, tailWord_5847640, baseEnd_5847640] using wordTrace_append hprefix tailTrace_5847640
  have hstable : (prefixWord ++ tailWord_5847640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847640).length < 2 ^ (prefixWord ++ tailWord_5847640).sum := by decide
  have hdescent : baseEnd_5847640 < baseStart_5847640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847660 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 4]
def baseStart_5847660 : Nat := 118140960795 + 5847660 * 2 ^ 59
def prefixEnd_5847660 : Nat := 4983230072969 + 3 ^ 40 * 5847660 * 2
def baseEnd_5847660 : Nat := 3002660284070696237057107

theorem tailTrace_5847660 : CollatzResearch.WordTrace tailWord_5847660 prefixEnd_5847660 3002660284070696237057107 := by
  unfold tailWord_5847660
  simp only [CollatzResearch.WordTrace]
  refine ⟨106640840997466997831238217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142187787996622663774984289 106640840997466997831238217)
  ·
    refine ⟨79980630748100248373428663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106640840997466997831238217 79980630748100248373428663)
    ·
      refine ⟨119970946122150372560142995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79980630748100248373428663 119970946122150372560142995)
      ·
        refine ⟨179956419183225558840214493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119970946122150372560142995 179956419183225558840214493)
        ·
          refine ⟨67483657193709584565080435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179956419183225558840214493 67483657193709584565080435)
          ·
            refine ⟨101225485790564376847620653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67483657193709584565080435 101225485790564376847620653)
            ·
              refine ⟨37959557171461641317857745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101225485790564376847620653 37959557171461641317857745)
              ·
                refine ⟨28469667878596230988393309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37959557171461641317857745 28469667878596230988393309)
                ·
                  refine ⟨10676125454473586620647491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28469667878596230988393309 10676125454473586620647491)
                  ·
                    refine ⟨16014188181710379930971237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10676125454473586620647491 16014188181710379930971237)
                    ·
                      refine ⟨3002660284070696237057107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16014188181710379930971237 3002660284070696237057107)
                      ·
                        rfl

theorem cell23_5847660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_5847660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847660 prefixEnd_5847660 := by exact prefixLift 5847660
  have htrace : WordTrace (prefixWord ++ tailWord_5847660) baseStart_5847660 baseEnd_5847660 := by
    simpa [prefixWord, tailWord_5847660, baseEnd_5847660] using wordTrace_append hprefix tailTrace_5847660
  have hstable : (prefixWord ++ tailWord_5847660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847660).length < 2 ^ (prefixWord ++ tailWord_5847660).sum := by decide
  have hdescent : baseEnd_5847660 < baseStart_5847660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847683 : List Nat := [1, 1, 1, 3, 3, 1, 2, 11]
def baseStart_5847683 : Nat := 118140960795 + 5847683 * 2 ^ 59
def prefixEnd_5847683 : Nat := 4983230072969 + 3 ^ 40 * 5847683 * 2
def baseEnd_5847683 : Nat := 111210077560212949891463

theorem tailTrace_5847683 : CollatzResearch.WordTrace tailWord_5847683 prefixEnd_5847683 111210077560212949891463 := by
  unfold tailWord_5847683
  simp only [CollatzResearch.WordTrace]
  refine ⟨213282520873850670590563703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142188347249233780393709135 213282520873850670590563703)
  ·
    refine ⟨319923781310776005885845555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213282520873850670590563703 319923781310776005885845555)
    ·
      refine ⟨479885671966164008828768333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319923781310776005885845555 479885671966164008828768333)
      ·
        refine ⟨179957126987311503310788125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 479885671966164008828768333 179957126987311503310788125)
        ·
          refine ⟨67483922620241813741545547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179957126987311503310788125 67483922620241813741545547)
          ·
            refine ⟨101225883930362720612318321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67483922620241813741545547 101225883930362720612318321)
            ·
              refine ⟨75919412947772040459238741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101225883930362720612318321 75919412947772040459238741)
              ·
                refine ⟨111210077560212949891463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 75919412947772040459238741 111210077560212949891463)
                ·
                  rfl

theorem cell23_5847683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 11].length) (baseStart_5847683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847683 prefixEnd_5847683 := by exact prefixLift 5847683
  have htrace : WordTrace (prefixWord ++ tailWord_5847683) baseStart_5847683 baseEnd_5847683 := by
    simpa [prefixWord, tailWord_5847683, baseEnd_5847683] using wordTrace_append hprefix tailTrace_5847683
  have hstable : (prefixWord ++ tailWord_5847683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847683).length < 2 ^ (prefixWord ++ tailWord_5847683).sum := by decide
  have hdescent : baseEnd_5847683 < baseStart_5847683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847694 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2]
def baseStart_5847694 : Nat := 118140960795 + 5847694 * 2 ^ 59
def prefixEnd_5847694 : Nat := 4983230072969 + 3 ^ 40 * 5847694 * 2
def baseEnd_5847694 : Nat := 3002677742412949104031951

theorem tailTrace_5847694 : CollatzResearch.WordTrace tailWord_5847694 prefixEnd_5847694 3002677742412949104031951 := by
  unfold tailWord_5847694
  simp only [CollatzResearch.WordTrace]
  refine ⟨26660365259601352433651767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142188614717873879646142757 26660365259601352433651767)
  ·
    refine ⟨39990547889402028650477651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26660365259601352433651767 39990547889402028650477651)
    ·
      refine ⟨59985821834103042975716477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39990547889402028650477651 59985821834103042975716477)
      ·
        refine ⟨22494683187788641115893679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59985821834103042975716477 22494683187788641115893679)
        ·
          refine ⟨33742024781682961673840519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22494683187788641115893679 33742024781682961673840519)
          ·
            refine ⟨50613037172524442510760779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33742024781682961673840519 50613037172524442510760779)
            ·
              refine ⟨75919555758786663766141169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50613037172524442510760779 75919555758786663766141169)
              ·
                refine ⟨56939666819089997824605877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75919555758786663766141169 56939666819089997824605877)
                ·
                  refine ⟨5338093764289687296056801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56939666819089997824605877 5338093764289687296056801)
                  ·
                    refine ⟨4003570323217265472042601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5338093764289687296056801 4003570323217265472042601)
                    ·
                      refine ⟨3002677742412949104031951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4003570323217265472042601 3002677742412949104031951)
                      ·
                        rfl

theorem cell23_5847694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_5847694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847694 prefixEnd_5847694 := by exact prefixLift 5847694
  have htrace : WordTrace (prefixWord ++ tailWord_5847694) baseStart_5847694 baseEnd_5847694 := by
    simpa [prefixWord, tailWord_5847694, baseEnd_5847694] using wordTrace_append hprefix tailTrace_5847694
  have hstable : (prefixWord ++ tailWord_5847694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847694).length < 2 ^ (prefixWord ++ tailWord_5847694).sum := by decide
  have hdescent : baseEnd_5847694 < baseStart_5847694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847727 : List Nat := [1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 3]
def baseStart_5847727 : Nat := 118140960795 + 5847727 * 2 ^ 59
def prefixEnd_5847727 : Nat := 4983230072969 + 3 ^ 40 * 5847727 * 2
def baseEnd_5847727 : Nat := 3002694687274547474919299

theorem tailTrace_5847727 : CollatzResearch.WordTrace tailWord_5847727 prefixEnd_5847727 3002694687274547474919299 := by
  unfold tailWord_5847727
  simp only [CollatzResearch.WordTrace]
  refine ⟨213284125685691266105165435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142189417123794177403443623 213284125685691266105165435)
  ·
    refine ⟨319926188528536899157748153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213284125685691266105165435 319926188528536899157748153)
    ·
      refine ⟨239944641396402674368311115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319926188528536899157748153 239944641396402674368311115)
      ·
        refine ⟨359916962094604011552466673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239944641396402674368311115 359916962094604011552466673)
        ·
          refine ⟨269937721570953008664350005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359916962094604011552466673 269937721570953008664350005)
          ·
            refine ⟨25306661397276844562282813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 269937721570953008664350005 25306661397276844562282813)
            ·
              refine ⟨9489998023978816710856055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25306661397276844562282813 9489998023978816710856055)
              ·
                refine ⟨14234997035968225066284083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9489998023978816710856055 14234997035968225066284083)
                ·
                  refine ⟨21352495553952337599426125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14234997035968225066284083 21352495553952337599426125)
                  ·
                    refine ⟨8007185832732126599784797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21352495553952337599426125 8007185832732126599784797)
                    ·
                      refine ⟨3002694687274547474919299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8007185832732126599784797 3002694687274547474919299)
                      ·
                        rfl

theorem cell23_5847727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 3].length) (baseStart_5847727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847727 prefixEnd_5847727 := by exact prefixLift 5847727
  have htrace : WordTrace (prefixWord ++ tailWord_5847727) baseStart_5847727 baseEnd_5847727 := by
    simpa [prefixWord, tailWord_5847727, baseEnd_5847727] using wordTrace_append hprefix tailTrace_5847727
  have hstable : (prefixWord ++ tailWord_5847727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847727).length < 2 ^ (prefixWord ++ tailWord_5847727).sum := by decide
  have hdescent : baseEnd_5847727 < baseStart_5847727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847734 : List Nat := [5, 1, 3, 1, 2, 1, 1, 9]
def baseStart_5847734 : Nat := 118140960795 + 5847734 * 2 ^ 59
def prefixEnd_5847734 : Nat := 4983230072969 + 3 ^ 40 * 5847734 * 2
def baseEnd_5847734 : Nat := 111211047468115886945621

theorem tailTrace_5847734 : CollatzResearch.WordTrace tailWord_5847734 prefixEnd_5847734 111211047468115886945621 := by
  unfold tailWord_5847734
  simp only [CollatzResearch.WordTrace]
  refine ⟨13330273812291619143791891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142189587331110604200446837 13330273812291619143791891)
  ·
    refine ⟨19995410718437428715687837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13330273812291619143791891 19995410718437428715687837)
    ·
      refine ⟨7498279019414035768382939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19995410718437428715687837 7498279019414035768382939)
      ·
        refine ⟨11247418529121053652574409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7498279019414035768382939 11247418529121053652574409)
        ·
          refine ⟨8435563896840790239430807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11247418529121053652574409 8435563896840790239430807)
          ·
            refine ⟨12653345845261185359146211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8435563896840790239430807 12653345845261185359146211)
            ·
              refine ⟨18980018767891778038719317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12653345845261185359146211 18980018767891778038719317)
              ·
                refine ⟨111211047468115886945621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18980018767891778038719317 111211047468115886945621)
                ·
                  rfl

theorem cell23_5847734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_5847734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847734 prefixEnd_5847734 := by exact prefixLift 5847734
  have htrace : WordTrace (prefixWord ++ tailWord_5847734) baseStart_5847734 baseEnd_5847734 := by
    simpa [prefixWord, tailWord_5847734, baseEnd_5847734] using wordTrace_append hprefix tailTrace_5847734
  have hstable : (prefixWord ++ tailWord_5847734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847734).length < 2 ^ (prefixWord ++ tailWord_5847734).sum := by decide
  have hdescent : baseEnd_5847734 < baseStart_5847734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847740 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 1, 4, 5]
def baseStart_5847740 : Nat := 118140960795 + 5847740 * 2 ^ 59
def prefixEnd_5847740 : Nat := 4983230072969 + 3 ^ 40 * 5847740 * 2
def baseEnd_5847740 : Nat := 3002701362523055924056739

theorem tailTrace_5847740 : CollatzResearch.WordTrace tailWord_5847740 prefixEnd_5847740 3002701362523055924056739 := by
  unfold tailWord_5847740
  simp only [CollatzResearch.WordTrace]
  refine ⟨106642299917322084662694337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142189733223096112883592449 106642299917322084662694337)
  ·
    refine ⟨79981724937991563497020753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106642299917322084662694337 79981724937991563497020753)
    ·
      refine ⟨59986293703493672622765565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79981724937991563497020753 59986293703493672622765565)
      ·
        refine ⟨22494860138810127233537087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59986293703493672622765565 22494860138810127233537087)
        ·
          refine ⟨33742290208215190850305631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22494860138810127233537087 33742290208215190850305631)
          ·
            refine ⟨50613435312322786275458447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33742290208215190850305631 50613435312322786275458447)
            ·
              refine ⟨75920152968484179413187671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50613435312322786275458447 75920152968484179413187671)
              ·
                refine ⟨113880229452726269119781507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75920152968484179413187671 113880229452726269119781507)
                ·
                  refine ⟨170820344179089403679672261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113880229452726269119781507 170820344179089403679672261)
                  ·
                    refine ⟨32028814533579263189938549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 170820344179089403679672261 32028814533579263189938549)
                    ·
                      refine ⟨3002701362523055924056739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32028814533579263189938549 3002701362523055924056739)
                      ·
                        rfl

theorem cell23_5847740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_5847740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847740 prefixEnd_5847740 := by exact prefixLift 5847740
  have htrace : WordTrace (prefixWord ++ tailWord_5847740) baseStart_5847740 baseEnd_5847740 := by
    simpa [prefixWord, tailWord_5847740, baseEnd_5847740] using wordTrace_append hprefix tailTrace_5847740
  have hstable : (prefixWord ++ tailWord_5847740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847740).length < 2 ^ (prefixWord ++ tailWord_5847740).sum := by decide
  have hdescent : baseEnd_5847740 < baseStart_5847740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847770 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5]
def baseStart_5847770 : Nat := 118140960795 + 5847770 * 2 ^ 59
def prefixEnd_5847770 : Nat := 4983230072969 + 3 ^ 40 * 5847770 * 2
def baseEnd_5847770 : Nat := 3002716766942690806681601

theorem tailTrace_5847770 : CollatzResearch.WordTrace tailWord_5847770 prefixEnd_5847770 3002716766942690806681601 := by
  unfold tailWord_5847770
  simp only [CollatzResearch.WordTrace]
  refine ⟨53321423506133871112245191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142190462683023656299320509 53321423506133871112245191)
  ·
    refine ⟨79982135259200806668367787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53321423506133871112245191 79982135259200806668367787)
    ·
      refine ⟨119973202888801210002551681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79982135259200806668367787 119973202888801210002551681)
      ·
        refine ⟨89979902166600907501913761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119973202888801210002551681 89979902166600907501913761)
        ·
          refine ⟨67484926624950680626435321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89979902166600907501913761 67484926624950680626435321)
          ·
            refine ⟨50613694968713010469826491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67484926624950680626435321 50613694968713010469826491)
            ·
              refine ⟨75920542453069515704739737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50613694968713010469826491 75920542453069515704739737)
              ·
                refine ⟨56940406839802136778554803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75920542453069515704739737 56940406839802136778554803)
                ·
                  refine ⟨85410610259703205167832205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56940406839802136778554803 85410610259703205167832205)
                  ·
                    refine ⟨32028978847388701937937077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85410610259703205167832205 32028978847388701937937077)
                    ·
                      refine ⟨3002716766942690806681601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32028978847388701937937077 3002716766942690806681601)
                      ·
                        rfl

theorem cell23_5847770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_5847770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847770 prefixEnd_5847770 := by exact prefixLift 5847770
  have htrace : WordTrace (prefixWord ++ tailWord_5847770) baseStart_5847770 baseEnd_5847770 := by
    simpa [prefixWord, tailWord_5847770, baseEnd_5847770] using wordTrace_append hprefix tailTrace_5847770
  have hstable : (prefixWord ++ tailWord_5847770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847770).length < 2 ^ (prefixWord ++ tailWord_5847770).sum := by decide
  have hdescent : baseEnd_5847770 < baseStart_5847770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847807 : List Nat := [1, 1, 2, 2, 1, 3, 1, 7, 5]
def baseStart_5847807 : Nat := 118140960795 + 5847807 * 2 ^ 59
def prefixEnd_5847807 : Nat := 4983230072969 + 3 ^ 40 * 5847807 * 2
def baseEnd_5847807 : Nat := 333637307302989684657659

theorem tailTrace_5847807 : CollatzResearch.WordTrace tailWord_5847807 prefixEnd_5847807 333637307302989684657659 := by
  unfold tailWord_5847807
  simp only [CollatzResearch.WordTrace]
  refine ⟨213287043525401439768077675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142191362350267626512051783 213287043525401439768077675)
  ·
    refine ⟨319930565288102159652116513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213287043525401439768077675 319930565288102159652116513)
    ·
      refine ⟨239947923966076619739087385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319930565288102159652116513 239947923966076619739087385)
      ·
        refine ⟨179960942974557464804315539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239947923966076619739087385 179960942974557464804315539)
        ·
          refine ⟨269941414461836197206473309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179960942974557464804315539 269941414461836197206473309)
          ·
            refine ⟨101228030423188573952427491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 269941414461836197206473309 101228030423188573952427491)
            ·
              refine ⟨151842045634782860928641237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101228030423188573952427491 151842045634782860928641237)
              ·
                refine ⟨3558797944565223303015029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 151842045634782860928641237 3558797944565223303015029)
                ·
                  refine ⟨333637307302989684657659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3558797944565223303015029 333637307302989684657659)
                  ·
                    rfl

theorem cell23_5847807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 5].length) (baseStart_5847807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847807 prefixEnd_5847807 := by exact prefixLift 5847807
  have htrace : WordTrace (prefixWord ++ tailWord_5847807) baseStart_5847807 baseEnd_5847807 := by
    simpa [prefixWord, tailWord_5847807, baseEnd_5847807] using wordTrace_append hprefix tailTrace_5847807
  have hstable : (prefixWord ++ tailWord_5847807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847807).length < 2 ^ (prefixWord ++ tailWord_5847807).sum := by decide
  have hdescent : baseEnd_5847807 < baseStart_5847807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847820 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 3, 7]
def baseStart_5847820 : Nat := 118140960795 + 5847820 * 2 ^ 59
def prefixEnd_5847820 : Nat := 4983230072969 + 3 ^ 40 * 5847820 * 2
def baseEnd_5847820 : Nat := 1000914146991805203685457

theorem tailTrace_5847820 : CollatzResearch.WordTrace tailWord_5847820 prefixEnd_5847820 1000914146991805203685457 := by
  unfold tailWord_5847820
  simp only [CollatzResearch.WordTrace]
  refine ⟨106643758837177171494150457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142191678449569561992200609 106643758837177171494150457)
  ·
    refine ⟨79982819127882878620612843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106643758837177171494150457 79982819127882878620612843)
    ·
      refine ⟨119974228691824317930919265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79982819127882878620612843 119974228691824317930919265)
      ·
        refine ⟨89980671518868238448189449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119974228691824317930919265 89980671518868238448189449)
        ·
          refine ⟨67485503639151178836142087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89980671518868238448189449 67485503639151178836142087)
          ·
            refine ⟨101228255458726768254213131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67485503639151178836142087 101228255458726768254213131)
            ·
              refine ⟨151842383188090152381319697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101228255458726768254213131 151842383188090152381319697)
              ·
                refine ⟨113881787391067614285989773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151842383188090152381319697 113881787391067614285989773)
                ·
                  refine ⟨42705670271650355357246165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113881787391067614285989773 42705670271650355357246165)
                  ·
                    refine ⟨1000914146991805203685457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42705670271650355357246165 1000914146991805203685457)
                    ·
                      rfl

theorem cell23_5847820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_5847820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847820 prefixEnd_5847820 := by exact prefixLift 5847820
  have htrace : WordTrace (prefixWord ++ tailWord_5847820) baseStart_5847820 baseEnd_5847820 := by
    simpa [prefixWord, tailWord_5847820, baseEnd_5847820] using wordTrace_append hprefix tailTrace_5847820
  have hstable : (prefixWord ++ tailWord_5847820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847820).length < 2 ^ (prefixWord ++ tailWord_5847820).sum := by decide
  have hdescent : baseEnd_5847820 < baseStart_5847820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847827 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 1, 7, 2]
def baseStart_5847827 : Nat := 118140960795 + 5847827 * 2 ^ 59
def prefixEnd_5847827 : Nat := 4983230072969 + 3 ^ 40 * 5847827 * 2
def baseEnd_5847827 : Nat := 3002746035339997083668839

theorem tailTrace_5847827 : CollatzResearch.WordTrace tailWord_5847827 prefixEnd_5847827 3002746035339997083668839 := by
  unfold tailWord_5847827
  simp only [CollatzResearch.WordTrace]
  refine ⟨213287772985328983183805735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142191848656885988789203823 213287772985328983183805735)
  ·
    refine ⟨319931659477993474775708603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213287772985328983183805735 319931659477993474775708603)
    ·
      refine ⟨479897489216990212163562905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319931659477993474775708603 479897489216990212163562905)
      ·
        refine ⟨359923116912742659122672179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479897489216990212163562905 359923116912742659122672179)
        ·
          refine ⟨539884675369113988684008269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359923116912742659122672179 539884675369113988684008269)
          ·
            refine ⟨202456753263417745756503101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 539884675369113988684008269 202456753263417745756503101)
            ·
              refine ⟨75921282473781654658688663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202456753263417745756503101 75921282473781654658688663)
              ·
                refine ⟨113881923710672481988032995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75921282473781654658688663 113881923710672481988032995)
                ·
                  refine ⟨170822885566008722982049493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113881923710672481988032995 170822885566008722982049493)
                  ·
                    refine ⟨4003661380453329444891785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 170822885566008722982049493 4003661380453329444891785)
                    ·
                      refine ⟨3002746035339997083668839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4003661380453329444891785 3002746035339997083668839)
                      ·
                        rfl

theorem cell23_5847827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 7, 2].length) (baseStart_5847827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847827 prefixEnd_5847827 := by exact prefixLift 5847827
  have htrace : WordTrace (prefixWord ++ tailWord_5847827) baseStart_5847827 baseEnd_5847827 := by
    simpa [prefixWord, tailWord_5847827, baseEnd_5847827] using wordTrace_append hprefix tailTrace_5847827
  have hstable : (prefixWord ++ tailWord_5847827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847827).length < 2 ^ (prefixWord ++ tailWord_5847827).sum := by decide
  have hdescent : baseEnd_5847827 < baseStart_5847827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847854 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 1, 7]
def baseStart_5847854 : Nat := 118140960795 + 5847854 * 2 ^ 59
def prefixEnd_5847854 : Nat := 4983230072969 + 3 ^ 40 * 5847854 * 2
def baseEnd_5847854 : Nat := 1000919966439222826010405

theorem tailTrace_5847854 : CollatzResearch.WordTrace tailWord_5847854 prefixEnd_5847854 1000919966439222826010405 := by
  unfold tailWord_5847854
  simp only [CollatzResearch.WordTrace]
  refine ⟨26661094719528895849379827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142192505170820777863359077 26661094719528895849379827)
  ·
    refine ⟨39991642079293343774069741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26661094719528895849379827 39991642079293343774069741)
    ·
      refine ⟨14996865779735003915276153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39991642079293343774069741 14996865779735003915276153)
      ·
        refine ⟨11247649334801252936457115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14996865779735003915276153 11247649334801252936457115)
        ·
          refine ⟨16871474002201879404685673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11247649334801252936457115 16871474002201879404685673)
          ·
            refine ⟨12653605501651409553514255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16871474002201879404685673 12653605501651409553514255)
            ·
              refine ⟨18980408252477114330271383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12653605501651409553514255 18980408252477114330271383)
              ·
                refine ⟨28470612378715671495407075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18980408252477114330271383 28470612378715671495407075)
                ·
                  refine ⟨42705918568073507243110613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28470612378715671495407075 42705918568073507243110613)
                  ·
                    refine ⟨1000919966439222826010405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42705918568073507243110613 1000919966439222826010405)
                    ·
                      rfl

theorem cell23_5847854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_5847854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847854 prefixEnd_5847854 := by exact prefixLift 5847854
  have htrace : WordTrace (prefixWord ++ tailWord_5847854) baseStart_5847854 baseEnd_5847854 := by
    simpa [prefixWord, tailWord_5847854, baseEnd_5847854] using wordTrace_append hprefix tailTrace_5847854
  have hstable : (prefixWord ++ tailWord_5847854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847854).length < 2 ^ (prefixWord ++ tailWord_5847854).sum := by decide
  have hdescent : baseEnd_5847854 < baseStart_5847854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847857 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 1, 3, 4]
def baseStart_5847857 : Nat := 118140960795 + 5847857 * 2 ^ 59
def prefixEnd_5847857 : Nat := 4983230072969 + 3 ^ 40 * 5847857 * 2
def baseEnd_5847857 : Nat := 3002761439759631966293701

theorem tailTrace_5847857 : CollatzResearch.WordTrace tailWord_5847857 prefixEnd_5847857 3002761439759631966293701 := by
  unfold tailWord_5847857
  simp only [CollatzResearch.WordTrace]
  refine ⟨213288867175220298307397825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142192578116813532204931883 213288867175220298307397825)
  ·
    refine ⟨159966650381415223730548369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213288867175220298307397825 159966650381415223730548369)
    ·
      refine ⟨119974987786061417797911277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159966650381415223730548369 119974987786061417797911277)
      ·
        refine ⟨44990620419773031674216729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119974987786061417797911277 44990620419773031674216729)
        ·
          refine ⟨33742965314829773755662547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44990620419773031674216729 33742965314829773755662547)
          ·
            refine ⟨50614447972244660633493821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33742965314829773755662547 50614447972244660633493821)
            ·
              refine ⟨18980417989591747737560183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50614447972244660633493821 18980417989591747737560183)
              ·
                refine ⟨28470626984387621606340275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18980417989591747737560183 28470626984387621606340275)
                ·
                  refine ⟨42705940476581432409510413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28470626984387621606340275 42705940476581432409510413)
                  ·
                    refine ⟨16014727678718037153566405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42705940476581432409510413 16014727678718037153566405)
                    ·
                      refine ⟨3002761439759631966293701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16014727678718037153566405 3002761439759631966293701)
                      ·
                        rfl

theorem cell23_5847857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_5847857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847857 prefixEnd_5847857 := by exact prefixLift 5847857
  have htrace : WordTrace (prefixWord ++ tailWord_5847857) baseStart_5847857 baseEnd_5847857 := by
    simpa [prefixWord, tailWord_5847857, baseEnd_5847857] using wordTrace_append hprefix tailTrace_5847857
  have hstable : (prefixWord ++ tailWord_5847857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847857).length < 2 ^ (prefixWord ++ tailWord_5847857).sum := by decide
  have hdescent : baseEnd_5847857 < baseStart_5847857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847884 : List Nat := [2, 2, 1, 3, 3, 1, 1, 3, 3, 4]
def baseStart_5847884 : Nat := 118140960795 + 5847884 * 2 ^ 59
def prefixEnd_5847884 : Nat := 4983230072969 + 3 ^ 40 * 5847884 * 2
def baseEnd_5847884 : Nat := 1000925101245767786885359

theorem tailTrace_5847884 : CollatzResearch.WordTrace tailWord_5847884 prefixEnd_5847884 1000925101245767786885359 := by
  unfold tailWord_5847884
  simp only [CollatzResearch.WordTrace]
  refine ⟨106644925973061240959315353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142193234630748321279087137 106644925973061240959315353)
  ·
    refine ⟨79983694479795930719486515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106644925973061240959315353 79983694479795930719486515)
    ·
      refine ⟨119975541719693896079229773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79983694479795930719486515 119975541719693896079229773)
      ·
        refine ⟨44990828144885211029711165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119975541719693896079229773 44990828144885211029711165)
        ·
          refine ⟨16871560554331954136141687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44990828144885211029711165 16871560554331954136141687)
          ·
            refine ⟨25307340831497931204212531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16871560554331954136141687 25307340831497931204212531)
            ·
              refine ⟨37961011247246896806318797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25307340831497931204212531 37961011247246896806318797)
              ·
                refine ⟨14235379217717586302369549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37961011247246896806318797 14235379217717586302369549)
                ·
                  refine ⟨5338267206644094863388581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14235379217717586302369549 5338267206644094863388581)
                  ·
                    refine ⟨1000925101245767786885359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5338267206644094863388581 1000925101245767786885359)
                    ·
                      rfl

theorem cell23_5847884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 3, 4].length) (baseStart_5847884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847884 prefixEnd_5847884 := by exact prefixLift 5847884
  have htrace : WordTrace (prefixWord ++ tailWord_5847884) baseStart_5847884 baseEnd_5847884 := by
    simpa [prefixWord, tailWord_5847884, baseEnd_5847884] using wordTrace_append hprefix tailTrace_5847884
  have hstable : (prefixWord ++ tailWord_5847884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847884).length < 2 ^ (prefixWord ++ tailWord_5847884).sum := by decide
  have hdescent : baseEnd_5847884 < baseStart_5847884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847941 : List Nat := [1, 3, 1, 1, 3, 3, 3, 1, 3, 1, 3]
def baseStart_5847941 : Nat := 118140960795 + 5847941 * 2 ^ 59
def prefixEnd_5847941 : Nat := 4983230072969 + 3 ^ 40 * 5847941 * 2
def baseEnd_5847941 : Nat := 3002804572134609637643315

theorem tailTrace_5847941 : CollatzResearch.WordTrace tailWord_5847941 prefixEnd_5847941 3002804572134609637643315 := by
  unfold tailWord_5847941
  simp only [CollatzResearch.WordTrace]
  refine ⟨213291930906915980653455677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142194620604610653768970451 213291930906915980653455677)
  ·
    refine ⟨79984474090093492745045879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213291930906915980653455677 79984474090093492745045879)
    ·
      refine ⟨119976711135140239117568819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79984474090093492745045879 119976711135140239117568819)
      ·
        refine ⟨179965066702710358676353229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119976711135140239117568819 179965066702710358676353229)
        ·
          refine ⟨67486900013516384503632461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179965066702710358676353229 67486900013516384503632461)
          ·
            refine ⟨25307587505068644188862173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67486900013516384503632461 25307587505068644188862173)
            ·
              refine ⟨9490345314400741570823315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25307587505068644188862173 9490345314400741570823315)
              ·
                refine ⟨14235517971601112356234973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9490345314400741570823315 14235517971601112356234973)
                ·
                  refine ⟨5338319239350417133588115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14235517971601112356234973 5338319239350417133588115)
                  ·
                    refine ⟨8007478859025625700382173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5338319239350417133588115 8007478859025625700382173)
                    ·
                      refine ⟨3002804572134609637643315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8007478859025625700382173 3002804572134609637643315)
                      ·
                        rfl

theorem cell23_5847941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 1, 3].length) (baseStart_5847941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847941 prefixEnd_5847941 := by exact prefixLift 5847941
  have htrace : WordTrace (prefixWord ++ tailWord_5847941) baseStart_5847941 baseEnd_5847941 := by
    simpa [prefixWord, tailWord_5847941, baseEnd_5847941] using wordTrace_append hprefix tailTrace_5847941
  have hstable : (prefixWord ++ tailWord_5847941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847941).length < 2 ^ (prefixWord ++ tailWord_5847941).sum := by decide
  have hdescent : baseEnd_5847941 < baseStart_5847941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847998 : List Nat := [4, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2]
def baseStart_5847998 : Nat := 118140960795 + 5847998 * 2 ^ 59
def prefixEnd_5847998 : Nat := 4983230072969 + 3 ^ 40 * 5847998 * 2
def baseEnd_5847998 : Nat := 3002833840531915914630553

theorem tailTrace_5847998 : CollatzResearch.WordTrace tailWord_5847998 prefixEnd_5847998 3002833840531915914630553 := by
  unfold tailWord_5847998
  simp only [CollatzResearch.WordTrace]
  refine ⟨26661751233463684923535081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142196006578472986258853765 26661751233463684923535081)
  ·
    refine ⟨19996313425097763692651311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26661751233463684923535081 19996313425097763692651311)
    ·
      refine ⟨29994470137646645538976967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19996313425097763692651311 29994470137646645538976967)
      ·
        refine ⟨44991705206469968308465451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29994470137646645538976967 44991705206469968308465451)
        ·
          refine ⟨67487557809704952462698177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44991705206469968308465451 67487557809704952462698177)
          ·
            refine ⟨50615668357278714347023633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67487557809704952462698177 50615668357278714347023633)
            ·
              refine ⟨37961751267959035760267725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50615668357278714347023633 37961751267959035760267725)
              ·
                refine ⟨14235656725484638410100397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37961751267959035760267725 14235656725484638410100397)
                ·
                  refine ⟨5338371272056739403787649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14235656725484638410100397 5338371272056739403787649)
                  ·
                    refine ⟨4003778454042554552840737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5338371272056739403787649 4003778454042554552840737)
                    ·
                      refine ⟨3002833840531915914630553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4003778454042554552840737 3002833840531915914630553)
                      ·
                        rfl

theorem cell23_5847998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_5847998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5847998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5847998 prefixEnd_5847998 := by exact prefixLift 5847998
  have htrace : WordTrace (prefixWord ++ tailWord_5847998) baseStart_5847998 baseEnd_5847998 := by
    simpa [prefixWord, tailWord_5847998, baseEnd_5847998] using wordTrace_append hprefix tailTrace_5847998
  have hstable : (prefixWord ++ tailWord_5847998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847998).length < 2 ^ (prefixWord ++ tailWord_5847998).sum := by decide
  have hdescent : baseEnd_5847998 < baseStart_5847998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848007 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_5848007 : Nat := 118140960795 + 5848007 * 2 ^ 59
def prefixEnd_5848007 : Nat := 4983230072969 + 3 ^ 40 * 5848007 * 2
def baseEnd_5848007 : Nat := 3002838461857806379418011

theorem tailTrace_5848007 : CollatzResearch.WordTrace tailWord_5848007 prefixEnd_5848007 3002838461857806379418011 := by
  unfold tailWord_5848007
  simp only [CollatzResearch.WordTrace]
  refine ⟨213294338124676873925358275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142196225416451249283572183 213294338124676873925358275)
  ·
    refine ⟨319941507187015310888037413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213294338124676873925358275 319941507187015310888037413)
    ·
      refine ⟨59989032597565370791507015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319941507187015310888037413 59989032597565370791507015)
      ·
        refine ⟨89983548896348056187260523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59989032597565370791507015 89983548896348056187260523)
        ·
          refine ⟨134975323344522084280890785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89983548896348056187260523 134975323344522084280890785)
          ·
            refine ⟨101231492508391563210668089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134975323344522084280890785 101231492508391563210668089)
            ·
              refine ⟨75923619381293672408001067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101231492508391563210668089 75923619381293672408001067)
              ·
                refine ⟨113885429071940508612001601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75923619381293672408001067 113885429071940508612001601)
                ·
                  refine ⟨85414071803955381459001201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113885429071940508612001601 85414071803955381459001201)
                  ·
                    refine ⟨64060553852966536094250901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85414071803955381459001201 64060553852966536094250901)
                    ·
                      refine ⟨3002838461857806379418011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64060553852966536094250901 3002838461857806379418011)
                      ·
                        rfl

theorem cell23_5848007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_5848007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848007 prefixEnd_5848007 := by exact prefixLift 5848007
  have htrace : WordTrace (prefixWord ++ tailWord_5848007) baseStart_5848007 baseEnd_5848007 := by
    simpa [prefixWord, tailWord_5848007, baseEnd_5848007] using wordTrace_append hprefix tailTrace_5848007
  have hstable : (prefixWord ++ tailWord_5848007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848007).length < 2 ^ (prefixWord ++ tailWord_5848007).sum := by decide
  have hdescent : baseEnd_5848007 < baseStart_5848007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848017 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 2, 7]
def baseStart_5848017 : Nat := 118140960795 + 5848017 * 2 ^ 59
def prefixEnd_5848017 : Nat := 4983230072969 + 3 ^ 40 * 5848017 * 2
def baseEnd_5848017 : Nat := 1000947865554783780097655

theorem tailTrace_5848017 : CollatzResearch.WordTrace tailWord_5848017 prefixEnd_5848017 1000947865554783780097655 := by
  unfold tailWord_5848017
  simp only [CollatzResearch.WordTrace]
  refine ⟨213294702854640645633222305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142196468569760430422148203 213294702854640645633222305)
  ·
    refine ⟨159971027140980484224916729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213294702854640645633222305 159971027140980484224916729)
    ·
      refine ⟨119978270355735363168687547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159971027140980484224916729 119978270355735363168687547)
      ·
        refine ⟨179967405533603044753031321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119978270355735363168687547 179967405533603044753031321)
        ·
          refine ⟨134975554150202283564773491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179967405533603044753031321 134975554150202283564773491)
          ·
            refine ⟨202463331225303425347160237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134975554150202283564773491 202463331225303425347160237)
            ·
              refine ⟨75923749209488784505185089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202463331225303425347160237 75923749209488784505185089)
              ·
                refine ⟨56942811907116588378888817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75923749209488784505185089 56942811907116588378888817)
                ·
                  refine ⟨42707108930337441284166613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56942811907116588378888817 42707108930337441284166613)
                  ·
                    refine ⟨1000947865554783780097655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42707108930337441284166613 1000947865554783780097655)
                    ·
                      rfl

theorem cell23_5848017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_5848017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848017 prefixEnd_5848017 := by exact prefixLift 5848017
  have htrace : WordTrace (prefixWord ++ tailWord_5848017) baseStart_5848017 baseEnd_5848017 := by
    simpa [prefixWord, tailWord_5848017, baseEnd_5848017] using wordTrace_append hprefix tailTrace_5848017
  have hstable : (prefixWord ++ tailWord_5848017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848017).length < 2 ^ (prefixWord ++ tailWord_5848017).sum := by decide
  have hdescent : baseEnd_5848017 < baseStart_5848017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848021 : List Nat := [1, 3, 2, 3, 3, 1, 3, 7]
def baseStart_5848021 : Nat := 118140960795 + 5848021 * 2 ^ 59
def prefixEnd_5848021 : Nat := 4983230072969 + 3 ^ 40 * 5848021 * 2
def baseEnd_5848021 : Nat := 111216505577295160171961

theorem tailTrace_5848021 : CollatzResearch.WordTrace tailWord_5848021 prefixEnd_5848021 111216505577295160171961 := by
  unfold tailWord_5848021
  simp only [CollatzResearch.WordTrace]
  refine ⟨213294848746626154316367917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142196565831084102877578611 213294848746626154316367917)
  ·
    refine ⟨79985568279984807868637969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213294848746626154316367917 79985568279984807868637969)
    ·
      refine ⟨59989176209988605901478477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79985568279984807868637969 59989176209988605901478477)
      ·
        refine ⟨22495941078745727213054429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59989176209988605901478477 22495941078745727213054429)
        ·
          refine ⟨8435977904529647704895411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22495941078745727213054429 8435977904529647704895411)
          ·
            refine ⟨12653966856794471557343117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8435977904529647704895411 12653966856794471557343117)
            ·
              refine ⟨4745237571297926834003669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12653966856794471557343117 4745237571297926834003669)
              ·
                refine ⟨111216505577295160171961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4745237571297926834003669 111216505577295160171961)
                ·
                  rfl

theorem cell23_5848021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 7].length) (baseStart_5848021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848021 prefixEnd_5848021 := by exact prefixLift 5848021
  have htrace : WordTrace (prefixWord ++ tailWord_5848021) baseStart_5848021 baseEnd_5848021 := by
    simpa [prefixWord, tailWord_5848021, baseEnd_5848021] using wordTrace_append hprefix tailTrace_5848021
  have hstable : (prefixWord ++ tailWord_5848021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848021).length < 2 ^ (prefixWord ++ tailWord_5848021).sum := by decide
  have hdescent : baseEnd_5848021 < baseStart_5848021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848052 : List Nat := [2, 6, 2, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_5848052 : Nat := 118140960795 + 5848052 * 2 ^ 59
def prefixEnd_5848052 : Nat := 4983230072969 + 3 ^ 40 * 5848052 * 2
def baseEnd_5848052 : Nat := 3002861568487258703355305

theorem tailTrace_5848052 : CollatzResearch.WordTrace tailWord_5848052 prefixEnd_5848052 3002861568487258703355305 := by
  unfold tailWord_5848052
  simp only [CollatzResearch.WordTrace]
  refine ⟨106647989704756923305373205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142197319606342564407164273 106647989704756923305373205)
  ·
    refine ⟨4999124517410480779939369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 106647989704756923305373205 4999124517410480779939369)
    ·
      refine ⟨3749343388057860584954527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4999124517410480779939369 3749343388057860584954527)
      ·
        refine ⟨5624015082086790877431791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3749343388057860584954527 5624015082086790877431791)
        ·
          refine ⟨8436022623130186316147687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5624015082086790877431791 8436022623130186316147687)
          ·
            refine ⟨12654033934695279474221531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8436022623130186316147687 12654033934695279474221531)
            ·
              refine ⟨18981050902042919211332297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12654033934695279474221531 18981050902042919211332297)
              ·
                refine ⟨14235788176532189408499223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18981050902042919211332297 14235788176532189408499223)
                ·
                  refine ⟨21353682264798284112748835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14235788176532189408499223 21353682264798284112748835)
                  ·
                    refine ⟨32030523397197426169123253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21353682264798284112748835 32030523397197426169123253)
                    ·
                      refine ⟨3002861568487258703355305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32030523397197426169123253 3002861568487258703355305)
                      ·
                        rfl

theorem cell23_5848052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_5848052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848052 prefixEnd_5848052 := by exact prefixLift 5848052
  have htrace : WordTrace (prefixWord ++ tailWord_5848052) baseStart_5848052 baseEnd_5848052 := by
    simpa [prefixWord, tailWord_5848052, baseEnd_5848052] using wordTrace_append hprefix tailTrace_5848052
  have hstable : (prefixWord ++ tailWord_5848052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848052).length < 2 ^ (prefixWord ++ tailWord_5848052).sum := by decide
  have hdescent : baseEnd_5848052 < baseStart_5848052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848065 : List Nat := [1, 2, 4, 1, 2, 3, 3, 1, 2, 1, 3]
def baseStart_5848065 : Nat := 118140960795 + 5848065 * 2 ^ 59
def prefixEnd_5848065 : Nat := 4983230072969 + 3 ^ 40 * 5848065 * 2
def baseEnd_5848065 : Nat := 3002868243735767152492745

theorem tailTrace_5848065 : CollatzResearch.WordTrace tailWord_5848065 prefixEnd_5848065 3002868243735767152492745 := by
  unfold tailWord_5848065
  simp only [CollatzResearch.WordTrace]
  refine ⟨213296453558466749830969649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142197635705644499887313099 213296453558466749830969649)
  ·
    refine ⟨159972340168850062373227237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213296453558466749830969649 159972340168850062373227237)
    ·
      refine ⟨29994813781659386694980107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159972340168850062373227237 29994813781659386694980107)
      ·
        refine ⟨44992220672489080042470161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29994813781659386694980107 44992220672489080042470161)
        ·
          refine ⟨33744165504366810031852621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44992220672489080042470161 33744165504366810031852621)
          ·
            refine ⟨12654062064137553761944733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33744165504366810031852621 12654062064137553761944733)
            ·
              refine ⟨4745273274051582660729275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12654062064137553761944733 4745273274051582660729275)
              ·
                refine ⟨7117909911077373991093913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4745273274051582660729275 7117909911077373991093913)
                ·
                  refine ⟨5338432433308030493320435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7117909911077373991093913 5338432433308030493320435)
                  ·
                    refine ⟨8007648649962045739980653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5338432433308030493320435 8007648649962045739980653)
                    ·
                      refine ⟨3002868243735767152492745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8007648649962045739980653 3002868243735767152492745)
                      ·
                        rfl

theorem cell23_5848065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_5848065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848065 prefixEnd_5848065 := by exact prefixLift 5848065
  have htrace : WordTrace (prefixWord ++ tailWord_5848065) baseStart_5848065 baseEnd_5848065 := by
    simpa [prefixWord, tailWord_5848065, baseEnd_5848065] using wordTrace_append hprefix tailTrace_5848065
  have hstable : (prefixWord ++ tailWord_5848065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848065).length < 2 ^ (prefixWord ++ tailWord_5848065).sum := by decide
  have hdescent : baseEnd_5848065 < baseStart_5848065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848088 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 4, 2, 2]
def baseStart_5848088 : Nat := 118140960795 + 5848088 * 2 ^ 59
def prefixEnd_5848088 : Nat := 4983230072969 + 3 ^ 40 * 5848088 * 2
def baseEnd_5848088 : Nat := 3002880053790820562505139

theorem tailTrace_5848088 : CollatzResearch.WordTrace tailWord_5848088 prefixEnd_5848088 3002880053790820562505139 := by
  unfold tailWord_5848088
  simp only [CollatzResearch.WordTrace]
  refine ⟨106648646218691712379528459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142198194958255616506037945 106648646218691712379528459)
  ·
    refine ⟨159972969328037568569292689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106648646218691712379528459 159972969328037568569292689)
    ·
      refine ⟨119979726996028176426969517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159972969328037568569292689 119979726996028176426969517)
      ·
        refine ⟨44992397623510566160113569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119979726996028176426969517 44992397623510566160113569)
        ·
          refine ⟨33744298217632924620085177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44992397623510566160113569 33744298217632924620085177)
          ·
            refine ⟨25308223663224693465063883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33744298217632924620085177 25308223663224693465063883)
            ·
              refine ⟨37962335494837040197595825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25308223663224693465063883 37962335494837040197595825)
              ·
                refine ⟨28471751621127780148196869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37962335494837040197595825 28471751621127780148196869)
                ·
                  refine ⟨5338453428961458777786913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28471751621127780148196869 5338453428961458777786913)
                  ·
                    refine ⟨4003840071721094083340185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5338453428961458777786913 4003840071721094083340185)
                    ·
                      refine ⟨3002880053790820562505139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4003840071721094083340185 3002880053790820562505139)
                      ·
                        rfl

theorem cell23_5848088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_5848088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848088 prefixEnd_5848088 := by exact prefixLift 5848088
  have htrace : WordTrace (prefixWord ++ tailWord_5848088) baseStart_5848088 baseEnd_5848088 := by
    simpa [prefixWord, tailWord_5848088, baseEnd_5848088] using wordTrace_append hprefix tailTrace_5848088
  have hstable : (prefixWord ++ tailWord_5848088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848088).length < 2 ^ (prefixWord ++ tailWord_5848088).sum := by decide
  have hdescent : baseEnd_5848088 < baseStart_5848088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848144 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 4]
def baseStart_5848144 : Nat := 118140960795 + 5848144 * 2 ^ 59
def prefixEnd_5848144 : Nat := 4983230072969 + 3 ^ 40 * 5848144 * 2
def baseEnd_5848144 : Nat := 3002908808707472343404881

theorem tailTrace_5848144 : CollatzResearch.WordTrace tailWord_5848144 prefixEnd_5848144 3002908808707472343404881 := by
  unfold tailWord_5848144
  simp only [CollatzResearch.WordTrace]
  refine ⟨106649667462590273161547743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142199556616787030882063657 106649667462590273161547743)
  ·
    refine ⟨159974501193885409742321615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106649667462590273161547743 159974501193885409742321615)
    ·
      refine ⟨239961751790828114613482423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159974501193885409742321615 239961751790828114613482423)
      ·
        refine ⟨359942627686242171920223635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239961751790828114613482423 359942627686242171920223635)
        ·
          refine ⟨539913941529363257880335453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359942627686242171920223635 539913941529363257880335453)
          ·
            refine ⟨202467728073511221705125795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 539913941529363257880335453 202467728073511221705125795)
            ·
              refine ⟨303701592110266832557688693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202467728073511221705125795 303701592110266832557688693)
              ·
                refine ⟨28472024260337515552283315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 303701592110266832557688693 28472024260337515552283315)
                ·
                  refine ⟨42708036390506273328424973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28472024260337515552283315 42708036390506273328424973)
                  ·
                    refine ⟨16015513646439852498159365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42708036390506273328424973 16015513646439852498159365)
                    ·
                      refine ⟨3002908808707472343404881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16015513646439852498159365 3002908808707472343404881)
                      ·
                        rfl

theorem cell23_5848144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 4].length) (baseStart_5848144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848144 prefixEnd_5848144 := by exact prefixLift 5848144
  have htrace : WordTrace (prefixWord ++ tailWord_5848144) baseStart_5848144 baseEnd_5848144 := by
    simpa [prefixWord, tailWord_5848144, baseEnd_5848144] using wordTrace_append hprefix tailTrace_5848144
  have hstable : (prefixWord ++ tailWord_5848144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848144).length < 2 ^ (prefixWord ++ tailWord_5848144).sum := by decide
  have hdescent : baseEnd_5848144 < baseStart_5848144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848161 : List Nat := [1, 2, 3, 1, 1, 2, 4, 2, 2, 1, 4]
def baseStart_5848161 : Nat := 118140960795 + 5848161 * 2 ^ 59
def prefixEnd_5848161 : Nat := 4983230072969 + 3 ^ 40 * 5848161 * 2
def baseEnd_5848161 : Nat := 3002917537878598776892303

theorem tailTrace_5848161 : CollatzResearch.WordTrace tailWord_5848161 prefixEnd_5848161 3002917537878598776892303 := by
  unfold tailWord_5848161
  simp only [CollatzResearch.WordTrace]
  refine ⟨213299954966118958226464337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142199969977412638817642891 213299954966118958226464337)
  ·
    refine ⟨159974966224589218669848253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213299954966118958226464337 159974966224589218669848253)
    ·
      refine ⟨59990612334220957001193095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159974966224589218669848253 59990612334220957001193095)
      ·
        refine ⟨89985918501331435501789643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59990612334220957001193095 89985918501331435501789643)
        ·
          refine ⟨134978877751997153252684465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89985918501331435501789643 134978877751997153252684465)
          ·
            refine ⟨101234158313997864939513349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134978877751997153252684465 101234158313997864939513349)
            ·
              refine ⟨18981404683874599676158753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101234158313997864939513349 18981404683874599676158753)
              ·
                refine ⟨14236053512905949757119065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18981404683874599676158753 14236053512905949757119065)
                ·
                  refine ⟨10677040134679462317839299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14236053512905949757119065 10677040134679462317839299)
                  ·
                    refine ⟨16015560202019193476758949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10677040134679462317839299 16015560202019193476758949)
                    ·
                      refine ⟨3002917537878598776892303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16015560202019193476758949 3002917537878598776892303)
                      ·
                        rfl

theorem cell23_5848161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_5848161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848161 prefixEnd_5848161 := by exact prefixLift 5848161
  have htrace : WordTrace (prefixWord ++ tailWord_5848161) baseStart_5848161 baseEnd_5848161 := by
    simpa [prefixWord, tailWord_5848161, baseEnd_5848161] using wordTrace_append hprefix tailTrace_5848161
  have hstable : (prefixWord ++ tailWord_5848161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848161).length < 2 ^ (prefixWord ++ tailWord_5848161).sum := by decide
  have hdescent : baseEnd_5848161 < baseStart_5848161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848162 : List Nat := [3, 3, 2, 2, 1, 3, 2, 2, 5]
def baseStart_5848162 : Nat := 118140960795 + 5848162 * 2 ^ 59
def prefixEnd_5848162 : Nat := 4983230072969 + 3 ^ 40 * 5848162 * 2
def baseEnd_5848162 : Nat := 333657561262139252553311

theorem tailTrace_5848162 : CollatzResearch.WordTrace tailWord_5848162 prefixEnd_5848162 333657561262139252553311 := by
  unfold tailWord_5848162
  simp only [CollatzResearch.WordTrace]
  refine ⟨53324997859778833849312685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142199994292743556931500493 53324997859778833849312685)
  ·
    refine ⟨19996874197417062693492257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53324997859778833849312685 19996874197417062693492257)
    ·
      refine ⟨14997655648062797020119193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19996874197417062693492257 14997655648062797020119193)
      ·
        refine ⟨11248241736047097765089395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14997655648062797020119193 11248241736047097765089395)
        ·
          refine ⟨16872362604070646647634093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11248241736047097765089395 16872362604070646647634093)
          ·
            refine ⟨6327135976526492492862785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16872362604070646647634093 6327135976526492492862785)
            ·
              refine ⟨4745351982394869369647089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6327135976526492492862785 4745351982394869369647089)
              ·
                refine ⟨3559013986796152027235317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4745351982394869369647089 3559013986796152027235317)
                ·
                  refine ⟨333657561262139252553311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3559013986796152027235317 333657561262139252553311)
                  ·
                    rfl

theorem cell23_5848162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_5848162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848162 prefixEnd_5848162 := by exact prefixLift 5848162
  have htrace : WordTrace (prefixWord ++ tailWord_5848162) baseStart_5848162 baseEnd_5848162 := by
    simpa [prefixWord, tailWord_5848162, baseEnd_5848162] using wordTrace_append hprefix tailTrace_5848162
  have hstable : (prefixWord ++ tailWord_5848162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848162).length < 2 ^ (prefixWord ++ tailWord_5848162).sum := by decide
  have hdescent : baseEnd_5848162 < baseStart_5848162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848164 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_5848164 : Nat := 118140960795 + 5848164 * 2 ^ 59
def prefixEnd_5848164 : Nat := 4983230072969 + 3 ^ 40 * 5848164 * 2
def baseEnd_5848164 : Nat := 3002919078320562265154789

theorem tailTrace_5848164 : CollatzResearch.WordTrace tailWord_5848164 prefixEnd_5848164 3002919078320562265154789 := by
  unfold tailWord_5848164
  simp only [CollatzResearch.WordTrace]
  refine ⟨106650032192554044869411773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142200042923405393159215697 106650032192554044869411773)
  ·
    refine ⟨39993762072207766826029415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106650032192554044869411773 39993762072207766826029415)
    ·
      refine ⟨59990643108311650239044123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39993762072207766826029415 59990643108311650239044123)
      ·
        refine ⟨89985964662467475358566185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59990643108311650239044123 89985964662467475358566185)
        ·
          refine ⟨67489473496850606518924639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89985964662467475358566185 67489473496850606518924639)
          ·
            refine ⟨101234210245275909778386959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67489473496850606518924639 101234210245275909778386959)
            ·
              refine ⟨151851315367913864667580439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101234210245275909778386959 151851315367913864667580439)
              ·
                refine ⟨227776973051870797001370659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151851315367913864667580439 227776973051870797001370659)
                ·
                  refine ⟨341665459577806195502055989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227776973051870797001370659 341665459577806195502055989)
                  ·
                    refine ⟨32031136835419330828317749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 341665459577806195502055989 32031136835419330828317749)
                    ·
                      refine ⟨3002919078320562265154789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32031136835419330828317749 3002919078320562265154789)
                      ·
                        rfl

theorem cell23_5848164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_5848164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848164 prefixEnd_5848164 := by exact prefixLift 5848164
  have htrace : WordTrace (prefixWord ++ tailWord_5848164) baseStart_5848164 baseEnd_5848164 := by
    simpa [prefixWord, tailWord_5848164, baseEnd_5848164] using wordTrace_append hprefix tailTrace_5848164
  have hstable : (prefixWord ++ tailWord_5848164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848164).length < 2 ^ (prefixWord ++ tailWord_5848164).sum := by decide
  have hdescent : baseEnd_5848164 < baseStart_5848164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848178 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 2, 4, 2]
def baseStart_5848178 : Nat := 118140960795 + 5848178 * 2 ^ 59
def prefixEnd_5848178 : Nat := 4983230072969 + 3 ^ 40 * 5848178 * 2
def baseEnd_5848178 : Nat := 3002926267049725210379725

theorem tailTrace_5848178 : CollatzResearch.WordTrace tailWord_5848178 prefixEnd_5848178 3002926267049725210379725 := by
  unfold tailWord_5848178
  simp only [CollatzResearch.WordTrace]
  refine ⟨53325143751764342532458297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142200383338038246753222125 53325143751764342532458297)
  ·
    refine ⟨39993857813823256899343723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53325143751764342532458297 39993857813823256899343723)
    ·
      refine ⟨59990786720734885349015585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39993857813823256899343723 59990786720734885349015585)
      ·
        refine ⟨44993090040551164011761689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59990786720734885349015585 44993090040551164011761689)
        ·
          refine ⟨33744817530413373008821267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44993090040551164011761689 33744817530413373008821267)
          ·
            refine ⟨50617226295620059513231901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33744817530413373008821267 50617226295620059513231901)
            ·
              refine ⟨18981459860857522317461963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50617226295620059513231901 18981459860857522317461963)
              ·
                refine ⟨28472189791286283476192945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18981459860857522317461963 28472189791286283476192945)
                ·
                  refine ⟨21354142343464712607144709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28472189791286283476192945 21354142343464712607144709)
                  ·
                    refine ⟨4003901689399633613839633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21354142343464712607144709 4003901689399633613839633)
                    ·
                      refine ⟨3002926267049725210379725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4003901689399633613839633 3002926267049725210379725)
                      ·
                        rfl

theorem cell23_5848178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_5848178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848178 prefixEnd_5848178 := by exact prefixLift 5848178
  have htrace : WordTrace (prefixWord ++ tailWord_5848178) baseStart_5848178 baseEnd_5848178 := by
    simpa [prefixWord, tailWord_5848178, baseEnd_5848178] using wordTrace_append hprefix tailTrace_5848178
  have hstable : (prefixWord ++ tailWord_5848178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848178).length < 2 ^ (prefixWord ++ tailWord_5848178).sum := by decide
  have hdescent : baseEnd_5848178 < baseStart_5848178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848204 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 6]
def baseStart_5848204 : Nat := 118140960795 + 5848204 * 2 ^ 59
def prefixEnd_5848204 : Nat := 4983230072969 + 3 ^ 40 * 5848204 * 2
def baseEnd_5848204 : Nat := 3002939617546742108654605

theorem tailTrace_5848204 : CollatzResearch.WordTrace tailWord_5848204 prefixEnd_5848204 3002939617546742108654605 := by
  unfold tailWord_5848204
  simp only [CollatzResearch.WordTrace]
  refine ⟨106650761652481588285139833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142201015536642117713519777 106650761652481588285139833)
  ·
    refine ⟨79988071239361191213854875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106650761652481588285139833 79988071239361191213854875)
    ·
      refine ⟨119982106859041786820782313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79988071239361191213854875 119982106859041786820782313)
      ·
        refine ⟨89986580144281340115586735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119982106859041786820782313 89986580144281340115586735)
        ·
          refine ⟨134979870216422010173380103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89986580144281340115586735 134979870216422010173380103)
          ·
            refine ⟨202469805324633015260070155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134979870216422010173380103 202469805324633015260070155)
            ·
              refine ⟨303704707986949522890105233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202469805324633015260070155 303704707986949522890105233)
              ·
                refine ⟨227778530990212142167578925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303704707986949522890105233 227778530990212142167578925)
                ·
                  refine ⟨85416949121329553312842097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227778530990212142167578925 85416949121329553312842097)
                  ·
                    refine ⟨64062711840997164984631573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85416949121329553312842097 64062711840997164984631573)
                    ·
                      refine ⟨3002939617546742108654605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64062711840997164984631573 3002939617546742108654605)
                      ·
                        rfl

theorem cell23_5848204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_5848204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848204 prefixEnd_5848204 := by exact prefixLift 5848204
  have htrace : WordTrace (prefixWord ++ tailWord_5848204) baseStart_5848204 baseEnd_5848204 := by
    simpa [prefixWord, tailWord_5848204, baseEnd_5848204] using wordTrace_append hprefix tailTrace_5848204
  have hstable : (prefixWord ++ tailWord_5848204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848204).length < 2 ^ (prefixWord ++ tailWord_5848204).sum := by decide
  have hdescent : baseEnd_5848204 < baseStart_5848204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848218 : List Nat := [3, 1, 1, 5, 1, 1, 3, 2, 6]
def baseStart_5848218 : Nat := 118140960795 + 5848218 * 2 ^ 59
def prefixEnd_5848218 : Nat := 4983230072969 + 3 ^ 40 * 5848218 * 2
def baseEnd_5848218 : Nat := 333660756252878339319949

theorem tailTrace_5848218 : CollatzResearch.WordTrace tailWord_5848218 prefixEnd_5848218 333660756252878339319949 := by
  unfold tailWord_5848218
  simp only [CollatzResearch.WordTrace]
  refine ⟨53325508481728114240322327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142201355951274971307526205 53325508481728114240322327)
  ·
    refine ⟨79988262722592171360483491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53325508481728114240322327 79988262722592171360483491)
    ·
      refine ⟨119982394083888257040725237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79988262722592171360483491 119982394083888257040725237)
      ·
        refine ⟨11248349445364524097567991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119982394083888257040725237 11248349445364524097567991)
        ·
          refine ⟨16872524168046786146351987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11248349445364524097567991 16872524168046786146351987)
          ·
            refine ⟨25308786252070179219527981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16872524168046786146351987 25308786252070179219527981)
            ·
              refine ⟨9490794844526317207322993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25308786252070179219527981 9490794844526317207322993)
              ·
                refine ⟨7118096133394737905492245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9490794844526317207322993 7118096133394737905492245)
                ·
                  refine ⟨333660756252878339319949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7118096133394737905492245 333660756252878339319949)
                  ·
                    rfl

theorem cell23_5848218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 6].length) (baseStart_5848218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848218 prefixEnd_5848218 := by exact prefixLift 5848218
  have htrace : WordTrace (prefixWord ++ tailWord_5848218) baseStart_5848218 baseEnd_5848218 := by
    simpa [prefixWord, tailWord_5848218, baseEnd_5848218] using wordTrace_append hprefix tailTrace_5848218
  have hstable : (prefixWord ++ tailWord_5848218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848218).length < 2 ^ (prefixWord ++ tailWord_5848218).sum := by decide
  have hdescent : baseEnd_5848218 < baseStart_5848218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848222 : List Nat := [4, 3, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_5848222 : Nat := 118140960795 + 5848222 * 2 ^ 59
def prefixEnd_5848222 : Nat := 4983230072969 + 3 ^ 40 * 5848222 * 2
def baseEnd_5848222 : Nat := 1000982953399507679409841

theorem tailTrace_5848222 : CollatzResearch.WordTrace tailWord_5848222 prefixEnd_5848222 1000982953399507679409841 := by
  unfold tailWord_5848222
  simp only [CollatzResearch.WordTrace]
  refine ⟨26662772477362245705554365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142201453212598643762956613 26662772477362245705554365)
  ·
    refine ⟨9998539679010842139582887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26662772477362245705554365 9998539679010842139582887)
    ·
      refine ⟨14997809518516263209374331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9998539679010842139582887 14997809518516263209374331)
      ·
        refine ⟨22496714277774394814061497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14997809518516263209374331 22496714277774394814061497)
        ·
          refine ⟨16872535708330796110546123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22496714277774394814061497 16872535708330796110546123)
          ·
            refine ⟨25308803562496194165819185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16872535708330796110546123 25308803562496194165819185)
            ·
              refine ⟨18981602671872145624364389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25308803562496194165819185 18981602671872145624364389)
              ·
                refine ⟨3559050500976027304568323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18981602671872145624364389 3559050500976027304568323)
                ·
                  refine ⟨5338575751464040956852485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3559050500976027304568323 5338575751464040956852485)
                  ·
                    refine ⟨1000982953399507679409841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5338575751464040956852485 1000982953399507679409841)
                    ·
                      rfl

theorem cell23_5848222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_5848222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848222 prefixEnd_5848222 := by exact prefixLift 5848222
  have htrace : WordTrace (prefixWord ++ tailWord_5848222) baseStart_5848222 baseEnd_5848222 := by
    simpa [prefixWord, tailWord_5848222, baseEnd_5848222] using wordTrace_append hprefix tailTrace_5848222
  have hstable : (prefixWord ++ tailWord_5848222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848222).length < 2 ^ (prefixWord ++ tailWord_5848222).sum := by decide
  have hdescent : baseEnd_5848222 < baseStart_5848222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848322 : List Nat := [3, 4, 1, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_5848322 : Nat := 118140960795 + 5848322 * 2 ^ 59
def prefixEnd_5848322 : Nat := 4983230072969 + 3 ^ 40 * 5848322 * 2
def baseEnd_5848322 : Nat := 3003000208263972646979063

theorem tailTrace_5848322 : CollatzResearch.WordTrace tailWord_5848322 prefixEnd_5848322 3003000208263972646979063 := by
  unfold tailWord_5848322
  simp only [CollatzResearch.WordTrace]
  refine ⟨53326456779633920680768805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142203884745690455148716813 53326456779633920680768805)
  ·
    refine ⟨9998710646181360127644151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53326456779633920680768805 9998710646181360127644151)
    ·
      refine ⟨14998065969272040191466227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9998710646181360127644151 14998065969272040191466227)
      ·
        refine ⟨22497098953908060287199341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14998065969272040191466227 22497098953908060287199341)
        ·
          refine ⟨8436412107715522607699753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22497098953908060287199341 8436412107715522607699753)
          ·
            refine ⟨6327309080786641955774815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8436412107715522607699753 6327309080786641955774815)
            ·
              refine ⟨9490963621179962933662223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6327309080786641955774815 9490963621179962933662223)
              ·
                refine ⟨14236445431769944400493335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9490963621179962933662223 14236445431769944400493335)
                ·
                  refine ⟨21354668147654916600740003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14236445431769944400493335 21354668147654916600740003)
                  ·
                    refine ⟨32032002221482374901110005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21354668147654916600740003 32032002221482374901110005)
                    ·
                      refine ⟨3003000208263972646979063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32032002221482374901110005 3003000208263972646979063)
                      ·
                        rfl

theorem cell23_5848322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_5848322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848322 prefixEnd_5848322 := by exact prefixLift 5848322
  have htrace : WordTrace (prefixWord ++ tailWord_5848322) baseStart_5848322 baseEnd_5848322 := by
    simpa [prefixWord, tailWord_5848322, baseEnd_5848322] using wordTrace_append hprefix tailTrace_5848322
  have hstable : (prefixWord ++ tailWord_5848322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848322).length < 2 ^ (prefixWord ++ tailWord_5848322).sum := by decide
  have hdescent : baseEnd_5848322 < baseStart_5848322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848362 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 3, 3, 2]
def baseStart_5848362 : Nat := 118140960795 + 5848362 * 2 ^ 59
def prefixEnd_5848362 : Nat := 4983230072969 + 3 ^ 40 * 5848362 * 2
def baseEnd_5848362 : Nat := 3003020747490152490478879

theorem tailTrace_5848362 : CollatzResearch.WordTrace tailWord_5848362 prefixEnd_5848362 3003020747490152490478879 := by
  unfold tailWord_5848362
  simp only [CollatzResearch.WordTrace]
  refine ⟨53326821509597692388632835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142204857358927179703020893 53326821509597692388632835)
  ·
    refine ⟨79990232264396538582949253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53326821509597692388632835 79990232264396538582949253)
    ·
      refine ⟨14998168549574350984302985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79990232264396538582949253 14998168549574350984302985)
      ·
        refine ⟨11248626412180763238227239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14998168549574350984302985 11248626412180763238227239)
        ·
          refine ⟨16872939618271144857340859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11248626412180763238227239 16872939618271144857340859)
          ·
            refine ⟨25309409427406717286011289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16872939618271144857340859 25309409427406717286011289)
            ·
              refine ⟨18982057070555037964508467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25309409427406717286011289 18982057070555037964508467)
              ·
                refine ⟨28473085605832556946762701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18982057070555037964508467 28473085605832556946762701)
                ·
                  refine ⟨10677407102187208855036013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28473085605832556946762701 10677407102187208855036013)
                  ·
                    refine ⟨4004027663320203320638505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10677407102187208855036013 4004027663320203320638505)
                    ·
                      refine ⟨3003020747490152490478879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4004027663320203320638505 3003020747490152490478879)
                      ·
                        rfl

theorem cell23_5848362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_5848362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848362 prefixEnd_5848362 := by exact prefixLift 5848362
  have htrace : WordTrace (prefixWord ++ tailWord_5848362) baseStart_5848362 baseEnd_5848362 := by
    simpa [prefixWord, tailWord_5848362, baseEnd_5848362] using wordTrace_append hprefix tailTrace_5848362
  have hstable : (prefixWord ++ tailWord_5848362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848362).length < 2 ^ (prefixWord ++ tailWord_5848362).sum := by decide
  have hdescent : baseEnd_5848362 < baseStart_5848362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848398 : List Nat := [4, 1, 1, 1, 1, 1, 6, 1, 7]
def baseStart_5848398 : Nat := 118140960795 + 5848398 * 2 ^ 59
def prefixEnd_5848398 : Nat := 4983230072969 + 3 ^ 40 * 5848398 * 2
def baseEnd_5848398 : Nat := 333671025865968261069857

theorem tailTrace_5848398 : CollatzResearch.WordTrace tailWord_5848398 prefixEnd_5848398 333671025865968261069857 := by
  unfold tailWord_5848398
  simp only [CollatzResearch.WordTrace]
  refine ⟨26663574883282543462855231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142205732710840231801894565 26663574883282543462855231)
  ·
    refine ⟨39995362324923815194282847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26663574883282543462855231 39995362324923815194282847)
    ·
      refine ⟨59993043487385722791424271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39995362324923815194282847 59993043487385722791424271)
      ·
        refine ⟨89989565231078584187136407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59993043487385722791424271 89989565231078584187136407)
        ·
          refine ⟨134984347846617876280704611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89989565231078584187136407 134984347846617876280704611)
          ·
            refine ⟨202476521769926814421056917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134984347846617876280704611 202476521769926814421056917)
            ·
              refine ⟨9491086957965319425987043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 202476521769926814421056917 9491086957965319425987043)
              ·
                refine ⟨14236630436947979138980565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9491086957965319425987043 14236630436947979138980565)
                ·
                  refine ⟨333671025865968261069857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14236630436947979138980565 333671025865968261069857)
                  ·
                    rfl

theorem cell23_5848398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_5848398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848398 prefixEnd_5848398 := by exact prefixLift 5848398
  have htrace : WordTrace (prefixWord ++ tailWord_5848398) baseStart_5848398 baseEnd_5848398 := by
    simpa [prefixWord, tailWord_5848398, baseEnd_5848398] using wordTrace_append hprefix tailTrace_5848398
  have hstable : (prefixWord ++ tailWord_5848398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848398).length < 2 ^ (prefixWord ++ tailWord_5848398).sum := by decide
  have hdescent : baseEnd_5848398 < baseStart_5848398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848408 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 2, 3, 3]
def baseStart_5848408 : Nat := 118140960795 + 5848408 * 2 ^ 59
def prefixEnd_5848408 : Nat := 4983230072969 + 3 ^ 40 * 5848408 * 2
def baseEnd_5848408 : Nat := 3003044367600259310503667

theorem tailTrace_5848408 : CollatzResearch.WordTrace tailWord_5848408 prefixEnd_5848408 3003044367600259310503667 := by
  unfold tailWord_5848408
  simp only [CollatzResearch.WordTrace]
  refine ⟨106654481898112059705352939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142205975864149412940470585 106654481898112059705352939)
  ·
    refine ⟨159981722847168089558029409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106654481898112059705352939 159981722847168089558029409)
    ·
      refine ⟨119986292135376067168522057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159981722847168089558029409 119986292135376067168522057)
      ·
        refine ⟨89989719101532050376391543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119986292135376067168522057 89989719101532050376391543)
        ·
          refine ⟨134984578652298075564587315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89989719101532050376391543 134984578652298075564587315)
          ·
            refine ⟨202476867978447113346880973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134984578652298075564587315 202476867978447113346880973)
            ·
              refine ⟨75928825491917667505080365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202476867978447113346880973 75928825491917667505080365)
              ·
                refine ⟨28473309559469125314405137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75928825491917667505080365 28473309559469125314405137)
                ·
                  refine ⟨21354982169601843985803853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28473309559469125314405137 21354982169601843985803853)
                  ·
                    refine ⟨8008118313600691494676445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21354982169601843985803853 8008118313600691494676445)
                    ·
                      refine ⟨3003044367600259310503667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8008118313600691494676445 3003044367600259310503667)
                      ·
                        rfl

theorem cell23_5848408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_5848408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848408 prefixEnd_5848408 := by exact prefixLift 5848408
  have htrace : WordTrace (prefixWord ++ tailWord_5848408) baseStart_5848408 baseEnd_5848408 := by
    simpa [prefixWord, tailWord_5848408, baseEnd_5848408] using wordTrace_append hprefix tailTrace_5848408
  have hstable : (prefixWord ++ tailWord_5848408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848408).length < 2 ^ (prefixWord ++ tailWord_5848408).sum := by decide
  have hdescent : baseEnd_5848408 < baseStart_5848408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848413 : List Nat := [1, 4, 5, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_5848413 : Nat := 118140960795 + 5848413 * 2 ^ 59
def prefixEnd_5848413 : Nat := 4983230072969 + 3 ^ 40 * 5848413 * 2
def baseEnd_5848413 : Nat := 3003046935003531790941145

theorem tailTrace_5848413 : CollatzResearch.WordTrace tailWord_5848413 prefixEnd_5848413 3003046935003531790941145 := by
  unfold tailWord_5848413
  simp only [CollatzResearch.WordTrace]
  refine ⟨213309146161206005264637893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142206097440804003509758595 213309146161206005264637893)
  ·
    refine ⟨39995464905226125987119605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213309146161206005264637893 39995464905226125987119605)
    ·
      refine ⟨3749574834864949311292463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39995464905226125987119605 3749574834864949311292463)
      ·
        refine ⟨5624362252297423966938695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3749574834864949311292463 5624362252297423966938695)
        ·
          refine ⟨8436543378446135950408043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5624362252297423966938695 8436543378446135950408043)
          ·
            refine ⟨12654815067669203925612065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8436543378446135950408043 12654815067669203925612065)
            ·
              refine ⟨9491111300751902944209049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12654815067669203925612065 9491111300751902944209049)
              ·
                refine ⟨7118333475563927208156787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9491111300751902944209049 7118333475563927208156787)
                ·
                  refine ⟨10677500213345890812235181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7118333475563927208156787 10677500213345890812235181)
                  ·
                    refine ⟨4004062580004709054588193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10677500213345890812235181 4004062580004709054588193)
                    ·
                      refine ⟨3003046935003531790941145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4004062580004709054588193 3003046935003531790941145)
                      ·
                        rfl

theorem cell23_5848413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_5848413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848413 prefixEnd_5848413 := by exact prefixLift 5848413
  have htrace : WordTrace (prefixWord ++ tailWord_5848413) baseStart_5848413 baseEnd_5848413 := by
    simpa [prefixWord, tailWord_5848413, baseEnd_5848413] using wordTrace_append hprefix tailTrace_5848413
  have hstable : (prefixWord ++ tailWord_5848413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848413).length < 2 ^ (prefixWord ++ tailWord_5848413).sum := by decide
  have hdescent : baseEnd_5848413 < baseStart_5848413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848428 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 1, 7]
def baseStart_5848428 : Nat := 118140960795 + 5848428 * 2 ^ 59
def prefixEnd_5848428 : Nat := 4983230072969 + 3 ^ 40 * 5848428 * 2
def baseEnd_5848428 : Nat := 1001018212404449744084525

theorem tailTrace_5848428 : CollatzResearch.WordTrace tailWord_5848428 prefixEnd_5848428 1001018212404449744084525 := by
  unfold tailWord_5848428
  simp only [CollatzResearch.WordTrace]
  refine ⟨106654846628075831413216969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142206462170767775217622625 106654846628075831413216969)
  ·
    refine ⟨79991134971056873559912727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106654846628075831413216969 79991134971056873559912727)
    ·
      refine ⟨119986702456585310339869091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79991134971056873559912727 119986702456585310339869091)
      ·
        refine ⟨179980053684877965509803637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119986702456585310339869091 179980053684877965509803637)
        ·
          refine ⟨16873130032957309266544091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179980053684877965509803637 16873130032957309266544091)
          ·
            refine ⟨25309695049435963899816137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16873130032957309266544091 25309695049435963899816137)
            ·
              refine ⟨18982271287076972924862103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25309695049435963899816137 18982271287076972924862103)
              ·
                refine ⟨28473406930615459387293155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18982271287076972924862103 28473406930615459387293155)
                ·
                  refine ⟨42710110395923189080939733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28473406930615459387293155 42710110395923189080939733)
                  ·
                    refine ⟨1001018212404449744084525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42710110395923189080939733 1001018212404449744084525)
                    ·
                      rfl

theorem cell23_5848428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_5848428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848428 prefixEnd_5848428 := by exact prefixLift 5848428
  have htrace : WordTrace (prefixWord ++ tailWord_5848428) baseStart_5848428 baseEnd_5848428 := by
    simpa [prefixWord, tailWord_5848428, baseEnd_5848428] using wordTrace_append hprefix tailTrace_5848428
  have hstable : (prefixWord ++ tailWord_5848428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848428).length < 2 ^ (prefixWord ++ tailWord_5848428).sum := by decide
  have hdescent : baseEnd_5848428 < baseStart_5848428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848449 : List Nat := [1, 2, 4, 3, 2, 1, 3, 2, 5]
def baseStart_5848449 : Nat := 118140960795 + 5848449 * 2 ^ 59
def prefixEnd_5848449 : Nat := 4983230072969 + 3 ^ 40 * 5848449 * 2
def baseEnd_5848449 : Nat := 333673935589677072232331

theorem tailTrace_5848449 : CollatzResearch.WordTrace tailWord_5848449 prefixEnd_5848449 333673935589677072232331 := by
  unfold tailWord_5848449
  simp only [CollatzResearch.WordTrace]
  refine ⟨213310459189075583412948401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142206972792717055608632267 213310459189075583412948401)
  ·
    refine ⟨159982844391806687559711301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213310459189075583412948401 159982844391806687559711301)
    ·
      refine ⟨29996783323463753917445869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159982844391806687559711301 29996783323463753917445869)
      ·
        refine ⟨11248793746298907719042201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29996783323463753917445869 11248793746298907719042201)
        ·
          refine ⟨8436595309724180789281651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11248793746298907719042201 8436595309724180789281651)
          ·
            refine ⟨12654892964586271183922477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8436595309724180789281651 12654892964586271183922477)
            ·
              refine ⟨4745584861719851693970929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12654892964586271183922477 4745584861719851693970929)
              ·
                refine ⟨3559188646289888770478197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4745584861719851693970929 3559188646289888770478197)
                ·
                  refine ⟨333673935589677072232331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3559188646289888770478197 333673935589677072232331)
                  ·
                    rfl

theorem cell23_5848449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 5].length) (baseStart_5848449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848449 prefixEnd_5848449 := by exact prefixLift 5848449
  have htrace : WordTrace (prefixWord ++ tailWord_5848449) baseStart_5848449 baseEnd_5848449 := by
    simpa [prefixWord, tailWord_5848449, baseEnd_5848449] using wordTrace_append hprefix tailTrace_5848449
  have hstable : (prefixWord ++ tailWord_5848449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848449).length < 2 ^ (prefixWord ++ tailWord_5848449).sum := by decide
  have hdescent : baseEnd_5848449 < baseStart_5848449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848482 : List Nat := [3, 3, 1, 2, 1, 3, 2, 1, 2, 1, 4]
def baseStart_5848482 : Nat := 118140960795 + 5848482 * 2 ^ 59
def prefixEnd_5848482 : Nat := 4983230072969 + 3 ^ 40 * 5848482 * 2
def baseEnd_5848482 : Nat := 3003082365168692020978327

theorem tailTrace_5848482 : CollatzResearch.WordTrace tailWord_5848482 prefixEnd_5848482 3003082365168692020978327 := by
  unfold tailWord_5848482
  simp only [CollatzResearch.WordTrace]
  refine ⟨53327915699489007512224925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142207775198637353365933133 53327915699489007512224925)
  ·
    refine ⟨19997968387308377817084347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53327915699489007512224925 19997968387308377817084347)
    ·
      refine ⟨29996952580962566725626521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19997968387308377817084347 29996952580962566725626521)
      ·
        refine ⟨22497714435721925044219891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29996952580962566725626521 22497714435721925044219891)
        ·
          refine ⟨33746571653582887566329837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22497714435721925044219891 33746571653582887566329837)
          ·
            refine ⟨12654964370093582837373689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33746571653582887566329837 12654964370093582837373689)
            ·
              refine ⟨9491223277570187128030267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12654964370093582837373689 9491223277570187128030267)
              ·
                refine ⟨14236834916355280692045401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9491223277570187128030267 14236834916355280692045401)
                ·
                  refine ⟨10677626187266460519034051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14236834916355280692045401 10677626187266460519034051)
                  ·
                    refine ⟨16016439280899690778551077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10677626187266460519034051 16016439280899690778551077)
                    ·
                      refine ⟨3003082365168692020978327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16016439280899690778551077 3003082365168692020978327)
                      ·
                        rfl

theorem cell23_5848482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_5848482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848482 prefixEnd_5848482 := by exact prefixLift 5848482
  have htrace : WordTrace (prefixWord ++ tailWord_5848482) baseStart_5848482 baseEnd_5848482 := by
    simpa [prefixWord, tailWord_5848482, baseEnd_5848482] using wordTrace_append hprefix tailTrace_5848482
  have hstable : (prefixWord ++ tailWord_5848482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848482).length < 2 ^ (prefixWord ++ tailWord_5848482).sum := by decide
  have hdescent : baseEnd_5848482 < baseStart_5848482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848566 : List Nat := [5, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3]
def baseStart_5848566 : Nat := 118140960795 + 5848566 * 2 ^ 59
def prefixEnd_5848566 : Nat := 4983230072969 + 3 ^ 40 * 5848566 * 2
def baseEnd_5848566 : Nat := 3003125497543669692327941

theorem tailTrace_5848566 : CollatzResearch.WordTrace tailWord_5848566 prefixEnd_5848566 3003125497543669692327941 := by
  unfold tailWord_5848566
  simp only [CollatzResearch.WordTrace]
  refine ⟨13332170408103232024684847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142209817686434474929971701 13332170408103232024684847)
  ·
    refine ⟨19998255612154848037027271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13332170408103232024684847 19998255612154848037027271)
    ·
      refine ⟨29997383418232272055540907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19998255612154848037027271 29997383418232272055540907)
      ·
        refine ⟨44996075127348408083311361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29997383418232272055540907 44996075127348408083311361)
        ·
          refine ⟨33747056345511306062483521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44996075127348408083311361 33747056345511306062483521)
          ·
            refine ⟨25310292259133479546862641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33747056345511306062483521 25310292259133479546862641)
            ·
              refine ⟨18982719194350109660146981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25310292259133479546862641 18982719194350109660146981)
              ·
                refine ⟨3559259848940645561277559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18982719194350109660146981 3559259848940645561277559)
                ·
                  refine ⟨5338889773410968341916339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3559259848940645561277559 5338889773410968341916339)
                  ·
                    refine ⟨8008334660116452512874509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5338889773410968341916339 8008334660116452512874509)
                    ·
                      refine ⟨3003125497543669692327941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8008334660116452512874509 3003125497543669692327941)
                      ·
                        rfl

theorem cell23_5848566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_5848566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848566 prefixEnd_5848566 := by exact prefixLift 5848566
  have htrace : WordTrace (prefixWord ++ tailWord_5848566) baseStart_5848566 baseEnd_5848566 := by
    simpa [prefixWord, tailWord_5848566, baseEnd_5848566] using wordTrace_append hprefix tailTrace_5848566
  have hstable : (prefixWord ++ tailWord_5848566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848566).length < 2 ^ (prefixWord ++ tailWord_5848566).sum := by decide
  have hdescent : baseEnd_5848566 < baseStart_5848566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848575 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 3]
def baseStart_5848575 : Nat := 118140960795 + 5848575 * 2 ^ 59
def prefixEnd_5848575 : Nat := 4983230072969 + 3 ^ 40 * 5848575 * 2
def baseEnd_5848575 : Nat := 3003130118869560157115399

theorem tailTrace_5848575 : CollatzResearch.WordTrace tailWord_5848575 prefixEnd_5848575 3003130118869560157115399 := by
  unfold tailWord_5848575
  simp only [CollatzResearch.WordTrace]
  refine ⟨213315054786619106932035179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142210036524412737954690119 213315054786619106932035179)
  ·
    refine ⟨319972582179928660398052769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213315054786619106932035179 319972582179928660398052769)
    ·
      refine ⟨239979436634946495298539577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319972582179928660398052769 239979436634946495298539577)
      ·
        refine ⟨179984577476209871473904683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239979436634946495298539577 179984577476209871473904683)
        ·
          refine ⟨269976866214314807210857025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179984577476209871473904683 269976866214314807210857025)
          ·
            refine ⟨202482649660736105408142769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269976866214314807210857025 202482649660736105408142769)
            ·
              refine ⟨151861987245552079056107077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202482649660736105408142769 151861987245552079056107077)
              ·
                refine ⟨28474122608541014823020077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151861987245552079056107077 28474122608541014823020077)
                ·
                  refine ⟨10677795978202880558632529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28474122608541014823020077 10677795978202880558632529)
                  ·
                    refine ⟨8008346983652160418974397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10677795978202880558632529 8008346983652160418974397)
                    ·
                      refine ⟨3003130118869560157115399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8008346983652160418974397 3003130118869560157115399)
                      ·
                        rfl

theorem cell23_5848575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 3].length) (baseStart_5848575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848575 prefixEnd_5848575 := by exact prefixLift 5848575
  have htrace : WordTrace (prefixWord ++ tailWord_5848575) baseStart_5848575 baseEnd_5848575 := by
    simpa [prefixWord, tailWord_5848575, baseEnd_5848575] using wordTrace_append hprefix tailTrace_5848575
  have hstable : (prefixWord ++ tailWord_5848575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848575).length < 2 ^ (prefixWord ++ tailWord_5848575).sum := by decide
  have hdescent : baseEnd_5848575 < baseStart_5848575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848595 : List Nat := [1, 1, 1, 2, 1, 6, 4, 7]
def baseStart_5848595 : Nat := 118140960795 + 5848595 * 2 ^ 59
def prefixEnd_5848595 : Nat := 4983230072969 + 3 ^ 40 * 5848595 * 2
def baseEnd_5848595 : Nat := 111227421795653706624641

theorem tailTrace_5848595 : CollatzResearch.WordTrace tailWord_5848595 prefixEnd_5848595 111227421795653706624641 := by
  unfold tailWord_5848595
  simp only [CollatzResearch.WordTrace]
  refine ⟨213315784246546650347763239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142210522831031100231842159 213315784246546650347763239)
  ·
    refine ⟨319973676369819975521644859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213315784246546650347763239 319973676369819975521644859)
    ·
      refine ⟨479960514554729963282467289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319973676369819975521644859 479960514554729963282467289)
      ·
        refine ⟨359970385916047472461850467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479960514554729963282467289 359970385916047472461850467)
        ·
          refine ⟨539955578874071208692775701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359970385916047472461850467 539955578874071208692775701)
          ·
            refine ⟨25310417759722087907473861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 539955578874071208692775701 25310417759722087907473861)
            ·
              refine ⟨4745703329947891482651349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25310417759722087907473861 4745703329947891482651349)
              ·
                refine ⟨111227421795653706624641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4745703329947891482651349 111227421795653706624641)
                ·
                  rfl

theorem cell23_5848595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 7].length) (baseStart_5848595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848595 prefixEnd_5848595 := by exact prefixLift 5848595
  have htrace : WordTrace (prefixWord ++ tailWord_5848595) baseStart_5848595 baseEnd_5848595 := by
    simpa [prefixWord, tailWord_5848595, baseEnd_5848595] using wordTrace_append hprefix tailTrace_5848595
  have hstable : (prefixWord ++ tailWord_5848595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848595).length < 2 ^ (prefixWord ++ tailWord_5848595).sum := by decide
  have hdescent : baseEnd_5848595 < baseStart_5848595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5848639 : List Nat := [1, 1, 2, 2, 3, 4, 1, 3, 2, 1, 3]
def baseStart_5848639 : Nat := 118140960795 + 5848639 * 2 ^ 59
def prefixEnd_5848639 : Nat := 4983230072969 + 3 ^ 40 * 5848639 * 2
def baseEnd_5848639 : Nat := 3003162981631447906715105

theorem tailTrace_5848639 : CollatzResearch.WordTrace tailWord_5848639 prefixEnd_5848639 3003162981631447906715105 := by
  unfold tailWord_5848639
  simp only [CollatzResearch.WordTrace]
  refine ⟨213317389058387245862364971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142211592705591497241576647 213317389058387245862364971)
  ·
    refine ⟨319976083587580868793547457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213317389058387245862364971 319976083587580868793547457)
    ·
      refine ⟨239982062690685651595160593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319976083587580868793547457 239982062690685651595160593)
      ·
        refine ⟨179986547018014238696370445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239982062690685651595160593 179986547018014238696370445)
        ·
          refine ⟨67494955131755339511138917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179986547018014238696370445 67494955131755339511138917)
          ·
            refine ⟨12655304087204126158338547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67494955131755339511138917 12655304087204126158338547)
            ·
              refine ⟨18982956130806189237507821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12655304087204126158338547 18982956130806189237507821)
              ·
                refine ⟨7118608549052320964065433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18982956130806189237507821 7118608549052320964065433)
                ·
                  refine ⟨5338956411789240723049075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7118608549052320964065433 5338956411789240723049075)
                  ·
                    refine ⟨8008434617683861084573613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5338956411789240723049075 8008434617683861084573613)
                    ·
                      refine ⟨3003162981631447906715105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8008434617683861084573613 3003162981631447906715105)
                      ·
                        rfl

theorem cell23_5848639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 1, 3].length) (baseStart_5848639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5848639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5848639 prefixEnd_5848639 := by exact prefixLift 5848639
  have htrace : WordTrace (prefixWord ++ tailWord_5848639) baseStart_5848639 baseEnd_5848639 := by
    simpa [prefixWord, tailWord_5848639, baseEnd_5848639] using wordTrace_append hprefix tailTrace_5848639
  have hstable : (prefixWord ++ tailWord_5848639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5848639).length < 2 ^ (prefixWord ++ tailWord_5848639).sum := by decide
  have hdescent : baseEnd_5848639 < baseStart_5848639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5848639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
