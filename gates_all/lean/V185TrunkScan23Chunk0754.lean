import V185TrunkScan23Chunk0753

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4458919 : List Nat := [1, 1, 6, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_4458919 : Nat := 118140960795 + 4458919 * 2 ^ 59
def prefixEnd_4458919 : Nat := 4983230072969 + 3 ^ 40 * 4458919 * 2
def baseEnd_4458919 : Nat := 2289568646465145192606311

theorem tailTrace_4458919 : CollatzResearch.WordTrace tailWord_4458919 prefixEnd_4458919 2289568646465145192606311 := by
  unfold tailWord_4458919
  simp only [CollatzResearch.WordTrace]
  refine ⟨162630136533105460582387811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108420091022070307054925207 162630136533105460582387811)
  ·
    refine ⟨243945204799658190873581717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162630136533105460582387811 243945204799658190873581717)
    ·
      refine ⟨11434931474983977697199143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 243945204799658190873581717 11434931474983977697199143)
      ·
        refine ⟨17152397212475966545798715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11434931474983977697199143 17152397212475966545798715)
        ·
          refine ⟨25728595818713949818698073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17152397212475966545798715 25728595818713949818698073)
          ·
            refine ⟨19296446864035462364023555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25728595818713949818698073 19296446864035462364023555)
            ·
              refine ⟨28944670296053193546035333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19296446864035462364023555 28944670296053193546035333)
              ·
                refine ⟨5427125680509973789881625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28944670296053193546035333 5427125680509973789881625)
                ·
                  refine ⟨4070344260382480342411219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5427125680509973789881625 4070344260382480342411219)
                  ·
                    refine ⟨6105516390573720513616829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4070344260382480342411219 6105516390573720513616829)
                    ·
                      refine ⟨2289568646465145192606311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6105516390573720513616829 2289568646465145192606311)
                      ·
                        rfl

theorem cell23_4458919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_4458919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458919 prefixEnd_4458919 := by exact prefixLift 4458919
  have htrace : WordTrace (prefixWord ++ tailWord_4458919) baseStart_4458919 baseEnd_4458919 := by
    simpa [prefixWord, tailWord_4458919, baseEnd_4458919] using wordTrace_append hprefix tailTrace_4458919
  have hstable : (prefixWord ++ tailWord_4458919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458919).length < 2 ^ (prefixWord ++ tailWord_4458919).sum := by decide
  have hdescent : baseEnd_4458919 < baseStart_4458919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458920 : List Nat := [2, 1, 6, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_4458920 : Nat := 118140960795 + 4458920 * 2 ^ 59
def prefixEnd_4458920 : Nat := 4983230072969 + 3 ^ 40 * 4458920 * 2
def baseEnd_4458920 : Nat := 2289569159945799688693807

theorem tailTrace_4458920 : CollatzResearch.WordTrace tailWord_4458920 prefixEnd_4458920 2289569159945799688693807 := by
  unfold tailWord_4458920
  simp only [CollatzResearch.WordTrace]
  refine ⟨81315086503050918876587107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108420115337401225168782809 81315086503050918876587107)
  ·
    refine ⟨121972629754576378314880661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81315086503050918876587107 121972629754576378314880661)
    ·
      refine ⟨5717467019745767733510031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 121972629754576378314880661 5717467019745767733510031)
      ·
        refine ⟨8576200529618651600265047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5717467019745767733510031 8576200529618651600265047)
        ·
          refine ⟨12864300794427977400397571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8576200529618651600265047 12864300794427977400397571)
          ·
            refine ⟨19296451191641966100596357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12864300794427977400397571 19296451191641966100596357)
            ·
              refine ⟨3618084598432868643861817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19296451191641966100596357 3618084598432868643861817)
              ·
                refine ⟨2713563448824651482896363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3618084598432868643861817 2713563448824651482896363)
                ·
                  refine ⟨4070345173236977224344545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2713563448824651482896363 4070345173236977224344545)
                  ·
                    refine ⟨3052758879927732918258409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4070345173236977224344545 3052758879927732918258409)
                    ·
                      refine ⟨2289569159945799688693807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3052758879927732918258409 2289569159945799688693807)
                      ·
                        rfl

theorem cell23_4458920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_4458920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458920 prefixEnd_4458920 := by exact prefixLift 4458920
  have htrace : WordTrace (prefixWord ++ tailWord_4458920) baseStart_4458920 baseEnd_4458920 := by
    simpa [prefixWord, tailWord_4458920, baseEnd_4458920] using wordTrace_append hprefix tailTrace_4458920
  have hstable : (prefixWord ++ tailWord_4458920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458920).length < 2 ^ (prefixWord ++ tailWord_4458920).sum := by decide
  have hdescent : baseEnd_4458920 < baseStart_4458920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4458935 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 2, 6]
def baseStart_4458935 : Nat := 118140960795 + 4458935 * 2 ^ 59
def prefixEnd_4458935 : Nat := 4983230072969 + 3 ^ 40 * 4458935 * 2
def baseEnd_4458935 : Nat := 763192287385205710002079

theorem tailTrace_4458935 : CollatzResearch.WordTrace tailWord_4458935 prefixEnd_4458935 763192287385205710002079 := by
  unfold tailWord_4458935
  simp only [CollatzResearch.WordTrace]
  refine ⟨162630720101047495314970259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108420480067364996876646839 162630720101047495314970259)
  ·
    refine ⟨243946080151571242972455389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162630720101047495314970259 243946080151571242972455389)
    ·
      refine ⟨91479780056839216114670771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243946080151571242972455389 91479780056839216114670771)
      ·
        refine ⟨137219670085258824172006157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91479780056839216114670771 137219670085258824172006157)
        ·
          refine ⟨51457376281972059064502309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137219670085258824172006157 51457376281972059064502309)
          ·
            refine ⟨9648258052869761074594183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51457376281972059064502309 9648258052869761074594183)
            ·
              refine ⟨14472387079304641611891275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9648258052869761074594183 14472387079304641611891275)
              ·
                refine ⟨21708580618956962417836913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14472387079304641611891275 21708580618956962417836913)
                ·
                  refine ⟨16281435464217721813377685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21708580618956962417836913 16281435464217721813377685)
                  ·
                    refine ⟨763192287385205710002079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16281435464217721813377685 763192287385205710002079)
                    ·
                      rfl

theorem cell23_4458935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_4458935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4458935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4458935 prefixEnd_4458935 := by exact prefixLift 4458935
  have htrace : WordTrace (prefixWord ++ tailWord_4458935) baseStart_4458935 baseEnd_4458935 := by
    simpa [prefixWord, tailWord_4458935, baseEnd_4458935] using wordTrace_append hprefix tailTrace_4458935
  have hstable : (prefixWord ++ tailWord_4458935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4458935).length < 2 ^ (prefixWord ++ tailWord_4458935).sum := by decide
  have hdescent : baseEnd_4458935 < baseStart_4458935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4458935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459012 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 1, 7]
def baseStart_4459012 : Nat := 118140960795 + 4459012 * 2 ^ 59
def prefixEnd_4459012 : Nat := 4983230072969 + 3 ^ 40 * 4459012 * 2
def baseEnd_4459012 : Nat := 763205466722004442914461

theorem tailTrace_4459012 : CollatzResearch.WordTrace tailWord_4459012 prefixEnd_4459012 763205466722004442914461 := by
  unfold tailWord_4459012
  simp only [CollatzResearch.WordTrace]
  refine ⟨81316764260884268732761645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108422352347845691643682193 81316764260884268732761645)
  ·
    refine ⟨30493786597831600774785617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81316764260884268732761645 30493786597831600774785617)
    ·
      refine ⟨22870339948373700581089213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30493786597831600774785617 22870339948373700581089213)
      ·
        refine ⟨8576377480640137717908455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22870339948373700581089213 8576377480640137717908455)
        ·
          refine ⟨12864566220960206576862683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8576377480640137717908455 12864566220960206576862683)
          ·
            refine ⟨19296849331440309865294025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12864566220960206576862683 19296849331440309865294025)
            ·
              refine ⟨14472636998580232398970519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19296849331440309865294025 14472636998580232398970519)
              ·
                refine ⟨21708955497870348598455779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14472636998580232398970519 21708955497870348598455779)
                ·
                  refine ⟨32563433246805522897683669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21708955497870348598455779 32563433246805522897683669)
                  ·
                    refine ⟨763205466722004442914461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32563433246805522897683669 763205466722004442914461)
                    ·
                      rfl

theorem cell23_4459012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_4459012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459012 prefixEnd_4459012 := by exact prefixLift 4459012
  have htrace : WordTrace (prefixWord ++ tailWord_4459012) baseStart_4459012 baseEnd_4459012 := by
    simpa [prefixWord, tailWord_4459012, baseEnd_4459012] using wordTrace_append hprefix tailTrace_4459012
  have hstable : (prefixWord ++ tailWord_4459012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459012).length < 2 ^ (prefixWord ++ tailWord_4459012).sum := by decide
  have hdescent : baseEnd_4459012 < baseStart_4459012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459032 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 4, 1, 4]
def baseStart_4459032 : Nat := 118140960795 + 4459032 * 2 ^ 59
def prefixEnd_4459032 : Nat := 4983230072969 + 3 ^ 40 * 4459032 * 2
def baseEnd_4459032 : Nat := 2289626669779103250493291

theorem tailTrace_4459032 : CollatzResearch.WordTrace tailWord_4459032 prefixEnd_4459032 2289626669779103250493291 := by
  unfold tailWord_4459032
  simp only [CollatzResearch.WordTrace]
  refine ⟨81317128990848040440625675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108422838654464053920834233 81317128990848040440625675)
  ·
    refine ⟨121975693486272060660938513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81317128990848040440625675 121975693486272060660938513)
    ·
      refine ⟨91481770114704045495703885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121975693486272060660938513 91481770114704045495703885)
      ·
        refine ⟨34305663793014017060888957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91481770114704045495703885 34305663793014017060888957)
        ·
          refine ⟨12864623922380256397833359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34305663793014017060888957 12864623922380256397833359)
          ·
            refine ⟨19296935883570384596750039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12864623922380256397833359 19296935883570384596750039)
            ·
              refine ⟨28945403825355576895125059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19296935883570384596750039 28945403825355576895125059)
              ·
                refine ⟨43418105738033365342687589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28945403825355576895125059 43418105738033365342687589)
                ·
                  refine ⟨8140894825881256001753923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43418105738033365342687589 8140894825881256001753923)
                  ·
                    refine ⟨12211342238821884002630885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8140894825881256001753923 12211342238821884002630885)
                    ·
                      refine ⟨2289626669779103250493291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12211342238821884002630885 2289626669779103250493291)
                      ·
                        rfl

theorem cell23_4459032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_4459032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459032 prefixEnd_4459032 := by exact prefixLift 4459032
  have htrace : WordTrace (prefixWord ++ tailWord_4459032) baseStart_4459032 baseEnd_4459032 := by
    simpa [prefixWord, tailWord_4459032, baseEnd_4459032] using wordTrace_append hprefix tailTrace_4459032
  have hstable : (prefixWord ++ tailWord_4459032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459032).length < 2 ^ (prefixWord ++ tailWord_4459032).sum := by decide
  have hdescent : baseEnd_4459032 < baseStart_4459032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459035 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 3]
def baseStart_4459035 : Nat := 118140960795 + 4459035 * 2 ^ 59
def prefixEnd_4459035 : Nat := 4983230072969 + 3 ^ 40 * 4459035 * 2
def baseEnd_4459035 : Nat := 2289628210221066738755777

theorem tailTrace_4459035 : CollatzResearch.WordTrace tailWord_4459035 prefixEnd_4459035 2289628210221066738755777 := by
  unfold tailWord_4459035
  simp only [CollatzResearch.WordTrace]
  refine ⟨162634367400685212393610559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108422911600456808262407039 162634367400685212393610559)
  ·
    refine ⟨243951551101027818590415839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162634367400685212393610559 243951551101027818590415839)
    ·
      refine ⟨365927326651541727885623759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243951551101027818590415839 365927326651541727885623759)
      ·
        refine ⟨548890989977312591828435639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365927326651541727885623759 548890989977312591828435639)
        ·
          refine ⟨823336484965968887742653459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548890989977312591828435639 823336484965968887742653459)
          ·
            refine ⟨1235004727448953331613980189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 823336484965968887742653459 1235004727448953331613980189)
            ·
              refine ⟨463126772793357499355242571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1235004727448953331613980189 463126772793357499355242571)
              ·
                refine ⟨694690159190036249032863857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463126772793357499355242571 694690159190036249032863857)
                ·
                  refine ⟨521017619392527186774647893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 694690159190036249032863857 521017619392527186774647893)
                  ·
                    refine ⟨6105675227256177970015405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 521017619392527186774647893 6105675227256177970015405)
                    ·
                      refine ⟨2289628210221066738755777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6105675227256177970015405 2289628210221066738755777)
                      ·
                        rfl

theorem cell23_4459035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 3].length) (baseStart_4459035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459035 prefixEnd_4459035 := by exact prefixLift 4459035
  have htrace : WordTrace (prefixWord ++ tailWord_4459035) baseStart_4459035 baseEnd_4459035 := by
    simpa [prefixWord, tailWord_4459035, baseEnd_4459035] using wordTrace_append hprefix tailTrace_4459035
  have hstable : (prefixWord ++ tailWord_4459035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459035).length < 2 ^ (prefixWord ++ tailWord_4459035).sum := by decide
  have hdescent : baseEnd_4459035 < baseStart_4459035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459045 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 2, 1, 6]
def baseStart_4459045 : Nat := 118140960795 + 4459045 * 2 ^ 59
def prefixEnd_4459045 : Nat := 4983230072969 + 3 ^ 40 * 4459045 * 2
def baseEnd_4459045 : Nat := 2289633345027611699630731

theorem tailTrace_4459045 : CollatzResearch.WordTrace tailWord_4459045 prefixEnd_4459045 2289633345027611699630731 := by
  unfold tailWord_4459045
  simp only [CollatzResearch.WordTrace]
  refine ⟨162634732130648984101474589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108423154753765989400983059 162634732130648984101474589)
  ·
    refine ⟨60988024548993369038052971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162634732130648984101474589 60988024548993369038052971)
    ·
      refine ⟨91482036823490053557079457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60988024548993369038052971 91482036823490053557079457)
      ·
        refine ⟨68611527617617540167809593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91482036823490053557079457 68611527617617540167809593)
        ·
          refine ⟨51458645713213155125857195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68611527617617540167809593 51458645713213155125857195)
          ·
            refine ⟨77187968569819732688785793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51458645713213155125857195 77187968569819732688785793)
            ·
              refine ⟨57890976427364799516589345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77187968569819732688785793 57890976427364799516589345)
              ·
                refine ⟨43418232320523599637442009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57890976427364799516589345 43418232320523599637442009)
                ·
                  refine ⟨32563674240392699728081507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43418232320523599637442009 32563674240392699728081507)
                  ·
                    refine ⟨48845511360589049592122261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32563674240392699728081507 48845511360589049592122261)
                    ·
                      refine ⟨2289633345027611699630731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48845511360589049592122261 2289633345027611699630731)
                      ·
                        rfl

theorem cell23_4459045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_4459045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459045 prefixEnd_4459045 := by exact prefixLift 4459045
  have htrace : WordTrace (prefixWord ++ tailWord_4459045) baseStart_4459045 baseEnd_4459045 := by
    simpa [prefixWord, tailWord_4459045, baseEnd_4459045] using wordTrace_append hprefix tailTrace_4459045
  have hstable : (prefixWord ++ tailWord_4459045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459045).length < 2 ^ (prefixWord ++ tailWord_4459045).sum := by decide
  have hdescent : baseEnd_4459045 < baseStart_4459045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459069 : List Nat := [1, 4, 1, 3, 2, 1, 1, 3, 2, 2, 3]
def baseStart_4459069 : Nat := 118140960795 + 4459069 * 2 ^ 59
def prefixEnd_4459069 : Nat := 4983230072969 + 3 ^ 40 * 4459069 * 2
def baseEnd_4459069 : Nat := 2289645668563319605730621

theorem tailTrace_4459069 : CollatzResearch.WordTrace tailWord_4459069 prefixEnd_4459069 2289645668563319605730621 := by
  unfold tailWord_4459069
  simp only [CollatzResearch.WordTrace]
  refine ⟨162635607482562036200348261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108423738321708024133565507 162635607482562036200348261)
  ·
    refine ⟨30494176402980381787565299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162635607482562036200348261 30494176402980381787565299)
    ·
      refine ⟨45741264604470572681347949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30494176402980381787565299 45741264604470572681347949)
      ·
        refine ⟨17152974226676464755505481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45741264604470572681347949 17152974226676464755505481)
        ·
          refine ⟨12864730670007348566629111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17152974226676464755505481 12864730670007348566629111)
          ·
            refine ⟨19297096005011022849943667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12864730670007348566629111 19297096005011022849943667)
            ·
              refine ⟨28945644007516534274915501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19297096005011022849943667 28945644007516534274915501)
              ·
                refine ⟨10854616502818700353093313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28945644007516534274915501 10854616502818700353093313)
                ·
                  refine ⟨8140962377114025264819985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10854616502818700353093313 8140962377114025264819985)
                  ·
                    refine ⟨6105721782835518948614989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8140962377114025264819985 6105721782835518948614989)
                    ·
                      refine ⟨2289645668563319605730621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6105721782835518948614989 2289645668563319605730621)
                      ·
                        rfl

theorem cell23_4459069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_4459069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459069 prefixEnd_4459069 := by exact prefixLift 4459069
  have htrace : WordTrace (prefixWord ++ tailWord_4459069) baseStart_4459069 baseEnd_4459069 := by
    simpa [prefixWord, tailWord_4459069, baseEnd_4459069] using wordTrace_append hprefix tailTrace_4459069
  have hstable : (prefixWord ++ tailWord_4459069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459069).length < 2 ^ (prefixWord ++ tailWord_4459069).sum := by decide
  have hdescent : baseEnd_4459069 < baseStart_4459069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459132 : List Nat := [2, 2, 2, 1, 1, 2, 4, 2, 1, 6]
def baseStart_4459132 : Nat := 118140960795 + 4459132 * 2 ^ 59
def prefixEnd_4459132 : Nat := 4983230072969 + 3 ^ 40 * 4459132 * 2
def baseEnd_4459132 : Nat := 763226005948184286414277

theorem tailTrace_4459132 : CollatzResearch.WordTrace tailWord_4459132 prefixEnd_4459132 763226005948184286414277 := by
  unfold tailWord_4459132
  simp only [CollatzResearch.WordTrace]
  refine ⟨81318952640666898979945825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108425270187555865306594433 81318952640666898979945825)
  ·
    refine ⟨60989214480500174234959369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81318952640666898979945825 60989214480500174234959369)
    ·
      refine ⟨45741910860375130676219527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60989214480500174234959369 45741910860375130676219527)
      ·
        refine ⟨68612866290562696014329291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45741910860375130676219527 68612866290562696014329291)
        ·
          refine ⟨102919299435844044021493937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68612866290562696014329291 102919299435844044021493937)
          ·
            refine ⟨77189474576883033016120453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102919299435844044021493937 77189474576883033016120453)
            ·
              refine ⟨14473026483165568690522585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77189474576883033016120453 14473026483165568690522585)
              ·
                refine ⟨10854769862374176517891939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14473026483165568690522585 10854769862374176517891939)
                ·
                  refine ⟨16282154793561264776837909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10854769862374176517891939 16282154793561264776837909)
                  ·
                    refine ⟨763226005948184286414277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16282154793561264776837909 763226005948184286414277)
                    ·
                      rfl

theorem cell23_4459132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_4459132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459132 prefixEnd_4459132 := by exact prefixLift 4459132
  have htrace : WordTrace (prefixWord ++ tailWord_4459132) baseStart_4459132 baseEnd_4459132 := by
    simpa [prefixWord, tailWord_4459132, baseEnd_4459132] using wordTrace_append hprefix tailTrace_4459132
  have hstable : (prefixWord ++ tailWord_4459132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459132).length < 2 ^ (prefixWord ++ tailWord_4459132).sum := by decide
  have hdescent : baseEnd_4459132 < baseStart_4459132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459136 : List Nat := [2, 1, 1, 2, 1, 7, 2, 1, 1, 5]
def baseStart_4459136 : Nat := 118140960795 + 4459136 * 2 ^ 59
def prefixEnd_4459136 : Nat := 4983230072969 + 3 ^ 40 * 4459136 * 2
def baseEnd_4459136 : Nat := 763226690589056947864271

theorem tailTrace_4459136 : CollatzResearch.WordTrace tailWord_4459136 prefixEnd_4459136 763226690589056947864271 := by
  unfold tailWord_4459136
  simp only [CollatzResearch.WordTrace]
  refine ⟨81319025586659653321518631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108425367448879537762024841 81319025586659653321518631)
  ·
    refine ⟨121978538379989479982277947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81319025586659653321518631 121978538379989479982277947)
    ·
      refine ⟨182967807569984219973416921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121978538379989479982277947 182967807569984219973416921)
      ·
        refine ⟨137225855677488164980062691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182967807569984219973416921 137225855677488164980062691)
        ·
          refine ⟨205838783516232247470094037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137225855677488164980062691 205838783516232247470094037)
          ·
            refine ⟨4824346488661693300080329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 205838783516232247470094037 4824346488661693300080329)
            ·
              refine ⟨3618259866496269975060247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4824346488661693300080329 3618259866496269975060247)
              ·
                refine ⟨5427389799744404962590371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3618259866496269975060247 5427389799744404962590371)
                ·
                  refine ⟨8141084699616607443885557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5427389799744404962590371 8141084699616607443885557)
                  ·
                    refine ⟨763226690589056947864271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8141084699616607443885557 763226690589056947864271)
                    ·
                      rfl

theorem cell23_4459136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 1, 5].length) (baseStart_4459136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459136 prefixEnd_4459136 := by exact prefixLift 4459136
  have htrace : WordTrace (prefixWord ++ tailWord_4459136) baseStart_4459136 baseEnd_4459136 := by
    simpa [prefixWord, tailWord_4459136, baseEnd_4459136] using wordTrace_append hprefix tailTrace_4459136
  have hstable : (prefixWord ++ tailWord_4459136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459136).length < 2 ^ (prefixWord ++ tailWord_4459136).sum := by decide
  have hdescent : baseEnd_4459136 < baseStart_4459136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459169 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 1, 1, 6]
def baseStart_4459169 : Nat := 118140960795 + 4459169 * 2 ^ 59
def prefixEnd_4459169 : Nat := 4983230072969 + 3 ^ 40 * 4459169 * 2
def baseEnd_4459169 : Nat := 2289697016628769214480161

theorem tailTrace_4459169 : CollatzResearch.WordTrace tailWord_4459169 prefixEnd_4459169 2289697016628769214480161 := by
  unfold tailWord_4459169
  simp only [CollatzResearch.WordTrace]
  refine ⟨162639254782199753278988561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108426169854799835519325707 162639254782199753278988561)
  ·
    refine ⟨121979441086649814959241421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162639254782199753278988561 121979441086649814959241421)
    ·
      refine ⟨45742290407493680609715533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121979441086649814959241421 45742290407493680609715533)
      ·
        refine ⟨17153358902810130228643325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45742290407493680609715533 17153358902810130228643325)
        ·
          refine ⟨6432509588553798835741247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17153358902810130228643325 6432509588553798835741247)
          ·
            refine ⟨9648764382830698253611871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6432509588553798835741247 9648764382830698253611871)
            ·
              refine ⟨14473146574246047380417807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9648764382830698253611871 14473146574246047380417807)
              ·
                refine ⟨21709719861369071070626711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14473146574246047380417807 21709719861369071070626711)
                ·
                  refine ⟨32564579792053606605940067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21709719861369071070626711 32564579792053606605940067)
                  ·
                    refine ⟨48846869688080409908910101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32564579792053606605940067 48846869688080409908910101)
                    ·
                      refine ⟨2289697016628769214480161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48846869688080409908910101 2289697016628769214480161)
                      ·
                        rfl

theorem cell23_4459169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_4459169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459169 prefixEnd_4459169 := by exact prefixLift 4459169
  have htrace : WordTrace (prefixWord ++ tailWord_4459169) baseStart_4459169 baseEnd_4459169 := by
    simpa [prefixWord, tailWord_4459169, baseEnd_4459169] using wordTrace_append hprefix tailTrace_4459169
  have hstable : (prefixWord ++ tailWord_4459169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459169).length < 2 ^ (prefixWord ++ tailWord_4459169).sum := by decide
  have hdescent : baseEnd_4459169 < baseStart_4459169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459223 : List Nat := [1, 1, 3, 2, 1, 4, 4, 1, 2, 1, 3]
def baseStart_4459223 : Nat := 118140960795 + 4459223 * 2 ^ 59
def prefixEnd_4459223 : Nat := 4983230072969 + 3 ^ 40 * 4459223 * 2
def baseEnd_4459223 : Nat := 2289724744584112003204913

theorem tailTrace_4459223 : CollatzResearch.WordTrace tailWord_4459223 prefixEnd_4459223 2289724744584112003204913 := by
  unfold tailWord_4459223
  simp only [CollatzResearch.WordTrace]
  refine ⟨162641224324004120501454323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108427482882669413667636215 162641224324004120501454323)
  ·
    refine ⟨243961836486006180752181485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162641224324004120501454323 243961836486006180752181485)
    ·
      refine ⟨91485688682252317782068057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243961836486006180752181485 91485688682252317782068057)
      ·
        refine ⟨68614266511689238336551043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91485688682252317782068057 68614266511689238336551043)
        ·
          refine ⟨102921399767533857504826565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68614266511689238336551043 102921399767533857504826565)
          ·
            refine ⟨19297762456412598282154981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102921399767533857504826565 19297762456412598282154981)
            ·
              refine ⟨3618330460577362177904059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19297762456412598282154981 3618330460577362177904059)
              ·
                refine ⟨5427495690866043266856089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3618330460577362177904059 5427495690866043266856089)
                ·
                  refine ⟨4070621768149532450142067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5427495690866043266856089 4070621768149532450142067)
                  ·
                    refine ⟨6105932652224298675213101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4070621768149532450142067 6105932652224298675213101)
                    ·
                      refine ⟨2289724744584112003204913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6105932652224298675213101 2289724744584112003204913)
                      ·
                        rfl

theorem cell23_4459223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_4459223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459223 prefixEnd_4459223 := by exact prefixLift 4459223
  have htrace : WordTrace (prefixWord ++ tailWord_4459223) baseStart_4459223 baseEnd_4459223 := by
    simpa [prefixWord, tailWord_4459223, baseEnd_4459223] using wordTrace_append hprefix tailTrace_4459223
  have hstable : (prefixWord ++ tailWord_4459223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459223).length < 2 ^ (prefixWord ++ tailWord_4459223).sum := by decide
  have hdescent : baseEnd_4459223 < baseStart_4459223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459233 : List Nat := [1, 2, 3, 1, 4, 1, 3, 2, 1, 3, 2]
def baseStart_4459233 : Nat := 118140960795 + 4459233 * 2 ^ 59
def prefixEnd_4459233 : Nat := 4983230072969 + 3 ^ 40 * 4459233 * 2
def baseEnd_4459233 : Nat := 2289729879390656964079867

theorem tailTrace_4459233 : CollatzResearch.WordTrace tailWord_4459233 prefixEnd_4459233 2289729879390656964079867 := by
  unfold tailWord_4459233
  simp only [CollatzResearch.WordTrace]
  refine ⟨162641589053967892209318353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108427726035978594806212235 162641589053967892209318353)
  ·
    refine ⟨121981191790475919156988765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162641589053967892209318353 121981191790475919156988765)
    ·
      refine ⟨45742946921428469683870787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121981191790475919156988765 45742946921428469683870787)
      ·
        refine ⟨68614420382142704525806181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45742946921428469683870787 68614420382142704525806181)
        ·
          refine ⟨12865203821651757098588659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68614420382142704525806181 12865203821651757098588659)
          ·
            refine ⟨19297805732477635647882989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12865203821651757098588659 19297805732477635647882989)
            ·
              refine ⟨7236677149679113367956121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19297805732477635647882989 7236677149679113367956121)
              ·
                refine ⟨5427507862259335025967091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7236677149679113367956121 5427507862259335025967091)
                ·
                  refine ⟨8141261793389002538950637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5427507862259335025967091 8141261793389002538950637)
                  ·
                    refine ⟨3052973172520875952106489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8141261793389002538950637 3052973172520875952106489)
                    ·
                      refine ⟨2289729879390656964079867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3052973172520875952106489 2289729879390656964079867)
                      ·
                        rfl

theorem cell23_4459233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_4459233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459233 prefixEnd_4459233 := by exact prefixLift 4459233
  have htrace : WordTrace (prefixWord ++ tailWord_4459233) baseStart_4459233 baseEnd_4459233 := by
    simpa [prefixWord, tailWord_4459233, baseEnd_4459233] using wordTrace_append hprefix tailTrace_4459233
  have hstable : (prefixWord ++ tailWord_4459233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459233).length < 2 ^ (prefixWord ++ tailWord_4459233).sum := by decide
  have hdescent : baseEnd_4459233 < baseStart_4459233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459246 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 3, 4, 2]
def baseStart_4459246 : Nat := 118140960795 + 4459246 * 2 ^ 59
def prefixEnd_4459246 : Nat := 4983230072969 + 3 ^ 40 * 4459246 * 2
def baseEnd_4459246 : Nat := 2289736554639165413217307

theorem tailTrace_4459246 : CollatzResearch.WordTrace tailWord_4459246 prefixEnd_4459246 2289736554639165413217307 := by
  unfold tailWord_4459246
  simp only [CollatzResearch.WordTrace]
  refine ⟨20330257900365099428692699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108428042135280530286361061 20330257900365099428692699)
  ·
    refine ⟨30495386850547649143039049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20330257900365099428692699 30495386850547649143039049)
    ·
      refine ⟨22871540137910736857279287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30495386850547649143039049 22871540137910736857279287)
      ·
        refine ⟨34307310206866105285918931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22871540137910736857279287 34307310206866105285918931)
        ·
          refine ⟨51460965310299157928878397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34307310206866105285918931 51460965310299157928878397)
          ·
            refine ⟨19297861991362184223329399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51460965310299157928878397 19297861991362184223329399)
            ·
              refine ⟨28946792987043276334994099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19297861991362184223329399 28946792987043276334994099)
              ·
                refine ⟨43420189480564914502491149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28946792987043276334994099 43420189480564914502491149)
                ·
                  refine ⟨16282571055211842938434181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43420189480564914502491149 16282571055211842938434181)
                  ·
                    refine ⟨3052982072852220550956409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16282571055211842938434181 3052982072852220550956409)
                    ·
                      refine ⟨2289736554639165413217307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3052982072852220550956409 2289736554639165413217307)
                      ·
                        rfl

theorem cell23_4459246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_4459246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459246 prefixEnd_4459246 := by exact prefixLift 4459246
  have htrace : WordTrace (prefixWord ++ tailWord_4459246) baseStart_4459246 baseEnd_4459246 := by
    simpa [prefixWord, tailWord_4459246, baseEnd_4459246] using wordTrace_append hprefix tailTrace_4459246
  have hstable : (prefixWord ++ tailWord_4459246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459246).length < 2 ^ (prefixWord ++ tailWord_4459246).sum := by decide
  have hdescent : baseEnd_4459246 < baseStart_4459246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459250 : List Nat := [3, 2, 1, 3, 1, 3, 3, 1, 1, 3, 2]
def baseStart_4459250 : Nat := 118140960795 + 4459250 * 2 ^ 59
def prefixEnd_4459250 : Nat := 4983230072969 + 3 ^ 40 * 4459250 * 2
def baseEnd_4459250 : Nat := 2289738608561783397567289

theorem tailTrace_4459250 : CollatzResearch.WordTrace tailWord_4459250 prefixEnd_4459250 2289738608561783397567289 := by
  unfold tailWord_4459250
  simp only [CollatzResearch.WordTrace]
  refine ⟨40660552273726576028171801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108428139396604202741791469 40660552273726576028171801)
  ·
    refine ⟨30495414205294932021128851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40660552273726576028171801 30495414205294932021128851)
    ·
      refine ⟨45743121307942398031693277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30495414205294932021128851 45743121307942398031693277)
      ·
        refine ⟨17153670490478399261884979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45743121307942398031693277 17153670490478399261884979)
        ·
          refine ⟨25730505735717598892827469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17153670490478399261884979 25730505735717598892827469)
          ·
            refine ⟨9648939650894099584810301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25730505735717598892827469 9648939650894099584810301)
            ·
              refine ⟨3618352369085287344303863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9648939650894099584810301 3618352369085287344303863)
              ·
                refine ⟨5427528553627931016455795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3618352369085287344303863 5427528553627931016455795)
                ·
                  refine ⟨8141292830441896524683693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5427528553627931016455795 8141292830441896524683693)
                  ·
                    refine ⟨3052984811415711196756385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8141292830441896524683693 3052984811415711196756385)
                    ·
                      refine ⟨2289738608561783397567289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3052984811415711196756385 2289738608561783397567289)
                      ·
                        rfl

theorem cell23_4459250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_4459250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459250 prefixEnd_4459250 := by exact prefixLift 4459250
  have htrace : WordTrace (prefixWord ++ tailWord_4459250) baseStart_4459250 baseEnd_4459250 := by
    simpa [prefixWord, tailWord_4459250, baseEnd_4459250] using wordTrace_append hprefix tailTrace_4459250
  have hstable : (prefixWord ++ tailWord_4459250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459250).length < 2 ^ (prefixWord ++ tailWord_4459250).sum := by decide
  have hdescent : baseEnd_4459250 < baseStart_4459250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459266 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_4459266 : Nat := 118140960795 + 4459266 * 2 ^ 59
def prefixEnd_4459266 : Nat := 4983230072969 + 3 ^ 40 * 4459266 * 2
def baseEnd_4459266 : Nat := 2289746824252255334967215

theorem tailTrace_4459266 : CollatzResearch.WordTrace tailWord_4459266 prefixEnd_4459266 2289746824252255334967215 := by
  unfold tailWord_4459266
  simp only [CollatzResearch.WordTrace]
  refine ⟨40660698165712084711317413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108428528441898892563513101 40660698165712084711317413)
  ·
    refine ⟨7623880906071015883372015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40660698165712084711317413 7623880906071015883372015)
    ·
      refine ⟨11435821359106523825058023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7623880906071015883372015 11435821359106523825058023)
      ·
        refine ⟨17153732038659785737587035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11435821359106523825058023 17153732038659785737587035)
        ·
          refine ⟨25730598057989678606380553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17153732038659785737587035 25730598057989678606380553)
          ·
            refine ⟨19297948543492258954785415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25730598057989678606380553 19297948543492258954785415)
            ·
              refine ⟨28946922815238388432178123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19297948543492258954785415 28946922815238388432178123)
              ·
                refine ⟨43420384222857582648267185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28946922815238388432178123 43420384222857582648267185)
                ·
                  refine ⟨32565288167143186986200389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43420384222857582648267185 32565288167143186986200389)
                  ·
                    refine ⟨6105991531339347559912573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32565288167143186986200389 6105991531339347559912573)
                    ·
                      refine ⟨2289746824252255334967215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6105991531339347559912573 2289746824252255334967215)
                      ·
                        rfl

theorem cell23_4459266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_4459266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459266 prefixEnd_4459266 := by exact prefixLift 4459266
  have htrace : WordTrace (prefixWord ++ tailWord_4459266) baseStart_4459266 baseEnd_4459266 := by
    simpa [prefixWord, tailWord_4459266, baseEnd_4459266] using wordTrace_append hprefix tailTrace_4459266
  have hstable : (prefixWord ++ tailWord_4459266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459266).length < 2 ^ (prefixWord ++ tailWord_4459266).sum := by decide
  have hdescent : baseEnd_4459266 < baseStart_4459266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459279 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 3]
def baseStart_4459279 : Nat := 118140960795 + 4459279 * 2 ^ 59
def prefixEnd_4459279 : Nat := 4983230072969 + 3 ^ 40 * 4459279 * 2
def baseEnd_4459279 : Nat := 2289753499500763784104655

theorem tailTrace_4459279 : CollatzResearch.WordTrace tailWord_4459279 prefixEnd_4459279 2289753499500763784104655 := by
  unfold tailWord_4459279
  simp only [CollatzResearch.WordTrace]
  refine ⟨162643266811801242065492891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108428844541200828043661927 162643266811801242065492891)
  ·
    refine ⟨243964900217701863098239337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162643266811801242065492891 243964900217701863098239337)
    ·
      refine ⟨182973675163276397323679503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243964900217701863098239337 182973675163276397323679503)
      ·
        refine ⟨274460512744914595985519255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182973675163276397323679503 274460512744914595985519255)
        ·
          refine ⟨411690769117371893978278883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274460512744914595985519255 411690769117371893978278883)
          ·
            refine ⟨617536153676057840967418325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 411690769117371893978278883 617536153676057840967418325)
            ·
              refine ⟨14473503601782605647673867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 617536153676057840967418325 14473503601782605647673867)
              ·
                refine ⟨21710255402673908471510801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14473503601782605647673867 21710255402673908471510801)
                ·
                  refine ⟨16282691552005431353633101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21710255402673908471510801 16282691552005431353633101)
                  ·
                    refine ⟨6106009332002036757612413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16282691552005431353633101 6106009332002036757612413)
                    ·
                      refine ⟨2289753499500763784104655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6106009332002036757612413 2289753499500763784104655)
                      ·
                        rfl

theorem cell23_4459279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 3].length) (baseStart_4459279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459279 prefixEnd_4459279 := by exact prefixLift 4459279
  have htrace : WordTrace (prefixWord ++ tailWord_4459279) baseStart_4459279 baseEnd_4459279 := by
    simpa [prefixWord, tailWord_4459279, baseEnd_4459279] using wordTrace_append hprefix tailTrace_4459279
  have hstable : (prefixWord ++ tailWord_4459279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459279).length < 2 ^ (prefixWord ++ tailWord_4459279).sum := by decide
  have hdescent : baseEnd_4459279 < baseStart_4459279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459312 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 1, 10]
def baseStart_4459312 : Nat := 118140960795 + 4459312 * 2 ^ 59
def prefixEnd_4459312 : Nat := 4983230072969 + 3 ^ 40 * 4459312 * 2
def baseEnd_4459312 : Nat := 763256814787454051664001

theorem tailTrace_4459312 : CollatzResearch.WordTrace tailWord_4459312 prefixEnd_4459312 763256814787454051664001 := by
  unfold tailWord_4459312
  simp only [CollatzResearch.WordTrace]
  refine ⟨81322235210340844350722095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108429646947121125800962793 81322235210340844350722095)
  ·
    refine ⟨121983352815511266526083143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81322235210340844350722095 121983352815511266526083143)
    ·
      refine ⟨182975029223266899789124715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121983352815511266526083143 182975029223266899789124715)
      ·
        refine ⟨274462543834900349683687073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182975029223266899789124715 274462543834900349683687073)
        ·
          refine ⟨205846907876175262262765305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274462543834900349683687073 205846907876175262262765305)
          ·
            refine ⟨154385180907131446697073979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205846907876175262262765305 154385180907131446697073979)
            ·
              refine ⟨231577771360697170045610969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154385180907131446697073979 231577771360697170045610969)
              ·
                refine ⟨173683328520522877534208227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231577771360697170045610969 173683328520522877534208227)
                ·
                  refine ⟨260524992780784316301312341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173683328520522877534208227 260524992780784316301312341)
                  ·
                    refine ⟨763256814787454051664001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 260524992780784316301312341 763256814787454051664001)
                    ·
                      rfl

theorem cell23_4459312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 10].length) (baseStart_4459312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459312 prefixEnd_4459312 := by exact prefixLift 4459312
  have htrace : WordTrace (prefixWord ++ tailWord_4459312) baseStart_4459312 baseEnd_4459312 := by
    simpa [prefixWord, tailWord_4459312, baseEnd_4459312] using wordTrace_append hprefix tailTrace_4459312
  have hstable : (prefixWord ++ tailWord_4459312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459312).length < 2 ^ (prefixWord ++ tailWord_4459312).sum := by decide
  have hdescent : baseEnd_4459312 < baseStart_4459312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459319 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 4]
def baseStart_4459319 : Nat := 118140960795 + 4459319 * 2 ^ 59
def prefixEnd_4459319 : Nat := 4983230072969 + 3 ^ 40 * 4459319 * 2
def baseEnd_4459319 : Nat := 2289774038726943627604471

theorem tailTrace_4459319 : CollatzResearch.WordTrace tailWord_4459319 prefixEnd_4459319 2289774038726943627604471 := by
  unfold tailWord_4459319
  simp only [CollatzResearch.WordTrace]
  refine ⟨162644725731656328896949011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108429817154437552597966007 162644725731656328896949011)
  ·
    refine ⟨243967088597484493345423517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162644725731656328896949011 243967088597484493345423517)
    ·
      refine ⟨91487658224056685004533819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243967088597484493345423517 91487658224056685004533819)
      ·
        refine ⟨137231487336085027506800729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91487658224056685004533819 137231487336085027506800729)
        ·
          refine ⟨102923615502063770630100547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137231487336085027506800729 102923615502063770630100547)
          ·
            refine ⟨154385423253095655945150821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102923615502063770630100547 154385423253095655945150821)
            ·
              refine ⟨28947266859955435489715779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154385423253095655945150821 28947266859955435489715779)
              ·
                refine ⟨43420900289933153234573669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28947266859955435489715779 43420900289933153234573669)
                ·
                  refine ⟨8141418804362466231482563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43420900289933153234573669 8141418804362466231482563)
                  ·
                    refine ⟨12212128206543699347223845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8141418804362466231482563 12212128206543699347223845)
                    ·
                      refine ⟨2289774038726943627604471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12212128206543699347223845 2289774038726943627604471)
                      ·
                        rfl

theorem cell23_4459319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_4459319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459319 prefixEnd_4459319 := by exact prefixLift 4459319
  have htrace : WordTrace (prefixWord ++ tailWord_4459319) baseStart_4459319 baseEnd_4459319 := by
    simpa [prefixWord, tailWord_4459319, baseEnd_4459319] using wordTrace_append hprefix tailTrace_4459319
  have hstable : (prefixWord ++ tailWord_4459319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459319).length < 2 ^ (prefixWord ++ tailWord_4459319).sum := by decide
  have hdescent : baseEnd_4459319 < baseStart_4459319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459336 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 2, 4, 2]
def baseStart_4459336 : Nat := 118140960795 + 4459336 * 2 ^ 59
def prefixEnd_4459336 : Nat := 4983230072969 + 3 ^ 40 * 4459336 * 2
def baseEnd_4459336 : Nat := 2289782767898070061091893

theorem tailTrace_4459336 : CollatzResearch.WordTrace tailWord_4459336 prefixEnd_4459336 2289782767898070061091893 := by
  unfold tailWord_4459336
  simp only [CollatzResearch.WordTrace]
  refine ⟨81322672886297370400158931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108430230515063160533545241 81322672886297370400158931)
  ·
    refine ⟨121984009329446055600238397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81322672886297370400158931 121984009329446055600238397)
    ·
      refine ⟨45744003498542270850089399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121984009329446055600238397 45744003498542270850089399)
      ·
        refine ⟨68616005247813406275134099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45744003498542270850089399 68616005247813406275134099)
        ·
          refine ⟨102924007871720109412701149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68616005247813406275134099 102924007871720109412701149)
          ·
            refine ⟨38596502951895041029762931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102924007871720109412701149 38596502951895041029762931)
            ·
              refine ⟨57894754427842561544644397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38596502951895041029762931 57894754427842561544644397)
              ·
                refine ⟨21710532910440960579241649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57894754427842561544644397 21710532910440960579241649)
                ·
                  refine ⟨16282899682830720434431237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21710532910440960579241649 16282899682830720434431237)
                  ·
                    refine ⟨3053043690530760081455857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16282899682830720434431237 3053043690530760081455857)
                    ·
                      refine ⟨2289782767898070061091893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3053043690530760081455857 2289782767898070061091893)
                      ·
                        rfl

theorem cell23_4459336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_4459336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459336 prefixEnd_4459336 := by exact prefixLift 4459336
  have htrace : WordTrace (prefixWord ++ tailWord_4459336) baseStart_4459336 baseEnd_4459336 := by
    simpa [prefixWord, tailWord_4459336, baseEnd_4459336] using wordTrace_append hprefix tailTrace_4459336
  have hstable : (prefixWord ++ tailWord_4459336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459336).length < 2 ^ (prefixWord ++ tailWord_4459336).sum := by decide
  have hdescent : baseEnd_4459336 < baseStart_4459336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459346 : List Nat := [3, 2, 2, 1, 1, 2, 1, 4, 3, 4]
def baseStart_4459346 : Nat := 118140960795 + 4459346 * 2 ^ 59
def prefixEnd_4459346 : Nat := 4983230072969 + 3 ^ 40 * 4459346 * 2
def baseEnd_4459346 : Nat := 763262634234871673988949

theorem tailTrace_4459346 : CollatzResearch.WordTrace tailWord_4459346 prefixEnd_4459346 763262634234871673988949 := by
  unfold tailWord_4459346
  simp only [CollatzResearch.WordTrace]
  refine ⟨40661427625639628127045473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108430473668372341672121261 40661427625639628127045473)
  ·
    refine ⟨30496070719229721095284105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40661427625639628127045473 30496070719229721095284105)
    ·
      refine ⟨22872053039422290821463079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30496070719229721095284105 22872053039422290821463079)
      ·
        refine ⟨34308079559133436232194619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22872053039422290821463079 34308079559133436232194619)
        ·
          refine ⟨51462119338700154348291929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34308079559133436232194619 51462119338700154348291929)
          ·
            refine ⟨38596589504025115761218947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51462119338700154348291929 38596589504025115761218947)
            ·
              refine ⟨57894884256037673641828421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38596589504025115761218947 57894884256037673641828421)
              ·
                refine ⟨10855290798007063807842829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57894884256037673641828421 10855290798007063807842829)
                ·
                  refine ⟨4070734049252648927941061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10855290798007063807842829 4070734049252648927941061)
                  ·
                    refine ⟨763262634234871673988949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4070734049252648927941061 763262634234871673988949)
                    ·
                      rfl

theorem cell23_4459346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_4459346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459346 prefixEnd_4459346 := by exact prefixLift 4459346
  have htrace : WordTrace (prefixWord ++ tailWord_4459346) baseStart_4459346 baseEnd_4459346 := by
    simpa [prefixWord, tailWord_4459346, baseEnd_4459346] using wordTrace_append hprefix tailTrace_4459346
  have hstable : (prefixWord ++ tailWord_4459346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459346).length < 2 ^ (prefixWord ++ tailWord_4459346).sum := by decide
  have hdescent : baseEnd_4459346 < baseStart_4459346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459349 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 2, 4, 4]
def baseStart_4459349 : Nat := 118140960795 + 4459349 * 2 ^ 59
def prefixEnd_4459349 : Nat := 4983230072969 + 3 ^ 40 * 4459349 * 2
def baseEnd_4459349 : Nat := 2289789443146578510229333

theorem tailTrace_4459349 : CollatzResearch.WordTrace tailWord_4459349 prefixEnd_4459349 2289789443146578510229333 := by
  unfold tailWord_4459349
  simp only [CollatzResearch.WordTrace]
  refine ⟨162645819921547644020541101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108430546614365096013694067 162645819921547644020541101)
  ·
    refine ⟨60992182470580366507702913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162645819921547644020541101 60992182470580366507702913)
    ·
      refine ⟨45744136852935274880777185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60992182470580366507702913 45744136852935274880777185)
      ·
        refine ⟨34308102639701456160582889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45744136852935274880777185 34308102639701456160582889)
        ·
          refine ⟨25731076979776092120437167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34308102639701456160582889 25731076979776092120437167)
          ·
            refine ⟨38596615469664138180655751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25731076979776092120437167 38596615469664138180655751)
            ·
              refine ⟨57894923204496207270983627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38596615469664138180655751 57894923204496207270983627)
              ·
                refine ⟨86842384806744310906475441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57894923204496207270983627 86842384806744310906475441)
                ·
                  refine ⟨65131788605058233179856581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86842384806744310906475441 65131788605058233179856581)
                  ·
                    refine ⟨12212210363448418721223109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65131788605058233179856581 12212210363448418721223109)
                    ·
                      refine ⟨2289789443146578510229333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12212210363448418721223109 2289789443146578510229333)
                      ·
                        rfl

theorem cell23_4459349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_4459349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459349 prefixEnd_4459349 := by exact prefixLift 4459349
  have htrace : WordTrace (prefixWord ++ tailWord_4459349) baseStart_4459349 baseEnd_4459349 := by
    simpa [prefixWord, tailWord_4459349, baseEnd_4459349] using wordTrace_append hprefix tailTrace_4459349
  have hstable : (prefixWord ++ tailWord_4459349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459349).length < 2 ^ (prefixWord ++ tailWord_4459349).sum := by decide
  have hdescent : baseEnd_4459349 < baseStart_4459349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459413 : List Nat := [1, 3, 2, 1, 1, 4, 1, 3, 2, 3, 2]
def baseStart_4459413 : Nat := 118140960795 + 4459413 * 2 ^ 59
def prefixEnd_4459413 : Nat := 4983230072969 + 3 ^ 40 * 4459413 * 2
def baseEnd_4459413 : Nat := 2289822305908466259829039

theorem tailTrace_4459413 : CollatzResearch.WordTrace tailWord_4459413 prefixEnd_4459413 2289822305908466259829039 := by
  unfold tailWord_4459413
  simp only [CollatzResearch.WordTrace]
  refine ⟨162648154193315782950870893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108432102795543855300580595 162648154193315782950870893)
  ·
    refine ⟨60993057822493418606576585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162648154193315782950870893 60993057822493418606576585)
    ·
      refine ⟨45744793366870063954932439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60993057822493418606576585 45744793366870063954932439)
      ·
        refine ⟨68617190050305095932398659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45744793366870063954932439 68617190050305095932398659)
        ·
          refine ⟨102925785075457643898597989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68617190050305095932398659 102925785075457643898597989)
          ·
            refine ⟨19298584701648308230987123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102925785075457643898597989 19298584701648308230987123)
            ·
              refine ⟨28947877052472462346480685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19298584701648308230987123 28947877052472462346480685)
              ·
                refine ⟨10855453894677173379930257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28947877052472462346480685 10855453894677173379930257)
                ·
                  refine ⟨8141590421007880034947693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10855453894677173379930257 8141590421007880034947693)
                  ·
                    refine ⟨3053096407877955013105385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8141590421007880034947693 3053096407877955013105385)
                    ·
                      refine ⟨2289822305908466259829039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3053096407877955013105385 2289822305908466259829039)
                      ·
                        rfl

theorem cell23_4459413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_4459413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459413 prefixEnd_4459413 := by exact prefixLift 4459413
  have htrace : WordTrace (prefixWord ++ tailWord_4459413) baseStart_4459413 baseEnd_4459413 := by
    simpa [prefixWord, tailWord_4459413, baseEnd_4459413] using wordTrace_append hprefix tailTrace_4459413
  have hstable : (prefixWord ++ tailWord_4459413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459413).length < 2 ^ (prefixWord ++ tailWord_4459413).sum := by decide
  have hdescent : baseEnd_4459413 < baseStart_4459413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459439 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 6]
def baseStart_4459439 : Nat := 118140960795 + 4459439 * 2 ^ 59
def prefixEnd_4459439 : Nat := 4983230072969 + 3 ^ 40 * 4459439 * 2
def baseEnd_4459439 : Nat := 2289835656405483158103919

theorem tailTrace_4459439 : CollatzResearch.WordTrace tailWord_4459439 prefixEnd_4459439 2289835656405483158103919 := by
  unfold tailWord_4459439
  simp only [CollatzResearch.WordTrace]
  refine ⟨162649102491221589391317371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108432734994147726260878247 162649102491221589391317371)
  ·
    refine ⟨243973653736832384086976057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162649102491221589391317371 243973653736832384086976057)
    ·
      refine ⟨182980240302624288065232043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243973653736832384086976057 182980240302624288065232043)
      ·
        refine ⟨274470360453936432097848065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182980240302624288065232043 274470360453936432097848065)
        ·
          refine ⟨205852770340452324073386049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274470360453936432097848065 205852770340452324073386049)
          ·
            refine ⟨154389577755339243055039537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205852770340452324073386049 154389577755339243055039537)
            ·
              refine ⟨115792183316504432291279653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154389577755339243055039537 115792183316504432291279653)
              ·
                refine ⟨21711034371844581054614935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115792183316504432291279653 21711034371844581054614935)
                ·
                  refine ⟨32566551557766871581922403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21711034371844581054614935 32566551557766871581922403)
                  ·
                    refine ⟨48849827336650307372883605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32566551557766871581922403 48849827336650307372883605)
                    ·
                      refine ⟨2289835656405483158103919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48849827336650307372883605 2289835656405483158103919)
                      ·
                        rfl

theorem cell23_4459439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 6].length) (baseStart_4459439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459439 prefixEnd_4459439 := by exact prefixLift 4459439
  have htrace : WordTrace (prefixWord ++ tailWord_4459439) baseStart_4459439 baseEnd_4459439 := by
    simpa [prefixWord, tailWord_4459439, baseEnd_4459439] using wordTrace_append hprefix tailTrace_4459439
  have hstable : (prefixWord ++ tailWord_4459439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459439).length < 2 ^ (prefixWord ++ tailWord_4459439).sum := by decide
  have hdescent : baseEnd_4459439 < baseStart_4459439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459453 : List Nat := [1, 4, 1, 2, 4, 1, 2, 1, 1, 6]
def baseStart_4459453 : Nat := 118140960795 + 4459453 * 2 ^ 59
def prefixEnd_4459453 : Nat := 4983230072969 + 3 ^ 40 * 4459453 * 2
def baseEnd_4459453 : Nat := 763280948378215367776285

theorem tailTrace_4459453 : CollatzResearch.WordTrace tailWord_4459453 prefixEnd_4459453 763280948378215367776285 := by
  unfold tailWord_4459453
  simp only [CollatzResearch.WordTrace]
  refine ⟨162649613113170869782327013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108433075408780579854884675 162649613113170869782327013)
  ·
    refine ⟨30496802458719538084186315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162649613113170869782327013 30496802458719538084186315)
    ·
      refine ⟨45745203688079307126279473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30496802458719538084186315 45745203688079307126279473)
      ·
        refine ⟨34308902766059480344709605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45745203688079307126279473 34308902766059480344709605)
        ·
          refine ⟨6432919268636152564633051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34308902766059480344709605 6432919268636152564633051)
          ·
            refine ⟨9649378902954228846949577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6432919268636152564633051 9649378902954228846949577)
            ·
              refine ⟨7237034177215671635212183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9649378902954228846949577 7237034177215671635212183)
              ·
                refine ⟨10855551265823507452818275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7237034177215671635212183 10855551265823507452818275)
                ·
                  refine ⟨16283326898735261179227413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10855551265823507452818275 16283326898735261179227413)
                  ·
                    refine ⟨763280948378215367776285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16283326898735261179227413 763280948378215367776285)
                    ·
                      rfl

theorem cell23_4459453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_4459453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459453 prefixEnd_4459453 := by exact prefixLift 4459453
  have htrace : WordTrace (prefixWord ++ tailWord_4459453) baseStart_4459453 baseEnd_4459453 := by
    simpa [prefixWord, tailWord_4459453, baseEnd_4459453] using wordTrace_append hprefix tailTrace_4459453
  have hstable : (prefixWord ++ tailWord_4459453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459453).length < 2 ^ (prefixWord ++ tailWord_4459453).sum := by decide
  have hdescent : baseEnd_4459453 < baseStart_4459453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459456 : List Nat := [2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 4]
def baseStart_4459456 : Nat := 118140960795 + 4459456 * 2 ^ 59
def prefixEnd_4459456 : Nat := 4983230072969 + 3 ^ 40 * 4459456 * 2
def baseEnd_4459456 : Nat := 2289844385576609591591341

theorem tailTrace_4459456 : CollatzResearch.WordTrace tailWord_4459456 prefixEnd_4459456 2289844385576609591591341 := by
  unfold tailWord_4459456
  simp only [CollatzResearch.WordTrace]
  refine ⟨81324861266080000647343111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108433148354773334196457481 81324861266080000647343111)
  ·
    refine ⟨121987291899120000971014667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81324861266080000647343111 121987291899120000971014667)
    ·
      refine ⟨182980937848680001456522001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121987291899120000971014667 182980937848680001456522001)
      ·
        refine ⟨137235703386510001092391501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182980937848680001456522001 137235703386510001092391501)
        ·
          refine ⟨51463388769941250409646813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137235703386510001092391501 51463388769941250409646813)
          ·
            refine ⟨19298770788727968903617555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51463388769941250409646813 19298770788727968903617555)
            ·
              refine ⟨28948156183091953355426333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19298770788727968903617555 28948156183091953355426333)
              ·
                refine ⟨10855558568659482508284875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28948156183091953355426333 10855558568659482508284875)
                ·
                  refine ⟨16283337852989223762427313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10855558568659482508284875 16283337852989223762427313)
                  ·
                    refine ⟨12212503389741917821820485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16283337852989223762427313 12212503389741917821820485)
                    ·
                      refine ⟨2289844385576609591591341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12212503389741917821820485 2289844385576609591591341)
                      ·
                        rfl

theorem cell23_4459456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_4459456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459456 prefixEnd_4459456 := by exact prefixLift 4459456
  have htrace : WordTrace (prefixWord ++ tailWord_4459456) baseStart_4459456 baseEnd_4459456 := by
    simpa [prefixWord, tailWord_4459456, baseEnd_4459456] using wordTrace_append hprefix tailTrace_4459456
  have hstable : (prefixWord ++ tailWord_4459456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459456).length < 2 ^ (prefixWord ++ tailWord_4459456).sum := by decide
  have hdescent : baseEnd_4459456 < baseStart_4459456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459477 : List Nat := [1, 3, 2, 3, 3, 2, 2, 1, 1, 1, 4]
def baseStart_4459477 : Nat := 118140960795 + 4459477 * 2 ^ 59
def prefixEnd_4459477 : Nat := 4983230072969 + 3 ^ 40 * 4459477 * 2
def baseEnd_4459477 : Nat := 2289855168670354009428745

theorem tailTrace_4459477 : CollatzResearch.WordTrace tailWord_4459477 prefixEnd_4459477 2289855168670354009428745 := by
  unfold tailWord_4459477
  simp only [CollatzResearch.WordTrace]
  refine ⟨162650488465083921881200685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108433658976722614587467123 162650488465083921881200685)
  ·
    refine ⟨60993933174406470705450257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162650488465083921881200685 60993933174406470705450257)
    ·
      refine ⟨45745449880804853029087693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60993933174406470705450257 45745449880804853029087693)
      ·
        refine ⟨17154543705301819885907885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45745449880804853029087693 17154543705301819885907885)
        ·
          refine ⟨6432953889488182457215457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17154543705301819885907885 6432953889488182457215457)
          ·
            refine ⟨4824715417116136842911593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6432953889488182457215457 4824715417116136842911593)
            ·
              refine ⟨3618536562837102632183695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4824715417116136842911593 3618536562837102632183695)
              ·
                refine ⟨5427804844255653948275543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3618536562837102632183695 5427804844255653948275543)
                ·
                  refine ⟨8141707266383480922413315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5427804844255653948275543 8141707266383480922413315)
                  ·
                    refine ⟨12212560899575221383619973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8141707266383480922413315 12212560899575221383619973)
                    ·
                      refine ⟨2289855168670354009428745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12212560899575221383619973 2289855168670354009428745)
                      ·
                        rfl

theorem cell23_4459477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_4459477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459477 prefixEnd_4459477 := by exact prefixLift 4459477
  have htrace : WordTrace (prefixWord ++ tailWord_4459477) baseStart_4459477 baseEnd_4459477 := by
    simpa [prefixWord, tailWord_4459477, baseEnd_4459477] using wordTrace_append hprefix tailTrace_4459477
  have hstable : (prefixWord ++ tailWord_4459477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459477).length < 2 ^ (prefixWord ++ tailWord_4459477).sum := by decide
  have hdescent : baseEnd_4459477 < baseStart_4459477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459479 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 1, 9]
def baseStart_4459479 : Nat := 118140960795 + 4459479 * 2 ^ 59
def prefixEnd_4459479 : Nat := 4983230072969 + 3 ^ 40 * 4459479 * 2
def baseEnd_4459479 : Nat := 763285398543887667201245

theorem tailTrace_4459479 : CollatzResearch.WordTrace tailWord_4459479 prefixEnd_4459479 763285398543887667201245 := by
  unfold tailWord_4459479
  simp only [CollatzResearch.WordTrace]
  refine ⟨162650561411076676222773491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108433707607384450815182327 162650561411076676222773491)
  ·
    refine ⟨243975842116615014334160237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162650561411076676222773491 243975842116615014334160237)
    ·
      refine ⟨91490940793730630375310089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243975842116615014334160237 91490940793730630375310089)
      ·
        refine ⟨68618205595297972781482567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91490940793730630375310089 68618205595297972781482567)
        ·
          refine ⟨102927308392946959172223851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68618205595297972781482567 102927308392946959172223851)
          ·
            refine ⟨154390962589420438758335777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102927308392946959172223851 154390962589420438758335777)
            ·
              refine ⟨115793221942065329068751833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154390962589420438758335777 115793221942065329068751833)
              ·
                refine ⟨86844916456548996801563875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115793221942065329068751833 86844916456548996801563875)
                ·
                  refine ⟨130267374684823495202345813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86844916456548996801563875 130267374684823495202345813)
                  ·
                    refine ⟨763285398543887667201245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 130267374684823495202345813 763285398543887667201245)
                    ·
                      rfl

theorem cell23_4459479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_4459479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459479 prefixEnd_4459479 := by exact prefixLift 4459479
  have htrace : WordTrace (prefixWord ++ tailWord_4459479) baseStart_4459479 baseEnd_4459479 := by
    simpa [prefixWord, tailWord_4459479, baseEnd_4459479] using wordTrace_append hprefix tailTrace_4459479
  have hstable : (prefixWord ++ tailWord_4459479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459479).length < 2 ^ (prefixWord ++ tailWord_4459479).sum := by decide
  have hdescent : baseEnd_4459479 < baseStart_4459479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459480 : List Nat := [2, 1, 2, 2, 2, 3, 4, 1, 1, 2, 3]
def baseStart_4459480 : Nat := 118140960795 + 4459480 * 2 ^ 59
def prefixEnd_4459480 : Nat := 4983230072969 + 3 ^ 40 * 4459480 * 2
def baseEnd_4459480 : Nat := 2289856709112317497691231

theorem tailTrace_4459480 : CollatzResearch.WordTrace tailWord_4459480 prefixEnd_4459480 2289856709112317497691231 := by
  unfold tailWord_4459480
  simp only [CollatzResearch.WordTrace]
  refine ⟨81325298942036526696779947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108433731922715368929039929 81325298942036526696779947)
  ·
    refine ⟨121987948413054790045169921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81325298942036526696779947 121987948413054790045169921)
    ·
      refine ⟨91490961309791092533877441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121987948413054790045169921 91490961309791092533877441)
      ·
        refine ⟨68618220982343319400408081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91490961309791092533877441 68618220982343319400408081)
        ·
          refine ⟨51463665736757489550306061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68618220982343319400408081 51463665736757489550306061)
          ·
            refine ⟨19298874651284058581364773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51463665736757489550306061 19298874651284058581364773)
            ·
              refine ⟨3618538997115760984005895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19298874651284058581364773 3618538997115760984005895)
              ·
                refine ⟨5427808495673641476008843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3618538997115760984005895 5427808495673641476008843)
                ·
                  refine ⟨8141712743510462214013265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5427808495673641476008843 8141712743510462214013265)
                  ·
                    refine ⟨6106284557632846660509949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8141712743510462214013265 6106284557632846660509949)
                    ·
                      refine ⟨2289856709112317497691231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6106284557632846660509949 2289856709112317497691231)
                      ·
                        rfl

theorem cell23_4459480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_4459480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459480 prefixEnd_4459480 := by exact prefixLift 4459480
  have htrace : WordTrace (prefixWord ++ tailWord_4459480) baseStart_4459480 baseEnd_4459480 := by
    simpa [prefixWord, tailWord_4459480, baseEnd_4459480] using wordTrace_append hprefix tailTrace_4459480
  have hstable : (prefixWord ++ tailWord_4459480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459480).length < 2 ^ (prefixWord ++ tailWord_4459480).sum := by decide
  have hdescent : baseEnd_4459480 < baseStart_4459480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459487 : List Nat := [1, 1, 2, 3, 6, 1, 1, 2, 2, 4]
def baseStart_4459487 : Nat := 118140960795 + 4459487 * 2 ^ 59
def prefixEnd_4459487 : Nat := 4983230072969 + 3 ^ 40 * 4459487 * 2
def baseEnd_4459487 : Nat := 763286767825632990101233

theorem tailTrace_4459487 : CollatzResearch.WordTrace tailWord_4459487 prefixEnd_4459487 763286767825632990101233 := by
  unfold tailWord_4459487
  simp only [CollatzResearch.WordTrace]
  refine ⟨162650853195047693589064715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108433902130031795726043143 162650853195047693589064715)
  ·
    refine ⟨243976279792571540383597073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162650853195047693589064715 243976279792571540383597073)
    ·
      refine ⟨182982209844428655287697805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243976279792571540383597073 182982209844428655287697805)
      ·
        refine ⟨68618328691660745732886677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182982209844428655287697805 68618328691660745732886677)
        ·
          refine ⟨3216484157421597456229063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 68618328691660745732886677 3216484157421597456229063)
          ·
            refine ⟨4824726236132396184343595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3216484157421597456229063 4824726236132396184343595)
            ·
              refine ⟨7237089354198594276515393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4824726236132396184343595 7237089354198594276515393)
              ·
                refine ⟨5427817015648945707386545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7237089354198594276515393 5427817015648945707386545)
                ·
                  refine ⟨4070862761736709280539909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5427817015648945707386545 4070862761736709280539909)
                  ·
                    refine ⟨763286767825632990101233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4070862761736709280539909 763286767825632990101233)
                    ·
                      rfl

theorem cell23_4459487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 2, 4].length) (baseStart_4459487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459487 prefixEnd_4459487 := by exact prefixLift 4459487
  have htrace : WordTrace (prefixWord ++ tailWord_4459487) baseStart_4459487 baseEnd_4459487 := by
    simpa [prefixWord, tailWord_4459487, baseEnd_4459487] using wordTrace_append hprefix tailTrace_4459487
  have hstable : (prefixWord ++ tailWord_4459487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459487).length < 2 ^ (prefixWord ++ tailWord_4459487).sum := by decide
  have hdescent : baseEnd_4459487 < baseStart_4459487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459510 : List Nat := [5, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3]
def baseStart_4459510 : Nat := 118140960795 + 4459510 * 2 ^ 59
def prefixEnd_4459510 : Nat := 4983230072969 + 3 ^ 40 * 4459510 * 2
def baseEnd_4459510 : Nat := 2289872113531952380316093

theorem tailTrace_4459510 : CollatzResearch.WordTrace tailWord_4459510 prefixEnd_4459510 2289872113531952380316093 := by
  unfold tailWord_4459510
  simp only [CollatzResearch.WordTrace]
  refine ⟨10165730754622773032321999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108434461382642912344767989 10165730754622773032321999)
  ·
    refine ⟨15248596131934159548482999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10165730754622773032321999 15248596131934159548482999)
    ·
      refine ⟨22872894197901239322724499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15248596131934159548482999 22872894197901239322724499)
      ·
        refine ⟨34309341296851858984086749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22872894197901239322724499 34309341296851858984086749)
        ·
          refine ⟨12866002986319447119032531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34309341296851858984086749 12866002986319447119032531)
          ·
            refine ⟨19299004479479170678548797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12866002986319447119032531 19299004479479170678548797)
            ·
              refine ⟨7237126679804689004455799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19299004479479170678548797 7237126679804689004455799)
              ·
                refine ⟨10855690019707033506683699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7237126679804689004455799 10855690019707033506683699)
                ·
                  refine ⟨16283535029560550260025549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10855690019707033506683699 16283535029560550260025549)
                  ·
                    refine ⟨6106325636085206347509581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16283535029560550260025549 6106325636085206347509581)
                    ·
                      refine ⟨2289872113531952380316093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6106325636085206347509581 2289872113531952380316093)
                      ·
                        rfl

theorem cell23_4459510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_4459510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459510 prefixEnd_4459510 := by exact prefixLift 4459510
  have htrace : WordTrace (prefixWord ++ tailWord_4459510) baseStart_4459510 baseEnd_4459510 := by
    simpa [prefixWord, tailWord_4459510, baseEnd_4459510] using wordTrace_append hprefix tailTrace_4459510
  have hstable : (prefixWord ++ tailWord_4459510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459510).length < 2 ^ (prefixWord ++ tailWord_4459510).sum := by decide
  have hdescent : baseEnd_4459510 < baseStart_4459510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459680 : List Nat := [2, 1, 1, 4, 2, 1, 5, 1, 6]
def baseStart_4459680 : Nat := 118140960795 + 4459680 * 2 ^ 59
def prefixEnd_4459680 : Nat := 4983230072969 + 3 ^ 40 * 4459680 * 2
def baseEnd_4459680 : Nat := 254439933915912968354479

theorem tailTrace_4459680 : CollatzResearch.WordTrace tailWord_4459680 prefixEnd_4459680 254439933915912968354479 := by
  unfold tailWord_4459680
  simp only [CollatzResearch.WordTrace]
  refine ⟨81328946241674243775420247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108438594988898991700560329 81328946241674243775420247)
  ·
    refine ⟨121993419362511365663130371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81328946241674243775420247 121993419362511365663130371)
    ·
      refine ⟨182990129043767048494695557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121993419362511365663130371 182990129043767048494695557)
      ·
        refine ⟨34310649195706321592755417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182990129043767048494695557 34310649195706321592755417)
        ·
          refine ⟨25732986896779741194566563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34310649195706321592755417 25732986896779741194566563)
          ·
            refine ⟨38599480345169611791849845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25732986896779741194566563 38599480345169611791849845)
            ·
              refine ⟨3618701282359651105485923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38599480345169611791849845 3618701282359651105485923)
              ·
                refine ⟨5428051923539476658228885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3618701282359651105485923 5428051923539476658228885)
                ·
                  refine ⟨254439933915912968354479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5428051923539476658228885 254439933915912968354479)
                  ·
                    rfl

theorem cell23_4459680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 6].length) (baseStart_4459680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459680 prefixEnd_4459680 := by exact prefixLift 4459680
  have htrace : WordTrace (prefixWord ++ tailWord_4459680) baseStart_4459680 baseEnd_4459680 := by
    simpa [prefixWord, tailWord_4459680, baseEnd_4459680] using wordTrace_append hprefix tailTrace_4459680
  have hstable : (prefixWord ++ tailWord_4459680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459680).length < 2 ^ (prefixWord ++ tailWord_4459680).sum := by decide
  have hdescent : baseEnd_4459680 < baseStart_4459680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459707 : List Nat := [1, 1, 1, 1, 1, 2, 4, 7, 1, 1, 3]
def baseStart_4459707 : Nat := 118140960795 + 4459707 * 2 ^ 59
def prefixEnd_4459707 : Nat := 4983230072969 + 3 ^ 40 * 4459707 * 2
def baseEnd_4459707 : Nat := 2289973269220888109552687

theorem tailTrace_4459707 : CollatzResearch.WordTrace tailWord_4459707 prefixEnd_4459707 2289973269220888109552687 := by
  unfold tailWord_4459707
  simp only [CollatzResearch.WordTrace]
  refine ⟨162658877254250671162073375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108439251502833780774715583 162658877254250671162073375)
  ·
    refine ⟨243988315881376006743110063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162658877254250671162073375 243988315881376006743110063)
    ·
      refine ⟨365982473822064010114665095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243988315881376006743110063 365982473822064010114665095)
      ·
        refine ⟨548973710733096015171997643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365982473822064010114665095 548973710733096015171997643)
        ·
          refine ⟨823460566099644022757996465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548973710733096015171997643 823460566099644022757996465)
          ·
            refine ⟨617595424574733017068497349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 823460566099644022757996465 617595424574733017068497349)
            ·
              refine ⟨115799142107762440700343253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 617595424574733017068497349 115799142107762440700343253)
              ·
                refine ⟨2714042393150682203914295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 115799142107762440700343253 2714042393150682203914295)
                ·
                  refine ⟨4071063589726023305871443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2714042393150682203914295 4071063589726023305871443)
                  ·
                    refine ⟨6106595384589034958807165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4071063589726023305871443 6106595384589034958807165)
                    ·
                      refine ⟨2289973269220888109552687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6106595384589034958807165 2289973269220888109552687)
                      ·
                        rfl

theorem cell23_4459707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 1, 1, 3].length) (baseStart_4459707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459707 prefixEnd_4459707 := by exact prefixLift 4459707
  have htrace : WordTrace (prefixWord ++ tailWord_4459707) baseStart_4459707 baseEnd_4459707 := by
    simpa [prefixWord, tailWord_4459707, baseEnd_4459707] using wordTrace_append hprefix tailTrace_4459707
  have hstable : (prefixWord ++ tailWord_4459707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459707).length < 2 ^ (prefixWord ++ tailWord_4459707).sum := by decide
  have hdescent : baseEnd_4459707 < baseStart_4459707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459718 : List Nat := [6, 1, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_4459718 : Nat := 118140960795 + 4459718 * 2 ^ 59
def prefixEnd_4459718 : Nat := 4983230072969 + 3 ^ 40 * 4459718 * 2
def baseEnd_4459718 : Nat := 763326305836029188838379

theorem tailTrace_4459718 : CollatzResearch.WordTrace tailWord_4459718 prefixEnd_4459718 763326305836029188838379 := by
  unfold tailWord_4459718
  simp only [CollatzResearch.WordTrace]
  refine ⟨5083102451787838126272619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 108439518971473880027149205 5083102451787838126272619)
  ·
    refine ⟨7624653677681757189408929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5083102451787838126272619 7624653677681757189408929)
    ·
      refine ⟨5718490258261317892056697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7624653677681757189408929 5718490258261317892056697)
      ·
        refine ⟨4288867693695988419042523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5718490258261317892056697 4288867693695988419042523)
        ·
          refine ⟨6433301540543982628563785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4288867693695988419042523 6433301540543982628563785)
          ·
            refine ⟨4824976155407986971422839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6433301540543982628563785 4824976155407986971422839)
            ·
              refine ⟨7237464233111980457134259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4824976155407986971422839 7237464233111980457134259)
              ·
                refine ⟨10856196349667970685701389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7237464233111980457134259 10856196349667970685701389)
                ·
                  refine ⟨4071073631125489007138021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10856196349667970685701389 4071073631125489007138021)
                  ·
                    refine ⟨763326305836029188838379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4071073631125489007138021 763326305836029188838379)
                    ·
                      rfl

theorem cell23_4459718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_4459718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459718 prefixEnd_4459718 := by exact prefixLift 4459718
  have htrace : WordTrace (prefixWord ++ tailWord_4459718) baseStart_4459718 baseEnd_4459718 := by
    simpa [prefixWord, tailWord_4459718, baseEnd_4459718] using wordTrace_append hprefix tailTrace_4459718
  have hstable : (prefixWord ++ tailWord_4459718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459718).length < 2 ^ (prefixWord ++ tailWord_4459718).sum := by decide
  have hdescent : baseEnd_4459718 < baseStart_4459718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459730 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_4459730 : Nat := 118140960795 + 4459730 * 2 ^ 59
def prefixEnd_4459730 : Nat := 4983230072969 + 3 ^ 40 * 4459730 * 2
def baseEnd_4459730 : Nat := 2289985079275941519565081

theorem tailTrace_4459730 : CollatzResearch.WordTrace tailWord_4459730 prefixEnd_4459730 2289985079275941519565081 := by
  unfold tailWord_4459730
  simp only [CollatzResearch.WordTrace]
  refine ⟨40664929033291836522540161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108439810755444897393440429 40664929033291836522540161)
  ·
    refine ⟨30498696774968877391905121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40664929033291836522540161 30498696774968877391905121)
    ·
      refine ⟨22874022581226658043928841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30498696774968877391905121 22874022581226658043928841)
      ·
        refine ⟨17155516935919993532946631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22874022581226658043928841 17155516935919993532946631)
        ·
          refine ⟨25733275403879990299419947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17155516935919993532946631 25733275403879990299419947)
          ·
            refine ⟨38599913105819985449129921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25733275403879990299419947 38599913105819985449129921)
            ·
              refine ⟨28949934829364989086847441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38599913105819985449129921 28949934829364989086847441)
              ·
                refine ⟨21712451122023741815135581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28949934829364989086847441 21712451122023741815135581)
                ·
                  refine ⟨8142169170758903180675843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21712451122023741815135581 8142169170758903180675843)
                  ·
                    refine ⟨12213253756138354771013765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8142169170758903180675843 12213253756138354771013765)
                    ·
                      refine ⟨2289985079275941519565081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12213253756138354771013765 2289985079275941519565081)
                      ·
                        rfl

theorem cell23_4459730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_4459730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459730 prefixEnd_4459730 := by exact prefixLift 4459730
  have htrace : WordTrace (prefixWord ++ tailWord_4459730) baseStart_4459730 baseEnd_4459730 := by
    simpa [prefixWord, tailWord_4459730, baseEnd_4459730] using wordTrace_append hprefix tailTrace_4459730
  have hstable : (prefixWord ++ tailWord_4459730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459730).length < 2 ^ (prefixWord ++ tailWord_4459730).sum := by decide
  have hdescent : baseEnd_4459730 < baseStart_4459730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459743 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 6]
def baseStart_4459743 : Nat := 118140960795 + 4459743 * 2 ^ 59
def prefixEnd_4459743 : Nat := 4983230072969 + 3 ^ 40 * 4459743 * 2
def baseEnd_4459743 : Nat := 2289991754524449968702521

theorem tailTrace_4459743 : CollatzResearch.WordTrace tailWord_4459743 prefixEnd_4459743 2289991754524449968702521 := by
  unfold tailWord_4459743
  simp only [CollatzResearch.WordTrace]
  refine ⟨162660190282120249310383883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108440126854746832873589255 162660190282120249310383883)
  ·
    refine ⟨243990285423180373965575825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162660190282120249310383883 243990285423180373965575825)
    ·
      refine ⟨182992714067385280474181869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243990285423180373965575825 182992714067385280474181869)
      ·
        refine ⟨68622267775269480177818201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182992714067385280474181869 68622267775269480177818201)
        ·
          refine ⟨51466700831452110133363651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68622267775269480177818201 51466700831452110133363651)
          ·
            refine ⟨77200051247178165200045477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51466700831452110133363651 77200051247178165200045477)
            ·
              refine ⟨14475009608845905975008527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77200051247178165200045477 14475009608845905975008527)
              ·
                refine ⟨21712514413268858962512791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14475009608845905975008527 21712514413268858962512791)
                ·
                  refine ⟨32568771619903288443769187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21712514413268858962512791 32568771619903288443769187)
                  ·
                    refine ⟨48853157429854932665653781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32568771619903288443769187 48853157429854932665653781)
                    ·
                      refine ⟨2289991754524449968702521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48853157429854932665653781 2289991754524449968702521)
                      ·
                        rfl

theorem cell23_4459743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_4459743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459743 prefixEnd_4459743 := by exact prefixLift 4459743
  have htrace : WordTrace (prefixWord ++ tailWord_4459743) baseStart_4459743 baseEnd_4459743 := by
    simpa [prefixWord, tailWord_4459743, baseEnd_4459743] using wordTrace_append hprefix tailTrace_4459743
  have hstable : (prefixWord ++ tailWord_4459743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459743).length < 2 ^ (prefixWord ++ tailWord_4459743).sum := by decide
  have hdescent : baseEnd_4459743 < baseStart_4459743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459774 : List Nat := [4, 2, 2, 1, 1, 3, 2, 2, 2, 4]
def baseStart_4459774 : Nat := 118140960795 + 4459774 * 2 ^ 59
def prefixEnd_4459774 : Nat := 4983230072969 + 3 ^ 40 * 4459774 * 2
def baseEnd_4459774 : Nat := 763335890808246449138293

theorem tailTrace_4459774 : CollatzResearch.WordTrace tailWord_4459774 prefixEnd_4459774 763335890808246449138293 := by
  unfold tailWord_4459774
  simp only [CollatzResearch.WordTrace]
  refine ⟨20332665118125992700595297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108440880630005294403174917 20332665118125992700595297)
  ·
    refine ⟨15249498838594494525446473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20332665118125992700595297 15249498838594494525446473)
    ·
      refine ⟨11437124128945870894084855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15249498838594494525446473 11437124128945870894084855)
      ·
        refine ⟨17155686193418806341127283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11437124128945870894084855 17155686193418806341127283)
        ·
          refine ⟨25733529290128209511690925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17155686193418806341127283 25733529290128209511690925)
          ·
            refine ⟨9650073483798078566884097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25733529290128209511690925 9650073483798078566884097)
            ·
              refine ⟨7237555112848558925163073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9650073483798078566884097 7237555112848558925163073)
              ·
                refine ⟨5428166334636419193872305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7237555112848558925163073 5428166334636419193872305)
                ·
                  refine ⟨4071124750977314395404229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5428166334636419193872305 4071124750977314395404229)
                  ·
                    refine ⟨763335890808246449138293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4071124750977314395404229 763335890808246449138293)
                    ·
                      rfl

theorem cell23_4459774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_4459774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459774 prefixEnd_4459774 := by exact prefixLift 4459774
  have htrace : WordTrace (prefixWord ++ tailWord_4459774) baseStart_4459774 baseEnd_4459774 := by
    simpa [prefixWord, tailWord_4459774, baseEnd_4459774] using wordTrace_append hprefix tailTrace_4459774
  have hstable : (prefixWord ++ tailWord_4459774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459774).length < 2 ^ (prefixWord ++ tailWord_4459774).sum := by decide
  have hdescent : baseEnd_4459774 < baseStart_4459774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459803 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 4]
def baseStart_4459803 : Nat := 118140960795 + 4459803 * 2 ^ 59
def prefixEnd_4459803 : Nat := 4983230072969 + 3 ^ 40 * 4459803 * 2
def baseEnd_4459803 : Nat := 2290022563363719733952245

theorem tailTrace_4459803 : CollatzResearch.WordTrace tailWord_4459803 prefixEnd_4459803 2290022563363719733952245 := by
  unfold tailWord_4459803
  simp only [CollatzResearch.WordTrace]
  refine ⟨162662378661902879557568063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108441585774601919705045375 162662378661902879557568063)
  ·
    refine ⟨243993567992854319336352095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162662378661902879557568063 243993567992854319336352095)
    ·
      refine ⟨365990351989281479004528143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243993567992854319336352095 365990351989281479004528143)
      ·
        refine ⟨548985527983922218506792215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365990351989281479004528143 548985527983922218506792215)
        ·
          refine ⟨823478291975883327760188323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548985527983922218506792215 823478291975883327760188323)
          ·
            refine ⟨1235217437963824991640282485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 823478291975883327760188323 1235217437963824991640282485)
            ·
              refine ⟨115801634809108592966276483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1235217437963824991640282485 115801634809108592966276483)
              ·
                refine ⟨173702452213662889449414725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115801634809108592966276483 173702452213662889449414725)
                ·
                  refine ⟨32569209790061791771765261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 173702452213662889449414725 32569209790061791771765261)
                  ·
                    refine ⟨12213453671273171914411973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32569209790061791771765261 12213453671273171914411973)
                    ·
                      refine ⟨2290022563363719733952245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12213453671273171914411973 2290022563363719733952245)
                      ·
                        rfl

theorem cell23_4459803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 4].length) (baseStart_4459803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459803 prefixEnd_4459803 := by exact prefixLift 4459803
  have htrace : WordTrace (prefixWord ++ tailWord_4459803) baseStart_4459803 baseEnd_4459803 := by
    simpa [prefixWord, tailWord_4459803, baseEnd_4459803] using wordTrace_append hprefix tailTrace_4459803
  have hstable : (prefixWord ++ tailWord_4459803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459803).length < 2 ^ (prefixWord ++ tailWord_4459803).sum := by decide
  have hdescent : baseEnd_4459803 < baseStart_4459803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459823 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 5]
def baseStart_4459823 : Nat := 118140960795 + 4459823 * 2 ^ 59
def prefixEnd_4459823 : Nat := 4983230072969 + 3 ^ 40 * 4459823 * 2
def baseEnd_4459823 : Nat := 2290032832976809655702153

theorem tailTrace_4459823 : CollatzResearch.WordTrace tailWord_4459823 prefixEnd_4459823 2290032832976809655702153 := by
  unfold tailWord_4459823
  simp only [CollatzResearch.WordTrace]
  refine ⟨162663108121830422973296123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108442072081220281982197415 162663108121830422973296123)
  ·
    refine ⟨243994662182745634459944185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162663108121830422973296123 243994662182745634459944185)
    ·
      refine ⟨182995996637059225844958139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243994662182745634459944185 182995996637059225844958139)
      ·
        refine ⟨274493994955588838767437209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182995996637059225844958139 274493994955588838767437209)
        ·
          refine ⟨205870496216691629075577907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274493994955588838767437209 205870496216691629075577907)
          ·
            refine ⟨308805744325037443613366861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205870496216691629075577907 308805744325037443613366861)
            ·
              refine ⟨115802154121889041355012573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 308805744325037443613366861 115802154121889041355012573)
              ·
                refine ⟨43425807795708390508129715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115802154121889041355012573 43425807795708390508129715)
                ·
                  refine ⟨65138711693562585762194573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43425807795708390508129715 65138711693562585762194573)
                  ·
                    refine ⟨24427016885085969660822965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65138711693562585762194573 24427016885085969660822965)
                    ·
                      refine ⟨2290032832976809655702153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24427016885085969660822965 2290032832976809655702153)
                      ·
                        rfl

theorem cell23_4459823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_4459823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459823 prefixEnd_4459823 := by exact prefixLift 4459823
  have htrace : WordTrace (prefixWord ++ tailWord_4459823) baseStart_4459823 baseEnd_4459823 := by
    simpa [prefixWord, tailWord_4459823, baseEnd_4459823] using wordTrace_append hprefix tailTrace_4459823
  have hstable : (prefixWord ++ tailWord_4459823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459823).length < 2 ^ (prefixWord ++ tailWord_4459823).sum := by decide
  have hdescent : baseEnd_4459823 < baseStart_4459823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459860 : List Nat := [2, 4, 1, 1, 2, 1, 1, 4, 7]
def baseStart_4459860 : Nat := 118140960795 + 4459860 * 2 ^ 59
def prefixEnd_4459860 : Nat := 4983230072969 + 3 ^ 40 * 4459860 * 2
def baseEnd_4459860 : Nat := 254450203529002890104387

theorem tailTrace_4459860 : CollatzResearch.WordTrace tailWord_4459860 prefixEnd_4459860 254450203529002890104387 := by
  unfold tailWord_4459860
  simp only [CollatzResearch.WordTrace]
  refine ⟨81332228811348189146196517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108442971748464252194928689 81332228811348189146196517)
  ·
    refine ⟨15249792902127785464911847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81332228811348189146196517 15249792902127785464911847)
    ·
      refine ⟨22874689353191678197367771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15249792902127785464911847 22874689353191678197367771)
      ·
        refine ⟨34312034029787517296051657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22874689353191678197367771 34312034029787517296051657)
        ·
          refine ⟨25734025522340637972038743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34312034029787517296051657 25734025522340637972038743)
          ·
            refine ⟨38601038283510956958058115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25734025522340637972038743 38601038283510956958058115)
            ·
              refine ⟨57901557425266435437087173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38601038283510956958058115 57901557425266435437087173)
              ·
                refine ⟨10856542017237456644453845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57901557425266435437087173 10856542017237456644453845)
                ·
                  refine ⟨254450203529002890104387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10856542017237456644453845 254450203529002890104387)
                  ·
                    rfl

theorem cell23_4459860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_4459860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459860 prefixEnd_4459860 := by exact prefixLift 4459860
  have htrace : WordTrace (prefixWord ++ tailWord_4459860) baseStart_4459860 baseEnd_4459860 := by
    simpa [prefixWord, tailWord_4459860, baseEnd_4459860] using wordTrace_append hprefix tailTrace_4459860
  have hstable : (prefixWord ++ tailWord_4459860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459860).length < 2 ^ (prefixWord ++ tailWord_4459860).sum := by decide
  have hdescent : baseEnd_4459860 < baseStart_4459860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459900 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 1, 2, 5]
def baseStart_4459900 : Nat := 118140960795 + 4459900 * 2 ^ 59
def prefixEnd_4459900 : Nat := 4983230072969 + 3 ^ 40 * 4459900 * 2
def baseEnd_4459900 : Nat := 2290072370987205854439299

theorem tailTrace_4459900 : CollatzResearch.WordTrace tailWord_4459900 prefixEnd_4459900 2290072370987205854439299 := by
  unfold tailWord_4459900
  simp only [CollatzResearch.WordTrace]
  refine ⟨81332958271275732561924577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108443944361700976749232769 81332958271275732561924577)
  ·
    refine ⟨60999718703456799421443433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81332958271275732561924577 60999718703456799421443433)
    ·
      refine ⟨45749789027592599566082575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60999718703456799421443433 45749789027592599566082575)
      ·
        refine ⟨68624683541388899349123863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45749789027592599566082575 68624683541388899349123863)
        ·
          refine ⟨102937025312083349023685795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68624683541388899349123863 102937025312083349023685795)
          ·
            refine ⟨154405537968125023535528693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102937025312083349023685795 154405537968125023535528693)
            ·
              refine ⟨14475519184511720956455815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 154405537968125023535528693 14475519184511720956455815)
              ·
                refine ⟨21713278776767581434683723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14475519184511720956455815 21713278776767581434683723)
                ·
                  refine ⟨32569918165151372152025585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21713278776767581434683723 32569918165151372152025585)
                  ·
                    refine ⟨24427438623863529114019189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32569918165151372152025585 24427438623863529114019189)
                    ·
                      refine ⟨2290072370987205854439299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24427438623863529114019189 2290072370987205854439299)
                      ·
                        rfl

theorem cell23_4459900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_4459900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459900 prefixEnd_4459900 := by exact prefixLift 4459900
  have htrace : WordTrace (prefixWord ++ tailWord_4459900) baseStart_4459900 baseEnd_4459900 := by
    simpa [prefixWord, tailWord_4459900, baseEnd_4459900] using wordTrace_append hprefix tailTrace_4459900
  have hstable : (prefixWord ++ tailWord_4459900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459900).length < 2 ^ (prefixWord ++ tailWord_4459900).sum := by decide
  have hdescent : baseEnd_4459900 < baseStart_4459900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459905 : List Nat := [1, 2, 4, 3, 2, 2, 2, 1, 2, 2, 2]
def baseStart_4459905 : Nat := 118140960795 + 4459905 * 2 ^ 59
def prefixEnd_4459905 : Nat := 4983230072969 + 3 ^ 40 * 4459905 * 2
def baseEnd_4459905 : Nat := 2290074938390478334876777

theorem tailTrace_4459905 : CollatzResearch.WordTrace tailWord_4459905 prefixEnd_4459905 2290074938390478334876777 := by
  unfold tailWord_4459905
  simp only [CollatzResearch.WordTrace]
  refine ⟨162666098907533350977781169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108444065938355567318520779 162666098907533350977781169)
  ·
    refine ⟨121999574180650013233335877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162666098907533350977781169 121999574180650013233335877)
    ·
      refine ⟨22874920158871877481250477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121999574180650013233335877 22874920158871877481250477)
      ·
        refine ⟨8578095059576954055468929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22874920158871877481250477 8578095059576954055468929)
        ·
          refine ⟨6433571294682715541601697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8578095059576954055468929 6433571294682715541601697)
          ·
            refine ⟨4825178471012036656201273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6433571294682715541601697 4825178471012036656201273)
            ·
              refine ⟨3618883853259027492150955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4825178471012036656201273 3618883853259027492150955)
              ·
                refine ⟨5428325779888541238226433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3618883853259027492150955 5428325779888541238226433)
                ·
                  refine ⟨4071244334916405928669825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5428325779888541238226433 4071244334916405928669825)
                  ·
                    refine ⟨3053433251187304446502369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4071244334916405928669825 3053433251187304446502369)
                    ·
                      refine ⟨2290074938390478334876777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3053433251187304446502369 2290074938390478334876777)
                      ·
                        rfl

theorem cell23_4459905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_4459905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459905 prefixEnd_4459905 := by exact prefixLift 4459905
  have htrace : WordTrace (prefixWord ++ tailWord_4459905) baseStart_4459905 baseEnd_4459905 := by
    simpa [prefixWord, tailWord_4459905, baseEnd_4459905] using wordTrace_append hprefix tailTrace_4459905
  have hstable : (prefixWord ++ tailWord_4459905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459905).length < 2 ^ (prefixWord ++ tailWord_4459905).sum := by decide
  have hdescent : baseEnd_4459905 < baseStart_4459905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459924 : List Nat := [2, 4, 2, 1, 2, 2, 2, 1, 2, 5]
def baseStart_4459924 : Nat := 118140960795 + 4459924 * 2 ^ 59
def prefixEnd_4459924 : Nat := 4983230072969 + 3 ^ 40 * 4459924 * 2
def baseEnd_4459924 : Nat := 763361564840971253513063

theorem tailTrace_4459924 : CollatzResearch.WordTrace tailWord_4459924 prefixEnd_4459924 763361564840971253513063 := by
  unfold tailWord_4459924
  simp only [CollatzResearch.WordTrace]
  refine ⟨81333395947232258611361413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108444527929643011481815217 81333395947232258611361413)
  ·
    refine ⟨15250011740106048489630265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81333395947232258611361413 15250011740106048489630265)
    ·
      refine ⟨11437508805079536367222699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15250011740106048489630265 11437508805079536367222699)
      ·
        refine ⟨17156263207619304550834049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11437508805079536367222699 17156263207619304550834049)
        ·
          refine ⟨12867197405714478413125537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17156263207619304550834049 12867197405714478413125537)
          ·
            refine ⟨9650398054285858809844153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12867197405714478413125537 9650398054285858809844153)
            ·
              refine ⟨7237798540714394107383115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9650398054285858809844153 7237798540714394107383115)
              ·
                refine ⟨10856697811071591161074673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7237798540714394107383115 10856697811071591161074673)
                ·
                  refine ⟨8142523358303693370806005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10856697811071591161074673 8142523358303693370806005)
                  ·
                    refine ⟨763361564840971253513063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8142523358303693370806005 763361564840971253513063)
                    ·
                      rfl

theorem cell23_4459924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_4459924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459924 prefixEnd_4459924 := by exact prefixLift 4459924
  have htrace : WordTrace (prefixWord ++ tailWord_4459924) baseStart_4459924 baseEnd_4459924 := by
    simpa [prefixWord, tailWord_4459924, baseEnd_4459924] using wordTrace_append hprefix tailTrace_4459924
  have hstable : (prefixWord ++ tailWord_4459924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459924).length < 2 ^ (prefixWord ++ tailWord_4459924).sum := by decide
  have hdescent : baseEnd_4459924 < baseStart_4459924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459927 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 4, 4, 2]
def baseStart_4459927 : Nat := 118140960795 + 4459927 * 2 ^ 59
def prefixEnd_4459927 : Nat := 4983230072969 + 3 ^ 40 * 4459927 * 2
def baseEnd_4459927 : Nat := 2290086234964877248801675

theorem tailTrace_4459927 : CollatzResearch.WordTrace tailWord_4459927 prefixEnd_4459927 2290086234964877248801675 := by
  unfold tailWord_4459927
  simp only [CollatzResearch.WordTrace]
  refine ⟨162666901313453648735082035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108444600875635765823388023 162666901313453648735082035)
  ·
    refine ⟨244000351970180473102623053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162666901313453648735082035 244000351970180473102623053)
    ·
      refine ⟨91500131988817677413483645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244000351970180473102623053 91500131988817677413483645)
      ·
        refine ⟨34312549495806629030056367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91500131988817677413483645 34312549495806629030056367)
        ·
          refine ⟨51468824243709943545084551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34312549495806629030056367 51468824243709943545084551)
          ·
            refine ⟨77203236365564915317626827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51468824243709943545084551 77203236365564915317626827)
            ·
              refine ⟨115804854548347372976440241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77203236365564915317626827 115804854548347372976440241)
              ·
                refine ⟨86853640911260529732330181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115804854548347372976440241 86853640911260529732330181)
                ·
                  refine ⟨16285057670861349324811909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86853640911260529732330181 16285057670861349324811909)
                  ·
                    refine ⟨3053448313286502998402233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16285057670861349324811909 3053448313286502998402233)
                    ·
                      refine ⟨2290086234964877248801675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3053448313286502998402233 2290086234964877248801675)
                      ·
                        rfl

theorem cell23_4459927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_4459927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459927 prefixEnd_4459927 := by exact prefixLift 4459927
  have htrace : WordTrace (prefixWord ++ tailWord_4459927) baseStart_4459927 baseEnd_4459927 := by
    simpa [prefixWord, tailWord_4459927, baseEnd_4459927] using wordTrace_append hprefix tailTrace_4459927
  have hstable : (prefixWord ++ tailWord_4459927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459927).length < 2 ^ (prefixWord ++ tailWord_4459927).sum := by decide
  have hdescent : baseEnd_4459927 < baseStart_4459927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459940 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_4459940 : Nat := 118140960795 + 4459940 * 2 ^ 59
def prefixEnd_4459940 : Nat := 4983230072969 + 3 ^ 40 * 4459940 * 2
def baseEnd_4459940 : Nat := 2290092910213385697939115

theorem tailTrace_4459940 : CollatzResearch.WordTrace tailWord_4459940 prefixEnd_4459940 2290092910213385697939115 := by
  unfold tailWord_4459940
  simp only [CollatzResearch.WordTrace]
  refine ⟨81333687731203275977652637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108444916974937701303536849 81333687731203275977652637)
  ·
    refine ⟨30500132899201228491619739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81333687731203275977652637 30500132899201228491619739)
    ·
      refine ⟨45750199348801842737429609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30500132899201228491619739 45750199348801842737429609)
      ·
        refine ⟨34312649511601382053072207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45750199348801842737429609 34312649511601382053072207)
        ·
          refine ⟨51468974267402073079608311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34312649511601382053072207 51468974267402073079608311)
          ·
            refine ⟨77203461401103109619412467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51468974267402073079608311 77203461401103109619412467)
            ·
              refine ⟨115805192101654664429118701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77203461401103109619412467 115805192101654664429118701)
              ·
                refine ⟨43426947038120499160919513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115805192101654664429118701 43426947038120499160919513)
                ·
                  refine ⟨32570210278590374370689635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43426947038120499160919513 32570210278590374370689635)
                  ·
                    refine ⟨48855315417885561556034453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32570210278590374370689635 48855315417885561556034453)
                    ·
                      refine ⟨2290092910213385697939115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48855315417885561556034453 2290092910213385697939115)
                      ·
                        rfl

theorem cell23_4459940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_4459940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459940 prefixEnd_4459940 := by exact prefixLift 4459940
  have htrace : WordTrace (prefixWord ++ tailWord_4459940) baseStart_4459940 baseEnd_4459940 := by
    simpa [prefixWord, tailWord_4459940, baseEnd_4459940] using wordTrace_append hprefix tailTrace_4459940
  have hstable : (prefixWord ++ tailWord_4459940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459940).length < 2 ^ (prefixWord ++ tailWord_4459940).sum := by decide
  have hdescent : baseEnd_4459940 < baseStart_4459940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4459988 : List Nat := [2, 4, 1, 2, 3, 1, 2, 3, 1, 4]
def baseStart_4459988 : Nat := 118140960795 + 4459988 * 2 ^ 59
def prefixEnd_4459988 : Nat := 4983230072969 + 3 ^ 40 * 4459988 * 2
def baseEnd_4459988 : Nat := 763372519094933836712965

theorem tailTrace_4459988 : CollatzResearch.WordTrace tailWord_4459988 prefixEnd_4459988 763372519094933836712965 := by
  unfold tailWord_4459988
  simp only [CollatzResearch.WordTrace]
  refine ⟨81334563083116328076526309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108446084110821770768701745 81334563083116328076526309)
  ·
    refine ⟨15250230578084311514348683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81334563083116328076526309 15250230578084311514348683)
    ·
      refine ⟨22875345867126467271523025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15250230578084311514348683 22875345867126467271523025)
      ·
        refine ⟨17156509400344850453642269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22875345867126467271523025 17156509400344850453642269)
        ·
          refine ⟨6433691025129318920115851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17156509400344850453642269 6433691025129318920115851)
          ·
            refine ⟨9650536537693978380173777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6433691025129318920115851 9650536537693978380173777)
            ·
              refine ⟨7237902403270483785130333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9650536537693978380173777 7237902403270483785130333)
              ·
                refine ⟨2714213401226431419423875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7237902403270483785130333 2714213401226431419423875)
                ·
                  refine ⟨4071320101839647129135813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2714213401226431419423875 4071320101839647129135813)
                  ·
                    refine ⟨763372519094933836712965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4071320101839647129135813 763372519094933836712965)
                    ·
                      rfl

theorem cell23_4459988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_4459988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4459988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4459988 prefixEnd_4459988 := by exact prefixLift 4459988
  have htrace : WordTrace (prefixWord ++ tailWord_4459988) baseStart_4459988 baseEnd_4459988 := by
    simpa [prefixWord, tailWord_4459988, baseEnd_4459988] using wordTrace_append hprefix tailTrace_4459988
  have hstable : (prefixWord ++ tailWord_4459988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4459988).length < 2 ^ (prefixWord ++ tailWord_4459988).sum := by decide
  have hdescent : baseEnd_4459988 < baseStart_4459988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4459988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460004 : List Nat := [2, 3, 1, 1, 1, 1, 1, 6, 2, 3, 2]
def baseStart_4460004 : Nat := 118140960795 + 4460004 * 2 ^ 59
def prefixEnd_4460004 : Nat := 4983230072969 + 3 ^ 40 * 4460004 * 2
def baseEnd_4460004 : Nat := 2290125772975273447538821

theorem tailTrace_4460004 : CollatzResearch.WordTrace tailWord_4460004 prefixEnd_4460004 2290125772975273447538821 := by
  unfold tailWord_4460004
  simp only [CollatzResearch.WordTrace]
  refine ⟨81334854867087345442817533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108446473156116460590423377 81334854867087345442817533)
  ·
    refine ⟨30500570575157754541056575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81334854867087345442817533 30500570575157754541056575)
    ·
      refine ⟨45750855862736631811584863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30500570575157754541056575 45750855862736631811584863)
      ·
        refine ⟨68626283794104947717377295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45750855862736631811584863 68626283794104947717377295)
        ·
          refine ⟨102939425691157421576065943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68626283794104947717377295 102939425691157421576065943)
          ·
            refine ⟨154409138536736132364098915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102939425691157421576065943 154409138536736132364098915)
            ·
              refine ⟨231613707805104198546148373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154409138536736132364098915 231613707805104198546148373)
              ·
                refine ⟨10856892553364259306850705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 231613707805104198546148373 10856892553364259306850705)
                ·
                  refine ⟨8142669415023194480138029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10856892553364259306850705 8142669415023194480138029)
                  ·
                    refine ⟨3053501030633697930051761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8142669415023194480138029 3053501030633697930051761)
                    ·
                      refine ⟨2290125772975273447538821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3053501030633697930051761 2290125772975273447538821)
                      ·
                        rfl

theorem cell23_4460004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_4460004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460004 prefixEnd_4460004 := by exact prefixLift 4460004
  have htrace : WordTrace (prefixWord ++ tailWord_4460004) baseStart_4460004 baseEnd_4460004 := by
    simpa [prefixWord, tailWord_4460004, baseEnd_4460004] using wordTrace_append hprefix tailTrace_4460004
  have hstable : (prefixWord ++ tailWord_4460004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460004).length < 2 ^ (prefixWord ++ tailWord_4460004).sum := by decide
  have hdescent : baseEnd_4460004 < baseStart_4460004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460021 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_4460021 : Nat := 118140960795 + 4460021 * 2 ^ 59
def prefixEnd_4460021 : Nat := 4983230072969 + 3 ^ 40 * 4460021 * 2
def baseEnd_4460021 : Nat := 2290134502146399881026243

theorem tailTrace_4460021 : CollatzResearch.WordTrace tailWord_4460021 prefixEnd_4460021 2290134502146399881026243 := by
  unfold tailWord_4460021
  simp only [CollatzResearch.WordTrace]
  refine ⟨162670329775113102789003917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108446886516742068526002611 162670329775113102789003917)
  ·
    refine ⟨61001373665667413545876469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162670329775113102789003917 61001373665667413545876469)
    ·
      refine ⟨5718878781156320019925919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61001373665667413545876469 5718878781156320019925919)
      ·
        refine ⟨8578318171734480029888879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5718878781156320019925919 8578318171734480029888879)
        ·
          refine ⟨12867477257601720044833319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8578318171734480029888879 12867477257601720044833319)
          ·
            refine ⟨19301215886402580067249979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12867477257601720044833319 19301215886402580067249979)
            ·
              refine ⟨28951823829603870100874969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19301215886402580067249979 28951823829603870100874969)
              ·
                refine ⟨21713867872202902575656227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28951823829603870100874969 21713867872202902575656227)
                ·
                  refine ⟨32570801808304353863484341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21713867872202902575656227 32570801808304353863484341)
                  ·
                    refine ⟨3053512669528533174701657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32570801808304353863484341 3053512669528533174701657)
                    ·
                      refine ⟨2290134502146399881026243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3053512669528533174701657 2290134502146399881026243)
                      ·
                        rfl

theorem cell23_4460021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_4460021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460021 prefixEnd_4460021 := by exact prefixLift 4460021
  have htrace : WordTrace (prefixWord ++ tailWord_4460021) baseStart_4460021 baseEnd_4460021 := by
    simpa [prefixWord, tailWord_4460021, baseEnd_4460021] using wordTrace_append hprefix tailTrace_4460021
  have hstable : (prefixWord ++ tailWord_4460021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460021).length < 2 ^ (prefixWord ++ tailWord_4460021).sum := by decide
  have hdescent : baseEnd_4460021 < baseStart_4460021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460078 : List Nat := [4, 1, 3, 1, 2, 1, 4, 1, 2, 4]
def baseStart_4460078 : Nat := 118140960795 + 4460078 * 2 ^ 59
def prefixEnd_4460078 : Nat := 4983230072969 + 3 ^ 40 * 4460078 * 2
def baseEnd_4460078 : Nat := 763387923514568719337827

theorem tailTrace_4460078 : CollatzResearch.WordTrace tailWord_4460078 prefixEnd_4460078 763387923514568719337827 := by
  unfold tailWord_4460078
  simp only [CollatzResearch.WordTrace]
  refine ⟨20334051091988325190478611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108448272490604401015885925 20334051091988325190478611)
  ·
    refine ⟨30501076637982487785717917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20334051091988325190478611 30501076637982487785717917)
    ·
      refine ⟨11437903739243432919644219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30501076637982487785717917 11437903739243432919644219)
      ·
        refine ⟨17156855608865149379466329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11437903739243432919644219 17156855608865149379466329)
        ·
          refine ⟨12867641706648862034599747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17156855608865149379466329 12867641706648862034599747)
          ·
            refine ⟨19301462559973293051899621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12867641706648862034599747 19301462559973293051899621)
            ·
              refine ⟨3619024229994992447231179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19301462559973293051899621 3619024229994992447231179)
              ·
                refine ⟨5428536344992488670846769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3619024229994992447231179 5428536344992488670846769)
                ·
                  refine ⟨4071402258744366503135077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5428536344992488670846769 4071402258744366503135077)
                  ·
                    refine ⟨763387923514568719337827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4071402258744366503135077 763387923514568719337827)
                    ·
                      rfl

theorem cell23_4460078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_4460078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460078 prefixEnd_4460078 := by exact prefixLift 4460078
  have htrace : WordTrace (prefixWord ++ tailWord_4460078) baseStart_4460078 baseEnd_4460078 := by
    simpa [prefixWord, tailWord_4460078, baseEnd_4460078] using wordTrace_append hprefix tailTrace_4460078
  have hstable : (prefixWord ++ tailWord_4460078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460078).length < 2 ^ (prefixWord ++ tailWord_4460078).sum := by decide
  have hdescent : baseEnd_4460078 < baseStart_4460078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460117 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 2, 6]
def baseStart_4460117 : Nat := 118140960795 + 4460117 * 2 ^ 59
def prefixEnd_4460117 : Nat := 4983230072969 + 3 ^ 40 * 4460117 * 2
def baseEnd_4460117 : Nat := 763394598763077168475267

theorem tailTrace_4460117 : CollatzResearch.WordTrace tailWord_4460117 prefixEnd_4460117 763394598763077168475267 := by
  unfold tailWord_4460117
  simp only [CollatzResearch.WordTrace]
  refine ⟨162673831182765311184498605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108449220788510207456332403 162673831182765311184498605)
  ·
    refine ⟨61002686693536991694186977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162673831182765311184498605 61002686693536991694186977)
    ·
      refine ⟨45752015020152743770640233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61002686693536991694186977 45752015020152743770640233)
      ·
        refine ⟨34314011265114557827980175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45752015020152743770640233 34314011265114557827980175)
        ·
          refine ⟨51471016897671836741970263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34314011265114557827980175 51471016897671836741970263)
          ·
            refine ⟨77206525346507755112955395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51471016897671836741970263 77206525346507755112955395)
            ·
              refine ⟨115809788019761632669433093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77206525346507755112955395 115809788019761632669433093)
              ·
                refine ⟨21714335253705306125518705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115809788019761632669433093 21714335253705306125518705)
                ·
                  refine ⟨16285751440278979594139029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21714335253705306125518705 16285751440278979594139029)
                  ·
                    refine ⟨763394598763077168475267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16285751440278979594139029 763394598763077168475267)
                    ·
                      rfl

theorem cell23_4460117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_4460117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460117 prefixEnd_4460117 := by exact prefixLift 4460117
  have htrace : WordTrace (prefixWord ++ tailWord_4460117) baseStart_4460117 baseEnd_4460117 := by
    simpa [prefixWord, tailWord_4460117, baseEnd_4460117] using wordTrace_append hprefix tailTrace_4460117
  have hstable : (prefixWord ++ tailWord_4460117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460117).length < 2 ^ (prefixWord ++ tailWord_4460117).sum := by decide
  have hdescent : baseEnd_4460117 < baseStart_4460117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460124 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_4460124 : Nat := 118140960795 + 4460124 * 2 ^ 59
def prefixEnd_4460124 : Nat := 4983230072969 + 3 ^ 40 * 4460124 * 2
def baseEnd_4460124 : Nat := 2290187390653812978038269

theorem tailTrace_4460124 : CollatzResearch.WordTrace tailWord_4460124 prefixEnd_4460124 2290187390653812978038269 := by
  unfold tailWord_4460124
  simp only [CollatzResearch.WordTrace]
  refine ⟨81337043246869975690001713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108449390995826634253335617 81337043246869975690001713)
  ·
    refine ⟨61002782435152481767501285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81337043246869975690001713 61002782435152481767501285)
    ·
      refine ⟨11438021706591090331406491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61002782435152481767501285 11438021706591090331406491)
      ·
        refine ⟨17157032559886635497109737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11438021706591090331406491 17157032559886635497109737)
        ·
          refine ⟨12867774419914976622832303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17157032559886635497109737 12867774419914976622832303)
          ·
            refine ⟨19301661629872464934248455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12867774419914976622832303 19301661629872464934248455)
            ·
              refine ⟨28952492444808697401372683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19301661629872464934248455 28952492444808697401372683)
              ·
                refine ⟨43428738667213046102059025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28952492444808697401372683 43428738667213046102059025)
                ·
                  refine ⟨32571554000409784576544269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43428738667213046102059025 32571554000409784576544269)
                  ·
                    refine ⟨12214332750153669216204101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32571554000409784576544269 12214332750153669216204101)
                    ·
                      refine ⟨2290187390653812978038269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12214332750153669216204101 2290187390653812978038269)
                      ·
                        rfl

theorem cell23_4460124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_4460124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460124 prefixEnd_4460124 := by exact prefixLift 4460124
  have htrace : WordTrace (prefixWord ++ tailWord_4460124) baseStart_4460124 baseEnd_4460124 := by
    simpa [prefixWord, tailWord_4460124, baseEnd_4460124] using wordTrace_append hprefix tailTrace_4460124
  have hstable : (prefixWord ++ tailWord_4460124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460124).length < 2 ^ (prefixWord ++ tailWord_4460124).sum := by decide
  have hdescent : baseEnd_4460124 < baseStart_4460124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460137 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 1, 4, 4]
def baseStart_4460137 : Nat := 118140960795 + 4460137 * 2 ^ 59
def prefixEnd_4460137 : Nat := 4983230072969 + 3 ^ 40 * 4460137 * 2
def baseEnd_4460137 : Nat := 2290194065902321427175709

theorem tailTrace_4460137 : CollatzResearch.WordTrace tailWord_4460137 prefixEnd_4460137 2290194065902321427175709 := by
  unfold tailWord_4460137
  simp only [CollatzResearch.WordTrace]
  refine ⟨162674560642692854600226665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108449707095128569733484443 162674560642692854600226665)
  ·
    refine ⟨122005920482019640950169999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162674560642692854600226665 122005920482019640950169999)
    ·
      refine ⟨183008880723029461425254999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122005920482019640950169999 183008880723029461425254999)
      ·
        refine ⟨274513321084544192137882499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183008880723029461425254999 274513321084544192137882499)
        ·
          refine ⟨411769981626816288206823749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274513321084544192137882499 411769981626816288206823749)
          ·
            refine ⟨77206871555028054038779453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 411769981626816288206823749 77206871555028054038779453)
            ·
              refine ⟨28952576833135520264542295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77206871555028054038779453 28952576833135520264542295)
              ·
                refine ⟨43428865249703280396813443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28952576833135520264542295 43428865249703280396813443)
                ·
                  refine ⟨65143297874554920595220165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43428865249703280396813443 65143297874554920595220165)
                  ·
                    refine ⟨12214368351479047611603781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65143297874554920595220165 12214368351479047611603781)
                    ·
                      refine ⟨2290194065902321427175709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12214368351479047611603781 2290194065902321427175709)
                      ·
                        rfl

theorem cell23_4460137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 4, 4].length) (baseStart_4460137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460137 prefixEnd_4460137 := by exact prefixLift 4460137
  have htrace : WordTrace (prefixWord ++ tailWord_4460137) baseStart_4460137 baseEnd_4460137 := by
    simpa [prefixWord, tailWord_4460137, baseEnd_4460137] using wordTrace_append hprefix tailTrace_4460137
  have hstable : (prefixWord ++ tailWord_4460137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460137).length < 2 ^ (prefixWord ++ tailWord_4460137).sum := by decide
  have hdescent : baseEnd_4460137 < baseStart_4460137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460207 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 2, 8]
def baseStart_4460207 : Nat := 118140960795 + 4460207 * 2 ^ 59
def prefixEnd_4460207 : Nat := 4983230072969 + 3 ^ 40 * 4460207 * 2
def baseEnd_4460207 : Nat := 763410003182712051100129

theorem tailTrace_4460207 : CollatzResearch.WordTrace tailWord_4460207 prefixEnd_4460207 763410003182712051100129 := by
  unfold tailWord_4460207
  simp only [CollatzResearch.WordTrace]
  refine ⟨162677113752439256555274875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108451409168292837703516583 162677113752439256555274875)
  ·
    refine ⟨244015670628658884832912313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162677113752439256555274875 244015670628658884832912313)
    ·
      refine ⟨183011752971494163624684235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244015670628658884832912313 183011752971494163624684235)
      ·
        refine ⟨274517629457241245437026353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183011752971494163624684235 274517629457241245437026353)
        ·
          refine ⟨205888222092930934077769765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274517629457241245437026353 205888222092930934077769765)
          ·
            refine ⟨38604041642424550139581831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 205888222092930934077769765 38604041642424550139581831)
            ·
              refine ⟨57906062463636825209372747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38604041642424550139581831 57906062463636825209372747)
              ·
                refine ⟨86859093695455237814059121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57906062463636825209372747 86859093695455237814059121)
                ·
                  refine ⟨65144320271591428360544341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86859093695455237814059121 65144320271591428360544341)
                  ·
                    refine ⟨763410003182712051100129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65144320271591428360544341 763410003182712051100129)
                    ·
                      rfl

theorem cell23_4460207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 8].length) (baseStart_4460207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460207 prefixEnd_4460207 := by exact prefixLift 4460207
  have htrace : WordTrace (prefixWord ++ tailWord_4460207) baseStart_4460207 baseEnd_4460207 := by
    simpa [prefixWord, tailWord_4460207, baseEnd_4460207] using wordTrace_append hprefix tailTrace_4460207
  have hstable : (prefixWord ++ tailWord_4460207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460207).length < 2 ^ (prefixWord ++ tailWord_4460207).sum := by decide
  have hdescent : baseEnd_4460207 < baseStart_4460207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460241 : List Nat := [1, 2, 2, 1, 2, 4, 3, 1, 3, 4]
def baseStart_4460241 : Nat := 118140960795 + 4460241 * 2 ^ 59
def prefixEnd_4460241 : Nat := 4983230072969 + 3 ^ 40 * 4460241 * 2
def baseEnd_4460241 : Nat := 763415822630129673425077

theorem tailTrace_4460241 : CollatzResearch.WordTrace tailWord_4460241 prefixEnd_4460241 763415822630129673425077 := by
  unfold tailWord_4460241
  simp only [CollatzResearch.WordTrace]
  refine ⟨162678353834316080362012577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108452235889544053574675051 162678353834316080362012577)
  ·
    refine ⟨122008765375737060271509433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162678353834316080362012577 122008765375737060271509433)
    ·
      refine ⟨91506574031802795203632075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122008765375737060271509433 91506574031802795203632075)
      ·
        refine ⟨137259861047704192805448113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91506574031802795203632075 137259861047704192805448113)
        ·
          refine ⟨102944895785778144604086085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137259861047704192805448113 102944895785778144604086085)
          ·
            refine ⟨19302167959833402113266141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102944895785778144604086085 19302167959833402113266141)
            ·
              refine ⟨7238312984937525792474803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19302167959833402113266141 7238312984937525792474803)
              ·
                refine ⟨10857469477406288688712205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7238312984937525792474803 10857469477406288688712205)
                ·
                  refine ⟨4071551054027358258267077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10857469477406288688712205 4071551054027358258267077)
                  ·
                    refine ⟨763415822630129673425077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4071551054027358258267077 763415822630129673425077)
                    ·
                      rfl

theorem cell23_4460241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 4].length) (baseStart_4460241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460241 prefixEnd_4460241 := by exact prefixLift 4460241
  have htrace : WordTrace (prefixWord ++ tailWord_4460241) baseStart_4460241 baseEnd_4460241 := by
    simpa [prefixWord, tailWord_4460241, baseEnd_4460241] using wordTrace_append hprefix tailTrace_4460241
  have hstable : (prefixWord ++ tailWord_4460241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460241).length < 2 ^ (prefixWord ++ tailWord_4460241).sum := by decide
  have hdescent : baseEnd_4460241 < baseStart_4460241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460292 : List Nat := [2, 3, 2, 2, 1, 4, 2, 2, 1, 4]
def baseStart_4460292 : Nat := 118140960795 + 4460292 * 2 ^ 59
def prefixEnd_4460292 : Nat := 4983230072969 + 3 ^ 40 * 4460292 * 2
def baseEnd_4460292 : Nat := 763424551801256106912499

theorem tailTrace_4460292 : CollatzResearch.WordTrace tailWord_4460292 prefixEnd_4460292 763424551801256106912499 := by
  unfold tailWord_4460292
  simp only [CollatzResearch.WordTrace]
  refine ⟨81340106978565658036059565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108453475971420877381412753 81340106978565658036059565)
  ·
    refine ⟨30502540116962121763522337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81340106978565658036059565 30502540116962121763522337)
    ·
      refine ⟨22876905087721591322641753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30502540116962121763522337 22876905087721591322641753)
      ·
        refine ⟨17157678815791193491981315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22876905087721591322641753 17157678815791193491981315)
        ·
          refine ⟨25736518223686790237971973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17157678815791193491981315 25736518223686790237971973)
          ·
            refine ⟨4825597166941273169619745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25736518223686790237971973 4825597166941273169619745)
            ·
              refine ⟨3619197875205954877214809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4825597166941273169619745 3619197875205954877214809)
              ·
                refine ⟨2714398406404466157911107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3619197875205954877214809 2714398406404466157911107)
                ·
                  refine ⟨4071597609606699236866661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2714398406404466157911107 4071597609606699236866661)
                  ·
                    refine ⟨763424551801256106912499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4071597609606699236866661 763424551801256106912499)
                    ·
                      rfl

theorem cell23_4460292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_4460292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460292 prefixEnd_4460292 := by exact prefixLift 4460292
  have htrace : WordTrace (prefixWord ++ tailWord_4460292) baseStart_4460292 baseEnd_4460292 := by
    simpa [prefixWord, tailWord_4460292, baseEnd_4460292] using wordTrace_append hprefix tailTrace_4460292
  have hstable : (prefixWord ++ tailWord_4460292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460292).length < 2 ^ (prefixWord ++ tailWord_4460292).sum := by decide
  have hdescent : baseEnd_4460292 < baseStart_4460292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460321 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 3, 1, 4]
def baseStart_4460321 : Nat := 118140960795 + 4460321 * 2 ^ 59
def prefixEnd_4460321 : Nat := 4983230072969 + 3 ^ 40 * 4460321 * 2
def baseEnd_4460321 : Nat := 2290288546342748707274863

theorem tailTrace_4460321 : CollatzResearch.WordTrace tailWord_4460321 prefixEnd_4460321 2290288546342748707274863 := by
  unfold tailWord_4460321
  simp only [CollatzResearch.WordTrace]
  refine ⟨162681271674026254024924817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108454181116017502683283211 162681271674026254024924817)
  ·
    refine ⟨122010953755519690518693613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162681271674026254024924817 122010953755519690518693613)
    ·
      refine ⟨45754107658319883944510105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122010953755519690518693613 45754107658319883944510105)
      ·
        refine ⟨34315580743739912958382579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45754107658319883944510105 34315580743739912958382579)
        ·
          refine ⟨51473371115609869437573869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34315580743739912958382579 51473371115609869437573869)
          ·
            refine ⟨19302514168353701039090201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51473371115609869437573869 19302514168353701039090201)
            ·
              refine ⟨14476885626265275779317651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19302514168353701039090201 14476885626265275779317651)
              ·
                refine ⟨21715328439397913668976477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14476885626265275779317651 21715328439397913668976477)
                ·
                  refine ⟨8143248164774217625866179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21715328439397913668976477 8143248164774217625866179)
                  ·
                    refine ⟨12214872247161326438799269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8143248164774217625866179 12214872247161326438799269)
                    ·
                      refine ⟨2290288546342748707274863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12214872247161326438799269 2290288546342748707274863)
                      ·
                        rfl

theorem cell23_4460321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_4460321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460321 prefixEnd_4460321 := by exact prefixLift 4460321
  have htrace : WordTrace (prefixWord ++ tailWord_4460321) baseStart_4460321 baseEnd_4460321 := by
    simpa [prefixWord, tailWord_4460321, baseEnd_4460321] using wordTrace_append hprefix tailTrace_4460321
  have hstable : (prefixWord ++ tailWord_4460321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460321).length < 2 ^ (prefixWord ++ tailWord_4460321).sum := by decide
  have hdescent : baseEnd_4460321 < baseStart_4460321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460325 : List Nat := [1, 3, 1, 2, 3, 4, 1, 1, 2, 3, 2]
def baseStart_4460325 : Nat := 118140960795 + 4460325 * 2 ^ 59
def prefixEnd_4460325 : Nat := 4983230072969 + 3 ^ 40 * 4460325 * 2
def baseEnd_4460325 : Nat := 2290290600265366691624845

theorem tailTrace_4460325 : CollatzResearch.WordTrace tailWord_4460325 prefixEnd_4460325 2290290600265366691624845 := by
  unfold tailWord_4460325
  simp only [CollatzResearch.WordTrace]
  refine ⟨162681417566011762708070429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108454278377341175138713619 162681417566011762708070429)
  ·
    refine ⟨61005531587254411015526411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162681417566011762708070429 61005531587254411015526411)
    ·
      refine ⟨91508297380881616523289617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61005531587254411015526411 91508297380881616523289617)
      ·
        refine ⟨68631223035661212392467213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91508297380881616523289617 68631223035661212392467213)
        ·
          refine ⟨25736708638372954647175205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68631223035661212392467213 25736708638372954647175205)
          ·
            refine ⟨4825632869694928996345351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25736708638372954647175205 4825632869694928996345351)
            ·
              refine ⟨7238449304542393494518027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4825632869694928996345351 7238449304542393494518027)
              ·
                refine ⟨10857673956813590241777041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7238449304542393494518027 10857673956813590241777041)
                ·
                  refine ⟨8143255467610192681332781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10857673956813590241777041 8143255467610192681332781)
                  ·
                    refine ⟨3053720800353822255499793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8143255467610192681332781 3053720800353822255499793)
                    ·
                      refine ⟨2290290600265366691624845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3053720800353822255499793 2290290600265366691624845)
                      ·
                        rfl

theorem cell23_4460325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_4460325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460325 prefixEnd_4460325 := by exact prefixLift 4460325
  have htrace : WordTrace (prefixWord ++ tailWord_4460325) baseStart_4460325 baseEnd_4460325 := by
    simpa [prefixWord, tailWord_4460325, baseEnd_4460325] using wordTrace_append hprefix tailTrace_4460325
  have hstable : (prefixWord ++ tailWord_4460325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460325).length < 2 ^ (prefixWord ++ tailWord_4460325).sum := by decide
  have hdescent : baseEnd_4460325 < baseStart_4460325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460338 : List Nat := [3, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4]
def baseStart_4460338 : Nat := 118140960795 + 4460338 * 2 ^ 59
def prefixEnd_4460338 : Nat := 4983230072969 + 3 ^ 40 * 4460338 * 2
def baseEnd_4460338 : Nat := 2290297275513875140762285

theorem tailTrace_4460338 : CollatzResearch.WordTrace tailWord_4460338 prefixEnd_4460338 2290297275513875140762285 := by
  unfold tailWord_4460338
  simp only [CollatzResearch.WordTrace]
  refine ⟨40670472928741166482073417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108454594476643110618862445 40670472928741166482073417)
  ·
    refine ⟨30502854696555874861555063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40670472928741166482073417 30502854696555874861555063)
    ·
      refine ⟨45754282044833812292332595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30502854696555874861555063 45754282044833812292332595)
      ·
        refine ⟨68631423067250718438498893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45754282044833812292332595 68631423067250718438498893)
        ·
          refine ⟨25736783650219019414437085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68631423067250718438498893 25736783650219019414437085)
          ·
            refine ⟨9651293868832132280413907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25736783650219019414437085 9651293868832132280413907)
            ·
              refine ⟨14476940803248198420620861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9651293868832132280413907 14476940803248198420620861)
              ·
                refine ⟨5428852801218074407732823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14476940803248198420620861 5428852801218074407732823)
                ·
                  refine ⟨8143279201827111611599235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5428852801218074407732823 8143279201827111611599235)
                  ·
                    refine ⟨12214918802740667417398853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8143279201827111611599235 12214918802740667417398853)
                    ·
                      refine ⟨2290297275513875140762285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12214918802740667417398853 2290297275513875140762285)
                      ·
                        rfl

theorem cell23_4460338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_4460338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460338 prefixEnd_4460338 := by exact prefixLift 4460338
  have htrace : WordTrace (prefixWord ++ tailWord_4460338) baseStart_4460338 baseEnd_4460338 := by
    simpa [prefixWord, tailWord_4460338, baseEnd_4460338] using wordTrace_append hprefix tailTrace_4460338
  have hstable : (prefixWord ++ tailWord_4460338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460338).length < 2 ^ (prefixWord ++ tailWord_4460338).sum := by decide
  have hdescent : baseEnd_4460338 < baseStart_4460338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460344 : List Nat := [2, 1, 2, 1, 3, 4, 10]
def baseStart_4460344 : Nat := 118140960795 + 4460344 * 2 ^ 59
def prefixEnd_4460344 : Nat := 4983230072969 + 3 ^ 40 * 4460344 * 2
def baseEnd_4460344 : Nat := 28275313041948174287497

theorem tailTrace_4460344 : CollatzResearch.WordTrace tailWord_4460344 prefixEnd_4460344 28275313041948174287497 := by
  unfold tailWord_4460344
  simp only [CollatzResearch.WordTrace]
  refine ⟨81341055276471464476506043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108454740368628619302008057 81341055276471464476506043)
  ·
    refine ⟨122011582914707196714759065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81341055276471464476506043 122011582914707196714759065)
    ·
      refine ⟨91508687186030397536069299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122011582914707196714759065 91508687186030397536069299)
      ·
        refine ⟨137263030779045596304103949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91508687186030397536069299 137263030779045596304103949)
        ·
          refine ⟨51473636542142098614038981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137263030779045596304103949 51473636542142098614038981)
          ·
            refine ⟨9651306851651643490132309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51473636542142098614038981 9651306851651643490132309)
            ·
              refine ⟨28275313041948174287497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9651306851651643490132309 28275313041948174287497)
              ·
                rfl

theorem cell23_4460344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 10].length) (baseStart_4460344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460344 prefixEnd_4460344 := by exact prefixLift 4460344
  have htrace : WordTrace (prefixWord ++ tailWord_4460344) baseStart_4460344 baseEnd_4460344 := by
    simpa [prefixWord, tailWord_4460344, baseEnd_4460344] using wordTrace_append hprefix tailTrace_4460344
  have hstable : (prefixWord ++ tailWord_4460344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460344).length < 2 ^ (prefixWord ++ tailWord_4460344).sum := by decide
  have hdescent : baseEnd_4460344 < baseStart_4460344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460348 : List Nat := [2, 2, 2, 2, 1, 1, 5, 2, 2, 4]
def baseStart_4460348 : Nat := 118140960795 + 4460348 * 2 ^ 59
def prefixEnd_4460348 : Nat := 4983230072969 + 3 ^ 40 * 4460348 * 2
def baseEnd_4460348 : Nat := 763434136773473367212413

theorem tailTrace_4460348 : CollatzResearch.WordTrace tailWord_4460348 prefixEnd_4460348 763434136773473367212413 := by
  unfold tailWord_4460348
  simp only [CollatzResearch.WordTrace]
  refine ⟨81341128222464218818078849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108454837629952291757438465 81341128222464218818078849)
  ·
    refine ⟨61005846166848164113559137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81341128222464218818078849 61005846166848164113559137)
    ·
      refine ⟨45754384625136123085169353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61005846166848164113559137 45754384625136123085169353)
      ·
        refine ⟨34315788468852092313877015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45754384625136123085169353 34315788468852092313877015)
        ·
          refine ⟨51473682703278138470815523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34315788468852092313877015 51473682703278138470815523)
          ·
            refine ⟨77210524054917207706223285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51473682703278138470815523 77210524054917207706223285)
            ·
              refine ⟨7238486630148488222458433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77210524054917207706223285 7238486630148488222458433)
              ·
                refine ⟨5428864972611366166843825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7238486630148488222458433 5428864972611366166843825)
                ·
                  refine ⟨4071648729458524625132869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5428864972611366166843825 4071648729458524625132869)
                  ·
                    refine ⟨763434136773473367212413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4071648729458524625132869 763434136773473367212413)
                    ·
                      rfl

theorem cell23_4460348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_4460348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460348 prefixEnd_4460348 := by exact prefixLift 4460348
  have htrace : WordTrace (prefixWord ++ tailWord_4460348) baseStart_4460348 baseEnd_4460348 := by
    simpa [prefixWord, tailWord_4460348, baseEnd_4460348] using wordTrace_append hprefix tailTrace_4460348
  have hstable : (prefixWord ++ tailWord_4460348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460348).length < 2 ^ (prefixWord ++ tailWord_4460348).sum := by decide
  have hdescent : baseEnd_4460348 < baseStart_4460348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460355 : List Nat := [1, 1, 1, 3, 1, 6, 2, 1, 3, 2, 2]
def baseStart_4460355 : Nat := 118140960795 + 4460355 * 2 ^ 59
def prefixEnd_4460355 : Nat := 4983230072969 + 3 ^ 40 * 4460355 * 2
def baseEnd_4460355 : Nat := 2290306004685001574249707

theorem tailTrace_4460355 : CollatzResearch.WordTrace tailWord_4460355 prefixEnd_4460355 2290306004685001574249707 := by
  unfold tailWord_4460355
  simp only [CollatzResearch.WordTrace]
  refine ⟨162682511755903077831662519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108455007837268718554441679 162682511755903077831662519)
  ·
    refine ⟨244023767633854616747493779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162682511755903077831662519 244023767633854616747493779)
    ·
      refine ⟨366035651450781925121240669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244023767633854616747493779 366035651450781925121240669)
      ·
        refine ⟨137263369294043221920465251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 366035651450781925121240669 137263369294043221920465251)
        ·
          refine ⟨205895053941064832880697877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137263369294043221920465251 205895053941064832880697877)
          ·
            refine ⟨9651330653487414041282713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 205895053941064832880697877 9651330653487414041282713)
            ·
              refine ⟨7238497990115560530962035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9651330653487414041282713 7238497990115560530962035)
              ·
                refine ⟨10857746985173340796443053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7238497990115560530962035 10857746985173340796443053)
                ·
                  refine ⟨4071655119440002798666145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10857746985173340796443053 4071655119440002798666145)
                  ·
                    refine ⟨3053741339580002098999609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4071655119440002798666145 3053741339580002098999609)
                    ·
                      refine ⟨2290306004685001574249707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3053741339580002098999609 2290306004685001574249707)
                      ·
                        rfl

theorem cell23_4460355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 2, 2].length) (baseStart_4460355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460355 prefixEnd_4460355 := by exact prefixLift 4460355
  have htrace : WordTrace (prefixWord ++ tailWord_4460355) baseStart_4460355 baseEnd_4460355 := by
    simpa [prefixWord, tailWord_4460355, baseEnd_4460355] using wordTrace_append hprefix tailTrace_4460355
  have hstable : (prefixWord ++ tailWord_4460355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460355).length < 2 ^ (prefixWord ++ tailWord_4460355).sum := by decide
  have hdescent : baseEnd_4460355 < baseStart_4460355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460365 : List Nat := [1, 6, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_4460365 : Nat := 118140960795 + 4460365 * 2 ^ 59
def prefixEnd_4460365 : Nat := 4983230072969 + 3 ^ 40 * 4460365 * 2
def baseEnd_4460365 : Nat := 763437046497182178374887

theorem tailTrace_4460365 : CollatzResearch.WordTrace tailWord_4460365 prefixEnd_4460365 763437046497182178374887 := by
  unfold tailWord_4460365
  simp only [CollatzResearch.WordTrace]
  refine ⟨162682876485866849539526549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108455250990577899693017699 162682876485866849539526549)
  ·
    refine ⟨7625759835275008572165307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 162682876485866849539526549 7625759835275008572165307)
    ·
      refine ⟨11438639752912512858247961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7625759835275008572165307 11438639752912512858247961)
      ·
        refine ⟨8578979814684384643685971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11438639752912512858247961 8578979814684384643685971)
        ·
          refine ⟨12868469722026576965528957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8578979814684384643685971 12868469722026576965528957)
          ·
            refine ⟨4825676145759966362073359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12868469722026576965528957 4825676145759966362073359)
            ·
              refine ⟨7238514218639949543110039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4825676145759966362073359 7238514218639949543110039)
              ·
                refine ⟨10857771327959924314665059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7238514218639949543110039 10857771327959924314665059)
                ·
                  refine ⟨16286656991939886471997589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10857771327959924314665059 16286656991939886471997589)
                  ·
                    refine ⟨763437046497182178374887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16286656991939886471997589 763437046497182178374887)
                    ·
                      rfl

theorem cell23_4460365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_4460365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460365 prefixEnd_4460365 := by exact prefixLift 4460365
  have htrace : WordTrace (prefixWord ++ tailWord_4460365) baseStart_4460365 baseEnd_4460365 := by
    simpa [prefixWord, tailWord_4460365, baseEnd_4460365] using wordTrace_append hprefix tailTrace_4460365
  have hstable : (prefixWord ++ tailWord_4460365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460365).length < 2 ^ (prefixWord ++ tailWord_4460365).sum := by decide
  have hdescent : baseEnd_4460365 < baseStart_4460365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460375 : List Nat := [1, 1, 3, 2, 5, 1, 2, 2, 1, 2, 3]
def baseStart_4460375 : Nat := 118140960795 + 4460375 * 2 ^ 59
def prefixEnd_4460375 : Nat := 4983230072969 + 3 ^ 40 * 4460375 * 2
def baseEnd_4460375 : Nat := 2290316274298091495999615

theorem tailTrace_4460375 : CollatzResearch.WordTrace tailWord_4460375 prefixEnd_4460375 2290316274298091495999615 := by
  unfold tailWord_4460375
  simp only [CollatzResearch.WordTrace]
  refine ⟨162683241215830621247390579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108455494143887080831593719 162683241215830621247390579)
  ·
    refine ⟨244024861823745931871085869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162683241215830621247390579 244024861823745931871085869)
    ·
      refine ⟨91509323183904724451657201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244024861823745931871085869 91509323183904724451657201)
      ·
        refine ⟨68631992387928543338742901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91509323183904724451657201 68631992387928543338742901)
        ·
          refine ⟨6434249286368300938007147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68631992387928543338742901 6434249286368300938007147)
          ·
            refine ⟨9651373929552451407010721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6434249286368300938007147 9651373929552451407010721)
            ·
              refine ⟨7238530447164338555258041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9651373929552451407010721 7238530447164338555258041)
              ·
                refine ⟨5428897835373253916443531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7238530447164338555258041 5428897835373253916443531)
                ·
                  refine ⟨8143346753059880874665297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5428897835373253916443531 8143346753059880874665297)
                  ·
                    refine ⟨6107510064794910655998973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8143346753059880874665297 6107510064794910655998973)
                    ·
                      refine ⟨2290316274298091495999615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6107510064794910655998973 2290316274298091495999615)
                      ·
                        rfl

theorem cell23_4460375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_4460375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460375 prefixEnd_4460375 := by exact prefixLift 4460375
  have htrace : WordTrace (prefixWord ++ tailWord_4460375) baseStart_4460375 baseEnd_4460375 := by
    simpa [prefixWord, tailWord_4460375, baseEnd_4460375] using wordTrace_append hprefix tailTrace_4460375
  have hstable : (prefixWord ++ tailWord_4460375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460375).length < 2 ^ (prefixWord ++ tailWord_4460375).sum := by decide
  have hdescent : baseEnd_4460375 < baseStart_4460375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460405 : List Nat := [1, 3, 4, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_4460405 : Nat := 118140960795 + 4460405 * 2 ^ 59
def prefixEnd_4460405 : Nat := 4983230072969 + 3 ^ 40 * 4460405 * 2
def baseEnd_4460405 : Nat := 2290331678717726378624477

theorem tailTrace_4460405 : CollatzResearch.WordTrace tailWord_4460405 prefixEnd_4460405 2290331678717726378624477 := by
  unfold tailWord_4460405
  simp only [CollatzResearch.WordTrace]
  refine ⟨162684335405721936370982669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108456223603814624247321779 162684335405721936370982669)
  ·
    refine ⟨61006625777145726139118501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162684335405721936370982669 61006625777145726139118501)
    ·
      refine ⟨11438742333214823651084719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61006625777145726139118501 11438742333214823651084719)
      ·
        refine ⟨17158113499822235476627079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11438742333214823651084719 17158113499822235476627079)
        ·
          refine ⟨25737170249733353214940619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17158113499822235476627079 25737170249733353214940619)
          ·
            refine ⟨38605755374600029822410929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25737170249733353214940619 38605755374600029822410929)
            ·
              refine ⟨28954316530950022366808197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38605755374600029822410929 28954316530950022366808197)
              ·
                refine ⟨5428934349553129193776537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28954316530950022366808197 5428934349553129193776537)
                ·
                  refine ⟨4071700762164846895332403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5428934349553129193776537 4071700762164846895332403)
                  ·
                    refine ⟨6107551143247270342998605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4071700762164846895332403 6107551143247270342998605)
                    ·
                      refine ⟨2290331678717726378624477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6107551143247270342998605 2290331678717726378624477)
                      ·
                        rfl

theorem cell23_4460405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_4460405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460405 prefixEnd_4460405 := by exact prefixLift 4460405
  have htrace : WordTrace (prefixWord ++ tailWord_4460405) baseStart_4460405 baseEnd_4460405 := by
    simpa [prefixWord, tailWord_4460405, baseEnd_4460405] using wordTrace_append hprefix tailTrace_4460405
  have hstable : (prefixWord ++ tailWord_4460405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460405).length < 2 ^ (prefixWord ++ tailWord_4460405).sum := by decide
  have hdescent : baseEnd_4460405 < baseStart_4460405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460406 : List Nat := [5, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2]
def baseStart_4460406 : Nat := 118140960795 + 4460406 * 2 ^ 59
def prefixEnd_4460406 : Nat := 4983230072969 + 3 ^ 40 * 4460406 * 2
def baseEnd_4460406 : Nat := 2290332192198380874711973

theorem tailTrace_4460406 : CollatzResearch.WordTrace tailWord_4460406 prefixEnd_4460406 2290332192198380874711973 := by
  unfold tailWord_4460406
  simp only [CollatzResearch.WordTrace]
  refine ⟨10167773242419894596360567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108456247919145542361179381 10167773242419894596360567)
  ·
    refine ⟨15251659863629841894540851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10167773242419894596360567 15251659863629841894540851)
    ·
      refine ⟨22877489795444762841811277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15251659863629841894540851 22877489795444762841811277)
      ·
        refine ⟨8579058673291786065679229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22877489795444762841811277 8579058673291786065679229)
        ·
          refine ⟨3217147002484419774629711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8579058673291786065679229 3217147002484419774629711)
          ·
            refine ⟨4825720503726629661944567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3217147002484419774629711 4825720503726629661944567)
            ·
              refine ⟨7238580755589944492916851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4825720503726629661944567 7238580755589944492916851)
              ·
                refine ⟨10857871133384916739375277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7238580755589944492916851 10857871133384916739375277)
                ·
                  refine ⟨4071701675019343777265729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10857871133384916739375277 4071701675019343777265729)
                  ·
                    refine ⟨3053776256264507832949297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4071701675019343777265729 3053776256264507832949297)
                    ·
                      refine ⟨2290332192198380874711973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3053776256264507832949297 2290332192198380874711973)
                      ·
                        rfl

theorem cell23_4460406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_4460406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460406 prefixEnd_4460406 := by exact prefixLift 4460406
  have htrace : WordTrace (prefixWord ++ tailWord_4460406) baseStart_4460406 baseEnd_4460406 := by
    simpa [prefixWord, tailWord_4460406, baseEnd_4460406] using wordTrace_append hprefix tailTrace_4460406
  have hstable : (prefixWord ++ tailWord_4460406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460406).length < 2 ^ (prefixWord ++ tailWord_4460406).sum := by decide
  have hdescent : baseEnd_4460406 < baseStart_4460406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460428 : List Nat := [2, 2, 1, 2, 1, 2, 1, 5, 1, 4, 2]
def baseStart_4460428 : Nat := 118140960795 + 4460428 * 2 ^ 59
def prefixEnd_4460428 : Nat := 4983230072969 + 3 ^ 40 * 4460428 * 2
def baseEnd_4460428 : Nat := 2290343488772779788636871

theorem tailTrace_4460428 : CollatzResearch.WordTrace tailWord_4460428 prefixEnd_4460428 2290343488772779788636871 := by
  unfold tailWord_4460428
  simp only [CollatzResearch.WordTrace]
  refine ⟨81342587142319305649534969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108456782856425740866046625 81342587142319305649534969)
  ·
    refine ⟨61006940356739479237151227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81342587142319305649534969 61006940356739479237151227)
    ·
      refine ⟨91510410535109218855726841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61006940356739479237151227 91510410535109218855726841)
      ·
        refine ⟨68632807901331914141795131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91510410535109218855726841 68632807901331914141795131)
        ·
          refine ⟨102949211851997871212692697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68632807901331914141795131 102949211851997871212692697)
          ·
            refine ⟨77211908888998403409519523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102949211851997871212692697 77211908888998403409519523)
            ·
              refine ⟨115817863333497605114279285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77211908888998403409519523 115817863333497605114279285)
              ·
                refine ⟨10857924687515400479463683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115817863333497605114279285 10857924687515400479463683)
                ·
                  refine ⟨16286887031273100719195525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10857924687515400479463683 16286887031273100719195525)
                  ·
                    refine ⟨3053791318363706384849161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16286887031273100719195525 3053791318363706384849161)
                    ·
                      refine ⟨2290343488772779788636871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3053791318363706384849161 2290343488772779788636871)
                      ·
                        rfl

theorem cell23_4460428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_4460428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460428 prefixEnd_4460428 := by exact prefixLift 4460428
  have htrace : WordTrace (prefixWord ++ tailWord_4460428) baseStart_4460428 baseEnd_4460428 := by
    simpa [prefixWord, tailWord_4460428, baseEnd_4460428] using wordTrace_append hprefix tailTrace_4460428
  have hstable : (prefixWord ++ tailWord_4460428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460428).length < 2 ^ (prefixWord ++ tailWord_4460428).sum := by decide
  have hdescent : baseEnd_4460428 < baseStart_4460428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460445 : List Nat := [1, 4, 2, 1, 2, 3, 1, 2, 1, 4, 2]
def baseStart_4460445 : Nat := 118140960795 + 4460445 * 2 ^ 59
def prefixEnd_4460445 : Nat := 4983230072969 + 3 ^ 40 * 4460445 * 2
def baseEnd_4460445 : Nat := 2290352217943906222124293

theorem tailTrace_4460445 : CollatzResearch.WordTrace tailWord_4460445 prefixEnd_4460445 2290352217943906222124293 := by
  unfold tailWord_4460445
  simp only [CollatzResearch.WordTrace]
  refine ⟨162685794325577023202438789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108457196217051348801625859 162685794325577023202438789)
  ·
    refine ⟨30503586436045691850457273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162685794325577023202438789 30503586436045691850457273)
    ·
      refine ⟨22877689827034268887842955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30503586436045691850457273 22877689827034268887842955)
      ·
        refine ⟨34316534740551403331764433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22877689827034268887842955 34316534740551403331764433)
        ·
          refine ⟨25737401055413552498823325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34316534740551403331764433 25737401055413552498823325)
          ·
            refine ⟨9651525395780082187058747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25737401055413552498823325 9651525395780082187058747)
            ·
              refine ⟨14477288093670123280588121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9651525395780082187058747 14477288093670123280588121)
              ·
                refine ⟨10857966070252592460441091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14477288093670123280588121 10857966070252592460441091)
                ·
                  refine ⟨16286949105378888690661637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10857966070252592460441091 16286949105378888690661637)
                  ·
                    refine ⟨3053802957258541629499057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16286949105378888690661637 3053802957258541629499057)
                    ·
                      refine ⟨2290352217943906222124293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3053802957258541629499057 2290352217943906222124293)
                      ·
                        rfl

theorem cell23_4460445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_4460445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460445 prefixEnd_4460445 := by exact prefixLift 4460445
  have htrace : WordTrace (prefixWord ++ tailWord_4460445) baseStart_4460445 baseEnd_4460445 := by
    simpa [prefixWord, tailWord_4460445, baseEnd_4460445] using wordTrace_append hprefix tailTrace_4460445
  have hstable : (prefixWord ++ tailWord_4460445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460445).length < 2 ^ (prefixWord ++ tailWord_4460445).sum := by decide
  have hdescent : baseEnd_4460445 < baseStart_4460445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460449 : List Nat := [1, 2, 3, 4, 2, 1, 3, 1, 1, 3, 2]
def baseStart_4460449 : Nat := 118140960795 + 4460449 * 2 ^ 59
def prefixEnd_4460449 : Nat := 4983230072969 + 3 ^ 40 * 4460449 * 2
def baseEnd_4460449 : Nat := 2290354271866524206474275

theorem tailTrace_4460449 : CollatzResearch.WordTrace tailWord_4460449 prefixEnd_4460449 2290354271866524206474275 := by
  unfold tailWord_4460449
  simp only [CollatzResearch.WordTrace]
  refine ⟨162685940217562531885584401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108457293478375021257056267 162685940217562531885584401)
  ·
    refine ⟨122014455163171898914188301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162685940217562531885584401 122014455163171898914188301)
    ·
      refine ⟨45755420686189462092820613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122014455163171898914188301 45755420686189462092820613)
      ·
        refine ⟨8579141378660524142403865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45755420686189462092820613 8579141378660524142403865)
        ·
          refine ⟨6434356033995393106802899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8579141378660524142403865 6434356033995393106802899)
          ·
            refine ⟨9651534050993089660204349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6434356033995393106802899 9651534050993089660204349)
            ·
              refine ⟨3619325269122408622576631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9651534050993089660204349 3619325269122408622576631)
              ·
                refine ⟨5428987903683612933864947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3619325269122408622576631 5428987903683612933864947)
                ·
                  refine ⟨8143481855525419400797421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5428987903683612933864947 8143481855525419400797421)
                  ·
                    refine ⟨3053805695822032275299033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8143481855525419400797421 3053805695822032275299033)
                    ·
                      refine ⟨2290354271866524206474275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3053805695822032275299033 2290354271866524206474275)
                      ·
                        rfl

theorem cell23_4460449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_4460449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460449 prefixEnd_4460449 := by exact prefixLift 4460449
  have htrace : WordTrace (prefixWord ++ tailWord_4460449) baseStart_4460449 baseEnd_4460449 := by
    simpa [prefixWord, tailWord_4460449, baseEnd_4460449] using wordTrace_append hprefix tailTrace_4460449
  have hstable : (prefixWord ++ tailWord_4460449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460449).length < 2 ^ (prefixWord ++ tailWord_4460449).sum := by decide
  have hdescent : baseEnd_4460449 < baseStart_4460449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460478 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3]
def baseStart_4460478 : Nat := 118140960795 + 4460478 * 2 ^ 59
def prefixEnd_4460478 : Nat := 4983230072969 + 3 ^ 40 * 4460478 * 2
def baseEnd_4460478 : Nat := 2290369162805504593011641

theorem tailTrace_4460478 : CollatzResearch.WordTrace tailWord_4460478 prefixEnd_4460478 2290369162805504593011641 := by
  unfold tailWord_4460478
  simp only [CollatzResearch.WordTrace]
  refine ⟨20335874741807183729798761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108457998622971646558926725 20335874741807183729798761)
  ·
    refine ⟨15251906056355387797349071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20335874741807183729798761 15251906056355387797349071)
    ·
      refine ⟨22877859084533081696023607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15251906056355387797349071 22877859084533081696023607)
      ·
        refine ⟨34316788626799622544035411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22877859084533081696023607 34316788626799622544035411)
        ·
          refine ⟨51475182940199433816053117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34316788626799622544035411 51475182940199433816053117)
          ·
            refine ⟨19303193602574787681019919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51475182940199433816053117 19303193602574787681019919)
            ·
              refine ⟨28954790403862181521529879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19303193602574787681019919 28954790403862181521529879)
              ·
                refine ⟨43432185605793272282294819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28954790403862181521529879 43432185605793272282294819)
                ·
                  refine ⟨65148278408689908423442229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43432185605793272282294819 65148278408689908423442229)
                  ·
                    refine ⟨6107651100814678914697709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65148278408689908423442229 6107651100814678914697709)
                    ·
                      refine ⟨2290369162805504593011641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6107651100814678914697709 2290369162805504593011641)
                      ·
                        rfl

theorem cell23_4460478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_4460478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460478 prefixEnd_4460478 := by exact prefixLift 4460478
  have htrace : WordTrace (prefixWord ++ tailWord_4460478) baseStart_4460478 baseEnd_4460478 := by
    simpa [prefixWord, tailWord_4460478, baseEnd_4460478] using wordTrace_append hprefix tailTrace_4460478
  have hstable : (prefixWord ++ tailWord_4460478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460478).length < 2 ^ (prefixWord ++ tailWord_4460478).sum := by decide
  have hdescent : baseEnd_4460478 < baseStart_4460478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460528 : List Nat := [2, 1, 1, 1, 3, 2, 3, 3, 3, 4]
def baseStart_4460528 : Nat := 118140960795 + 4460528 * 2 ^ 59
def prefixEnd_4460528 : Nat := 4983230072969 + 3 ^ 40 * 4460528 * 2
def baseEnd_4460528 : Nat := 763464945612743132462137

theorem tailTrace_4460528 : CollatzResearch.WordTrace tailWord_4460528 prefixEnd_4460528 763464945612743132462137 := by
  unfold tailWord_4460528
  simp only [CollatzResearch.WordTrace]
  refine ⟨81344410792138164188855119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108459214389517552251806825 81344410792138164188855119)
  ·
    refine ⟨122016616188207246283282679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81344410792138164188855119 122016616188207246283282679)
    ·
      refine ⟨183024924282310869424924019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122016616188207246283282679 183024924282310869424924019)
      ·
        refine ⟨274537386423466304137386029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183024924282310869424924019 274537386423466304137386029)
        ·
          refine ⟨102951519908799864051519761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274537386423466304137386029 102951519908799864051519761)
          ·
            refine ⟨77213639931599898038639821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102951519908799864051519761 77213639931599898038639821)
            ·
              refine ⟨28955114974349961764489933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77213639931599898038639821 28955114974349961764489933)
              ·
                refine ⟨10858168115381235661683725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28955114974349961764489933 10858168115381235661683725)
                ·
                  refine ⟨4071813043267963373131397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10858168115381235661683725 4071813043267963373131397)
                  ·
                    refine ⟨763464945612743132462137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4071813043267963373131397 763464945612743132462137)
                    ·
                      rfl

theorem cell23_4460528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 3, 4].length) (baseStart_4460528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460528 prefixEnd_4460528 := by exact prefixLift 4460528
  have htrace : WordTrace (prefixWord ++ tailWord_4460528) baseStart_4460528 baseEnd_4460528 := by
    simpa [prefixWord, tailWord_4460528, baseEnd_4460528] using wordTrace_append hprefix tailTrace_4460528
  have hstable : (prefixWord ++ tailWord_4460528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460528).length < 2 ^ (prefixWord ++ tailWord_4460528).sum := by decide
  have hdescent : baseEnd_4460528 < baseStart_4460528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460622 : List Nat := [4, 1, 1, 1, 1, 5, 3, 1, 1, 5]
def baseStart_4460622 : Nat := 118140960795 + 4460622 * 2 ^ 59
def prefixEnd_4460622 : Nat := 4983230072969 + 3 ^ 40 * 4460622 * 2
def baseEnd_4460622 : Nat := 763481034673250676536993

theorem tailTrace_4460622 : CollatzResearch.WordTrace tailWord_4460622 prefixEnd_4460622 763481034673250676536993 := by
  unfold tailWord_4460622
  simp only [CollatzResearch.WordTrace]
  refine ⟨20336531255741972803954015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108461500030623854954421413 20336531255741972803954015)
  ·
    refine ⟨30504796883612959205931023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20336531255741972803954015 30504796883612959205931023)
    ·
      refine ⟨45757195325419438808896535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30504796883612959205931023 45757195325419438808896535)
      ·
        refine ⟨68635792988129158213344803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45757195325419438808896535 68635792988129158213344803)
        ·
          refine ⟨102953689482193737320017205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68635792988129158213344803 102953689482193737320017205)
          ·
            refine ⟨9651908388955662873751613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102953689482193737320017205 9651908388955662873751613)
            ·
              refine ⟨3619465645858373577656855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9651908388955662873751613 3619465645858373577656855)
              ·
                refine ⟨5429198468787560366485283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3619465645858373577656855 5429198468787560366485283)
                ·
                  refine ⟨8143797703181340549727925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5429198468787560366485283 8143797703181340549727925)
                  ·
                    refine ⟨763481034673250676536993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8143797703181340549727925 763481034673250676536993)
                    ·
                      rfl

theorem cell23_4460622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_4460622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460622 prefixEnd_4460622 := by exact prefixLift 4460622
  have htrace : WordTrace (prefixWord ++ tailWord_4460622) baseStart_4460622 baseEnd_4460622 := by
    simpa [prefixWord, tailWord_4460622, baseEnd_4460622] using wordTrace_append hprefix tailTrace_4460622
  have hstable : (prefixWord ++ tailWord_4460622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460622).length < 2 ^ (prefixWord ++ tailWord_4460622).sum := by decide
  have hdescent : baseEnd_4460622 < baseStart_4460622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460636 : List Nat := [2, 2, 4, 1, 1, 2, 4, 2, 1, 1, 3]
def baseStart_4460636 : Nat := 118140960795 + 4460636 * 2 ^ 59
def prefixEnd_4460636 : Nat := 4983230072969 + 3 ^ 40 * 4460636 * 2
def baseEnd_4460636 : Nat := 2290450292748914974835915

theorem tailTrace_4460636 : CollatzResearch.WordTrace tailWord_4460636 prefixEnd_4460636 2290450292748914974835915 := by
  unfold tailWord_4460636
  simp only [CollatzResearch.WordTrace]
  refine ⟨81346380333942531411320881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108461840445256708548427841 81346380333942531411320881)
  ·
    refine ⟨61009785250456898558490661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81346380333942531411320881 61009785250456898558490661)
    ·
      refine ⟨11439334734460668479716999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61009785250456898558490661 11439334734460668479716999)
      ·
        refine ⟨17159002101691002719575499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11439334734460668479716999 17159002101691002719575499)
        ·
          refine ⟨25738503152536504079363249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17159002101691002719575499 25738503152536504079363249)
          ·
            refine ⟨19303877364402378059522437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25738503152536504079363249 19303877364402378059522437)
            ·
              refine ⟨3619477005825445886160457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19303877364402378059522437 3619477005825445886160457)
              ·
                refine ⟨2714607754369084414620343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3619477005825445886160457 2714607754369084414620343)
                ·
                  refine ⟨4071911631553626621930515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2714607754369084414620343 4071911631553626621930515)
                  ·
                    refine ⟨6107867447330439932895773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4071911631553626621930515 6107867447330439932895773)
                    ·
                      refine ⟨2290450292748914974835915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6107867447330439932895773 2290450292748914974835915)
                      ·
                        rfl

theorem cell23_4460636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_4460636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460636 prefixEnd_4460636 := by exact prefixLift 4460636
  have htrace : WordTrace (prefixWord ++ tailWord_4460636) baseStart_4460636 baseEnd_4460636 := by
    simpa [prefixWord, tailWord_4460636, baseEnd_4460636] using wordTrace_append hprefix tailTrace_4460636
  have hstable : (prefixWord ++ tailWord_4460636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460636).length < 2 ^ (prefixWord ++ tailWord_4460636).sum := by decide
  have hdescent : baseEnd_4460636 < baseStart_4460636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460645 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 3, 2, 3]
def baseStart_4460645 : Nat := 118140960795 + 4460645 * 2 ^ 59
def prefixEnd_4460645 : Nat := 4983230072969 + 3 ^ 40 * 4460645 * 2
def baseEnd_4460645 : Nat := 2290454914074805439623373

theorem tailTrace_4460645 : CollatzResearch.WordTrace tailWord_4460645 prefixEnd_4460645 2290454914074805439623373 := by
  unfold tailWord_4460645
  simp only [CollatzResearch.WordTrace]
  refine ⟨162693088924852457359719389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108462059283234971573146259 162693088924852457359719389)
  ·
    refine ⟨61009908346819671509894771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162693088924852457359719389 61009908346819671509894771)
    ·
      refine ⟨91514862520229507264842157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61009908346819671509894771 91514862520229507264842157)
      ·
        refine ⟨34318073445086065224315809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91514862520229507264842157 34318073445086065224315809)
        ·
          refine ⟨25738555083814548918236857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34318073445086065224315809 25738555083814548918236857)
          ·
            refine ⟨19303916312860911688677643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25738555083814548918236857 19303916312860911688677643)
            ·
              refine ⟨28955874469291367533016465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19303916312860911688677643 28955874469291367533016465)
              ·
                refine ⟨21716905851968525649762349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28955874469291367533016465 21716905851968525649762349)
                ·
                  refine ⟨8143839694488197118660881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21716905851968525649762349 8143839694488197118660881)
                  ·
                    refine ⟨6107879770866147838995661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8143839694488197118660881 6107879770866147838995661)
                    ·
                      refine ⟨2290454914074805439623373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6107879770866147838995661 2290454914074805439623373)
                      ·
                        rfl

theorem cell23_4460645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_4460645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460645 prefixEnd_4460645 := by exact prefixLift 4460645
  have htrace : WordTrace (prefixWord ++ tailWord_4460645) baseStart_4460645 baseEnd_4460645 := by
    simpa [prefixWord, tailWord_4460645, baseEnd_4460645] using wordTrace_append hprefix tailTrace_4460645
  have hstable : (prefixWord ++ tailWord_4460645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460645).length < 2 ^ (prefixWord ++ tailWord_4460645).sum := by decide
  have hdescent : baseEnd_4460645 < baseStart_4460645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460655 : List Nat := [1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 4]
def baseStart_4460655 : Nat := 118140960795 + 4460655 * 2 ^ 59
def prefixEnd_4460655 : Nat := 4983230072969 + 3 ^ 40 * 4460655 * 2
def baseEnd_4460655 : Nat := 2290460048881350400498327

theorem tailTrace_4460655 : CollatzResearch.WordTrace tailWord_4460655 prefixEnd_4460655 2290460048881350400498327 := by
  unfold tailWord_4460655
  simp only [CollatzResearch.WordTrace]
  refine ⟨162693453654816229067583419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108462302436544152711722279 162693453654816229067583419)
  ·
    refine ⟨244040180482224343601375129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162693453654816229067583419 244040180482224343601375129)
    ·
      refine ⟨183030135361668257701031347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244040180482224343601375129 183030135361668257701031347)
      ·
        refine ⟨274545203042502386551547021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183030135361668257701031347 274545203042502386551547021)
        ·
          refine ⟨102954451140938394956830133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274545203042502386551547021 102954451140938394956830133)
          ·
            refine ⟨9651979794462974527202825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102954451140938394956830133 9651979794462974527202825)
            ·
              refine ⟨7238984845847230895402119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9651979794462974527202825 7238984845847230895402119)
              ·
                refine ⟨10858477268770846343103179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7238984845847230895402119 10858477268770846343103179)
                ·
                  refine ⟨16287715903156269514654769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10858477268770846343103179 16287715903156269514654769)
                  ·
                    refine ⟨12215786927367202135991077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16287715903156269514654769 12215786927367202135991077)
                    ·
                      refine ⟨2290460048881350400498327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12215786927367202135991077 2290460048881350400498327)
                      ·
                        rfl

theorem cell23_4460655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 4].length) (baseStart_4460655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460655 prefixEnd_4460655 := by exact prefixLift 4460655
  have htrace : WordTrace (prefixWord ++ tailWord_4460655) baseStart_4460655 baseEnd_4460655 := by
    simpa [prefixWord, tailWord_4460655, baseEnd_4460655] using wordTrace_append hprefix tailTrace_4460655
  have hstable : (prefixWord ++ tailWord_4460655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460655).length < 2 ^ (prefixWord ++ tailWord_4460655).sum := by decide
  have hdescent : baseEnd_4460655 < baseStart_4460655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460662 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3]
def baseStart_4460662 : Nat := 118140960795 + 4460662 * 2 ^ 59
def prefixEnd_4460662 : Nat := 4983230072969 + 3 ^ 40 * 4460662 * 2
def baseEnd_4460662 : Nat := 2290463643245931873110795

theorem tailTrace_4460662 : CollatzResearch.WordTrace tailWord_4460662 prefixEnd_4460662 2290463643245931873110795 := by
  unfold tailWord_4460662
  simp only [CollatzResearch.WordTrace]
  refine ⟨10168356810361929328943015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108462472643860579508725493 10168356810361929328943015)
  ·
    refine ⟨15252535215542893993414523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10168356810361929328943015 15252535215542893993414523)
    ·
      refine ⟨22878802823314340990121785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15252535215542893993414523 22878802823314340990121785)
      ·
        refine ⟨17159102117485755742591339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22878802823314340990121785 17159102117485755742591339)
        ·
          refine ⟨25738653176228633613887009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17159102117485755742591339 25738653176228633613887009)
          ·
            refine ⟨19303989882171475210415257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25738653176228633613887009 19303989882171475210415257)
            ·
              refine ⟨14477992411628606407811443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19303989882171475210415257 14477992411628606407811443)
              ·
                refine ⟨21716988617442909611717165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14477992411628606407811443 21716988617442909611717165)
                ·
                  refine ⟨8143870731541091104393937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21716988617442909611717165 8143870731541091104393937)
                  ·
                    refine ⟨6107903048655818328295453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8143870731541091104393937 6107903048655818328295453)
                    ·
                      refine ⟨2290463643245931873110795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6107903048655818328295453 2290463643245931873110795)
                      ·
                        rfl

theorem cell23_4460662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_4460662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460662 prefixEnd_4460662 := by exact prefixLift 4460662
  have htrace : WordTrace (prefixWord ++ tailWord_4460662) baseStart_4460662 baseEnd_4460662 := by
    simpa [prefixWord, tailWord_4460662, baseEnd_4460662] using wordTrace_append hprefix tailTrace_4460662
  have hstable : (prefixWord ++ tailWord_4460662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460662).length < 2 ^ (prefixWord ++ tailWord_4460662).sum := by decide
  have hdescent : baseEnd_4460662 < baseStart_4460662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460665 : List Nat := [1, 2, 1, 3, 4, 2, 3, 7]
def baseStart_4460665 : Nat := 118140960795 + 4460665 * 2 ^ 59
def prefixEnd_4460665 : Nat := 4983230072969 + 3 ^ 40 * 4460665 * 2
def baseEnd_4460665 : Nat := 84832043840292420791603

theorem tailTrace_4460665 : CollatzResearch.WordTrace tailWord_4460665 prefixEnd_4460665 84832043840292420791603 := by
  unfold tailWord_4460665
  simp only [CollatzResearch.WordTrace]
  refine ⟨162693818384780000775447449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108462545589853333850298299 162693818384780000775447449)
  ·
    refine ⟨122020363788585000581585587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162693818384780000775447449 122020363788585000581585587)
    ·
      refine ⟨183030545682877500872378381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122020363788585000581585587 183030545682877500872378381)
      ·
        refine ⟨68636454631079062827141893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183030545682877500872378381 68636454631079062827141893)
        ·
          refine ⟨12869335243327324280089105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68636454631079062827141893 12869335243327324280089105)
          ·
            refine ⟨9652001432495493210066829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12869335243327324280089105 9652001432495493210066829)
            ·
              refine ⟨3619500537185809953775061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9652001432495493210066829 3619500537185809953775061)
              ·
                refine ⟨84832043840292420791603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3619500537185809953775061 84832043840292420791603)
                ·
                  rfl

theorem cell23_4460665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 7].length) (baseStart_4460665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460665 prefixEnd_4460665 := by exact prefixLift 4460665
  have htrace : WordTrace (prefixWord ++ tailWord_4460665) baseStart_4460665 baseEnd_4460665 := by
    simpa [prefixWord, tailWord_4460665, baseEnd_4460665] using wordTrace_append hprefix tailTrace_4460665
  have hstable : (prefixWord ++ tailWord_4460665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460665).length < 2 ^ (prefixWord ++ tailWord_4460665).sum := by decide
  have hdescent : baseEnd_4460665 < baseStart_4460665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460675 : List Nat := [1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 3]
def baseStart_4460675 : Nat := 118140960795 + 4460675 * 2 ^ 59
def prefixEnd_4460675 : Nat := 4983230072969 + 3 ^ 40 * 4460675 * 2
def baseEnd_4460675 : Nat := 2290470318494440322248235

theorem tailTrace_4460675 : CollatzResearch.WordTrace tailWord_4460675 prefixEnd_4460675 2290470318494440322248235 := by
  unfold tailWord_4460675
  simp only [CollatzResearch.WordTrace]
  refine ⟨162694183114743772483311479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108462788743162514988874319 162694183114743772483311479)
  ·
    refine ⟨244041274672115658724967219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162694183114743772483311479 244041274672115658724967219)
    ·
      refine ⟨366061912008173488087450829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244041274672115658724967219 366061912008173488087450829)
      ·
        refine ⟨137273217003065058032794061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 366061912008173488087450829 137273217003065058032794061)
        ·
          refine ⟨51477456376149396762297773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137273217003065058032794061 51477456376149396762297773)
          ·
            refine ⟨19304046141056023785861665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51477456376149396762297773 19304046141056023785861665)
            ·
              refine ⟨14478034605792017839396249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19304046141056023785861665 14478034605792017839396249)
              ·
                refine ⟨10858525954344013379547187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14478034605792017839396249 10858525954344013379547187)
                ·
                  refine ⟨16287788931516020069320781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10858525954344013379547187 16287788931516020069320781)
                  ·
                    refine ⟨6107920849318507525995293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16287788931516020069320781 6107920849318507525995293)
                    ·
                      refine ⟨2290470318494440322248235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6107920849318507525995293 2290470318494440322248235)
                      ·
                        rfl

theorem cell23_4460675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 3].length) (baseStart_4460675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460675 prefixEnd_4460675 := by exact prefixLift 4460675
  have htrace : WordTrace (prefixWord ++ tailWord_4460675) baseStart_4460675 baseEnd_4460675 := by
    simpa [prefixWord, tailWord_4460675, baseEnd_4460675] using wordTrace_append hprefix tailTrace_4460675
  have hstable : (prefixWord ++ tailWord_4460675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460675).length < 2 ^ (prefixWord ++ tailWord_4460675).sum := by decide
  have hdescent : baseEnd_4460675 < baseStart_4460675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460676 : List Nat := [2, 3, 2, 1, 2, 1, 4, 3, 1, 2, 2]
def baseStart_4460676 : Nat := 118140960795 + 4460676 * 2 ^ 59
def prefixEnd_4460676 : Nat := 4983230072969 + 3 ^ 40 * 4460676 * 2
def baseEnd_4460676 : Nat := 2290470831975094818335731

theorem tailTrace_4460676 : CollatzResearch.WordTrace tailWord_4460676 prefixEnd_4460676 2290470831975094818335731 := by
  unfold tailWord_4460676
  simp only [CollatzResearch.WordTrace]
  refine ⟨81347109793870074827048941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108462813058493433102731921 81347109793870074827048941)
  ·
    refine ⟨30505166172701278060143353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81347109793870074827048941 30505166172701278060143353)
    ·
      refine ⟨22878874629525958545107515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30505166172701278060143353 22878874629525958545107515)
      ·
        refine ⟨34318311944288937817661273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22878874629525958545107515 34318311944288937817661273)
        ·
          refine ⟨25738733958216703363245955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34318311944288937817661273 25738733958216703363245955)
          ·
            refine ⟨38608100937325055044868933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25738733958216703363245955 38608100937325055044868933)
            ·
              refine ⟨7239018925748447820912925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38608100937325055044868933 7239018925748447820912925)
              ·
                refine ⟨2714632097155667932842347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7239018925748447820912925 2714632097155667932842347)
                ·
                  refine ⟨4071948145733501899263521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2714632097155667932842347 4071948145733501899263521)
                  ·
                    refine ⟨3053961109300126424447641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4071948145733501899263521 3053961109300126424447641)
                    ·
                      refine ⟨2290470831975094818335731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3053961109300126424447641 2290470831975094818335731)
                      ·
                        rfl

theorem cell23_4460676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_4460676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460676 prefixEnd_4460676 := by exact prefixLift 4460676
  have htrace : WordTrace (prefixWord ++ tailWord_4460676) baseStart_4460676 baseEnd_4460676 := by
    simpa [prefixWord, tailWord_4460676, baseEnd_4460676] using wordTrace_append hprefix tailTrace_4460676
  have hstable : (prefixWord ++ tailWord_4460676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460676).length < 2 ^ (prefixWord ++ tailWord_4460676).sum := by decide
  have hdescent : baseEnd_4460676 < baseStart_4460676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460686 : List Nat := [4, 1, 1, 3, 4, 1, 1, 2, 2, 4]
def baseStart_4460686 : Nat := 118140960795 + 4460686 * 2 ^ 59
def prefixEnd_4460686 : Nat := 4983230072969 + 3 ^ 40 * 4460686 * 2
def baseEnd_4460686 : Nat := 763491988927213259736895

theorem tailTrace_4460686 : CollatzResearch.WordTrace tailWord_4460686 prefixEnd_4460686 763491988927213259736895 := by
  unfold tailWord_4460686
  simp only [CollatzResearch.WordTrace]
  refine ⟨20336823039712990170245239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108463056211802614241307941 20336823039712990170245239)
  ·
    refine ⟨30505234559569485255367859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20336823039712990170245239 30505234559569485255367859)
    ·
      refine ⟨45757851839354227883051789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30505234559569485255367859 45757851839354227883051789)
      ·
        refine ⟨17159194439757835456144421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45757851839354227883051789 17159194439757835456144421)
        ·
          refine ⟨3217348957454594148027079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17159194439757835456144421 3217348957454594148027079)
          ·
            refine ⟨4826023436181891222040619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3217348957454594148027079 4826023436181891222040619)
            ·
              refine ⟨7239035154272836833060929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4826023436181891222040619 7239035154272836833060929)
              ·
                refine ⟨5429276365704627624795697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7239035154272836833060929 5429276365704627624795697)
                ·
                  refine ⟨4071957274278470718596773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5429276365704627624795697 4071957274278470718596773)
                  ·
                    refine ⟨763491988927213259736895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4071957274278470718596773 763491988927213259736895)
                    ·
                      rfl

theorem cell23_4460686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_4460686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460686 prefixEnd_4460686 := by exact prefixLift 4460686
  have htrace : WordTrace (prefixWord ++ tailWord_4460686) baseStart_4460686 baseEnd_4460686 := by
    simpa [prefixWord, tailWord_4460686, baseEnd_4460686] using wordTrace_append hprefix tailTrace_4460686
  have hstable : (prefixWord ++ tailWord_4460686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460686).length < 2 ^ (prefixWord ++ tailWord_4460686).sum := by decide
  have hdescent : baseEnd_4460686 < baseStart_4460686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460709 : List Nat := [1, 3, 1, 2, 1, 3, 5, 1, 2, 1, 3]
def baseStart_4460709 : Nat := 118140960795 + 4460709 * 2 ^ 59
def prefixEnd_4460709 : Nat := 4983230072969 + 3 ^ 40 * 4460709 * 2
def baseEnd_4460709 : Nat := 2290487776836693189223079

theorem tailTrace_4460709 : CollatzResearch.WordTrace tailWord_4460709 prefixEnd_4460709 2290487776836693189223079 := by
  unfold tailWord_4460709
  simp only [CollatzResearch.WordTrace]
  refine ⟨162695423196620596290049181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108463615464413730860032787 162695423196620596290049181)
  ·
    refine ⟨61010783698732723608768443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162695423196620596290049181 61010783698732723608768443)
    ·
      refine ⟨91516175548099085413152665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61010783698732723608768443 91516175548099085413152665)
      ·
        refine ⟨68637131661074314059864499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91516175548099085413152665 68637131661074314059864499)
        ·
          refine ⟨102955697491611471089796749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68637131661074314059864499 102955697491611471089796749)
          ·
            refine ⟨38608386559354301658673781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102955697491611471089796749 38608386559354301658673781)
            ·
              refine ⟨3619536239939465780500667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38608386559354301658673781 3619536239939465780500667)
              ·
                refine ⟨5429304359909198670751001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3619536239939465780500667 5429304359909198670751001)
                ·
                  refine ⟨4071978269931899003063251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5429304359909198670751001 4071978269931899003063251)
                  ·
                    refine ⟨6107967404897848504594877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4071978269931899003063251 6107967404897848504594877)
                    ·
                      refine ⟨2290487776836693189223079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6107967404897848504594877 2290487776836693189223079)
                      ·
                        rfl

theorem cell23_4460709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_4460709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460709 prefixEnd_4460709 := by exact prefixLift 4460709
  have htrace : WordTrace (prefixWord ++ tailWord_4460709) baseStart_4460709 baseEnd_4460709 := by
    simpa [prefixWord, tailWord_4460709, baseEnd_4460709] using wordTrace_append hprefix tailTrace_4460709
  have hstable : (prefixWord ++ tailWord_4460709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460709).length < 2 ^ (prefixWord ++ tailWord_4460709).sum := by decide
  have hdescent : baseEnd_4460709 < baseStart_4460709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460785 : List Nat := [1, 2, 2, 2, 2, 1, 3, 3, 2, 5]
def baseStart_4460785 : Nat := 118140960795 + 4460785 * 2 ^ 59
def prefixEnd_4460785 : Nat := 4983230072969 + 3 ^ 40 * 4460785 * 2
def baseEnd_4460785 : Nat := 763508933788811630624243

theorem tailTrace_4460785 : CollatzResearch.WordTrace tailWord_4460785 prefixEnd_4460785 763508933788811630624243 := by
  unfold tailWord_4460785
  simp only [CollatzResearch.WordTrace]
  refine ⟨162698195144345261269815809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108465463429563507513210539 162698195144345261269815809)
  ·
    refine ⟨122023646358258945952361857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162698195144345261269815809 122023646358258945952361857)
    ·
      refine ⟨91517734768694209464271393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122023646358258945952361857 91517734768694209464271393)
      ·
        refine ⟨68638301076520657098203545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91517734768694209464271393 68638301076520657098203545)
        ·
          refine ⟨51478725807390492823652659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68638301076520657098203545 51478725807390492823652659)
          ·
            refine ⟨77218088711085739235478989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51478725807390492823652659 77218088711085739235478989)
            ·
              refine ⟨28956783266657152213304621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77218088711085739235478989 28956783266657152213304621)
              ·
                refine ⟨10858793724996432079989233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28956783266657152213304621 10858793724996432079989233)
                ·
                  refine ⟨8144095293747324059991925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10858793724996432079989233 8144095293747324059991925)
                  ·
                    refine ⟨763508933788811630624243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8144095293747324059991925 763508933788811630624243)
                    ·
                      rfl

theorem cell23_4460785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_4460785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460785 prefixEnd_4460785 := by exact prefixLift 4460785
  have htrace : WordTrace (prefixWord ++ tailWord_4460785) baseStart_4460785 baseEnd_4460785 := by
    simpa [prefixWord, tailWord_4460785, baseEnd_4460785] using wordTrace_append hprefix tailTrace_4460785
  have hstable : (prefixWord ++ tailWord_4460785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460785).length < 2 ^ (prefixWord ++ tailWord_4460785).sum := by decide
  have hdescent : baseEnd_4460785 < baseStart_4460785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460805 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 4, 1, 4]
def baseStart_4460805 : Nat := 118140960795 + 4460805 * 2 ^ 59
def prefixEnd_4460805 : Nat := 4983230072969 + 3 ^ 40 * 4460805 * 2
def baseEnd_4460805 : Nat := 2290537070979524813622637

theorem tailTrace_4460805 : CollatzResearch.WordTrace tailWord_4460805 prefixEnd_4460805 2290537070979524813622637 := by
  unfold tailWord_4460805
  simp only [CollatzResearch.WordTrace]
  refine ⟨162698924604272804685543869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108465949736181869790362579 162698924604272804685543869)
  ·
    refine ⟨61012096726602301757078951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162698924604272804685543869 61012096726602301757078951)
    ·
      refine ⟨91518145089903452635618427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61012096726602301757078951 91518145089903452635618427)
      ·
        refine ⟨137277217634855178953427641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91518145089903452635618427 137277217634855178953427641)
        ·
          refine ⟨102957913226141384215070731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137277217634855178953427641 102957913226141384215070731)
          ·
            refine ⟨154436869839212076322606097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102957913226141384215070731 154436869839212076322606097)
            ·
              refine ⟨115827652379409057241954573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154436869839212076322606097 115827652379409057241954573)
              ·
                refine ⟨43435369642278396465732965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115827652379409057241954573 43435369642278396465732965)
                ·
                  refine ⟨8144131807927199337324931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43435369642278396465732965 8144131807927199337324931)
                  ·
                    refine ⟨12216197711890799005987397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8144131807927199337324931 12216197711890799005987397)
                    ·
                      refine ⟨2290537070979524813622637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12216197711890799005987397 2290537070979524813622637)
                      ·
                        rfl

theorem cell23_4460805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_4460805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460805 prefixEnd_4460805 := by exact prefixLift 4460805
  have htrace : WordTrace (prefixWord ++ tailWord_4460805) baseStart_4460805 baseEnd_4460805 := by
    simpa [prefixWord, tailWord_4460805, baseEnd_4460805] using wordTrace_append hprefix tailTrace_4460805
  have hstable : (prefixWord ++ tailWord_4460805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460805).length < 2 ^ (prefixWord ++ tailWord_4460805).sum := by decide
  have hdescent : baseEnd_4460805 < baseStart_4460805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460815 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 7, 4]
def baseStart_4460815 : Nat := 118140960795 + 4460815 * 2 ^ 59
def prefixEnd_4460815 : Nat := 4983230072969 + 3 ^ 40 * 4460815 * 2
def baseEnd_4460815 : Nat := 763514068595356591499197

theorem tailTrace_4460815 : CollatzResearch.WordTrace tailWord_4460815 prefixEnd_4460815 763514068595356591499197 := by
  unfold tailWord_4460815
  simp only [CollatzResearch.WordTrace]
  refine ⟨162699289334236576393407899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108466192889491050928938599 162699289334236576393407899)
  ·
    refine ⟨244048934001354864590111849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162699289334236576393407899 244048934001354864590111849)
    ·
      refine ⟨183036700501016148442583887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244048934001354864590111849 183036700501016148442583887)
      ·
        refine ⟨274555050751524222663875831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183036700501016148442583887 274555050751524222663875831)
        ·
          refine ⟨411832576127286333995813747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274555050751524222663875831 411832576127286333995813747)
          ·
            refine ⟨617748864190929500993720621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 411832576127286333995813747 617748864190929500993720621)
            ·
              refine ⟨231655824071598562872645233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 617748864190929500993720621 231655824071598562872645233)
              ·
                refine ⟨173741868053698922154483925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231655824071598562872645233 173741868053698922154483925)
                ·
                  refine ⟨4072075032508568487995717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 173741868053698922154483925 4072075032508568487995717)
                  ·
                    refine ⟨763514068595356591499197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4072075032508568487995717 763514068595356591499197)
                    ·
                      rfl

theorem cell23_4460815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 4].length) (baseStart_4460815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460815 prefixEnd_4460815 := by exact prefixLift 4460815
  have htrace : WordTrace (prefixWord ++ tailWord_4460815) baseStart_4460815 baseEnd_4460815 := by
    simpa [prefixWord, tailWord_4460815, baseEnd_4460815] using wordTrace_append hprefix tailTrace_4460815
  have hstable : (prefixWord ++ tailWord_4460815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460815).length < 2 ^ (prefixWord ++ tailWord_4460815).sum := by decide
  have hdescent : baseEnd_4460815 < baseStart_4460815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460832 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 5, 4]
def baseStart_4460832 : Nat := 118140960795 + 4460832 * 2 ^ 59
def prefixEnd_4460832 : Nat := 4983230072969 + 3 ^ 40 * 4460832 * 2
def baseEnd_4460832 : Nat := 763516978319065402661671

theorem tailTrace_4460832 : CollatzResearch.WordTrace tailWord_4460832 prefixEnd_4460832 763516978319065402661671 := by
  unfold tailWord_4460832
  simp only [CollatzResearch.WordTrace]
  refine ⟨81349954687587494148388375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108466606250116658864517833 81349954687587494148388375)
  ·
    refine ⟨122024932031381241222582563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81349954687587494148388375 122024932031381241222582563)
    ·
      refine ⟨183037398047071861833873845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122024932031381241222582563 183037398047071861833873845)
      ·
        refine ⟨17159756066912987046925673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 183037398047071861833873845 17159756066912987046925673)
        ·
          refine ⟨12869817050184740285194255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17159756066912987046925673 12869817050184740285194255)
          ·
            refine ⟨19304725575277110427791383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12869817050184740285194255 19304725575277110427791383)
            ·
              refine ⟨28957088362915665641687075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19304725575277110427791383 28957088362915665641687075)
              ·
                refine ⟨43435632544373498462530613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28957088362915665641687075 43435632544373498462530613)
                ·
                  refine ⟨4072090551035015480862245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43435632544373498462530613 4072090551035015480862245)
                  ·
                    refine ⟨763516978319065402661671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4072090551035015480862245 763516978319065402661671)
                    ·
                      rfl

theorem cell23_4460832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 5, 4].length) (baseStart_4460832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460832 prefixEnd_4460832 := by exact prefixLift 4460832
  have htrace : WordTrace (prefixWord ++ tailWord_4460832) baseStart_4460832 baseEnd_4460832 := by
    simpa [prefixWord, tailWord_4460832, baseEnd_4460832] using wordTrace_append hprefix tailTrace_4460832
  have hstable : (prefixWord ++ tailWord_4460832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460832).length < 2 ^ (prefixWord ++ tailWord_4460832).sum := by decide
  have hdescent : baseEnd_4460832 < baseStart_4460832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460852 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_4460852 : Nat := 118140960795 + 4460852 * 2 ^ 59
def prefixEnd_4460852 : Nat := 4983230072969 + 3 ^ 40 * 4460852 * 2
def baseEnd_4460852 : Nat := 2290561204570286129734921

theorem tailTrace_4460852 : CollatzResearch.WordTrace tailWord_4460852 prefixEnd_4460852 2290561204570286129734921 := by
  unfold tailWord_4460852
  simp only [CollatzResearch.WordTrace]
  refine ⟨81350319417551265856252405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108467092556735021141669873 81350319417551265856252405)
  ·
    refine ⟨7626592445395431174023663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81350319417551265856252405 7626592445395431174023663)
    ·
      refine ⟨11439888668093146761035495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7626592445395431174023663 11439888668093146761035495)
      ·
        refine ⟨17159833002139720141553243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11439888668093146761035495 17159833002139720141553243)
        ·
          refine ⟨25739749503209580212329865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17159833002139720141553243 25739749503209580212329865)
          ·
            refine ⟨19304812127407185159247399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25739749503209580212329865 19304812127407185159247399)
            ·
              refine ⟨28957218191110777738871099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19304812127407185159247399 28957218191110777738871099)
              ·
                refine ⟨43435827286666166608306649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28957218191110777738871099 43435827286666166608306649)
                ·
                  refine ⟨32576870464999624956229987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43435827286666166608306649 32576870464999624956229987)
                  ·
                    refine ⟨48865305697499437434344981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32576870464999624956229987 48865305697499437434344981)
                    ·
                      refine ⟨2290561204570286129734921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48865305697499437434344981 2290561204570286129734921)
                      ·
                        rfl

theorem cell23_4460852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_4460852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460852 prefixEnd_4460852 := by exact prefixLift 4460852
  have htrace : WordTrace (prefixWord ++ tailWord_4460852) baseStart_4460852 baseEnd_4460852 := by
    simpa [prefixWord, tailWord_4460852, baseEnd_4460852] using wordTrace_append hprefix tailTrace_4460852
  have hstable : (prefixWord ++ tailWord_4460852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460852).length < 2 ^ (prefixWord ++ tailWord_4460852).sum := by decide
  have hdescent : baseEnd_4460852 < baseStart_4460852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460855 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 3]
def baseStart_4460855 : Nat := 118140960795 + 4460855 * 2 ^ 59
def prefixEnd_4460855 : Nat := 4983230072969 + 3 ^ 40 * 4460855 * 2
def baseEnd_4460855 : Nat := 2290562745012249617997407

theorem tailTrace_4460855 : CollatzResearch.WordTrace tailWord_4460855 prefixEnd_4460855 2290562745012249617997407 := by
  unfold tailWord_4460855
  simp only [CollatzResearch.WordTrace]
  refine ⟨162700748254091663224864019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108467165502727775483242679 162700748254091663224864019)
  ·
    refine ⟨244051122381137494837296029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162700748254091663224864019 244051122381137494837296029)
    ·
      refine ⟨91519170892926560563986011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244051122381137494837296029 91519170892926560563986011)
      ·
        refine ⟨137278756339389840845979017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91519170892926560563986011 137278756339389840845979017)
        ·
          refine ⟨102959067254542380634484263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137278756339389840845979017 102959067254542380634484263)
          ·
            refine ⟨154438600881813570951726395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102959067254542380634484263 154438600881813570951726395)
            ·
              refine ⟨231657901322720356427589593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154438600881813570951726395 231657901322720356427589593)
              ·
                refine ⟨173743425992040267320692195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231657901322720356427589593 173743425992040267320692195)
                ·
                  refine ⟨260615138988060400981038293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173743425992040267320692195 260615138988060400981038293)
                  ·
                    refine ⟨6108167320032665647993085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 260615138988060400981038293 6108167320032665647993085)
                    ·
                      refine ⟨2290562745012249617997407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6108167320032665647993085 2290562745012249617997407)
                      ·
                        rfl

theorem cell23_4460855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_4460855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460855 prefixEnd_4460855 := by exact prefixLift 4460855
  have htrace : WordTrace (prefixWord ++ tailWord_4460855) baseStart_4460855 baseEnd_4460855 := by
    simpa [prefixWord, tailWord_4460855, baseEnd_4460855] using wordTrace_append hprefix tailTrace_4460855
  have hstable : (prefixWord ++ tailWord_4460855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460855).length < 2 ^ (prefixWord ++ tailWord_4460855).sum := by decide
  have hdescent : baseEnd_4460855 < baseStart_4460855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460862 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 8]
def baseStart_4460862 : Nat := 118140960795 + 4460862 * 2 ^ 59
def prefixEnd_4460862 : Nat := 4983230072969 + 3 ^ 40 * 4460862 * 2
def baseEnd_4460862 : Nat := 254507371041870121178875

theorem tailTrace_4460862 : CollatzResearch.WordTrace tailWord_4460862 prefixEnd_4460862 254507371041870121178875 := by
  unfold tailWord_4460862
  simp only [CollatzResearch.WordTrace]
  refine ⟨20337625445633287927546105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108467335710044202280245893 20337625445633287927546105)
  ·
    refine ⟨15253219084224965945659579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20337625445633287927546105 15253219084224965945659579)
    ·
      refine ⟨22879828626337448918489369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15253219084224965945659579 22879828626337448918489369)
      ·
        refine ⟨17159871469753086688867027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22879828626337448918489369 17159871469753086688867027)
        ·
          refine ⟨25739807204629630033300541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17159871469753086688867027 25739807204629630033300541)
          ·
            refine ⟨9652427701736111262487703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25739807204629630033300541 9652427701736111262487703)
            ·
              refine ⟨14478641552604166893731555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9652427701736111262487703 14478641552604166893731555)
              ·
                refine ⟨21717962328906250340597333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14478641552604166893731555 21717962328906250340597333)
                ·
                  refine ⟨254507371041870121178875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21717962328906250340597333 254507371041870121178875)
                  ·
                    rfl

theorem cell23_4460862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_4460862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460862 prefixEnd_4460862 := by exact prefixLift 4460862
  have htrace : WordTrace (prefixWord ++ tailWord_4460862) baseStart_4460862 baseEnd_4460862 := by
    simpa [prefixWord, tailWord_4460862, baseEnd_4460862] using wordTrace_append hprefix tailTrace_4460862
  have hstable : (prefixWord ++ tailWord_4460862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460862).length < 2 ^ (prefixWord ++ tailWord_4460862).sum := by decide
  have hdescent : baseEnd_4460862 < baseStart_4460862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460875 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 3, 5]
def baseStart_4460875 : Nat := 118140960795 + 4460875 * 2 ^ 59
def prefixEnd_4460875 : Nat := 4983230072969 + 3 ^ 40 * 4460875 * 2
def baseEnd_4460875 : Nat := 763524338208446513249105

theorem tailTrace_4460875 : CollatzResearch.WordTrace tailWord_4460875 prefixEnd_4460875 763524338208446513249105 := by
  unfold tailWord_4460875
  simp only [CollatzResearch.WordTrace]
  refine ⟨162701477714019206640592079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108467651809346137760394719 162701477714019206640592079)
  ·
    refine ⟨244052216571028809960888119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162701477714019206640592079 244052216571028809960888119)
    ·
      refine ⟨366078324856543214941332179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244052216571028809960888119 366078324856543214941332179)
      ·
        refine ⟨549117487284814822411998269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366078324856543214941332179 549117487284814822411998269)
        ·
          refine ⟨205919057731805558404499351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 549117487284814822411998269 205919057731805558404499351)
          ·
            refine ⟨308878586597708337606749027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205919057731805558404499351 308878586597708337606749027)
            ·
              refine ⟨463317879896562506410123541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308878586597708337606749027 463317879896562506410123541)
              ·
                refine ⟨21718025620151367487974541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 463317879896562506410123541 21718025620151367487974541)
                ·
                  refine ⟨8144259607556762807990453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21718025620151367487974541 8144259607556762807990453)
                  ·
                    refine ⟨763524338208446513249105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8144259607556762807990453 763524338208446513249105)
                    ·
                      rfl

theorem cell23_4460875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 5].length) (baseStart_4460875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460875 prefixEnd_4460875 := by exact prefixLift 4460875
  have htrace : WordTrace (prefixWord ++ tailWord_4460875) baseStart_4460875 baseEnd_4460875 := by
    simpa [prefixWord, tailWord_4460875, baseEnd_4460875] using wordTrace_append hprefix tailTrace_4460875
  have hstable : (prefixWord ++ tailWord_4460875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460875).length < 2 ^ (prefixWord ++ tailWord_4460875).sum := by decide
  have hdescent : baseEnd_4460875 < baseStart_4460875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460899 : List Nat := [1, 1, 1, 5, 2, 1, 2, 3, 2, 3, 2]
def baseStart_4460899 : Nat := 118140960795 + 4460899 * 2 ^ 59
def prefixEnd_4460899 : Nat := 4983230072969 + 3 ^ 40 * 4460899 * 2
def baseEnd_4460899 : Nat := 2290585338161047445847205

theorem tailTrace_4460899 : CollatzResearch.WordTrace tailWord_4460899 prefixEnd_4460899 2290585338161047445847205 := by
  unfold tailWord_4460899
  simp only [CollatzResearch.WordTrace]
  refine ⟨162702353065932258739465751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108468235377288172492977167 162702353065932258739465751)
  ·
    refine ⟨244053529598898388109198627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162702353065932258739465751 244053529598898388109198627)
    ·
      refine ⟨366080294398347582163797941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244053529598898388109198627 366080294398347582163797941)
      ·
        refine ⟨34320027599845085827856057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 366080294398347582163797941 34320027599845085827856057)
        ·
          refine ⟨25740020699883814370892043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34320027599845085827856057 25740020699883814370892043)
          ·
            refine ⟨38610031049825721556338065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25740020699883814370892043 38610031049825721556338065)
            ·
              refine ⟨28957523287369291167253549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38610031049825721556338065 28957523287369291167253549)
              ·
                refine ⟨10859071232763484187720081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28957523287369291167253549 10859071232763484187720081)
                ·
                  refine ⟨8144303424572613140790061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10859071232763484187720081 8144303424572613140790061)
                  ·
                    refine ⟨3054113784214729927796273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8144303424572613140790061 3054113784214729927796273)
                    ·
                      refine ⟨2290585338161047445847205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3054113784214729927796273 2290585338161047445847205)
                      ·
                        rfl

theorem cell23_4460899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_4460899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460899 prefixEnd_4460899 := by exact prefixLift 4460899
  have htrace : WordTrace (prefixWord ++ tailWord_4460899) baseStart_4460899 baseEnd_4460899 := by
    simpa [prefixWord, tailWord_4460899, baseEnd_4460899] using wordTrace_append hprefix tailTrace_4460899
  have hstable : (prefixWord ++ tailWord_4460899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460899).length < 2 ^ (prefixWord ++ tailWord_4460899).sum := by decide
  have hdescent : baseEnd_4460899 < baseStart_4460899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460905 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 3, 6]
def baseStart_4460905 : Nat := 118140960795 + 4460905 * 2 ^ 59
def prefixEnd_4460905 : Nat := 4983230072969 + 3 ^ 40 * 4460905 * 2
def baseEnd_4460905 : Nat := 763529473014991474124059

theorem tailTrace_4460905 : CollatzResearch.WordTrace tailWord_4460905 prefixEnd_4460905 763529473014991474124059 := by
  unfold tailWord_4460905
  simp only [CollatzResearch.WordTrace]
  refine ⟨162702571903910521764184169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108468381269273681176122779 162702571903910521764184169)
  ·
    refine ⟨122026928927932891323138127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162702571903910521764184169 122026928927932891323138127)
    ·
      refine ⟨183040393391899336984707191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122026928927932891323138127 183040393391899336984707191)
      ·
        refine ⟨274560590087849005477060787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183040393391899336984707191 274560590087849005477060787)
        ·
          refine ⟨411840885131773508215591181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274560590087849005477060787 411840885131773508215591181)
          ·
            refine ⟨154440331924415065580846693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 411840885131773508215591181 154440331924415065580846693)
            ·
              refine ⟨28957562235827824796408755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154440331924415065580846693 28957562235827824796408755)
              ·
                refine ⟨43436343353741737194613133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28957562235827824796408755 43436343353741737194613133)
                ·
                  refine ⟨16288628757653151447979925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43436343353741737194613133 16288628757653151447979925)
                  ·
                    refine ⟨763529473014991474124059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16288628757653151447979925 763529473014991474124059)
                    ·
                      rfl

theorem cell23_4460905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 6].length) (baseStart_4460905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460905 prefixEnd_4460905 := by exact prefixLift 4460905
  have htrace : WordTrace (prefixWord ++ tailWord_4460905) baseStart_4460905 baseEnd_4460905 := by
    simpa [prefixWord, tailWord_4460905, baseEnd_4460905] using wordTrace_append hprefix tailTrace_4460905
  have hstable : (prefixWord ++ tailWord_4460905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460905).length < 2 ^ (prefixWord ++ tailWord_4460905).sum := by decide
  have hdescent : baseEnd_4460905 < baseStart_4460905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460915 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 5]
def baseStart_4460915 : Nat := 118140960795 + 4460915 * 2 ^ 59
def prefixEnd_4460915 : Nat := 4983230072969 + 3 ^ 40 * 4460915 * 2
def baseEnd_4460915 : Nat := 2290593553851519383247131

theorem tailTrace_4460915 : CollatzResearch.WordTrace tailWord_4460915 prefixEnd_4460915 2290593553851519383247131 := by
  unfold tailWord_4460915
  simp only [CollatzResearch.WordTrace]
  refine ⟨162702936633874293472048199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108468624422582862314698799 162702936633874293472048199)
  ·
    refine ⟨244054404950811440208072299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162702936633874293472048199 244054404950811440208072299)
    ·
      refine ⟨366081607426217160312108449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244054404950811440208072299 366081607426217160312108449)
      ·
        refine ⟨274561205569662870234081337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 366081607426217160312108449 274561205569662870234081337)
        ·
          refine ⟨205920904177247152675561003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274561205569662870234081337 205920904177247152675561003)
          ·
            refine ⟨308881356265870729013341505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205920904177247152675561003 308881356265870729013341505)
            ·
              refine ⟨231661017199403046760006129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308881356265870729013341505 231661017199403046760006129)
              ·
                refine ⟨173745762899552285070004597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231661017199403046760006129 173745762899552285070004597)
                ·
                  refine ⟨16288665271833026725312931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 173745762899552285070004597 16288665271833026725312931)
                  ·
                    refine ⟨24432997907749540087969397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16288665271833026725312931 24432997907749540087969397)
                    ·
                      refine ⟨2290593553851519383247131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24432997907749540087969397 2290593553851519383247131)
                      ·
                        rfl

theorem cell23_4460915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 5].length) (baseStart_4460915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460915 prefixEnd_4460915 := by exact prefixLift 4460915
  have htrace : WordTrace (prefixWord ++ tailWord_4460915) baseStart_4460915 baseEnd_4460915 := by
    simpa [prefixWord, tailWord_4460915, baseEnd_4460915] using wordTrace_append hprefix tailTrace_4460915
  have hstable : (prefixWord ++ tailWord_4460915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460915).length < 2 ^ (prefixWord ++ tailWord_4460915).sum := by decide
  have hdescent : baseEnd_4460915 < baseStart_4460915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460923 : List Nat := [1, 1, 1, 1, 1, 8, 3, 2, 1, 1, 3]
def baseStart_4460923 : Nat := 118140960795 + 4460923 * 2 ^ 59
def prefixEnd_4460923 : Nat := 4983230072969 + 3 ^ 40 * 4460923 * 2
def baseEnd_4460923 : Nat := 2290597661696755351947095

theorem tailTrace_4460923 : CollatzResearch.WordTrace tailWord_4460923 prefixEnd_4460923 2290597661696755351947095 := by
  unfold tailWord_4460923
  simp only [CollatzResearch.WordTrace]
  refine ⟨162703228417845310838339423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108468818945230207225559615 162703228417845310838339423)
  ·
    refine ⟨244054842626767966257509135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162703228417845310838339423 244054842626767966257509135)
    ·
      refine ⟨366082263940151949386263703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244054842626767966257509135 366082263940151949386263703)
      ·
        refine ⟨549123395910227924079395555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366082263940151949386263703 549123395910227924079395555)
        ·
          refine ⟨823685093865341886119093333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549123395910227924079395555 823685093865341886119093333)
          ·
            refine ⟨9652559693734475227958125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 823685093865341886119093333 9652559693734475227958125)
            ·
              refine ⟨3619709885150428210484297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9652559693734475227958125 3619709885150428210484297)
              ·
                refine ⟨2714782413862821157863223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3619709885150428210484297 2714782413862821157863223)
                ·
                  refine ⟨4072173620794231736794835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2714782413862821157863223 4072173620794231736794835)
                  ·
                    refine ⟨6108260431191347605192253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4072173620794231736794835 6108260431191347605192253)
                    ·
                      refine ⟨2290597661696755351947095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6108260431191347605192253 2290597661696755351947095)
                      ·
                        rfl

theorem cell23_4460923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 1, 1, 3].length) (baseStart_4460923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460923 prefixEnd_4460923 := by exact prefixLift 4460923
  have htrace : WordTrace (prefixWord ++ tailWord_4460923) baseStart_4460923 baseEnd_4460923 := by
    simpa [prefixWord, tailWord_4460923, baseEnd_4460923] using wordTrace_append hprefix tailTrace_4460923
  have hstable : (prefixWord ++ tailWord_4460923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460923).length < 2 ^ (prefixWord ++ tailWord_4460923).sum := by decide
  have hdescent : baseEnd_4460923 < baseStart_4460923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460930 : List Nat := [3, 4, 2, 1, 3, 1, 2, 1, 6]
def baseStart_4460930 : Nat := 118140960795 + 4460930 * 2 ^ 59
def prefixEnd_4460930 : Nat := 4983230072969 + 3 ^ 40 * 4460930 * 2
def baseEnd_4460930 : Nat := 254511250673481869395507

theorem tailTrace_4460930 : CollatzResearch.WordTrace tailWord_4460930 prefixEnd_4460930 254511250673481869395507 := by
  unfold tailWord_4460930
  simp only [CollatzResearch.WordTrace]
  refine ⟨40675870932204987758461061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108468989152546634022562829 40675870932204987758461061)
  ·
    refine ⟨7626725799788435204711449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40675870932204987758461061 7626725799788435204711449)
    ·
      refine ⟨5720044349841326403533587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7626725799788435204711449 5720044349841326403533587)
      ·
        refine ⟨8580066524761989605300381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5720044349841326403533587 8580066524761989605300381)
        ·
          refine ⟨3217524946785746101987643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8580066524761989605300381 3217524946785746101987643)
          ·
            refine ⟨4826287420178619152981465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3217524946785746101987643 4826287420178619152981465)
            ·
              refine ⟨3619715565133964364736099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4826287420178619152981465 3619715565133964364736099)
              ·
                refine ⟨5429573347700946547104149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3619715565133964364736099 5429573347700946547104149)
                ·
                  refine ⟨254511250673481869395507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5429573347700946547104149 254511250673481869395507)
                  ·
                    rfl

theorem cell23_4460930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_4460930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460930 prefixEnd_4460930 := by exact prefixLift 4460930
  have htrace : WordTrace (prefixWord ++ tailWord_4460930) baseStart_4460930 baseEnd_4460930 := by
    simpa [prefixWord, tailWord_4460930, baseEnd_4460930] using wordTrace_append hprefix tailTrace_4460930
  have hstable : (prefixWord ++ tailWord_4460930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460930).length < 2 ^ (prefixWord ++ tailWord_4460930).sum := by decide
  have hdescent : baseEnd_4460930 < baseStart_4460930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460932 : List Nat := [2, 3, 2, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_4460932 : Nat := 118140960795 + 4460932 * 2 ^ 59
def prefixEnd_4460932 : Nat := 4983230072969 + 3 ^ 40 * 4460932 * 2
def baseEnd_4460932 : Nat := 2290602283022645816734553

theorem tailTrace_4460932 : CollatzResearch.WordTrace tailWord_4460932 prefixEnd_4460932 2290602283022645816734553 := by
  unfold tailWord_4460932
  simp only [CollatzResearch.WordTrace]
  refine ⟨81351778337406352687708525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108469037783208470250278033 81351778337406352687708525)
  ·
    refine ⟨30506916876527382257890697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81351778337406352687708525 30506916876527382257890697)
    ·
      refine ⟨22880187657395536693418023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30506916876527382257890697 22880187657395536693418023)
      ·
        refine ⟨34320281486093305040127035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22880187657395536693418023 34320281486093305040127035)
        ·
          refine ⟨51480422229139957560190553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34320281486093305040127035 51480422229139957560190553)
          ·
            refine ⟨38610316671854968170142915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51480422229139957560190553 38610316671854968170142915)
            ·
              refine ⟨57915475007782452255214373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38610316671854968170142915 57915475007782452255214373)
              ·
                refine ⟨10859151563959209797852695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57915475007782452255214373 10859151563959209797852695)
                ·
                  refine ⟨16288727345938814696779043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10859151563959209797852695 16288727345938814696779043)
                  ·
                    refine ⟨24433091018908222045168565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16288727345938814696779043 24433091018908222045168565)
                    ·
                      refine ⟨2290602283022645816734553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24433091018908222045168565 2290602283022645816734553)
                      ·
                        rfl

theorem cell23_4460932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_4460932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460932 prefixEnd_4460932 := by exact prefixLift 4460932
  have htrace : WordTrace (prefixWord ++ tailWord_4460932) baseStart_4460932 baseEnd_4460932 := by
    simpa [prefixWord, tailWord_4460932, baseEnd_4460932] using wordTrace_append hprefix tailTrace_4460932
  have hstable : (prefixWord ++ tailWord_4460932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460932).length < 2 ^ (prefixWord ++ tailWord_4460932).sum := by decide
  have hdescent : baseEnd_4460932 < baseStart_4460932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460939 : List Nat := [1, 1, 1, 1, 4, 5, 1, 3, 2, 4]
def baseStart_4460939 : Nat := 118140960795 + 4460939 * 2 ^ 59
def prefixEnd_4460939 : Nat := 4983230072969 + 3 ^ 40 * 4460939 * 2
def baseEnd_4460939 : Nat := 763535292462409096449007

theorem tailTrace_4460939 : CollatzResearch.WordTrace tailWord_4460939 prefixEnd_4460939 763535292462409096449007 := by
  unfold tailWord_4460939
  simp only [CollatzResearch.WordTrace]
  refine ⟨162703811985787345570921871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108469207990524897047281247 162703811985787345570921871)
  ·
    refine ⟨244055717978681018356382807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162703811985787345570921871 244055717978681018356382807)
    ·
      refine ⟨366083576968021527534574211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244055717978681018356382807 366083576968021527534574211)
      ·
        refine ⟨549125365452032291301861317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366083576968021527534574211 549125365452032291301861317)
        ·
          refine ⟨102961006022256054619098997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 549125365452032291301861317 102961006022256054619098997)
          ·
            refine ⟨9652594314586505120540531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102961006022256054619098997 9652594314586505120540531)
            ·
              refine ⟨14478891471879757680810797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9652594314586505120540531 14478891471879757680810797)
              ·
                refine ⟨5429584301954909130304049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14478891471879757680810797 5429584301954909130304049)
                ·
                  refine ⟨4072188226466181847728037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5429584301954909130304049 4072188226466181847728037)
                  ·
                    refine ⟨763535292462409096449007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4072188226466181847728037 763535292462409096449007)
                    ·
                      rfl

theorem cell23_4460939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 4].length) (baseStart_4460939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460939 prefixEnd_4460939 := by exact prefixLift 4460939
  have htrace : WordTrace (prefixWord ++ tailWord_4460939) baseStart_4460939 baseEnd_4460939 := by
    simpa [prefixWord, tailWord_4460939, baseEnd_4460939] using wordTrace_append hprefix tailTrace_4460939
  have hstable : (prefixWord ++ tailWord_4460939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460939).length < 2 ^ (prefixWord ++ tailWord_4460939).sum := by decide
  have hdescent : baseEnd_4460939 < baseStart_4460939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460952 : List Nat := [2, 1, 2, 5, 1, 1, 2, 9]
def baseStart_4460952 : Nat := 118140960795 + 4460952 * 2 ^ 59
def prefixEnd_4460952 : Nat := 4983230072969 + 3 ^ 40 * 4460952 * 2
def baseEnd_4460952 : Nat := 84837501949471694017943

theorem tailTrace_4460952 : CollatzResearch.WordTrace tailWord_4460952 prefixEnd_4460952 84837501949471694017943 := by
  unfold tailWord_4460952
  simp only [CollatzResearch.WordTrace]
  refine ⟨81352143067370124395572555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108469524089826832527430073 81352143067370124395572555)
  ·
    refine ⟨122028214601055186593358833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81352143067370124395572555 122028214601055186593358833)
    ·
      refine ⟨91521160950791389945019125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122028214601055186593358833 91521160950791389945019125)
      ·
        refine ⟨8580108839136692807345543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91521160950791389945019125 8580108839136692807345543)
        ·
          refine ⟨12870163258705039211018315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8580108839136692807345543 12870163258705039211018315)
          ·
            refine ⟨19305244888057558816527473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12870163258705039211018315 19305244888057558816527473)
            ·
              refine ⟨14478933666043169112395605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19305244888057558816527473 14478933666043169112395605)
              ·
                refine ⟨84837501949471694017943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14478933666043169112395605 84837501949471694017943)
                ·
                  rfl

theorem cell23_4460952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 9].length) (baseStart_4460952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460952 prefixEnd_4460952 := by exact prefixLift 4460952
  have htrace : WordTrace (prefixWord ++ tailWord_4460952) baseStart_4460952 baseEnd_4460952 := by
    simpa [prefixWord, tailWord_4460952, baseEnd_4460952] using wordTrace_append hprefix tailTrace_4460952
  have hstable : (prefixWord ++ tailWord_4460952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460952).length < 2 ^ (prefixWord ++ tailWord_4460952).sum := by decide
  have hdescent : baseEnd_4460952 < baseStart_4460952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460973 : List Nat := [1, 5, 2, 2, 2, 1, 2, 2, 2, 4]
def baseStart_4460973 : Nat := 118140960795 + 4460973 * 2 ^ 59
def prefixEnd_4460973 : Nat := 4983230072969 + 3 ^ 40 * 4460973 * 2
def baseEnd_4460973 : Nat := 763541111909826718773955

theorem tailTrace_4460973 : CollatzResearch.WordTrace tailWord_4460973 prefixEnd_4460973 763541111909826718773955 := by
  unfold tailWord_4460973
  simp only [CollatzResearch.WordTrace]
  refine ⟨162705052067664169377659573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108470034711776112918439715 162705052067664169377659573)
  ·
    refine ⟨15253598631343515879155585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 162705052067664169377659573 15253598631343515879155585)
    ·
      refine ⟨11440198973507636909366689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15253598631343515879155585 11440198973507636909366689)
      ·
        refine ⟨8580149230130727682025017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11440198973507636909366689 8580149230130727682025017)
        ·
          refine ⟨6435111922598045761518763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8580149230130727682025017 6435111922598045761518763)
          ·
            refine ⟨9652667883897068642278145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6435111922598045761518763 9652667883897068642278145)
            ·
              refine ⟨7239500912922801481708609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9652667883897068642278145 7239500912922801481708609)
              ·
                refine ⟨5429625684692101111281457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7239500912922801481708609 5429625684692101111281457)
                ·
                  refine ⟨4072219263519075833461093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5429625684692101111281457 4072219263519075833461093)
                  ·
                    refine ⟨763541111909826718773955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4072219263519075833461093 763541111909826718773955)
                    ·
                      rfl

theorem cell23_4460973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_4460973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460973 prefixEnd_4460973 := by exact prefixLift 4460973
  have htrace : WordTrace (prefixWord ++ tailWord_4460973) baseStart_4460973 baseEnd_4460973 := by
    simpa [prefixWord, tailWord_4460973, baseEnd_4460973] using wordTrace_append hprefix tailTrace_4460973
  have hstable : (prefixWord ++ tailWord_4460973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460973).length < 2 ^ (prefixWord ++ tailWord_4460973).sum := by decide
  have hdescent : baseEnd_4460973 < baseStart_4460973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4460975 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 7]
def baseStart_4460975 : Nat := 118140960795 + 4460975 * 2 ^ 59
def prefixEnd_4460975 : Nat := 4983230072969 + 3 ^ 40 * 4460975 * 2
def baseEnd_4460975 : Nat := 2290624362690789148496855

theorem tailTrace_4460975 : CollatzResearch.WordTrace tailWord_4460975 prefixEnd_4460975 2290624362690789148496855 := by
  unfold tailWord_4460975
  simp only [CollatzResearch.WordTrace]
  refine ⟨162705125013656923719232379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108470083342437949146154919 162705125013656923719232379)
  ·
    refine ⟨244057687520485385578848569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162705125013656923719232379 244057687520485385578848569)
    ·
      refine ⟨183043265640364039184136427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244057687520485385578848569 183043265640364039184136427)
      ·
        refine ⟨274564898460546058776204641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183043265640364039184136427 274564898460546058776204641)
        ·
          refine ⟨205923673845409544082153481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274564898460546058776204641 205923673845409544082153481)
          ·
            refine ⟨154442755384057158061615111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205923673845409544082153481 154442755384057158061615111)
            ·
              refine ⟨231664133076085737092422667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154442755384057158061615111 231664133076085737092422667)
              ·
                refine ⟨347496199614128605638634001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231664133076085737092422667 347496199614128605638634001)
                ·
                  refine ⟨260622149710596454228975501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 347496199614128605638634001 260622149710596454228975501)
                  ·
                    refine ⟨97733306141473670335865813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 260622149710596454228975501 97733306141473670335865813)
                    ·
                      refine ⟨2290624362690789148496855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97733306141473670335865813 2290624362690789148496855)
                      ·
                        rfl

theorem cell23_4460975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_4460975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4460975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4460975 prefixEnd_4460975 := by exact prefixLift 4460975
  have htrace : WordTrace (prefixWord ++ tailWord_4460975) baseStart_4460975 baseEnd_4460975 := by
    simpa [prefixWord, tailWord_4460975, baseEnd_4460975] using wordTrace_append hprefix tailTrace_4460975
  have hstable : (prefixWord ++ tailWord_4460975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4460975).length < 2 ^ (prefixWord ++ tailWord_4460975).sum := by decide
  have hdescent : baseEnd_4460975 < baseStart_4460975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4460975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461002 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 2, 3, 4]
def baseStart_4461002 : Nat := 118140960795 + 4461002 * 2 ^ 59
def prefixEnd_4461002 : Nat := 4983230072969 + 3 ^ 40 * 4461002 * 2
def baseEnd_4461002 : Nat := 2290638226668460542859231

theorem tailTrace_4461002 : CollatzResearch.WordTrace tailWord_4461002 prefixEnd_4461002 2290638226668460542859231 := by
  unfold tailWord_4461002
  simp only [CollatzResearch.WordTrace]
  refine ⟨40676527446139776832616315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108470739856372738220310173 40676527446139776832616315)
  ·
    refine ⟨61014791169209665248924473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40676527446139776832616315 61014791169209665248924473)
    ·
      refine ⟨45761093376907248936693355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61014791169209665248924473 45761093376907248936693355)
      ·
        refine ⟨68641640065360873405040033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45761093376907248936693355 68641640065360873405040033)
        ·
          refine ⟨51481230049020655053780025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68641640065360873405040033 51481230049020655053780025)
          ·
            refine ⟨38610922536765491290335019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51481230049020655053780025 38610922536765491290335019)
            ·
              refine ⟨57916383805148236935502529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38610922536765491290335019 57916383805148236935502529)
              ·
                refine ⟨43437287853861177701626897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57916383805148236935502529 43437287853861177701626897)
                ·
                  refine ⟨32577965890395883276220173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43437287853861177701626897 32577965890395883276220173)
                  ·
                    refine ⟨12216737208898456228582565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32577965890395883276220173 12216737208898456228582565)
                    ·
                      refine ⟨2290638226668460542859231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12216737208898456228582565 2290638226668460542859231)
                      ·
                        rfl

theorem cell23_4461002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_4461002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461002 prefixEnd_4461002 := by exact prefixLift 4461002
  have htrace : WordTrace (prefixWord ++ tailWord_4461002) baseStart_4461002 baseEnd_4461002 := by
    simpa [prefixWord, tailWord_4461002, baseEnd_4461002] using wordTrace_append hprefix tailTrace_4461002
  have hstable : (prefixWord ++ tailWord_4461002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461002).length < 2 ^ (prefixWord ++ tailWord_4461002).sum := by decide
  have hdescent : baseEnd_4461002 < baseStart_4461002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461006 : List Nat := [4, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2]
def baseStart_4461006 : Nat := 118140960795 + 4461006 * 2 ^ 59
def prefixEnd_4461006 : Nat := 4983230072969 + 3 ^ 40 * 4461006 * 2
def baseEnd_4461006 : Nat := 2290640280591078527209213

theorem tailTrace_4461006 : CollatzResearch.WordTrace tailWord_4461006 prefixEnd_4461006 2290640280591078527209213 := by
  unfold tailWord_4461006
  simp only [CollatzResearch.WordTrace]
  refine ⟨20338281959568077001701359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108470837117696410675740581 20338281959568077001701359)
  ·
    refine ⟨30507422939352115502552039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20338281959568077001701359 30507422939352115502552039)
    ·
      refine ⟨45761134409028173253828059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30507422939352115502552039 45761134409028173253828059)
      ·
        refine ⟨68641701613542259880742089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45761134409028173253828059 68641701613542259880742089)
        ·
          refine ⟨51481276210156694910556567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68641701613542259880742089 51481276210156694910556567)
          ·
            refine ⟨77221914315235042365834851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51481276210156694910556567 77221914315235042365834851)
            ·
              refine ⟨115832871472852563548752277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77221914315235042365834851 115832871472852563548752277)
              ·
                refine ⟨5429665850289963916347763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 115832871472852563548752277 5429665850289963916347763)
                ·
                  refine ⟨8144498775434945874521645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5429665850289963916347763 8144498775434945874521645)
                  ·
                    refine ⟨3054187040788104702945617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8144498775434945874521645 3054187040788104702945617)
                    ·
                      refine ⟨2290640280591078527209213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3054187040788104702945617 2290640280591078527209213)
                      ·
                        rfl

theorem cell23_4461006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_4461006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461006 prefixEnd_4461006 := by exact prefixLift 4461006
  have htrace : WordTrace (prefixWord ++ tailWord_4461006) baseStart_4461006 baseEnd_4461006 := by
    simpa [prefixWord, tailWord_4461006, baseEnd_4461006] using wordTrace_append hprefix tailTrace_4461006
  have hstable : (prefixWord ++ tailWord_4461006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461006).length < 2 ^ (prefixWord ++ tailWord_4461006).sum := by decide
  have hdescent : baseEnd_4461006 < baseStart_4461006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461023 : List Nat := [1, 1, 2, 3, 3, 2, 4, 1, 1, 3, 2]
def baseStart_4461023 : Nat := 118140960795 + 4461023 * 2 ^ 59
def prefixEnd_4461023 : Nat := 4983230072969 + 3 ^ 40 * 4461023 * 2
def baseEnd_4461023 : Nat := 2290649009762204960696635

theorem tailTrace_4461023 : CollatzResearch.WordTrace tailWord_4461023 prefixEnd_4461023 2290649009762204960696635 := by
  unfold tailWord_4461023
  simp only [CollatzResearch.WordTrace]
  refine ⟨162706875717483027916979723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108471250478322018611319815 162706875717483027916979723)
  ·
    refine ⟨244060313576224541875469585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162706875717483027916979723 244060313576224541875469585)
    ·
      refine ⟨183045235182168406406602189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244060313576224541875469585 183045235182168406406602189)
      ·
        refine ⟨68641963193313152402475821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183045235182168406406602189 68641963193313152402475821)
        ·
          refine ⟨25740736197492432150928433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68641963193313152402475821 25740736197492432150928433)
          ·
            refine ⟨19305552148119324113196325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25740736197492432150928433 19305552148119324113196325)
            ·
              refine ⟨3619791027772373271224311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19305552148119324113196325 3619791027772373271224311)
              ·
                refine ⟨5429686541658559906836467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3619791027772373271224311 5429686541658559906836467)
                ·
                  refine ⟨8144529812487839860254701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5429686541658559906836467 8144529812487839860254701)
                  ·
                    refine ⟨3054198679682939947595513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8144529812487839860254701 3054198679682939947595513)
                    ·
                      refine ⟨2290649009762204960696635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3054198679682939947595513 2290649009762204960696635)
                      ·
                        rfl

theorem cell23_4461023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_4461023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461023 prefixEnd_4461023 := by exact prefixLift 4461023
  have htrace : WordTrace (prefixWord ++ tailWord_4461023) baseStart_4461023 baseEnd_4461023 := by
    simpa [prefixWord, tailWord_4461023, baseEnd_4461023] using wordTrace_append hprefix tailTrace_4461023
  have hstable : (prefixWord ++ tailWord_4461023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461023).length < 2 ^ (prefixWord ++ tailWord_4461023).sum := by decide
  have hdescent : baseEnd_4461023 < baseStart_4461023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461036 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 4, 2, 2]
def baseStart_4461036 : Nat := 118140960795 + 4461036 * 2 ^ 59
def prefixEnd_4461036 : Nat := 4983230072969 + 3 ^ 40 * 4461036 * 2
def baseEnd_4461036 : Nat := 2290655685010713409834075

theorem tailTrace_4461036 : CollatzResearch.WordTrace tailWord_4461036 prefixEnd_4461036 2290655685010713409834075 := by
  unfold tailWord_4461036
  simp only [CollatzResearch.WordTrace]
  refine ⟨81353674933217965568601481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108471566577623954091468641 81353674933217965568601481)
  ·
    refine ⟨61015256199913474176451111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81353674933217965568601481 61015256199913474176451111)
    ·
      refine ⟨91522884299870211264676667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61015256199913474176451111 91522884299870211264676667)
      ·
        refine ⟨137284326449805316897015001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91522884299870211264676667 137284326449805316897015001)
        ·
          refine ⟨102963244837353987672761251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137284326449805316897015001 102963244837353987672761251)
          ·
            refine ⟨154444867256030981509141877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102963244837353987672761251 154444867256030981509141877)
            ·
              refine ⟨14479206305252904516482051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 154444867256030981509141877 14479206305252904516482051)
              ·
                refine ⟨21718809457879356774723077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14479206305252904516482051 21718809457879356774723077)
                ·
                  refine ⟨4072276773352379395260577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21718809457879356774723077 4072276773352379395260577)
                  ·
                    refine ⟨3054207580014284546445433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4072276773352379395260577 3054207580014284546445433)
                    ·
                      refine ⟨2290655685010713409834075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3054207580014284546445433 2290655685010713409834075)
                      ·
                        rfl

theorem cell23_4461036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 2, 2].length) (baseStart_4461036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461036 prefixEnd_4461036 := by exact prefixLift 4461036
  have htrace : WordTrace (prefixWord ++ tailWord_4461036) baseStart_4461036 baseEnd_4461036 := by
    simpa [prefixWord, tailWord_4461036, baseEnd_4461036] using wordTrace_append hprefix tailTrace_4461036
  have hstable : (prefixWord ++ tailWord_4461036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461036).length < 2 ^ (prefixWord ++ tailWord_4461036).sum := by decide
  have hdescent : baseEnd_4461036 < baseStart_4461036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461089 : List Nat := [1, 2, 3, 2, 2, 1, 3, 2, 2, 5]
def baseStart_4461089 : Nat := 118140960795 + 4461089 * 2 ^ 59
def prefixEnd_4461089 : Nat := 4983230072969 + 3 ^ 40 * 4461089 * 2
def baseEnd_4461089 : Nat := 763560966495133900823777

theorem tailTrace_4461089 : CollatzResearch.WordTrace tailWord_4461089 prefixEnd_4461089 763560966495133900823777 := by
  unfold tailWord_4461089
  simp only [CollatzResearch.WordTrace]
  refine ⟨162709282935243921188882321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108472855290162614125921547 162709282935243921188882321)
  ·
    refine ⟨122031962201432940891661741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162709282935243921188882321 122031962201432940891661741)
    ·
      refine ⟨45761985825537352834373153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122031962201432940891661741 45761985825537352834373153)
      ·
        refine ⟨34321489369153014625779865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45761985825537352834373153 34321489369153014625779865)
        ·
          refine ⟨25741117026864760969334899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34321489369153014625779865 25741117026864760969334899)
          ·
            refine ⟨38611675540297141454002349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25741117026864760969334899 38611675540297141454002349)
            ·
              refine ⟨14479378327611428045250881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38611675540297141454002349 14479378327611428045250881)
              ·
                refine ⟨10859533745708571033938161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14479378327611428045250881 10859533745708571033938161)
                ·
                  refine ⟨8144650309281428275453621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10859533745708571033938161 8144650309281428275453621)
                  ·
                    refine ⟨763560966495133900823777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8144650309281428275453621 763560966495133900823777)
                    ·
                      rfl

theorem cell23_4461089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_4461089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461089 prefixEnd_4461089 := by exact prefixLift 4461089
  have htrace : WordTrace (prefixWord ++ tailWord_4461089) baseStart_4461089 baseEnd_4461089 := by
    simpa [prefixWord, tailWord_4461089, baseEnd_4461089] using wordTrace_append hprefix tailTrace_4461089
  have hstable : (prefixWord ++ tailWord_4461089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461089).length < 2 ^ (prefixWord ++ tailWord_4461089).sum := by decide
  have hdescent : baseEnd_4461089 < baseStart_4461089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461109 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_4461109 : Nat := 118140960795 + 4461109 * 2 ^ 59
def prefixEnd_4461109 : Nat := 4983230072969 + 3 ^ 40 * 4461109 * 2
def baseEnd_4461109 : Nat := 2290693169098491624221239

theorem tailTrace_4461109 : CollatzResearch.WordTrace tailWord_4461109 prefixEnd_4461109 2290693169098491624221239 := by
  unfold tailWord_4461109
  simp only [CollatzResearch.WordTrace]
  refine ⟨162710012395171464604610381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108473341596780976403073587 162710012395171464604610381)
  ·
    refine ⟨61016254648189299226728893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162710012395171464604610381 61016254648189299226728893)
    ·
      refine ⟨22881095493070987210023335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61016254648189299226728893 22881095493070987210023335)
      ·
        refine ⟨34321643239606480815035003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22881095493070987210023335 34321643239606480815035003)
        ·
          refine ⟨51482464859409721222552505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34321643239606480815035003 51482464859409721222552505)
          ·
            refine ⟨38611848644557290916914379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51482464859409721222552505 38611848644557290916914379)
            ·
              refine ⟨57917772966835936375371569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38611848644557290916914379 57917772966835936375371569)
              ·
                refine ⟨43438329725126952281528677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57917772966835936375371569 43438329725126952281528677)
                ·
                  refine ⟨8144686823461303552786627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43438329725126952281528677 8144686823461303552786627)
                  ·
                    refine ⟨12217030235191955329179941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8144686823461303552786627 12217030235191955329179941)
                    ·
                      refine ⟨2290693169098491624221239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12217030235191955329179941 2290693169098491624221239)
                      ·
                        rfl

theorem cell23_4461109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_4461109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461109 prefixEnd_4461109 := by exact prefixLift 4461109
  have htrace : WordTrace (prefixWord ++ tailWord_4461109) baseStart_4461109 baseEnd_4461109 := by
    simpa [prefixWord, tailWord_4461109, baseEnd_4461109] using wordTrace_append hprefix tailTrace_4461109
  have hstable : (prefixWord ++ tailWord_4461109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461109).length < 2 ^ (prefixWord ++ tailWord_4461109).sum := by decide
  have hdescent : baseEnd_4461109 < baseStart_4461109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461119 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 5, 4]
def baseStart_4461119 : Nat := 118140960795 + 4461119 * 2 ^ 59
def prefixEnd_4461119 : Nat := 4983230072969 + 3 ^ 40 * 4461119 * 2
def baseEnd_4461119 : Nat := 763566101301678861698731

theorem tailTrace_4461119 : CollatzResearch.WordTrace tailWord_4461119 prefixEnd_4461119 763566101301678861698731 := by
  unfold tailWord_4461119
  simp only [CollatzResearch.WordTrace]
  refine ⟨162710377125135236312474411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108473584750090157541649607 162710377125135236312474411)
  ·
    refine ⟨244065565687702854468711617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162710377125135236312474411 244065565687702854468711617)
    ·
      refine ⟨183049174265777140851533713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244065565687702854468711617 183049174265777140851533713)
      ·
        refine ⟨137286880699332855638650285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183049174265777140851533713 137286880699332855638650285)
        ·
          refine ⟨51482580262249820864493857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137286880699332855638650285 51482580262249820864493857)
          ·
            refine ⟨38611935196687365648370393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51482580262249820864493857 38611935196687365648370393)
            ·
              refine ⟨28958951397515524236277795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38611935196687365648370393 28958951397515524236277795)
              ·
                refine ⟨43438427096273286354416693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28958951397515524236277795 43438427096273286354416693)
                ·
                  refine ⟨4072352540275620595726565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43438427096273286354416693 4072352540275620595726565)
                  ·
                    refine ⟨763566101301678861698731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4072352540275620595726565 763566101301678861698731)
                    ·
                      rfl

theorem cell23_4461119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 4].length) (baseStart_4461119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461119 prefixEnd_4461119 := by exact prefixLift 4461119
  have htrace : WordTrace (prefixWord ++ tailWord_4461119) baseStart_4461119 baseEnd_4461119 := by
    simpa [prefixWord, tailWord_4461119, baseEnd_4461119] using wordTrace_append hprefix tailTrace_4461119
  have hstable : (prefixWord ++ tailWord_4461119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461119).length < 2 ^ (prefixWord ++ tailWord_4461119).sum := by decide
  have hdescent : baseEnd_4461119 < baseStart_4461119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461153 : List Nat := [1, 2, 3, 1, 1, 5, 1, 4, 1, 4]
def baseStart_4461153 : Nat := 118140960795 + 4461153 * 2 ^ 59
def prefixEnd_4461153 : Nat := 4983230072969 + 3 ^ 40 * 4461153 * 2
def baseEnd_4461153 : Nat := 763571920749096484023679

theorem tailTrace_4461153 : CollatzResearch.WordTrace tailWord_4461153 prefixEnd_4461153 763571920749096484023679 := by
  unfold tailWord_4461153
  simp only [CollatzResearch.WordTrace]
  refine ⟨162711617207012060119212113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108474411471341373412808075 162711617207012060119212113)
  ·
    refine ⟨122033712905259045089409085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162711617207012060119212113 122033712905259045089409085)
    ·
      refine ⟨45762642339472141908528407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122033712905259045089409085 45762642339472141908528407)
      ·
        refine ⟨68643963509208212862792611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45762642339472141908528407 68643963509208212862792611)
        ·
          refine ⟨102965945263812319294188917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68643963509208212862792611 102965945263812319294188917)
          ·
            refine ⟨9653057368482404933830211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102965945263812319294188917 9653057368482404933830211)
            ·
              refine ⟨14479586052723607400745317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9653057368482404933830211 14479586052723607400745317)
              ·
                refine ⟨2714922384885676387639747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14479586052723607400745317 2714922384885676387639747)
                ·
                  refine ⟨4072383577328514581459621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2714922384885676387639747 4072383577328514581459621)
                  ·
                    refine ⟨763571920749096484023679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4072383577328514581459621 763571920749096484023679)
                    ·
                      rfl

theorem cell23_4461153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_4461153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461153 prefixEnd_4461153 := by exact prefixLift 4461153
  have htrace : WordTrace (prefixWord ++ tailWord_4461153) baseStart_4461153 baseEnd_4461153 := by
    simpa [prefixWord, tailWord_4461153, baseEnd_4461153] using wordTrace_append hprefix tailTrace_4461153
  have hstable : (prefixWord ++ tailWord_4461153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461153).length < 2 ^ (prefixWord ++ tailWord_4461153).sum := by decide
  have hdescent : baseEnd_4461153 < baseStart_4461153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461159 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 3]
def baseStart_4461159 : Nat := 118140960795 + 4461159 * 2 ^ 59
def prefixEnd_4461159 : Nat := 4983230072969 + 3 ^ 40 * 4461159 * 2
def baseEnd_4461159 : Nat := 2290718843131216428596009

theorem tailTrace_4461159 : CollatzResearch.WordTrace tailWord_4461159 prefixEnd_4461159 2290718843131216428596009 := by
  unfold tailWord_4461159
  simp only [CollatzResearch.WordTrace]
  refine ⟨162711836044990323143930531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108474557363326882095953687 162711836044990323143930531)
  ·
    refine ⟨244067754067485484715895797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162711836044990323143930531 244067754067485484715895797)
    ·
      refine ⟨22881351943826764192115231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 244067754067485484715895797 22881351943826764192115231)
      ·
        refine ⟨34322027915740146288172847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22881351943826764192115231 34322027915740146288172847)
        ·
          refine ⟨51483041873610219432259271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34322027915740146288172847 51483041873610219432259271)
          ·
            refine ⟨77224562810415329148388907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51483041873610219432259271 77224562810415329148388907)
            ·
              refine ⟨115836844215622993722583361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77224562810415329148388907 115836844215622993722583361)
              ·
                refine ⟨86877633161717245291937521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115836844215622993722583361 86877633161717245291937521)
                ·
                  refine ⟨65158224871287933968953141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86877633161717245291937521 65158224871287933968953141)
                  ·
                    refine ⟨6108583581683243809589357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65158224871287933968953141 6108583581683243809589357)
                    ·
                      refine ⟨2290718843131216428596009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6108583581683243809589357 2290718843131216428596009)
                      ·
                        rfl

theorem cell23_4461159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_4461159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461159 prefixEnd_4461159 := by exact prefixLift 4461159
  have htrace : WordTrace (prefixWord ++ tailWord_4461159) baseStart_4461159 baseEnd_4461159 := by
    simpa [prefixWord, tailWord_4461159, baseEnd_4461159] using wordTrace_append hprefix tailTrace_4461159
  have hstable : (prefixWord ++ tailWord_4461159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461159).length < 2 ^ (prefixWord ++ tailWord_4461159).sum := by decide
  have hdescent : baseEnd_4461159 < baseStart_4461159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461166 : List Nat := [4, 1, 2, 2, 2, 1, 2, 3, 6]
def baseStart_4461166 : Nat := 118140960795 + 4461166 * 2 ^ 59
def prefixEnd_4461166 : Nat := 4983230072969 + 3 ^ 40 * 4461166 * 2
def baseEnd_4461166 : Nat := 254524715277310877912053

theorem tailTrace_4461166 : CollatzResearch.WordTrace tailWord_4461166 prefixEnd_4461166 254524715277310877912053 := by
  unfold tailWord_4461166
  simp only [CollatzResearch.WordTrace]
  refine ⟨20339011419495620417429419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108474727570643308892956901 20339011419495620417429419)
  ·
    refine ⟨30508517129243430626144129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20339011419495620417429419 30508517129243430626144129)
    ·
      refine ⟨22881387846932572969608097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30508517129243430626144129 22881387846932572969608097)
      ·
        refine ⟨17161040885199429727206073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22881387846932572969608097 17161040885199429727206073)
        ·
          refine ⟨12870780663899572295404555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17161040885199429727206073 12870780663899572295404555)
          ·
            refine ⟨19306170995849358443106833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12870780663899572295404555 19306170995849358443106833)
            ·
              refine ⟨14479628246887018832330125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19306170995849358443106833 14479628246887018832330125)
              ·
                refine ⟨5429860592582632062123797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14479628246887018832330125 5429860592582632062123797)
                ·
                  refine ⟨254524715277310877912053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5429860592582632062123797 254524715277310877912053)
                  ·
                    rfl

theorem cell23_4461166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_4461166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461166 prefixEnd_4461166 := by exact prefixLift 4461166
  have htrace : WordTrace (prefixWord ++ tailWord_4461166) baseStart_4461166 baseEnd_4461166 := by
    simpa [prefixWord, tailWord_4461166, baseEnd_4461166] using wordTrace_append hprefix tailTrace_4461166
  have hstable : (prefixWord ++ tailWord_4461166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461166).length < 2 ^ (prefixWord ++ tailWord_4461166).sum := by decide
  have hdescent : baseEnd_4461166 < baseStart_4461166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461176 : List Nat := [2, 1, 2, 1, 1, 1, 2, 6, 3, 1, 3]
def baseStart_4461176 : Nat := 118140960795 + 4461176 * 2 ^ 59
def prefixEnd_4461176 : Nat := 4983230072969 + 3 ^ 40 * 4461176 * 2
def baseEnd_4461176 : Nat := 2290727572302342862083431

theorem tailTrace_4461176 : CollatzResearch.WordTrace tailWord_4461176 prefixEnd_4461176 2290727572302342862083431 := by
  unfold tailWord_4461176
  simp only [CollatzResearch.WordTrace]
  refine ⟨81356228042964367523649691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108474970723952490031532921 81356228042964367523649691)
  ·
    refine ⟨122034342064446551285474537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81356228042964367523649691 122034342064446551285474537)
    ·
      refine ⟨91525756548334913464105903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122034342064446551285474537 91525756548334913464105903)
      ·
        refine ⟨137288634822502370196158855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91525756548334913464105903 137288634822502370196158855)
        ·
          refine ⟨205932952233753555294238283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137288634822502370196158855 205932952233753555294238283)
          ·
            refine ⟨308899428350630332941357425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205932952233753555294238283 308899428350630332941357425)
            ·
              refine ⟨231674571262972749706018069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308899428350630332941357425 231674571262972749706018069)
              ·
                refine ⟨10859745527951847642469597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 231674571262972749706018069 10859745527951847642469597)
                ·
                  refine ⟨4072404572981942865926099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10859745527951847642469597 4072404572981942865926099)
                  ·
                    refine ⟨6108606859472914298889149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4072404572981942865926099 6108606859472914298889149)
                    ·
                      refine ⟨2290727572302342862083431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6108606859472914298889149 2290727572302342862083431)
                      ·
                        rfl

theorem cell23_4461176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 3, 1, 3].length) (baseStart_4461176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461176 prefixEnd_4461176 := by exact prefixLift 4461176
  have htrace : WordTrace (prefixWord ++ tailWord_4461176) baseStart_4461176 baseEnd_4461176 := by
    simpa [prefixWord, tailWord_4461176, baseEnd_4461176] using wordTrace_append hprefix tailTrace_4461176
  have hstable : (prefixWord ++ tailWord_4461176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461176).length < 2 ^ (prefixWord ++ tailWord_4461176).sum := by decide
  have hdescent : baseEnd_4461176 < baseStart_4461176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461219 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 3]
def baseStart_4461219 : Nat := 118140960795 + 4461219 * 2 ^ 59
def prefixEnd_4461219 : Nat := 4983230072969 + 3 ^ 40 * 4461219 * 2
def baseEnd_4461219 : Nat := 2290749651970486193845733

theorem tailTrace_4461219 : CollatzResearch.WordTrace tailWord_4461219 prefixEnd_4461219 2290749651970486193845733 := by
  unfold tailWord_4461219
  simp only [CollatzResearch.WordTrace]
  refine ⟨162714024424772953391114711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108476016283181968927409807 162714024424772953391114711)
  ·
    refine ⟨244071036637159430086672067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162714024424772953391114711 244071036637159430086672067)
    ·
      refine ⟨366106554955739145130008101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244071036637159430086672067 366106554955739145130008101)
      ·
        refine ⟨68644979054201089711876519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 366106554955739145130008101 68644979054201089711876519)
        ·
          refine ⟨102967468581301634567814779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68644979054201089711876519 102967468581301634567814779)
          ·
            refine ⟨154451202871952451851722169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102967468581301634567814779 154451202871952451851722169)
            ·
              refine ⟨115838402153964338888791627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154451202871952451851722169 115838402153964338888791627)
              ·
                refine ⟨173757603230946508333187441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115838402153964338888791627 173757603230946508333187441)
                ·
                  refine ⟨130318202423209881249890581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173757603230946508333187441 130318202423209881249890581)
                  ·
                    refine ⟨6108665738587963183588621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 130318202423209881249890581 6108665738587963183588621)
                    ·
                      refine ⟨2290749651970486193845733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6108665738587963183588621 2290749651970486193845733)
                      ·
                        rfl

theorem cell23_4461219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_4461219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461219 prefixEnd_4461219 := by exact prefixLift 4461219
  have htrace : WordTrace (prefixWord ++ tailWord_4461219) baseStart_4461219 baseEnd_4461219 := by
    simpa [prefixWord, tailWord_4461219, baseEnd_4461219] using wordTrace_append hprefix tailTrace_4461219
  have hstable : (prefixWord ++ tailWord_4461219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461219).length < 2 ^ (prefixWord ++ tailWord_4461219).sum := by decide
  have hdescent : baseEnd_4461219 < baseStart_4461219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461230 : List Nat := [4, 1, 4, 1, 1, 2, 2, 2, 1, 5]
def baseStart_4461230 : Nat := 118140960795 + 4461230 * 2 ^ 59
def prefixEnd_4461230 : Nat := 4983230072969 + 3 ^ 40 * 4461230 * 2
def baseEnd_4461230 : Nat := 763585100085895216936061

theorem tailTrace_4461230 : CollatzResearch.WordTrace tailWord_4461230 prefixEnd_4461230 763585100085895216936061 := by
  unfold tailWord_4461230
  simp only [CollatzResearch.WordTrace]
  refine ⟨20339303203466637783720643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108476283751822068179843429 20339303203466637783720643)
  ·
    refine ⟨30508954805199956675580965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20339303203466637783720643 30508954805199956675580965)
    ·
      refine ⟨5720429025974991876671431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30508954805199956675580965 5720429025974991876671431)
      ·
        refine ⟨8580643538962487815007147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5720429025974991876671431 8580643538962487815007147)
        ·
          refine ⟨12870965308443731722510721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8580643538962487815007147 12870965308443731722510721)
          ·
            refine ⟨9653223981332798791883041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12870965308443731722510721 9653223981332798791883041)
            ·
              refine ⟨7239917985999599093912281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9653223981332798791883041 7239917985999599093912281)
              ·
                refine ⟨5429938489499699320434211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7239917985999599093912281 5429938489499699320434211)
                ·
                  refine ⟨8144907734249548980651317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5429938489499699320434211 8144907734249548980651317)
                  ·
                    refine ⟨763585100085895216936061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8144907734249548980651317 763585100085895216936061)
                    ·
                      rfl

theorem cell23_4461230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_4461230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461230 prefixEnd_4461230 := by exact prefixLift 4461230
  have htrace : WordTrace (prefixWord ++ tailWord_4461230) baseStart_4461230 baseEnd_4461230 := by
    simpa [prefixWord, tailWord_4461230, baseEnd_4461230] using wordTrace_append hprefix tailTrace_4461230
  have hstable : (prefixWord ++ tailWord_4461230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461230).length < 2 ^ (prefixWord ++ tailWord_4461230).sum := by decide
  have hdescent : baseEnd_4461230 < baseStart_4461230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461246 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_4461246 : Nat := 118140960795 + 4461246 * 2 ^ 59
def prefixEnd_4461246 : Nat := 4983230072969 + 3 ^ 40 * 4461246 * 2
def baseEnd_4461246 : Nat := 2290763515948157588208109

theorem tailTrace_4461246 : CollatzResearch.WordTrace tailWord_4461246 prefixEnd_4461246 2290763515948157588208109 := by
  unfold tailWord_4461246
  simp only [CollatzResearch.WordTrace]
  refine ⟨20339376149459392125293449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108476672797116758001565061 20339376149459392125293449)
  ·
    refine ⟨15254532112094544093970087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20339376149459392125293449 15254532112094544093970087)
    ·
      refine ⟨22881798168141816140955131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15254532112094544093970087 22881798168141816140955131)
      ·
        refine ⟨34322697252212724211432697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22881798168141816140955131 34322697252212724211432697)
        ·
          refine ⟨25742022939159543158574523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34322697252212724211432697 25742022939159543158574523)
          ·
            refine ⟨38613034408739314737861785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25742022939159543158574523 38613034408739314737861785)
            ·
              refine ⟨28959775806554486053396339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38613034408739314737861785 28959775806554486053396339)
              ·
                refine ⟨43439663709831729080094509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28959775806554486053396339 43439663709831729080094509)
                ·
                  refine ⟨16289873891186898405035441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43439663709831729080094509 16289873891186898405035441)
                  ·
                    refine ⟨12217405418390173803776581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16289873891186898405035441 12217405418390173803776581)
                    ·
                      refine ⟨2290763515948157588208109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12217405418390173803776581 2290763515948157588208109)
                      ·
                        rfl

theorem cell23_4461246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_4461246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461246 prefixEnd_4461246 := by exact prefixLift 4461246
  have htrace : WordTrace (prefixWord ++ tailWord_4461246) baseStart_4461246 baseEnd_4461246 := by
    simpa [prefixWord, tailWord_4461246, baseEnd_4461246] using wordTrace_append hprefix tailTrace_4461246
  have hstable : (prefixWord ++ tailWord_4461246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461246).length < 2 ^ (prefixWord ++ tailWord_4461246).sum := by decide
  have hdescent : baseEnd_4461246 < baseStart_4461246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461254 : List Nat := [6, 1, 2, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_4461254 : Nat := 118140960795 + 4461254 * 2 ^ 59
def prefixEnd_4461254 : Nat := 4983230072969 + 3 ^ 40 * 4461254 * 2
def baseEnd_4461254 : Nat := 2290767623793393556908073

theorem tailTrace_4461254 : CollatzResearch.WordTrace tailWord_4461254 prefixEnd_4461254 2290767623793393556908073 := by
  unfold tailWord_4461254
  simp only [CollatzResearch.WordTrace]
  refine ⟨5084853155613942324019963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 108476867319764102912425877 5084853155613942324019963)
  ·
    refine ⟨7627279733420913486029945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5084853155613942324019963 7627279733420913486029945)
    ·
      refine ⟨5720459800065685114522459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7627279733420913486029945 5720459800065685114522459)
      ·
        refine ⟨8580689700098527671783689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5720459800065685114522459 8580689700098527671783689)
        ·
          refine ⟨6435517275073895753837767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8580689700098527671783689 6435517275073895753837767)
          ·
            refine ⟨9653275912610843630756651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6435517275073895753837767 9653275912610843630756651)
            ·
              refine ⟨14479913868916265446134977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9653275912610843630756651 14479913868916265446134977)
              ·
                refine ⟨10859935401687199084601233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14479913868916265446134977 10859935401687199084601233)
                ·
                  refine ⟨8144951551265399313450925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10859935401687199084601233 8144951551265399313450925)
                  ·
                    refine ⟨3054356831724524742544097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8144951551265399313450925 3054356831724524742544097)
                    ·
                      refine ⟨2290767623793393556908073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3054356831724524742544097 2290767623793393556908073)
                      ·
                        rfl

theorem cell23_4461254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_4461254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461254 prefixEnd_4461254 := by exact prefixLift 4461254
  have htrace : WordTrace (prefixWord ++ tailWord_4461254) baseStart_4461254 baseEnd_4461254 := by
    simpa [prefixWord, tailWord_4461254, baseEnd_4461254] using wordTrace_append hprefix tailTrace_4461254
  have hstable : (prefixWord ++ tailWord_4461254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461254).length < 2 ^ (prefixWord ++ tailWord_4461254).sum := by decide
  have hdescent : baseEnd_4461254 < baseStart_4461254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461261 : List Nat := [1, 6, 2, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_4461261 : Nat := 118140960795 + 4461261 * 2 ^ 59
def prefixEnd_4461261 : Nat := 4983230072969 + 3 ^ 40 * 4461261 * 2
def baseEnd_4461261 : Nat := 2290771218157975029520541

theorem tailTrace_4461261 : CollatzResearch.WordTrace tailWord_4461261 prefixEnd_4461261 2290771218157975029520541 := by
  unfold tailWord_4461261
  simp only [CollatzResearch.WordTrace]
  refine ⟨162715556290620794564143637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108477037527080529709429091 162715556290620794564143637)
  ·
    refine ⟨7627291701122849745194233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 162715556290620794564143637 7627291701122849745194233)
    ·
      refine ⟨5720468775842137308895675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7627291701122849745194233 5720468775842137308895675)
      ·
        refine ⟨8580703163763205963343513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5720468775842137308895675 8580703163763205963343513)
        ·
          refine ⟨6435527372822404472507635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8580703163763205963343513 6435527372822404472507635)
          ·
            refine ⟨9653291059233606708761453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6435527372822404472507635 9653291059233606708761453)
            ·
              refine ⟨3619984147212602515785545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9653291059233606708761453 3619984147212602515785545)
              ·
                refine ⟨2714988110409451886839159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3619984147212602515785545 2714988110409451886839159)
                ·
                  refine ⟨4072482165614177830258739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2714988110409451886839159 4072482165614177830258739)
                  ·
                    refine ⟨6108723248421266745388109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4072482165614177830258739 6108723248421266745388109)
                    ·
                      refine ⟨2290771218157975029520541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6108723248421266745388109 2290771218157975029520541)
                      ·
                        rfl

theorem cell23_4461261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_4461261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461261 prefixEnd_4461261 := by exact prefixLift 4461261
  have htrace : WordTrace (prefixWord ++ tailWord_4461261) baseStart_4461261 baseEnd_4461261 := by
    simpa [prefixWord, tailWord_4461261, baseEnd_4461261] using wordTrace_append hprefix tailTrace_4461261
  have hstable : (prefixWord ++ tailWord_4461261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461261).length < 2 ^ (prefixWord ++ tailWord_4461261).sum := by decide
  have hdescent : baseEnd_4461261 < baseStart_4461261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461299 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 4, 6]
def baseStart_4461299 : Nat := 118140960795 + 4461299 * 2 ^ 59
def prefixEnd_4461299 : Nat := 4983230072969 + 3 ^ 40 * 4461299 * 2
def baseEnd_4461299 : Nat := 763596910140948626948455

theorem tailTrace_4461299 : CollatzResearch.WordTrace tailWord_4461299 prefixEnd_4461299 763596910140948626948455 := by
  unfold tailWord_4461299
  simp only [CollatzResearch.WordTrace]
  refine ⟨162716942264483127054026951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108477961509655418036017967 162716942264483127054026951)
  ·
    refine ⟨244075413396724690581040427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162716942264483127054026951 244075413396724690581040427)
    ·
      refine ⟨366113120095087035871560641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244075413396724690581040427 366113120095087035871560641)
      ·
        refine ⟨274584840071315276903670481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 366113120095087035871560641 274584840071315276903670481)
        ·
          refine ⟨205938630053486457677752861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274584840071315276903670481 205938630053486457677752861)
          ·
            refine ⟨77226986270057421629157323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 205938630053486457677752861 77226986270057421629157323)
            ·
              refine ⟨115840479405086132443735985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77226986270057421629157323 115840479405086132443735985)
              ·
                refine ⟨86880359553814599332801989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115840479405086132443735985 86880359553814599332801989)
                ·
                  refine ⟨16290067416340237374900373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86880359553814599332801989 16290067416340237374900373)
                  ·
                    refine ⟨763596910140948626948455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16290067416340237374900373 763596910140948626948455)
                    ·
                      rfl

theorem cell23_4461299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 6].length) (baseStart_4461299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461299 prefixEnd_4461299 := by exact prefixLift 4461299
  have htrace : WordTrace (prefixWord ++ tailWord_4461299) baseStart_4461299 baseEnd_4461299 := by
    simpa [prefixWord, tailWord_4461299, baseEnd_4461299] using wordTrace_append hprefix tailTrace_4461299
  have hstable : (prefixWord ++ tailWord_4461299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461299).length < 2 ^ (prefixWord ++ tailWord_4461299).sum := by decide
  have hdescent : baseEnd_4461299 < baseStart_4461299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461316 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 2, 6]
def baseStart_4461316 : Nat := 118140960795 + 4461316 * 2 ^ 59
def prefixEnd_4461316 : Nat := 4983230072969 + 3 ^ 40 * 4461316 * 2
def baseEnd_4461316 : Nat := 763599819864657438110929

theorem tailTrace_4461316 : CollatzResearch.WordTrace tailWord_4461316 prefixEnd_4461316 763599819864657438110929 := by
  unfold tailWord_4461316
  simp only [CollatzResearch.WordTrace]
  refine ⟨81358781152710769478697901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108478374870281025971597201 81358781152710769478697901)
  ·
    refine ⟨30509542932266538554511713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81358781152710769478697901 30509542932266538554511713)
    ·
      refine ⟨22882157199199903915883785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30509542932266538554511713 22882157199199903915883785)
      ·
        refine ⟨17161617899399927936912839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22882157199199903915883785 17161617899399927936912839)
        ·
          refine ⟨25742426849099891905369259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17161617899399927936912839 25742426849099891905369259)
          ·
            refine ⟨38613640273649837858053889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25742426849099891905369259 38613640273649837858053889)
            ·
              refine ⟨28960230205237378393540417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38613640273649837858053889 28960230205237378393540417)
              ·
                refine ⟨21720172653928033795155313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28960230205237378393540417 21720172653928033795155313)
                ·
                  refine ⟨16290129490446025346366485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21720172653928033795155313 16290129490446025346366485)
                  ·
                    refine ⟨763599819864657438110929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16290129490446025346366485 763599819864657438110929)
                    ·
                      rfl

theorem cell23_4461316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_4461316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461316 prefixEnd_4461316 := by exact prefixLift 4461316
  have htrace : WordTrace (prefixWord ++ tailWord_4461316) baseStart_4461316 baseEnd_4461316 := by
    simpa [prefixWord, tailWord_4461316, baseEnd_4461316] using wordTrace_append hprefix tailTrace_4461316
  have hstable : (prefixWord ++ tailWord_4461316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461316).length < 2 ^ (prefixWord ++ tailWord_4461316).sum := by decide
  have hdescent : baseEnd_4461316 < baseStart_4461316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461340 : List Nat := [2, 2, 3, 1, 1, 4, 2, 1, 1, 4, 2]
def baseStart_4461340 : Nat := 118140960795 + 4461340 * 2 ^ 59
def prefixEnd_4461340 : Nat := 4983230072969 + 3 ^ 40 * 4461340 * 2
def baseEnd_4461340 : Nat := 2290811783129680220432677

theorem tailTrace_4461340 : CollatzResearch.WordTrace tailWord_4461340 prefixEnd_4461340 2290811783129680220432677 := by
  unfold tailWord_4461340
  simp only [CollatzResearch.WordTrace]
  refine ⟨81359218828667295528134737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108478958438223060704179649 81359218828667295528134737)
  ·
    refine ⟨61019414121500471646101053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81359218828667295528134737 61019414121500471646101053)
    ·
      refine ⟨22882280295562676867287895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61019414121500471646101053 22882280295562676867287895)
      ·
        refine ⟨34323420443344015300931843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22882280295562676867287895 34323420443344015300931843)
        ·
          refine ⟨51485130665016022951397765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34323420443344015300931843 51485130665016022951397765)
          ·
            refine ⟨9653461999690504303387081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51485130665016022951397765 9653461999690504303387081)
            ·
              refine ⟨7240096499767878227540311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9653461999690504303387081 7240096499767878227540311)
              ·
                refine ⟨10860144749651817341310467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7240096499767878227540311 10860144749651817341310467)
                ·
                  refine ⟨16290217124477726011965701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10860144749651817341310467 16290217124477726011965701)
                  ·
                    refine ⟨3054415710839573627243569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16290217124477726011965701 3054415710839573627243569)
                    ·
                      refine ⟨2290811783129680220432677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3054415710839573627243569 2290811783129680220432677)
                      ·
                        rfl

theorem cell23_4461340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_4461340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461340 prefixEnd_4461340 := by exact prefixLift 4461340
  have htrace : WordTrace (prefixWord ++ tailWord_4461340) baseStart_4461340 baseEnd_4461340 := by
    simpa [prefixWord, tailWord_4461340, baseEnd_4461340] using wordTrace_append hprefix tailTrace_4461340
  have hstable : (prefixWord ++ tailWord_4461340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461340).length < 2 ^ (prefixWord ++ tailWord_4461340).sum := by decide
  have hdescent : baseEnd_4461340 < baseStart_4461340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461346 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 9]
def baseStart_4461346 : Nat := 118140960795 + 4461346 * 2 ^ 59
def prefixEnd_4461346 : Nat := 4983230072969 + 3 ^ 40 * 4461346 * 2
def baseEnd_4461346 : Nat := 254534984890400799661961

theorem tailTrace_4461346 : CollatzResearch.WordTrace tailWord_4461346 prefixEnd_4461346 254534984890400799661961 := by
  unfold tailWord_4461346
  simp only [CollatzResearch.WordTrace]
  refine ⟨40679664123828213520246973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108479104330208569387325261 40679664123828213520246973)
  ·
    refine ⟨15254874046435580070092615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40679664123828213520246973 15254874046435580070092615)
    ·
      refine ⟨22882311069653370105138923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15254874046435580070092615 22882311069653370105138923)
      ·
        refine ⟨34323466604480055157708385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22882311069653370105138923 34323466604480055157708385)
        ·
          refine ⟨25742599953360041368281289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34323466604480055157708385 25742599953360041368281289)
          ·
            refine ⟨19306949965020031026210967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25742599953360041368281289 19306949965020031026210967)
            ·
              refine ⟨28960424947530046539316451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19306949965020031026210967 28960424947530046539316451)
              ·
                refine ⟨43440637421295069808974677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28960424947530046539316451 43440637421295069808974677)
                ·
                  refine ⟨254534984890400799661961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43440637421295069808974677 254534984890400799661961)
                  ·
                    rfl

theorem cell23_4461346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_4461346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461346 prefixEnd_4461346 := by exact prefixLift 4461346
  have htrace : WordTrace (prefixWord ++ tailWord_4461346) baseStart_4461346 baseEnd_4461346 := by
    simpa [prefixWord, tailWord_4461346, baseEnd_4461346] using wordTrace_append hprefix tailTrace_4461346
  have hstable : (prefixWord ++ tailWord_4461346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461346).length < 2 ^ (prefixWord ++ tailWord_4461346).sum := by decide
  have hdescent : baseEnd_4461346 < baseStart_4461346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461356 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 3]
def baseStart_4461356 : Nat := 118140960795 + 4461356 * 2 ^ 59
def prefixEnd_4461356 : Nat := 4983230072969 + 3 ^ 40 * 4461356 * 2
def baseEnd_4461356 : Nat := 2290819998820152157832603

theorem tailTrace_4461356 : CollatzResearch.WordTrace tailWord_4461356 prefixEnd_4461356 2290819998820152157832603 := by
  unfold tailWord_4461356
  simp only [CollatzResearch.WordTrace]
  refine ⟨81359510612638312894425961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108479347483517750525901281 81359510612638312894425961)
  ·
    refine ⟨61019632959478734670819471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81359510612638312894425961 61019632959478734670819471)
    ·
      refine ⟨91529449439218102006229207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61019632959478734670819471 91529449439218102006229207)
      ·
        refine ⟨137294174158827153009343811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91529449439218102006229207 137294174158827153009343811)
        ·
          refine ⟨205941261238240729514015717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137294174158827153009343811 205941261238240729514015717)
          ·
            refine ⟨38613986482170136783877947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 205941261238240729514015717 38613986482170136783877947)
            ·
              refine ⟨57920979723255205175816921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38613986482170136783877947 57920979723255205175816921)
              ·
                refine ⟨43440734792441403881862691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57920979723255205175816921 43440734792441403881862691)
                ·
                  refine ⟨65161102188662105822794037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43440734792441403881862691 65161102188662105822794037)
                  ·
                    refine ⟨6108853330187072420886941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65161102188662105822794037 6108853330187072420886941)
                    ·
                      refine ⟨2290819998820152157832603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6108853330187072420886941 2290819998820152157832603)
                      ·
                        rfl

theorem cell23_4461356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 3].length) (baseStart_4461356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461356 prefixEnd_4461356 := by exact prefixLift 4461356
  have htrace : WordTrace (prefixWord ++ tailWord_4461356) baseStart_4461356 baseEnd_4461356 := by
    simpa [prefixWord, tailWord_4461356, baseEnd_4461356] using wordTrace_append hprefix tailTrace_4461356
  have hstable : (prefixWord ++ tailWord_4461356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461356).length < 2 ^ (prefixWord ++ tailWord_4461356).sum := by decide
  have hdescent : baseEnd_4461356 < baseStart_4461356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461363 : List Nat := [1, 1, 1, 2, 6, 1, 1, 5, 5]
def baseStart_4461363 : Nat := 118140960795 + 4461363 * 2 ^ 59
def prefixEnd_4461363 : Nat := 4983230072969 + 3 ^ 40 * 4461363 * 2
def baseEnd_4461363 : Nat := 254535954798303736716119

theorem tailTrace_4461363 : CollatzResearch.WordTrace tailWord_4461363 prefixEnd_4461363 254535954798303736716119 := by
  unfold tailWord_4461363
  simp only [CollatzResearch.WordTrace]
  refine ⟨162719276536251265984356743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108479517690834177322904495 162719276536251265984356743)
  ·
    refine ⟨244078914804376898976535115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162719276536251265984356743 244078914804376898976535115)
    ·
      refine ⟨366118372206565348464802673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244078914804376898976535115 366118372206565348464802673)
      ·
        refine ⟨274588779154924011348602005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 366118372206565348464802673 274588779154924011348602005)
        ·
          refine ⟨12871349022887063031965719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 274588779154924011348602005 12871349022887063031965719)
          ·
            refine ⟨19307023534330594547948579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12871349022887063031965719 19307023534330594547948579)
            ·
              refine ⟨28960535301495891821922869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19307023534330594547948579 28960535301495891821922869)
              ·
                refine ⟨2715050184515239858305269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28960535301495891821922869 2715050184515239858305269)
                ·
                  refine ⟨254535954798303736716119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2715050184515239858305269 254535954798303736716119)
                  ·
                    rfl

theorem cell23_4461363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 5].length) (baseStart_4461363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461363 prefixEnd_4461363 := by exact prefixLift 4461363
  have htrace : WordTrace (prefixWord ++ tailWord_4461363) baseStart_4461363 baseEnd_4461363 := by
    simpa [prefixWord, tailWord_4461363, baseEnd_4461363] using wordTrace_append hprefix tailTrace_4461363
  have hstable : (prefixWord ++ tailWord_4461363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461363).length < 2 ^ (prefixWord ++ tailWord_4461363).sum := by decide
  have hdescent : baseEnd_4461363 < baseStart_4461363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461376 : List Nat := [2, 1, 1, 2, 2, 1, 1, 6, 2, 5]
def baseStart_4461376 : Nat := 118140960795 + 4461376 * 2 ^ 59
def prefixEnd_4461376 : Nat := 4983230072969 + 3 ^ 40 * 4461376 * 2
def baseEnd_4461376 : Nat := 763610089477747359860837

theorem tailTrace_4461376 : CollatzResearch.WordTrace tailWord_4461376 prefixEnd_4461376 763610089477747359860837 := by
  unfold tailWord_4461376
  simp only [CollatzResearch.WordTrace]
  refine ⟨81359875342602084602289991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108479833790136112803053321 81359875342602084602289991)
  ·
    refine ⟨122039813013903126903434987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81359875342602084602289991 122039813013903126903434987)
    ·
      refine ⟨183059719520854690355152481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122039813013903126903434987 183059719520854690355152481)
      ·
        refine ⟨137294789640641017766364361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183059719520854690355152481 137294789640641017766364361)
        ·
          refine ⟨102971092230480763324773271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137294789640641017766364361 102971092230480763324773271)
          ·
            refine ⟨154456638345721144987159907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102971092230480763324773271 154456638345721144987159907)
            ·
              refine ⟨231684957518581717480739861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154456638345721144987159907 231684957518581717480739861)
              ·
                refine ⟨10860232383683518006909681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 231684957518581717480739861 10860232383683518006909681)
                ·
                  refine ⟨8145174287762638505182261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10860232383683518006909681 8145174287762638505182261)
                  ·
                    refine ⟨763610089477747359860837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8145174287762638505182261 763610089477747359860837)
                    ·
                      rfl

theorem cell23_4461376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 2, 5].length) (baseStart_4461376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461376 prefixEnd_4461376 := by exact prefixLift 4461376
  have htrace : WordTrace (prefixWord ++ tailWord_4461376) baseStart_4461376 baseEnd_4461376 := by
    simpa [prefixWord, tailWord_4461376, baseEnd_4461376] using wordTrace_append hprefix tailTrace_4461376
  have hstable : (prefixWord ++ tailWord_4461376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461376).length < 2 ^ (prefixWord ++ tailWord_4461376).sum := by decide
  have hdescent : baseEnd_4461376 < baseStart_4461376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461413 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 1, 6, 2]
def baseStart_4461413 : Nat := 118140960795 + 4461413 * 2 ^ 59
def prefixEnd_4461413 : Nat := 4983230072969 + 3 ^ 40 * 4461413 * 2
def baseEnd_4461413 : Nat := 2290849267217458434819841

theorem tailTrace_4461413 : CollatzResearch.WordTrace tailWord_4461413 prefixEnd_4461413 2290849267217458434819841 := by
  unfold tailWord_4461413
  simp only [CollatzResearch.WordTrace]
  refine ⟨162721100186070124523676893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108480733457380083015784595 162721100186070124523676893)
  ·
    refine ⟨61020412569776296696378835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162721100186070124523676893 61020412569776296696378835)
    ·
      refine ⟨91530618854664445044568253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61020412569776296696378835 91530618854664445044568253)
      ·
        refine ⟨34323982070499166891713095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91530618854664445044568253 34323982070499166891713095)
        ·
          refine ⟨51485973105748750337569643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34323982070499166891713095 51485973105748750337569643)
          ·
            refine ⟨77228959658623125506354465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51485973105748750337569643 77228959658623125506354465)
            ·
              refine ⟨57921719743967344129765849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77228959658623125506354465 57921719743967344129765849)
              ·
                refine ⟨43441289807975508097324387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57921719743967344129765849 43441289807975508097324387)
                ·
                  refine ⟨65161934711963262145986581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43441289807975508097324387 65161934711963262145986581)
                  ·
                    refine ⟨3054465689623277913093121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65161934711963262145986581 3054465689623277913093121)
                    ·
                      refine ⟨2290849267217458434819841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3054465689623277913093121 2290849267217458434819841)
                      ·
                        rfl

theorem cell23_4461413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_4461413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461413 prefixEnd_4461413 := by exact prefixLift 4461413
  have htrace : WordTrace (prefixWord ++ tailWord_4461413) baseStart_4461413 baseEnd_4461413 := by
    simpa [prefixWord, tailWord_4461413, baseEnd_4461413] using wordTrace_append hprefix tailTrace_4461413
  have hstable : (prefixWord ++ tailWord_4461413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461413).length < 2 ^ (prefixWord ++ tailWord_4461413).sum := by decide
  have hdescent : baseEnd_4461413 < baseStart_4461413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461426 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_4461426 : Nat := 118140960795 + 4461426 * 2 ^ 59
def prefixEnd_4461426 : Nat := 4983230072969 + 3 ^ 40 * 4461426 * 2
def baseEnd_4461426 : Nat := 2290855942465966883957281

theorem tailTrace_4461426 : CollatzResearch.WordTrace tailWord_4461426 prefixEnd_4461426 2290855942465966883957281 := by
  unfold tailWord_4461426
  simp only [CollatzResearch.WordTrace]
  refine ⟨40680393583755756935975033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108481049556682018495933421 40680393583755756935975033)
  ·
    refine ⟨30510295187816817701981275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40680393583755756935975033 30510295187816817701981275)
    ·
      refine ⟨45765442781725226552971913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30510295187816817701981275 45765442781725226552971913)
      ·
        refine ⟨34324082086293919914728935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45765442781725226552971913 34324082086293919914728935)
        ·
          refine ⟨51486123129440879872093403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34324082086293919914728935 51486123129440879872093403)
          ·
            refine ⟨77229184694161319808140105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51486123129440879872093403 77229184694161319808140105)
            ·
              refine ⟨57921888520620989856105079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77229184694161319808140105 57921888520620989856105079)
              ·
                refine ⟨86882832780931484784157619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57921888520620989856105079 86882832780931484784157619)
                ·
                  refine ⟨130324249171397227176236429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86882832780931484784157619 130324249171397227176236429)
                  ·
                    refine ⟨48871593439273960191088661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 130324249171397227176236429 48871593439273960191088661)
                    ·
                      refine ⟨2290855942465966883957281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48871593439273960191088661 2290855942465966883957281)
                      ·
                        rfl

theorem cell23_4461426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_4461426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461426 prefixEnd_4461426 := by exact prefixLift 4461426
  have htrace : WordTrace (prefixWord ++ tailWord_4461426) baseStart_4461426 baseEnd_4461426 := by
    simpa [prefixWord, tailWord_4461426, baseEnd_4461426] using wordTrace_append hprefix tailTrace_4461426
  have hstable : (prefixWord ++ tailWord_4461426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461426).length < 2 ^ (prefixWord ++ tailWord_4461426).sum := by decide
  have hdescent : baseEnd_4461426 < baseStart_4461426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461430 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_4461430 : Nat := 118140960795 + 4461430 * 2 ^ 59
def prefixEnd_4461430 : Nat := 4983230072969 + 3 ^ 40 * 4461430 * 2
def baseEnd_4461430 : Nat := 2290857996388584868307263

theorem tailTrace_4461430 : CollatzResearch.WordTrace tailWord_4461430 prefixEnd_4461430 2290857996388584868307263 := by
  unfold tailWord_4461430
  simp only [CollatzResearch.WordTrace]
  refine ⟨10170107514188033526690359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108481146818005690951363829 10170107514188033526690359)
  ·
    refine ⟨15255161271282050290035539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10170107514188033526690359 15255161271282050290035539)
    ·
      refine ⟨22882741906923075435053309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15255161271282050290035539 22882741906923075435053309)
      ·
        refine ⟨8581028215096153288144991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22882741906923075435053309 8581028215096153288144991)
        ·
          refine ⟨12871542322644229932217487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8581028215096153288144991 12871542322644229932217487)
          ·
            refine ⟨19307313483966344898326231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12871542322644229932217487 19307313483966344898326231)
            ·
              refine ⟨28960970225949517347489347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19307313483966344898326231 28960970225949517347489347)
              ·
                refine ⟨43441455338924276021234021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28960970225949517347489347 43441455338924276021234021)
                ·
                  refine ⟨8145272876048301753981379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43441455338924276021234021 8145272876048301753981379)
                  ·
                    refine ⟨12217909314072452630972069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8145272876048301753981379 12217909314072452630972069)
                    ·
                      refine ⟨2290857996388584868307263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12217909314072452630972069 2290857996388584868307263)
                      ·
                        rfl

theorem cell23_4461430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_4461430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461430 prefixEnd_4461430 := by exact prefixLift 4461430
  have htrace : WordTrace (prefixWord ++ tailWord_4461430) baseStart_4461430 baseEnd_4461430 := by
    simpa [prefixWord, tailWord_4461430, baseEnd_4461430] using wordTrace_append hprefix tailTrace_4461430
  have hstable : (prefixWord ++ tailWord_4461430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461430).length < 2 ^ (prefixWord ++ tailWord_4461430).sum := by decide
  have hdescent : baseEnd_4461430 < baseStart_4461430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461433 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 4, 2, 3]
def baseStart_4461433 : Nat := 118140960795 + 4461433 * 2 ^ 59
def prefixEnd_4461433 : Nat := 4983230072969 + 3 ^ 40 * 4461433 * 2
def baseEnd_4461433 : Nat := 2290859536830548356569749

theorem tailTrace_4461433 : CollatzResearch.WordTrace tailWord_4461433 prefixEnd_4461433 2290859536830548356569749 := by
  unfold tailWord_4461433
  simp only [CollatzResearch.WordTrace]
  refine ⟨162721829645997667939404953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108481219763998445292936635 162721829645997667939404953)
  ·
    refine ⟨122041372234498250954553715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162721829645997667939404953 122041372234498250954553715)
    ·
      refine ⟨183062058351747376431830573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122041372234498250954553715 183062058351747376431830573)
      ·
        refine ⟨68648271881905266161936465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183062058351747376431830573 68648271881905266161936465)
        ·
          refine ⟨51486203911428949621452349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68648271881905266161936465 51486203911428949621452349)
          ·
            refine ⟨19307326466785856108044631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51486203911428949621452349 19307326466785856108044631)
            ·
              refine ⟨28960989700178784162066947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19307326466785856108044631 28960989700178784162066947)
              ·
                refine ⟨43441484550268176243100421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28960989700178784162066947 43441484550268176243100421)
                ·
                  refine ⟨8145278353175283045581329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43441484550268176243100421 8145278353175283045581329)
                  ·
                    refine ⟨6108958764881462284185997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8145278353175283045581329 6108958764881462284185997)
                    ·
                      refine ⟨2290859536830548356569749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6108958764881462284185997 2290859536830548356569749)
                      ·
                        rfl

theorem cell23_4461433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_4461433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461433 prefixEnd_4461433 := by exact prefixLift 4461433
  have htrace : WordTrace (prefixWord ++ tailWord_4461433) baseStart_4461433 baseEnd_4461433 := by
    simpa [prefixWord, tailWord_4461433, baseEnd_4461433] using wordTrace_append hprefix tailTrace_4461433
  have hstable : (prefixWord ++ tailWord_4461433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461433).length < 2 ^ (prefixWord ++ tailWord_4461433).sum := by decide
  have hdescent : baseEnd_4461433 < baseStart_4461433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461524 : List Nat := [2, 4, 1, 2, 1, 4, 1, 1, 2, 3, 2]
def baseStart_4461524 : Nat := 118140960795 + 4461524 * 2 ^ 59
def prefixEnd_4461524 : Nat := 4983230072969 + 3 ^ 40 * 4461524 * 2
def baseEnd_4461524 : Nat := 2290906263570107500531831

theorem tailTrace_4461524 : CollatzResearch.WordTrace tailWord_4461524 prefixEnd_4461524 2290906263570107500531831 := by
  unfold tailWord_4461524
  simp only [CollatzResearch.WordTrace]
  refine ⟨81362574344333995240483813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108483432459111993653978417 81362574344333995240483813)
  ·
    refine ⟨15255482689562624107590715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81362574344333995240483813 15255482689562624107590715)
    ·
      refine ⟨22883224034343936161386073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15255482689562624107590715 22883224034343936161386073)
      ·
        refine ⟨17162418025757952121039555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22883224034343936161386073 17162418025757952121039555)
        ·
          refine ⟨25743627038636928181559333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17162418025757952121039555 25743627038636928181559333)
          ·
            refine ⟨4826930069744424034042375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25743627038636928181559333 4826930069744424034042375)
            ·
              refine ⟨7240395104616636051063563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4826930069744424034042375 7240395104616636051063563)
              ·
                refine ⟨10860592656924954076595345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7240395104616636051063563 10860592656924954076595345)
                ·
                  refine ⟨8145444492693715557446509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10860592656924954076595345 8145444492693715557446509)
                  ·
                    refine ⟨3054541684760143334042441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8145444492693715557446509 3054541684760143334042441)
                    ·
                      refine ⟨2290906263570107500531831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3054541684760143334042441 2290906263570107500531831)
                      ·
                        rfl

theorem cell23_4461524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_4461524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461524 prefixEnd_4461524 := by exact prefixLift 4461524
  have htrace : WordTrace (prefixWord ++ tailWord_4461524) baseStart_4461524 baseEnd_4461524 := by
    simpa [prefixWord, tailWord_4461524, baseEnd_4461524] using wordTrace_append hprefix tailTrace_4461524
  have hstable : (prefixWord ++ tailWord_4461524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461524).length < 2 ^ (prefixWord ++ tailWord_4461524).sum := by decide
  have hdescent : baseEnd_4461524 < baseStart_4461524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461543 : List Nat := [1, 1, 5, 2, 2, 2, 10]
def baseStart_4461543 : Nat := 118140960795 + 4461543 * 2 ^ 59
def prefixEnd_4461543 : Nat := 4983230072969 + 3 ^ 40 * 4461543 * 2
def baseEnd_4461543 : Nat := 28282913823488184274003

theorem tailTrace_4461543 : CollatzResearch.WordTrace tailWord_4461543 prefixEnd_4461543 28282913823488184274003 := by
  unfold tailWord_4461543
  simp only [CollatzResearch.WordTrace]
  refine ⟨162725841675599156725909283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108483894450399437817272855 162725841675599156725909283)
  ·
    refine ⟨244088762513398735088863925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162725841675599156725909283 244088762513398735088863925)
    ·
      refine ⟨22883321485631131414580993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 244088762513398735088863925 22883321485631131414580993)
      ·
        refine ⟨17162491114223348560935745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22883321485631131414580993 17162491114223348560935745)
        ·
          refine ⟨12871868335667511420701809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17162491114223348560935745 12871868335667511420701809)
          ·
            refine ⟨9653901251750633565526357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12871868335667511420701809 9653901251750633565526357)
            ·
              refine ⟨28282913823488184274003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9653901251750633565526357 28282913823488184274003)
              ·
                rfl

theorem cell23_4461543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 10].length) (baseStart_4461543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461543 prefixEnd_4461543 := by exact prefixLift 4461543
  have htrace : WordTrace (prefixWord ++ tailWord_4461543) baseStart_4461543 baseEnd_4461543 := by
    simpa [prefixWord, tailWord_4461543, baseEnd_4461543] using wordTrace_append hprefix tailTrace_4461543
  have hstable : (prefixWord ++ tailWord_4461543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461543).length < 2 ^ (prefixWord ++ tailWord_4461543).sum := by decide
  have hdescent : baseEnd_4461543 < baseStart_4461543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461623 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 4]
def baseStart_4461623 : Nat := 118140960795 + 4461623 * 2 ^ 59
def prefixEnd_4461623 : Nat := 4983230072969 + 3 ^ 40 * 4461623 * 2
def baseEnd_4461623 : Nat := 2290957098154902613193875

theorem tailTrace_4461623 : CollatzResearch.WordTrace tailWord_4461623 prefixEnd_4461623 2290957098154902613193875 := by
  unfold tailWord_4461623
  simp only [CollatzResearch.WordTrace]
  refine ⟨162728759515309330388821523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108485839676872886925881015 162728759515309330388821523)
  ·
    refine ⟨244093139272963995583232285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162728759515309330388821523 244093139272963995583232285)
    ·
      refine ⟨91534927227361498343712107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244093139272963995583232285 91534927227361498343712107)
      ·
        refine ⟨137302390841042247515568161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91534927227361498343712107 137302390841042247515568161)
        ·
          refine ⟨102976793130781685636676121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137302390841042247515568161 102976793130781685636676121)
          ·
            refine ⟨77232594848086264227507091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102976793130781685636676121 77232594848086264227507091)
            ·
              refine ⟨115848892272129396341260637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77232594848086264227507091 115848892272129396341260637)
              ·
                refine ⟨43443334602048523627972739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115848892272129396341260637 43443334602048523627972739)
                ·
                  refine ⟨65165001903072785441959109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43443334602048523627972739 65165001903072785441959109)
                  ·
                    refine ⟨12218437856826147270367333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65165001903072785441959109 12218437856826147270367333)
                    ·
                      refine ⟨2290957098154902613193875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12218437856826147270367333 2290957098154902613193875)
                      ·
                        rfl

theorem cell23_4461623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_4461623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461623 prefixEnd_4461623 := by exact prefixLift 4461623
  have htrace : WordTrace (prefixWord ++ tailWord_4461623) baseStart_4461623 baseEnd_4461623 := by
    simpa [prefixWord, tailWord_4461623, baseEnd_4461623] using wordTrace_append hprefix tailTrace_4461623
  have hstable : (prefixWord ++ tailWord_4461623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461623).length < 2 ^ (prefixWord ++ tailWord_4461623).sum := by decide
  have hdescent : baseEnd_4461623 < baseStart_4461623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461677 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 2, 3, 3]
def baseStart_4461677 : Nat := 118140960795 + 4461677 * 2 ^ 59
def prefixEnd_4461677 : Nat := 4983230072969 + 3 ^ 40 * 4461677 * 2
def baseEnd_4461677 : Nat := 2290984826110245401918627

theorem tailTrace_4461677 : CollatzResearch.WordTrace tailWord_4461677 prefixEnd_4461677 2290984826110245401918627 := by
  unfold tailWord_4461677
  simp only [CollatzResearch.WordTrace]
  refine ⟨162730729057113697611287285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108487152704742465074191523 162730729057113697611287285)
  ·
    refine ⟨15256005849104409151058183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 162730729057113697611287285 15256005849104409151058183)
    ·
      refine ⟨22884008773656613726587275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15256005849104409151058183 22884008773656613726587275)
      ·
        refine ⟨34326013160484920589880913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22884008773656613726587275 34326013160484920589880913)
        ·
          refine ⟨25744509870363690442410685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34326013160484920589880913 25744509870363690442410685)
          ·
            refine ⟨9654191201386383915904007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25744509870363690442410685 9654191201386383915904007)
            ·
              refine ⟨14481286802079575873856011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9654191201386383915904007 14481286802079575873856011)
              ·
                refine ⟨21721930203119363810784017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14481286802079575873856011 21721930203119363810784017)
                ·
                  refine ⟨16291447652339522858088013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21721930203119363810784017 16291447652339522858088013)
                  ·
                    refine ⟨6109292869627321071783005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16291447652339522858088013 6109292869627321071783005)
                    ·
                      refine ⟨2290984826110245401918627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6109292869627321071783005 2290984826110245401918627)
                      ·
                        rfl

theorem cell23_4461677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_4461677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461677 prefixEnd_4461677 := by exact prefixLift 4461677
  have htrace : WordTrace (prefixWord ++ tailWord_4461677) baseStart_4461677 baseEnd_4461677 := by
    simpa [prefixWord, tailWord_4461677, baseEnd_4461677] using wordTrace_append hprefix tailTrace_4461677
  have hstable : (prefixWord ++ tailWord_4461677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461677).length < 2 ^ (prefixWord ++ tailWord_4461677).sum := by decide
  have hdescent : baseEnd_4461677 < baseStart_4461677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461697 : List Nat := [1, 2, 4, 2, 2, 1, 3, 1, 2, 5]
def baseStart_4461697 : Nat := 118140960795 + 4461697 * 2 ^ 59
def prefixEnd_4461697 : Nat := 4983230072969 + 3 ^ 40 * 4461697 * 2
def baseEnd_4461697 : Nat := 763665031907778441222845

theorem tailTrace_4461697 : CollatzResearch.WordTrace tailWord_4461697 prefixEnd_4461697 763665031907778441222845 := by
  unfold tailWord_4461697
  simp only [CollatzResearch.WordTrace]
  refine ⟨162731458517041241027015345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108487639011360827351343563 162731458517041241027015345)
  ·
    refine ⟨122048593887780930770261509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162731458517041241027015345 122048593887780930770261509)
    ·
      refine ⟨22884111353958924519424033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122048593887780930770261509 22884111353958924519424033)
      ·
        refine ⟨17163083515469193389568025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22884111353958924519424033 17163083515469193389568025)
        ·
          refine ⟨12872312636601895042176019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17163083515469193389568025 12872312636601895042176019)
          ·
            refine ⟨19308468954902842563264029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12872312636601895042176019 19308468954902842563264029)
            ·
              refine ⟨7240675858088565961224011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19308468954902842563264029 7240675858088565961224011)
              ·
                refine ⟨10861013787132848941836017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7240675858088565961224011 10861013787132848941836017)
                ·
                  refine ⟨8145760340349636706377013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10861013787132848941836017 8145760340349636706377013)
                  ·
                    refine ⟨763665031907778441222845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8145760340349636706377013 763665031907778441222845)
                    ·
                      rfl

theorem cell23_4461697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_4461697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461697 prefixEnd_4461697 := by exact prefixLift 4461697
  have htrace : WordTrace (prefixWord ++ tailWord_4461697) baseStart_4461697 baseEnd_4461697 := by
    simpa [prefixWord, tailWord_4461697, baseEnd_4461697] using wordTrace_append hprefix tailTrace_4461697
  have hstable : (prefixWord ++ tailWord_4461697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461697).length < 2 ^ (prefixWord ++ tailWord_4461697).sum := by decide
  have hdescent : baseEnd_4461697 < baseStart_4461697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461767 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 5, 1, 3]
def baseStart_4461767 : Nat := 118140960795 + 4461767 * 2 ^ 59
def prefixEnd_4461767 : Nat := 4983230072969 + 3 ^ 40 * 4461767 * 2
def baseEnd_4461767 : Nat := 2291031039369150049793213

theorem tailTrace_4461767 : CollatzResearch.WordTrace tailWord_4461767 prefixEnd_4461767 2291031039369150049793213 := by
  unfold tailWord_4461767
  simp only [CollatzResearch.WordTrace]
  refine ⟨162734011626787642982063555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108489341084525095321375703 162734011626787642982063555)
  ·
    refine ⟨244101017440181464473095333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162734011626787642982063555 244101017440181464473095333)
    ·
      refine ⟨45768940770034024588705375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 244101017440181464473095333 45768940770034024588705375)
      ·
        refine ⟨68653411155051036883058063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45768940770034024588705375 68653411155051036883058063)
        ·
          refine ⟨102980116732576555324587095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68653411155051036883058063 102980116732576555324587095)
          ·
            refine ⟨154470175098864832986880643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102980116732576555324587095 154470175098864832986880643)
            ·
              refine ⟨231705262648297249480320965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154470175098864832986880643 231705262648297249480320965)
              ·
                refine ⟨43444736746555734277560181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 231705262648297249480320965 43444736746555734277560181)
                ·
                  refine ⟨4072944069989600088521267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43444736746555734277560181 4072944069989600088521267)
                  ·
                    refine ⟨6109416104984400132781901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4072944069989600088521267 6109416104984400132781901)
                    ·
                      refine ⟨2291031039369150049793213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6109416104984400132781901 2291031039369150049793213)
                      ·
                        rfl

theorem cell23_4461767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_4461767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461767 prefixEnd_4461767 := by exact prefixLift 4461767
  have htrace : WordTrace (prefixWord ++ tailWord_4461767) baseStart_4461767 baseEnd_4461767 := by
    simpa [prefixWord, tailWord_4461767, baseEnd_4461767] using wordTrace_append hprefix tailTrace_4461767
  have hstable : (prefixWord ++ tailWord_4461767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461767).length < 2 ^ (prefixWord ++ tailWord_4461767).sum := by decide
  have hdescent : baseEnd_4461767 < baseStart_4461767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461804 : List Nat := [2, 2, 1, 1, 2, 6, 1, 2, 1, 5]
def baseStart_4461804 : Nat := 118140960795 + 4461804 * 2 ^ 59
def prefixEnd_4461804 : Nat := 4983230072969 + 3 ^ 40 * 4461804 * 2
def baseEnd_4461804 : Nat := 763683346051122135010181

theorem tailTrace_4461804 : CollatzResearch.WordTrace tailWord_4461804 prefixEnd_4461804 763683346051122135010181 := by
  unfold tailWord_4461804
  simp only [CollatzResearch.WordTrace]
  refine ⟨81367680563826799150580233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108490240751769065534106977 81367680563826799150580233)
  ·
    refine ⟨61025760422870099362935175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81367680563826799150580233 61025760422870099362935175)
    ·
      refine ⟨91538640634305149044402763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61025760422870099362935175 91538640634305149044402763)
      ·
        refine ⟨137307960951457723566604145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91538640634305149044402763 137307960951457723566604145)
        ·
          refine ⟨102980970713593292674953109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137307960951457723566604145 102980970713593292674953109)
          ·
            refine ⟨4827233002199685594138427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 102980970713593292674953109 4827233002199685594138427)
            ·
              refine ⟨7240849503299528391207641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4827233002199685594138427 7240849503299528391207641)
              ·
                refine ⟨5430637127474646293405731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7240849503299528391207641 5430637127474646293405731)
                ·
                  refine ⟨8145955691211969440108597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5430637127474646293405731 8145955691211969440108597)
                  ·
                    refine ⟨763683346051122135010181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8145955691211969440108597 763683346051122135010181)
                    ·
                      rfl

theorem cell23_4461804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 5].length) (baseStart_4461804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461804 prefixEnd_4461804 := by exact prefixLift 4461804
  have htrace : WordTrace (prefixWord ++ tailWord_4461804) baseStart_4461804 baseEnd_4461804 := by
    simpa [prefixWord, tailWord_4461804, baseEnd_4461804] using wordTrace_append hprefix tailTrace_4461804
  have hstable : (prefixWord ++ tailWord_4461804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461804).length < 2 ^ (prefixWord ++ tailWord_4461804).sum := by decide
  have hdescent : baseEnd_4461804 < baseStart_4461804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461827 : List Nat := [1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 5]
def baseStart_4461827 : Nat := 118140960795 + 4461827 * 2 ^ 59
def prefixEnd_4461827 : Nat := 4983230072969 + 3 ^ 40 * 4461827 * 2
def baseEnd_4461827 : Nat := 2291061848208419815042937

theorem tailTrace_4461827 : CollatzResearch.WordTrace tailWord_4461827 prefixEnd_4461827 2291061848208419815042937 := by
  unfold tailWord_4461827
  simp only [CollatzResearch.WordTrace]
  refine ⟨162736200006570273229247735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108490800004380182152831823 162736200006570273229247735)
  ·
    refine ⟨244104300009855409843871603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162736200006570273229247735 244104300009855409843871603)
    ·
      refine ⟨366156450014783114765807405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244104300009855409843871603 366156450014783114765807405)
      ·
        refine ⟨137308668755543668037177777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 366156450014783114765807405 137308668755543668037177777)
        ·
          refine ⟨102981501566657751027883333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137308668755543668037177777 102981501566657751027883333)
          ·
            refine ⟨19309031543748328317728125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102981501566657751027883333 19309031543748328317728125)
            ·
              refine ⟨7240886828905623119148047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19309031543748328317728125 7240886828905623119148047)
              ·
                refine ⟨10861330243358434678722071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7240886828905623119148047 10861330243358434678722071)
                ·
                  refine ⟨16291995365037652018083107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10861330243358434678722071 16291995365037652018083107)
                  ·
                    refine ⟨24437993047556478027124661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16291995365037652018083107 24437993047556478027124661)
                    ·
                      refine ⟨2291061848208419815042937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24437993047556478027124661 2291061848208419815042937)
                      ·
                        rfl

theorem cell23_4461827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 5].length) (baseStart_4461827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461827 prefixEnd_4461827 := by exact prefixLift 4461827
  have htrace : WordTrace (prefixWord ++ tailWord_4461827) baseStart_4461827 baseEnd_4461827 := by
    simpa [prefixWord, tailWord_4461827, baseEnd_4461827] using wordTrace_append hprefix tailTrace_4461827
  have hstable : (prefixWord ++ tailWord_4461827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461827).length < 2 ^ (prefixWord ++ tailWord_4461827).sum := by decide
  have hdescent : baseEnd_4461827 < baseStart_4461827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461858 : List Nat := [3, 3, 1, 1, 4, 1, 1, 2, 3, 2, 2]
def baseStart_4461858 : Nat := 118140960795 + 4461858 * 2 ^ 59
def prefixEnd_4461858 : Nat := 4983230072969 + 3 ^ 40 * 4461858 * 2
def baseEnd_4461858 : Nat := 2291077766108709193755295

theorem tailTrace_4461858 : CollatzResearch.WordTrace tailWord_4461858 prefixEnd_4461858 2291077766108709193755295 := by
  unfold tailWord_4461858
  simp only [CollatzResearch.WordTrace]
  refine ⟨40684332667364491380906557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108491553779638643682417485 40684332667364491380906557)
  ·
    refine ⟨15256624750261684267839959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40684332667364491380906557 15256624750261684267839959)
    ·
      refine ⟨22884937125392526401759939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15256624750261684267839959 22884937125392526401759939)
      ·
        refine ⟨34327405688088789602639909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22884937125392526401759939 34327405688088789602639909)
        ·
          refine ⟨6436388566516648050494983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34327405688088789602639909 6436388566516648050494983)
          ·
            refine ⟨9654582849774972075742475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6436388566516648050494983 9654582849774972075742475)
            ·
              refine ⟨14481874274662458113613713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9654582849774972075742475 14481874274662458113613713)
              ·
                refine ⟨10861405705996843585210285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14481874274662458113613713 10861405705996843585210285)
                ·
                  refine ⟨4073027139748816344453857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10861405705996843585210285 4073027139748816344453857)
                  ·
                    refine ⟨3054770354811612258340393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4073027139748816344453857 3054770354811612258340393)
                    ·
                      refine ⟨2291077766108709193755295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3054770354811612258340393 2291077766108709193755295)
                      ·
                        rfl

theorem cell23_4461858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_4461858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461858 prefixEnd_4461858 := by exact prefixLift 4461858
  have htrace : WordTrace (prefixWord ++ tailWord_4461858) baseStart_4461858 baseEnd_4461858 := by
    simpa [prefixWord, tailWord_4461858, baseEnd_4461858] using wordTrace_append hprefix tailTrace_4461858
  have hstable : (prefixWord ++ tailWord_4461858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461858).length < 2 ^ (prefixWord ++ tailWord_4461858).sum := by decide
  have hdescent : baseEnd_4461858 < baseStart_4461858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461864 : List Nat := [2, 1, 5, 1, 2, 2, 3, 7]
def baseStart_4461864 : Nat := 118140960795 + 4461864 * 2 ^ 59
def prefixEnd_4461864 : Nat := 4983230072969 + 3 ^ 40 * 4461864 * 2
def baseEnd_4461864 : Nat := 84854846184912450751121

theorem tailTrace_4461864 : CollatzResearch.WordTrace tailWord_4461864 prefixEnd_4461864 84854846184912450751121 := by
  unfold tailWord_4461864
  simp only [CollatzResearch.WordTrace]
  refine ⟨81368774753718114274172323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108491699671624152365563097 81368774753718114274172323)
  ·
    refine ⟨122053162130577171411258485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81368774753718114274172323 122053162130577171411258485)
    ·
      refine ⟨11442483949741609819805483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122053162130577171411258485 11442483949741609819805483)
      ·
        refine ⟨17163725924612414729708225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11442483949741609819805483 17163725924612414729708225)
        ·
          refine ⟨12872794443459311047281169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17163725924612414729708225 12872794443459311047281169)
          ·
            refine ⟨9654595832594483285460877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12872794443459311047281169 9654595832594483285460877)
            ·
              refine ⟨3620473437222931232047829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9654595832594483285460877 3620473437222931232047829)
              ·
                refine ⟨84854846184912450751121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3620473437222931232047829 84854846184912450751121)
                ·
                  rfl

theorem cell23_4461864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 7].length) (baseStart_4461864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461864 prefixEnd_4461864 := by exact prefixLift 4461864
  have htrace : WordTrace (prefixWord ++ tailWord_4461864) baseStart_4461864 baseEnd_4461864 := by
    simpa [prefixWord, tailWord_4461864, baseEnd_4461864] using wordTrace_append hprefix tailTrace_4461864
  have hstable : (prefixWord ++ tailWord_4461864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461864).length < 2 ^ (prefixWord ++ tailWord_4461864).sum := by decide
  have hdescent : baseEnd_4461864 < baseStart_4461864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461867 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 4, 7, 2]
def baseStart_4461867 : Nat := 118140960795 + 4461867 * 2 ^ 59
def prefixEnd_4461867 : Nat := 4983230072969 + 3 ^ 40 * 4461867 * 2
def baseEnd_4461867 : Nat := 2291082387434599658542753

theorem tailTrace_4461867 : CollatzResearch.WordTrace tailWord_4461867 prefixEnd_4461867 2291082387434599658542753 := by
  unfold tailWord_4461867
  simp only [CollatzResearch.WordTrace]
  refine ⟨162737658926425360060703855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108491772617616906707135903 162737658926425360060703855)
  ·
    refine ⟨244106488389638040091055783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162737658926425360060703855 244106488389638040091055783)
    ·
      refine ⟨366159732584457060136583675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244106488389638040091055783 366159732584457060136583675)
      ·
        refine ⟨549239598876685590204875513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366159732584457060136583675 549239598876685590204875513)
        ·
          refine ⟨411929699157514192653656635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 549239598876685590204875513 411929699157514192653656635)
          ·
            refine ⟨617894548736271288980484953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 411929699157514192653656635 617894548736271288980484953)
            ·
              refine ⟨463420911552203466735363715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 617894548736271288980484953 463420911552203466735363715)
              ·
                refine ⟨695131367328305200103045573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463420911552203466735363715 695131367328305200103045573)
                ·
                  refine ⟨130337131374057225019321045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 695131367328305200103045573 130337131374057225019321045)
                  ·
                    refine ⟨3054776516579466211390337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 130337131374057225019321045 3054776516579466211390337)
                    ·
                      refine ⟨2291082387434599658542753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3054776516579466211390337 2291082387434599658542753)
                      ·
                        rfl

theorem cell23_4461867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 7, 2].length) (baseStart_4461867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461867 prefixEnd_4461867 := by exact prefixLift 4461867
  have htrace : WordTrace (prefixWord ++ tailWord_4461867) baseStart_4461867 baseEnd_4461867 := by
    simpa [prefixWord, tailWord_4461867, baseEnd_4461867] using wordTrace_append hprefix tailTrace_4461867
  have hstable : (prefixWord ++ tailWord_4461867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461867).length < 2 ^ (prefixWord ++ tailWord_4461867).sum := by decide
  have hdescent : baseEnd_4461867 < baseStart_4461867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461874 : List Nat := [3, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3]
def baseStart_4461874 : Nat := 118140960795 + 4461874 * 2 ^ 59
def prefixEnd_4461874 : Nat := 4983230072969 + 3 ^ 40 * 4461874 * 2
def baseEnd_4461874 : Nat := 2291085981799181131155221

theorem tailTrace_4461874 : CollatzResearch.WordTrace tailWord_4461874 prefixEnd_4461874 2291085981799181131155221 := by
  unfold tailWord_4461874
  simp only [CollatzResearch.WordTrace]
  refine ⟨40684478559350000064052169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108491942824933333504139117 40684478559350000064052169)
  ·
    refine ⟨30513358919512500048039127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40684478559350000064052169 30513358919512500048039127)
    ·
      refine ⟨45770038379268750072058691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30513358919512500048039127 45770038379268750072058691)
      ·
        refine ⟨68655057568903125108088037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45770038379268750072058691 68655057568903125108088037)
        ·
          refine ⟨12872823294169335957766507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68655057568903125108088037 12872823294169335957766507)
          ·
            refine ⟨19309234941254003936649761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12872823294169335957766507 19309234941254003936649761)
            ·
              refine ⟨14481926205940502952487321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19309234941254003936649761 14481926205940502952487321)
              ·
                refine ⟨10861444654455377214365491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14481926205940502952487321 10861444654455377214365491)
                ·
                  refine ⟨16292166981683065821548237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10861444654455377214365491 16292166981683065821548237)
                  ·
                    refine ⟨6109562618131149683080589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16292166981683065821548237 6109562618131149683080589)
                    ·
                      refine ⟨2291085981799181131155221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6109562618131149683080589 2291085981799181131155221)
                      ·
                        rfl

theorem cell23_4461874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_4461874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461874 prefixEnd_4461874 := by exact prefixLift 4461874
  have htrace : WordTrace (prefixWord ++ tailWord_4461874) baseStart_4461874 baseEnd_4461874 := by
    simpa [prefixWord, tailWord_4461874, baseEnd_4461874] using wordTrace_append hprefix tailTrace_4461874
  have hstable : (prefixWord ++ tailWord_4461874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461874).length < 2 ^ (prefixWord ++ tailWord_4461874).sum := by decide
  have hdescent : baseEnd_4461874 < baseStart_4461874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461885 : List Nat := [1, 4, 1, 5, 2, 1, 1, 2, 2, 4]
def baseStart_4461885 : Nat := 118140960795 + 4461885 * 2 ^ 59
def prefixEnd_4461885 : Nat := 4983230072969 + 3 ^ 40 * 4461885 * 2
def baseEnd_4461885 : Nat := 763697210028793529372557

theorem tailTrace_4461885 : CollatzResearch.WordTrace tailWord_4461885 prefixEnd_4461885 763697210028793529372557 := by
  unfold tailWord_4461885
  simp only [CollatzResearch.WordTrace]
  refine ⟨162738315440360149134859109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108492210293573432756572739 162738315440360149134859109)
  ·
    refine ⟨30513434145067527962786083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162738315440360149134859109 30513434145067527962786083)
    ·
      refine ⟨45770151217601291944179125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30513434145067527962786083 45770151217601291944179125)
      ·
        refine ⟨4290951676650121119766793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45770151217601291944179125 4290951676650121119766793)
        ·
          refine ⟨3218213757487590839825095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4290951676650121119766793 3218213757487590839825095)
          ·
            refine ⟨4827320636231386259737643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3218213757487590839825095 4827320636231386259737643)
            ·
              refine ⟨7240980954347079389606465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4827320636231386259737643 7240980954347079389606465)
              ·
                refine ⟨5430735715760309542204849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7240980954347079389606465 5430735715760309542204849)
                ·
                  refine ⟨4073051786820232156653637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5430735715760309542204849 4073051786820232156653637)
                  ·
                    refine ⟨763697210028793529372557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4073051786820232156653637 763697210028793529372557)
                    ·
                      rfl

theorem cell23_4461885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_4461885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461885 prefixEnd_4461885 := by exact prefixLift 4461885
  have htrace : WordTrace (prefixWord ++ tailWord_4461885) baseStart_4461885 baseEnd_4461885 := by
    simpa [prefixWord, tailWord_4461885, baseEnd_4461885] using wordTrace_append hprefix tailTrace_4461885
  have hstable : (prefixWord ++ tailWord_4461885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461885).length < 2 ^ (prefixWord ++ tailWord_4461885).sum := by decide
  have hdescent : baseEnd_4461885 < baseStart_4461885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461908 : List Nat := [2, 4, 1, 1, 2, 1, 5, 1, 2, 1, 3]
def baseStart_4461908 : Nat := 118140960795 + 4461908 * 2 ^ 59
def prefixEnd_4461908 : Nat := 4983230072969 + 3 ^ 40 * 4461908 * 2
def baseEnd_4461908 : Nat := 2291103440141433998130065

theorem tailTrace_4461908 : CollatzResearch.WordTrace tailWord_4461908 prefixEnd_4461908 2291103440141433998130065 := by
  unfold tailWord_4461908
  simp only [CollatzResearch.WordTrace]
  refine ⟨81369577159638412031473189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108492769546184549375297585 81369577159638412031473189)
  ·
    refine ⟨15256795717432202255901223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81369577159638412031473189 15256795717432202255901223)
    ·
      refine ⟨22885193576148303383851835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15256795717432202255901223 22885193576148303383851835)
      ·
        refine ⟨34327790364222455075777753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22885193576148303383851835 34327790364222455075777753)
        ·
          refine ⟨25745842773166841306833315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34327790364222455075777753 25745842773166841306833315)
          ·
            refine ⟨38618764159750261960249973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25745842773166841306833315 38618764159750261960249973)
            ·
              refine ⟨3620509139976587058773435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38618764159750261960249973 3620509139976587058773435)
              ·
                refine ⟨5430763709964880588160153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3620509139976587058773435 5430763709964880588160153)
                ·
                  refine ⟨4073072782473660441120115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5430763709964880588160153 4073072782473660441120115)
                  ·
                    refine ⟨6109609173710490661680173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4073072782473660441120115 6109609173710490661680173)
                    ·
                      refine ⟨2291103440141433998130065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6109609173710490661680173 2291103440141433998130065)
                      ·
                        rfl

theorem cell23_4461908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_4461908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461908 prefixEnd_4461908 := by exact prefixLift 4461908
  have htrace : WordTrace (prefixWord ++ tailWord_4461908) baseStart_4461908 baseEnd_4461908 := by
    simpa [prefixWord, tailWord_4461908, baseEnd_4461908] using wordTrace_append hprefix tailTrace_4461908
  have hstable : (prefixWord ++ tailWord_4461908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461908).length < 2 ^ (prefixWord ++ tailWord_4461908).sum := by decide
  have hdescent : baseEnd_4461908 < baseStart_4461908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4461984 : List Nat := [2, 1, 1, 4, 1, 2, 4, 1, 2, 5]
def baseStart_4461984 : Nat := 118140960795 + 4461984 * 2 ^ 59
def prefixEnd_4461984 : Nat := 4983230072969 + 3 ^ 40 * 4461984 * 2
def baseEnd_4461984 : Nat := 763714154890391900259905

theorem tailTrace_4461984 : CollatzResearch.WordTrace tailWord_4461984 prefixEnd_4461984 763714154890391900259905 := by
  unfold tailWord_4461984
  simp only [CollatzResearch.WordTrace]
  refine ⟨81370963133500744521356503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108494617511334326028475337 81370963133500744521356503)
  ·
    refine ⟨122056444700251116782034755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81370963133500744521356503 122056444700251116782034755)
    ·
      refine ⟨183084667050376675173052133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122056444700251116782034755 183084667050376675173052133)
      ·
        refine ⟨34328375071945626594947275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183084667050376675173052133 34328375071945626594947275)
        ·
          refine ⟨51492562607918439892420913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34328375071945626594947275 51492562607918439892420913)
          ·
            refine ⟨38619421955938829919315685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51492562607918439892420913 38619421955938829919315685)
            ·
              refine ⟨7241141616738530609871691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38619421955938829919315685 7241141616738530609871691)
              ·
                refine ⟨10861712425107795914807537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7241141616738530609871691 10861712425107795914807537)
                ·
                  refine ⟨8146284318830846936105653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10861712425107795914807537 8146284318830846936105653)
                  ·
                    refine ⟨763714154890391900259905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8146284318830846936105653 763714154890391900259905)
                    ·
                      rfl

theorem cell23_4461984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 2, 5].length) (baseStart_4461984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4461984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4461984 prefixEnd_4461984 := by exact prefixLift 4461984
  have htrace : WordTrace (prefixWord ++ tailWord_4461984) baseStart_4461984 baseEnd_4461984 := by
    simpa [prefixWord, tailWord_4461984, baseEnd_4461984] using wordTrace_append hprefix tailTrace_4461984
  have hstable : (prefixWord ++ tailWord_4461984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4461984).length < 2 ^ (prefixWord ++ tailWord_4461984).sum := by decide
  have hdescent : baseEnd_4461984 < baseStart_4461984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4461984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462007 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 5]
def baseStart_4462007 : Nat := 118140960795 + 4462007 * 2 ^ 59
def prefixEnd_4462007 : Nat := 4983230072969 + 3 ^ 40 * 4462007 * 2
def baseEnd_4462007 : Nat := 2291154274726229110792109

theorem tailTrace_4462007 : CollatzResearch.WordTrace tailWord_4462007 prefixEnd_4462007 2291154274726229110792109 := by
  unfold tailWord_4462007
  simp only [CollatzResearch.WordTrace]
  refine ⟨162742765145918163970800275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108495176763945442647200183 162742765145918163970800275)
  ·
    refine ⟨244114147718877245956200413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162742765145918163970800275 244114147718877245956200413)
    ·
      refine ⟨91542805394578967233575155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244114147718877245956200413 91542805394578967233575155)
      ·
        refine ⟨137314208091868450850362733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91542805394578967233575155 137314208091868450850362733)
        ·
          refine ⟨51492828034450669068886025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137314208091868450850362733 51492828034450669068886025)
          ·
            refine ⟨38619621025838001801664519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51492828034450669068886025 38619621025838001801664519)
            ·
              refine ⟨57929431538757002702496779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38619621025838001801664519 57929431538757002702496779)
              ·
                refine ⟨86894147308135504053745169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57929431538757002702496779 86894147308135504053745169)
                ·
                  refine ⟨65170610481101628040308877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86894147308135504053745169 65170610481101628040308877)
                  ·
                    refine ⟨24438978930413110515115829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65170610481101628040308877 24438978930413110515115829)
                    ·
                      refine ⟨2291154274726229110792109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24438978930413110515115829 2291154274726229110792109)
                      ·
                        rfl

theorem cell23_4462007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_4462007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462007 prefixEnd_4462007 := by exact prefixLift 4462007
  have htrace : WordTrace (prefixWord ++ tailWord_4462007) baseStart_4462007 baseEnd_4462007 := by
    simpa [prefixWord, tailWord_4462007, baseEnd_4462007] using wordTrace_append hprefix tailTrace_4462007
  have hstable : (prefixWord ++ tailWord_4462007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462007).length < 2 ^ (prefixWord ++ tailWord_4462007).sum := by decide
  have hdescent : baseEnd_4462007 < baseStart_4462007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462024 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 1, 4, 3]
def baseStart_4462024 : Nat := 118140960795 + 4462024 * 2 ^ 59
def prefixEnd_4462024 : Nat := 4983230072969 + 3 ^ 40 * 4462024 * 2
def baseEnd_4462024 : Nat := 2291163003897355544279531

theorem tailTrace_4462024 : CollatzResearch.WordTrace tailWord_4462024 prefixEnd_4462024 2291163003897355544279531 := by
  unfold tailWord_4462024
  simp only [CollatzResearch.WordTrace]
  refine ⟨81371692593428287937084563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108495590124571050582779417 81371692593428287937084563)
  ·
    refine ⟨122057538890142431905626845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81371692593428287937084563 122057538890142431905626845)
    ·
      refine ⟨45771577083803411964610067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122057538890142431905626845 45771577083803411964610067)
      ·
        refine ⟨68657365625705117946915101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45771577083803411964610067 68657365625705117946915101)
        ·
          refine ⟨25746512109639419230093163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68657365625705117946915101 25746512109639419230093163)
          ·
            refine ⟨38619768164459128845139745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25746512109639419230093163 38619768164459128845139745)
            ·
              refine ⟨28964826123344346633854809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38619768164459128845139745 28964826123344346633854809)
              ·
                refine ⟨21723619592508259975391107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28964826123344346633854809 21723619592508259975391107)
                ·
                  refine ⟨32585429388762389963086661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21723619592508259975391107 32585429388762389963086661)
                  ·
                    refine ⟨6109768010392948118078749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32585429388762389963086661 6109768010392948118078749)
                    ·
                      refine ⟨2291163003897355544279531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6109768010392948118078749 2291163003897355544279531)
                      ·
                        rfl

theorem cell23_4462024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_4462024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462024 prefixEnd_4462024 := by exact prefixLift 4462024
  have htrace : WordTrace (prefixWord ++ tailWord_4462024) baseStart_4462024 baseEnd_4462024 := by
    simpa [prefixWord, tailWord_4462024, baseEnd_4462024] using wordTrace_append hprefix tailTrace_4462024
  have hstable : (prefixWord ++ tailWord_4462024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462024).length < 2 ^ (prefixWord ++ tailWord_4462024).sum := by decide
  have hdescent : baseEnd_4462024 < baseStart_4462024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462038 : List Nat := [5, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_4462038 : Nat := 118140960795 + 4462038 * 2 ^ 59
def prefixEnd_4462038 : Nat := 4983230072969 + 3 ^ 40 * 4462038 * 2
def baseEnd_4462038 : Nat := 2291170192626518489504467

theorem tailTrace_4462038 : CollatzResearch.WordTrace tailWord_4462038 prefixEnd_4462038 2291170192626518489504467 := by
  unfold tailWord_4462038
  simp only [CollatzResearch.WordTrace]
  refine ⟨10171493488050366016573673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108495930539203904176785845 10171493488050366016573673)
  ·
    refine ⟨7628620116037774512430255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10171493488050366016573673 7628620116037774512430255)
    ·
      refine ⟨11442930174056661768645383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7628620116037774512430255 11442930174056661768645383)
      ·
        refine ⟨17164395261084992652968075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11442930174056661768645383 17164395261084992652968075)
        ·
          refine ⟨25746592891627488979452113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17164395261084992652968075 25746592891627488979452113)
          ·
            refine ⟨19309944668720616734589085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25746592891627488979452113 19309944668720616734589085)
            ·
              refine ⟨7241229250770231275470907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19309944668720616734589085 7241229250770231275470907)
              ·
                refine ⟨10861843876155346913206361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7241229250770231275470907 10861843876155346913206361)
                ·
                  refine ⟨8146382907116510184904771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10861843876155346913206361 8146382907116510184904771)
                  ·
                    refine ⟨12219574360674765277357157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8146382907116510184904771 12219574360674765277357157)
                    ·
                      refine ⟨2291170192626518489504467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12219574360674765277357157 2291170192626518489504467)
                      ·
                        rfl

theorem cell23_4462038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_4462038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462038 prefixEnd_4462038 := by exact prefixLift 4462038
  have htrace : WordTrace (prefixWord ++ tailWord_4462038) baseStart_4462038 baseEnd_4462038 := by
    simpa [prefixWord, tailWord_4462038, baseEnd_4462038] using wordTrace_append hprefix tailTrace_4462038
  have hstable : (prefixWord ++ tailWord_4462038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462038).length < 2 ^ (prefixWord ++ tailWord_4462038).sum := by decide
  have hdescent : baseEnd_4462038 < baseStart_4462038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462041 : List Nat := [1, 2, 1, 2, 4, 2, 3, 1, 2, 2, 3]
def baseStart_4462041 : Nat := 118140960795 + 4462041 * 2 ^ 59
def prefixEnd_4462041 : Nat := 4983230072969 + 3 ^ 40 * 4462041 * 2
def baseEnd_4462041 : Nat := 2291171733068481977766953

theorem tailTrace_4462041 : CollatzResearch.WordTrace tailWord_4462041 prefixEnd_4462041 2291171733068481977766953 := by
  unfold tailWord_4462041
  simp only [CollatzResearch.WordTrace]
  refine ⟨162744005227794987777537977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108496003485196658518358651 162744005227794987777537977)
  ·
    refine ⟨122058003920846240833153483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162744005227794987777537977 122058003920846240833153483)
    ·
      refine ⟨183087005881269361249730225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122058003920846240833153483 183087005881269361249730225)
      ·
        refine ⟨137315254410952020937297669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183087005881269361249730225 137315254410952020937297669)
        ·
          refine ⟨25746610202053503925743313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137315254410952020937297669 25746610202053503925743313)
          ·
            refine ⟨19309957651540127944307485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25746610202053503925743313 19309957651540127944307485)
            ·
              refine ⟨7241234119327547979115307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19309957651540127944307485 7241234119327547979115307)
              ·
                refine ⟨10861851178991321968672961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7241234119327547979115307 10861851178991321968672961)
                ·
                  refine ⟨8146388384243491476504721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10861851178991321968672961 8146388384243491476504721)
                  ·
                    refine ⟨6109791288182618607378541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8146388384243491476504721 6109791288182618607378541)
                    ·
                      refine ⟨2291171733068481977766953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6109791288182618607378541 2291171733068481977766953)
                      ·
                        rfl

theorem cell23_4462041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 2, 3].length) (baseStart_4462041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462041 prefixEnd_4462041 := by exact prefixLift 4462041
  have htrace : WordTrace (prefixWord ++ tailWord_4462041) baseStart_4462041 baseEnd_4462041 := by
    simpa [prefixWord, tailWord_4462041, baseEnd_4462041] using wordTrace_append hprefix tailTrace_4462041
  have hstable : (prefixWord ++ tailWord_4462041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462041).length < 2 ^ (prefixWord ++ tailWord_4462041).sum := by decide
  have hdescent : baseEnd_4462041 < baseStart_4462041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462061 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 8]
def baseStart_4462061 : Nat := 118140960795 + 4462061 * 2 ^ 59
def prefixEnd_4462061 : Nat := 4983230072969 + 3 ^ 40 * 4462061 * 2
def baseEnd_4462061 : Nat := 254575778075730211057429

theorem tailTrace_4462061 : CollatzResearch.WordTrace tailWord_4462061 prefixEnd_4462061 254575778075730211057429 := by
  unfold tailWord_4462061
  simp only [CollatzResearch.WordTrace]
  refine ⟨162744734687722531193266037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108496489791815020795510691 162744734687722531193266037)
  ·
    refine ⟨15257318876973987299368691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 162744734687722531193266037 15257318876973987299368691)
    ·
      refine ⟨22885978315460980949053037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15257318876973987299368691 22885978315460980949053037)
      ·
        refine ⟨8582241868297867855894889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22885978315460980949053037 8582241868297867855894889)
        ·
          refine ⟨6436681401223400891921167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8582241868297867855894889 6436681401223400891921167)
          ·
            refine ⟨9655022101835101337881751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6436681401223400891921167 9655022101835101337881751)
            ·
              refine ⟨14482533152752652006822627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9655022101835101337881751 14482533152752652006822627)
              ·
                refine ⟨21723799729128978010233941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14482533152752652006822627 21723799729128978010233941)
                ·
                  refine ⟨254575778075730211057429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21723799729128978010233941 254575778075730211057429)
                  ·
                    rfl

theorem cell23_4462061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_4462061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462061 prefixEnd_4462061 := by exact prefixLift 4462061
  have htrace : WordTrace (prefixWord ++ tailWord_4462061) baseStart_4462061 baseEnd_4462061 := by
    simpa [prefixWord, tailWord_4462061, baseEnd_4462061] using wordTrace_append hprefix tailTrace_4462061
  have hstable : (prefixWord ++ tailWord_4462061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462061).length < 2 ^ (prefixWord ++ tailWord_4462061).sum := by decide
  have hdescent : baseEnd_4462061 < baseStart_4462061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462067 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 7]
def baseStart_4462067 : Nat := 118140960795 + 4462067 * 2 ^ 59
def prefixEnd_4462067 : Nat := 4983230072969 + 3 ^ 40 * 4462067 * 2
def baseEnd_4462067 : Nat := 2291185083565498876041833

theorem tailTrace_4462067 : CollatzResearch.WordTrace tailWord_4462067 prefixEnd_4462067 2291185083565498876041833 := by
  unfold tailWord_4462067
  simp only [CollatzResearch.WordTrace]
  refine ⟨162744953525700794217984455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108496635683800529478656303 162744953525700794217984455)
  ·
    refine ⟨244117430288551191326976683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162744953525700794217984455 244117430288551191326976683)
    ·
      refine ⟨366176145432826786990465025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244117430288551191326976683 366176145432826786990465025)
      ·
        refine ⟨274632109074620090242848769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 366176145432826786990465025 274632109074620090242848769)
        ·
          refine ⟨205974081805965067682136577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274632109074620090242848769 205974081805965067682136577)
          ·
            refine ⟨154480561354473800761602433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205974081805965067682136577 154480561354473800761602433)
            ·
              refine ⟨115860421015855350571201825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154480561354473800761602433 115860421015855350571201825)
              ·
                refine ⟨86895315761891512928401369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115860421015855350571201825 86895315761891512928401369)
                ·
                  refine ⟨65171486821418634696301027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86895315761891512928401369 65171486821418634696301027)
                  ·
                    refine ⟨97757230232127952044451541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65171486821418634696301027 97757230232127952044451541)
                    ·
                      refine ⟨2291185083565498876041833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97757230232127952044451541 2291185083565498876041833)
                      ·
                        rfl

theorem cell23_4462067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_4462067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462067 prefixEnd_4462067 := by exact prefixLift 4462067
  have htrace : WordTrace (prefixWord ++ tailWord_4462067) baseStart_4462067 baseEnd_4462067 := by
    simpa [prefixWord, tailWord_4462067, baseEnd_4462067] using wordTrace_append hprefix tailTrace_4462067
  have hstable : (prefixWord ++ tailWord_4462067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462067).length < 2 ^ (prefixWord ++ tailWord_4462067).sum := by decide
  have hdescent : baseEnd_4462067 < baseStart_4462067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462111 : List Nat := [1, 1, 2, 4, 1, 1, 4, 3, 1, 1, 4]
def baseStart_4462111 : Nat := 118140960795 + 4462111 * 2 ^ 59
def prefixEnd_4462111 : Nat := 4983230072969 + 3 ^ 40 * 4462111 * 2
def baseEnd_4462111 : Nat := 2291207676714296703891631

theorem tailTrace_4462111 : CollatzResearch.WordTrace tailWord_4462111 prefixEnd_4462111 2291207676714296703891631 := by
  unfold tailWord_4462111
  simp only [CollatzResearch.WordTrace]
  refine ⟨162746558337541389732586187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108497705558360926488390791 162746558337541389732586187)
  ·
    refine ⟨244119837506312084598879281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162746558337541389732586187 244119837506312084598879281)
    ·
      refine ⟨183089878129734063449159461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244119837506312084598879281 183089878129734063449159461)
      ·
        refine ⟨34329352149325136896717399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183089878129734063449159461 34329352149325136896717399)
        ·
          refine ⟨51494028223987705345076099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34329352149325136896717399 51494028223987705345076099)
          ·
            refine ⟨77241042335981558017614149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51494028223987705345076099 77241042335981558017614149)
            ·
              refine ⟨14482695437996542128302653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77241042335981558017614149 14482695437996542128302653)
              ·
                refine ⟨5431010789248703298113495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14482695437996542128302653 5431010789248703298113495)
                ·
                  refine ⟨8146516183873054947170243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5431010789248703298113495 8146516183873054947170243)
                  ·
                    refine ⟨12219774275809582420755365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8146516183873054947170243 12219774275809582420755365)
                    ·
                      refine ⟨2291207676714296703891631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12219774275809582420755365 2291207676714296703891631)
                      ·
                        rfl

theorem cell23_4462111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_4462111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462111 prefixEnd_4462111 := by exact prefixLift 4462111
  have htrace : WordTrace (prefixWord ++ tailWord_4462111) baseStart_4462111 baseEnd_4462111 := by
    simpa [prefixWord, tailWord_4462111, baseEnd_4462111] using wordTrace_append hprefix tailTrace_4462111
  have hstable : (prefixWord ++ tailWord_4462111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462111).length < 2 ^ (prefixWord ++ tailWord_4462111).sum := by decide
  have hdescent : baseEnd_4462111 < baseStart_4462111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462122 : List Nat := [3, 1, 4, 1, 1, 1, 5, 2, 1, 1, 3]
def baseStart_4462122 : Nat := 118140960795 + 4462122 * 2 ^ 59
def prefixEnd_4462122 : Nat := 4983230072969 + 3 ^ 40 * 4462122 * 2
def baseEnd_4462122 : Nat := 2291213325001496160854081

theorem tailTrace_4462122 : CollatzResearch.WordTrace tailWord_4462122 prefixEnd_4462122 2291213325001496160854081 := by
  unfold tailWord_4462122
  simp only [CollatzResearch.WordTrace]
  refine ⟨40686739885125384652809155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108497973027001025740824413 40686739885125384652809155)
  ·
    refine ⟨61030109827688076979213733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40686739885125384652809155 61030109827688076979213733)
    ·
      refine ⟨11443145592691514433602575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61030109827688076979213733 11443145592691514433602575)
      ·
        refine ⟨17164718389037271650403863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11443145592691514433602575 17164718389037271650403863)
        ·
          refine ⟨25747077583555907475605795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17164718389037271650403863 25747077583555907475605795)
          ·
            refine ⟨38620616375333861213408693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25747077583555907475605795 38620616375333861213408693)
            ·
              refine ⟨3620682785187549488757065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38620616375333861213408693 3620682785187549488757065)
              ·
                refine ⟨2715512088890662116567799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3620682785187549488757065 2715512088890662116567799)
                ·
                  refine ⟨4073268133335993174851699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2715512088890662116567799 4073268133335993174851699)
                  ·
                    refine ⟨6109902200003989762277549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4073268133335993174851699 6109902200003989762277549)
                    ·
                      refine ⟨2291213325001496160854081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6109902200003989762277549 2291213325001496160854081)
                      ·
                        rfl

theorem cell23_4462122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_4462122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462122 prefixEnd_4462122 := by exact prefixLift 4462122
  have htrace : WordTrace (prefixWord ++ tailWord_4462122) baseStart_4462122 baseEnd_4462122 := by
    simpa [prefixWord, tailWord_4462122, baseEnd_4462122] using wordTrace_append hprefix tailTrace_4462122
  have hstable : (prefixWord ++ tailWord_4462122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462122).length < 2 ^ (prefixWord ++ tailWord_4462122).sum := by decide
  have hdescent : baseEnd_4462122 < baseStart_4462122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462161 : List Nat := [1, 2, 2, 1, 3, 2, 3, 2, 1, 3, 3]
def baseStart_4462161 : Nat := 118140960795 + 4462161 * 2 ^ 59
def prefixEnd_4462161 : Nat := 4983230072969 + 3 ^ 40 * 4462161 * 2
def baseEnd_4462161 : Nat := 2291233350747021508266401

theorem tailTrace_4462161 : CollatzResearch.WordTrace tailWord_4462161 prefixEnd_4462161 2291233350747021508266401 := by
  unfold tailWord_4462161
  simp only [CollatzResearch.WordTrace]
  refine ⟨162748381987360248271906337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108498921324906832181270891 162748381987360248271906337)
  ·
    refine ⟨122061286490520186203929753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162748381987360248271906337 122061286490520186203929753)
    ·
      refine ⟨91545964867890139652947315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122061286490520186203929753 91545964867890139652947315)
      ·
        refine ⟨137318947301835209479420973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91545964867890139652947315 137318947301835209479420973)
        ·
          refine ⟨51494605238188203554782865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137318947301835209479420973 51494605238188203554782865)
          ·
            refine ⟨38620953928641152666087149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51494605238188203554782865 38620953928641152666087149)
            ·
              refine ⟨14482857723240432249782681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38620953928641152666087149 14482857723240432249782681)
              ·
                refine ⟨10862143292430324187337011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14482857723240432249782681 10862143292430324187337011)
                ·
                  refine ⟨16293214938645486281005517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10862143292430324187337011 16293214938645486281005517)
                  ·
                    refine ⟨6109955601992057355377069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16293214938645486281005517 6109955601992057355377069)
                    ·
                      refine ⟨2291233350747021508266401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6109955601992057355377069 2291233350747021508266401)
                      ·
                        rfl

theorem cell23_4462161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 3, 3].length) (baseStart_4462161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462161 prefixEnd_4462161 := by exact prefixLift 4462161
  have htrace : WordTrace (prefixWord ++ tailWord_4462161) baseStart_4462161 baseEnd_4462161 := by
    simpa [prefixWord, tailWord_4462161, baseEnd_4462161] using wordTrace_append hprefix tailTrace_4462161
  have hstable : (prefixWord ++ tailWord_4462161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462161).length < 2 ^ (prefixWord ++ tailWord_4462161).sum := by decide
  have hdescent : baseEnd_4462161 < baseStart_4462161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462173 : List Nat := [1, 4, 4, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_4462173 : Nat := 118140960795 + 4462173 * 2 ^ 59
def prefixEnd_4462173 : Nat := 4983230072969 + 3 ^ 40 * 4462173 * 2
def baseEnd_4462173 : Nat := 2291239512514875461316347

theorem tailTrace_4462173 : CollatzResearch.WordTrace tailWord_4462173 prefixEnd_4462173 2291239512514875461316347 := by
  unfold tailWord_4462173
  simp only [CollatzResearch.WordTrace]
  refine ⟨162748819663316774321343173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108499213108877849547562115 162748819663316774321343173)
  ·
    refine ⟨30515403686871895185251845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162748819663316774321343173 30515403686871895185251845)
    ·
      refine ⟨5721638191288480347234721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30515403686871895185251845 5721638191288480347234721)
      ·
        refine ⟨4291228643466360260426041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5721638191288480347234721 4291228643466360260426041)
        ·
          refine ⟨3218421482599770195319531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4291228643466360260426041 3218421482599770195319531)
          ·
            refine ⟨4827632223899655292979297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3218421482599770195319531 4827632223899655292979297)
            ·
              refine ⟨3620724167924741469734473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4827632223899655292979297 3620724167924741469734473)
              ·
                refine ⟨2715543125943556102300855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3620724167924741469734473 2715543125943556102300855)
                ·
                  refine ⟨4073314688915334153451283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2715543125943556102300855 4073314688915334153451283)
                  ·
                    refine ⟨6109972033373001230176925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4073314688915334153451283 6109972033373001230176925)
                    ·
                      refine ⟨2291239512514875461316347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6109972033373001230176925 2291239512514875461316347)
                      ·
                        rfl

theorem cell23_4462173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_4462173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462173 prefixEnd_4462173 := by exact prefixLift 4462173
  have htrace : WordTrace (prefixWord ++ tailWord_4462173) baseStart_4462173 baseEnd_4462173 := by
    simpa [prefixWord, tailWord_4462173, baseEnd_4462173] using wordTrace_append hprefix tailTrace_4462173
  have hstable : (prefixWord ++ tailWord_4462173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462173).length < 2 ^ (prefixWord ++ tailWord_4462173).sum := by decide
  have hdescent : baseEnd_4462173 < baseStart_4462173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462179 : List Nat := [1, 1, 1, 5, 1, 5, 2, 2, 1, 2, 2]
def baseStart_4462179 : Nat := 118140960795 + 4462179 * 2 ^ 59
def prefixEnd_4462179 : Nat := 4983230072969 + 3 ^ 40 * 4462179 * 2
def baseEnd_4462179 : Nat := 2291242593398802437841319

theorem tailTrace_4462179 : CollatzResearch.WordTrace tailWord_4462179 prefixEnd_4462179 2291242593398802437841319 := by
  unfold tailWord_4462179
  simp only [CollatzResearch.WordTrace]
  refine ⟨162749038501295037346061591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108499359000863358230707727 162749038501295037346061591)
  ·
    refine ⟨244123557751942556019092387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162749038501295037346061591 244123557751942556019092387)
    ·
      refine ⟨366185336627913834028638581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244123557751942556019092387 366185336627913834028638581)
      ·
        refine ⟨34329875308866921940184867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 366185336627913834028638581 34329875308866921940184867)
        ·
          refine ⟨51494812963300382910277301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34329875308866921940184867 51494812963300382910277301)
          ·
            refine ⟨4827638715309410897838497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51494812963300382910277301 4827638715309410897838497)
            ·
              refine ⟨3620729036482058173378873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4827638715309410897838497 3620729036482058173378873)
              ·
                refine ⟨2715546777361543630034155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3620729036482058173378873 2715546777361543630034155)
                ·
                  refine ⟨4073320166042315445051233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2715546777361543630034155 4073320166042315445051233)
                  ·
                    refine ⟨3054990124531736583788425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4073320166042315445051233 3054990124531736583788425)
                    ·
                      refine ⟨2291242593398802437841319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3054990124531736583788425 2291242593398802437841319)
                      ·
                        rfl

theorem cell23_4462179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_4462179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462179 prefixEnd_4462179 := by exact prefixLift 4462179
  have htrace : WordTrace (prefixWord ++ tailWord_4462179) baseStart_4462179 baseEnd_4462179 := by
    simpa [prefixWord, tailWord_4462179, baseEnd_4462179] using wordTrace_append hprefix tailTrace_4462179
  have hstable : (prefixWord ++ tailWord_4462179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462179).length < 2 ^ (prefixWord ++ tailWord_4462179).sum := by decide
  have hdescent : baseEnd_4462179 < baseStart_4462179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462222 : List Nat := [4, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2]
def baseStart_4462222 : Nat := 118140960795 + 4462222 * 2 ^ 59
def prefixEnd_4462222 : Nat := 4983230072969 + 3 ^ 40 * 4462222 * 2
def baseEnd_4462222 : Nat := 2291264673066945769603621

theorem tailTrace_4462222 : CollatzResearch.WordTrace tailWord_4462222 prefixEnd_4462222 2291264673066945769603621 := by
  unfold tailWord_4462222
  simp only [CollatzResearch.WordTrace]
  refine ⟨20343825855017406961234615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108500404560092837126584613 20343825855017406961234615)
  ·
    refine ⟨30515738782526110441851923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20343825855017406961234615 30515738782526110441851923)
    ·
      refine ⟨45773608173789165662777885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30515738782526110441851923 45773608173789165662777885)
      ·
        refine ⟨17165103065170937123541707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45773608173789165662777885 17165103065170937123541707)
        ·
          refine ⟨25747654597756405685312561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17165103065170937123541707 25747654597756405685312561)
          ·
            refine ⟨19310740948317304263984421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25747654597756405685312561 19310740948317304263984421)
            ·
              refine ⟨3620763927809494549497079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19310740948317304263984421 3620763927809494549497079)
              ·
                refine ⟨5431145891714241824245619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3620763927809494549497079 5431145891714241824245619)
                ·
                  refine ⟨8146718837571362736368429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5431145891714241824245619 8146718837571362736368429)
                  ·
                    refine ⟨3055019564089261026138161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8146718837571362736368429 3055019564089261026138161)
                    ·
                      refine ⟨2291264673066945769603621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3055019564089261026138161 2291264673066945769603621)
                      ·
                        rfl

theorem cell23_4462222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_4462222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462222 prefixEnd_4462222 := by exact prefixLift 4462222
  have htrace : WordTrace (prefixWord ++ tailWord_4462222) baseStart_4462222 baseEnd_4462222 := by
    simpa [prefixWord, tailWord_4462222, baseEnd_4462222] using wordTrace_append hprefix tailTrace_4462222
  have hstable : (prefixWord ++ tailWord_4462222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462222).length < 2 ^ (prefixWord ++ tailWord_4462222).sum := by decide
  have hdescent : baseEnd_4462222 < baseStart_4462222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462231 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 4]
def baseStart_4462231 : Nat := 118140960795 + 4462231 * 2 ^ 59
def prefixEnd_4462231 : Nat := 4983230072969 + 3 ^ 40 * 4462231 * 2
def baseEnd_4462231 : Nat := 2291269294392836234391079

theorem tailTrace_4462231 : CollatzResearch.WordTrace tailWord_4462231 prefixEnd_4462231 2291269294392836234391079 := by
  unfold tailWord_4462231
  simp only [CollatzResearch.WordTrace]
  refine ⟨162750935097106650226954547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108500623398071100151303031 162750935097106650226954547)
  ·
    refine ⟨244126402645659975340431821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162750935097106650226954547 244126402645659975340431821)
    ·
      refine ⟨91547400992122490752661933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244126402645659975340431821 91547400992122490752661933)
      ·
        refine ⟨34330275372045934032248225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91547400992122490752661933 34330275372045934032248225)
        ·
          refine ⟨25747706529034450524186169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34330275372045934032248225 25747706529034450524186169)
          ·
            refine ⟨19310779896775837893139627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25747706529034450524186169 19310779896775837893139627)
            ·
              refine ⟨28966169845163756839709441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19310779896775837893139627 28966169845163756839709441)
              ·
                refine ⟨21724627383872817629782081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28966169845163756839709441 21724627383872817629782081)
                ·
                  refine ⟨16293470537904613222336561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21724627383872817629782081 16293470537904613222336561)
                  ·
                    refine ⟨12220102903428459916752421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16293470537904613222336561 12220102903428459916752421)
                    ·
                      refine ⟨2291269294392836234391079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12220102903428459916752421 2291269294392836234391079)
                      ·
                        rfl

theorem cell23_4462231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_4462231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462231 prefixEnd_4462231 := by exact prefixLift 4462231
  have htrace : WordTrace (prefixWord ++ tailWord_4462231) baseStart_4462231 baseEnd_4462231 := by
    simpa [prefixWord, tailWord_4462231, baseEnd_4462231] using wordTrace_append hprefix tailTrace_4462231
  have hstable : (prefixWord ++ tailWord_4462231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462231).length < 2 ^ (prefixWord ++ tailWord_4462231).sum := by decide
  have hdescent : baseEnd_4462231 < baseStart_4462231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462241 : List Nat := [1, 2, 3, 3, 2, 1, 1, 3, 7]
def baseStart_4462241 : Nat := 118140960795 + 4462241 * 2 ^ 59
def prefixEnd_4462241 : Nat := 4983230072969 + 3 ^ 40 * 4462241 * 2
def baseEnd_4462241 : Nat := 254586047688820132807337

theorem tailTrace_4462241 : CollatzResearch.WordTrace tailWord_4462241 prefixEnd_4462241 254586047688820132807337 := by
  unfold tailWord_4462241
  simp only [CollatzResearch.WordTrace]
  refine ⟨162751299827070421934818577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108500866551380281289879051 162751299827070421934818577)
  ·
    refine ⟨122063474870302816451113933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162751299827070421934818577 122063474870302816451113933)
    ·
      refine ⟨45773803076363556169167725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122063474870302816451113933 45773803076363556169167725)
      ·
        refine ⟨17165176153636333563437897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45773803076363556169167725 17165176153636333563437897)
        ·
          refine ⟨12873882115227250172578423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17165176153636333563437897 12873882115227250172578423)
          ·
            refine ⟨19310823172840875258867635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12873882115227250172578423 19310823172840875258867635)
            ·
              refine ⟨28966234759261312888301453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19310823172840875258867635 28966234759261312888301453)
              ·
                refine ⟨10862338034722992333113045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28966234759261312888301453 10862338034722992333113045)
                ·
                  refine ⟨254586047688820132807337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10862338034722992333113045 254586047688820132807337)
                  ·
                    rfl

theorem cell23_4462241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 7].length) (baseStart_4462241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462241 prefixEnd_4462241 := by exact prefixLift 4462241
  have htrace : WordTrace (prefixWord ++ tailWord_4462241) baseStart_4462241 baseEnd_4462241 := by
    simpa [prefixWord, tailWord_4462241, baseEnd_4462241] using wordTrace_append hprefix tailTrace_4462241
  have hstable : (prefixWord ++ tailWord_4462241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462241).length < 2 ^ (prefixWord ++ tailWord_4462241).sum := by decide
  have hdescent : baseEnd_4462241 < baseStart_4462241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462271 : List Nat := [1, 1, 2, 2, 2, 3, 2, 3, 2, 5]
def baseStart_4462271 : Nat := 118140960795 + 4462271 * 2 ^ 59
def prefixEnd_4462271 : Nat := 4983230072969 + 3 ^ 40 * 4462271 * 2
def baseEnd_4462271 : Nat := 763763277873005359296965

theorem tailTrace_4462271 : CollatzResearch.WordTrace tailWord_4462271 prefixEnd_4462271 763763277873005359296965 := by
  unfold tailWord_4462271
  simp only [CollatzResearch.WordTrace]
  refine ⟨162752394016961737058410667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108501596011307824705607111 162752394016961737058410667)
  ·
    refine ⟨244128591025442605587616001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162752394016961737058410667 244128591025442605587616001)
    ·
      refine ⟨183096443269081954190712001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244128591025442605587616001 183096443269081954190712001)
      ·
        refine ⟨137322332451811465643034001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183096443269081954190712001 137322332451811465643034001)
        ·
          refine ⟨102991749338858599232275501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137322332451811465643034001 102991749338858599232275501)
          ·
            refine ⟨38621906002071974712103313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102991749338858599232275501 38621906002071974712103313)
            ·
              refine ⟨28966429501553981034077485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38621906002071974712103313 28966429501553981034077485)
              ·
                refine ⟨10862411063082742887779057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28966429501553981034077485 10862411063082742887779057)
                ·
                  refine ⟨8146808297312057165834293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10862411063082742887779057 8146808297312057165834293)
                  ·
                    refine ⟨763763277873005359296965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8146808297312057165834293 763763277873005359296965)
                    ·
                      rfl

theorem cell23_4462271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 5].length) (baseStart_4462271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462271 prefixEnd_4462271 := by exact prefixLift 4462271
  have htrace : WordTrace (prefixWord ++ tailWord_4462271) baseStart_4462271 baseEnd_4462271 := by
    simpa [prefixWord, tailWord_4462271, baseEnd_4462271] using wordTrace_append hprefix tailTrace_4462271
  have hstable : (prefixWord ++ tailWord_4462271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462271).length < 2 ^ (prefixWord ++ tailWord_4462271).sum := by decide
  have hdescent : baseEnd_4462271 < baseStart_4462271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462292 : List Nat := [2, 4, 1, 3, 1, 2, 3, 2, 5]
def baseStart_4462292 : Nat := 118140960795 + 4462292 * 2 ^ 59
def prefixEnd_4462292 : Nat := 4983230072969 + 3 ^ 40 * 4462292 * 2
def baseEnd_4462292 : Nat := 254588957412528943969811

theorem tailTrace_4462292 : CollatzResearch.WordTrace tailWord_4462292 prefixEnd_4462292 254588957412528943969811 := by
  unfold tailWord_4462292
  simp only [CollatzResearch.WordTrace]
  refine ⟨81376579974942828822462565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108502106633257105096616753 81376579974942828822462565)
  ·
    refine ⟨15258108745301780404211731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81376579974942828822462565 15258108745301780404211731)
    ·
      refine ⟨22887163117952670606317597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15258108745301780404211731 22887163117952670606317597)
      ·
        refine ⟨8582686169232251477369099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22887163117952670606317597 8582686169232251477369099)
        ·
          refine ⟨12874029253848377216053649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8582686169232251477369099 12874029253848377216053649)
          ·
            refine ⟨9655521940386282912040237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12874029253848377216053649 9655521940386282912040237)
            ·
              refine ⟨3620820727644856092015089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9655521940386282912040237 3620820727644856092015089)
              ·
                refine ⟨2715615545733642069011317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3620820727644856092015089 2715615545733642069011317)
                ·
                  refine ⟨254588957412528943969811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2715615545733642069011317 254588957412528943969811)
                  ·
                    rfl

theorem cell23_4462292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_4462292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462292 prefixEnd_4462292 := by exact prefixLift 4462292
  have htrace : WordTrace (prefixWord ++ tailWord_4462292) baseStart_4462292 baseEnd_4462292 := by
    simpa [prefixWord, tailWord_4462292, baseEnd_4462292] using wordTrace_append hprefix tailTrace_4462292
  have hstable : (prefixWord ++ tailWord_4462292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462292).length < 2 ^ (prefixWord ++ tailWord_4462292).sum := by decide
  have hdescent : baseEnd_4462292 < baseStart_4462292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462308 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 1, 6, 2]
def baseStart_4462308 : Nat := 118140960795 + 4462308 * 2 ^ 59
def prefixEnd_4462308 : Nat := 4983230072969 + 3 ^ 40 * 4462308 * 2
def baseEnd_4462308 : Nat := 2291308832403232433128225

theorem tailTrace_4462308 : CollatzResearch.WordTrace tailWord_4462308 prefixEnd_4462308 2291308832403232433128225 := by
  unfold tailWord_4462308
  simp only [CollatzResearch.WordTrace]
  refine ⟨81376871758913846188753789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108502495678551794918338385 81376871758913846188753789)
  ·
    refine ⟨30516326909592692320782671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81376871758913846188753789 30516326909592692320782671)
    ·
      refine ⟨45774490364389038481174007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30516326909592692320782671 45774490364389038481174007)
      ·
        refine ⟨68661735546583557721761011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45774490364389038481174007 68661735546583557721761011)
        ·
          refine ⟨102992603319875336582641517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68661735546583557721761011 102992603319875336582641517)
          ·
            refine ⟨38622226244953251218490569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102992603319875336582641517 38622226244953251218490569)
            ·
              refine ⟨28966669683714938413867927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38622226244953251218490569 28966669683714938413867927)
              ·
                refine ⟨43450004525572407620801891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28966669683714938413867927 43450004525572407620801891)
                ·
                  refine ⟨65175006788358611431202837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43450004525572407620801891 65175006788358611431202837)
                  ·
                    refine ⟨3055078443204309910837633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65175006788358611431202837 3055078443204309910837633)
                    ·
                      refine ⟨2291308832403232433128225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3055078443204309910837633 2291308832403232433128225)
                      ·
                        rfl

theorem cell23_4462308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_4462308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462308 prefixEnd_4462308 := by exact prefixLift 4462308
  have htrace : WordTrace (prefixWord ++ tailWord_4462308) baseStart_4462308 baseEnd_4462308 := by
    simpa [prefixWord, tailWord_4462308, baseEnd_4462308] using wordTrace_append hprefix tailTrace_4462308
  have hstable : (prefixWord ++ tailWord_4462308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462308).length < 2 ^ (prefixWord ++ tailWord_4462308).sum := by decide
  have hdescent : baseEnd_4462308 < baseStart_4462308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462318 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 5, 4]
def baseStart_4462318 : Nat := 118140960795 + 4462318 * 2 ^ 59
def prefixEnd_4462318 : Nat := 4983230072969 + 3 ^ 40 * 4462318 * 2
def baseEnd_4462318 : Nat := 763771322403259131334393

theorem tailTrace_4462318 : CollatzResearch.WordTrace tailWord_4462318 prefixEnd_4462318 763771322403259131334393 := by
  unfold tailWord_4462318
  simp only [CollatzResearch.WordTrace]
  refine ⟨20344263530973933010671451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108502738831860976056914405 20344263530973933010671451)
  ·
    refine ⟨30516395296460899516007177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20344263530973933010671451 30516395296460899516007177)
    ·
      refine ⟨22887296472345674637005383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30516395296460899516007177 22887296472345674637005383)
      ·
        refine ⟨34330944708518511955508075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22887296472345674637005383 34330944708518511955508075)
        ·
          refine ⟨51496417062777767933262113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34330944708518511955508075 51496417062777767933262113)
          ·
            refine ⟨38622312797083325949946585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51496417062777767933262113 38622312797083325949946585)
            ·
              refine ⟨28966734597812494462459939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38622312797083325949946585 28966734597812494462459939)
              ·
                refine ⟨43450101896718741693689909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28966734597812494462459939 43450101896718741693689909)
                ·
                  refine ⟨4073447052817382033783429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43450101896718741693689909 4073447052817382033783429)
                  ·
                    refine ⟨763771322403259131334393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4073447052817382033783429 763771322403259131334393)
                    ·
                      rfl

theorem cell23_4462318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_4462318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462318 prefixEnd_4462318 := by exact prefixLift 4462318
  have htrace : WordTrace (prefixWord ++ tailWord_4462318) baseStart_4462318 baseEnd_4462318 := by
    simpa [prefixWord, tailWord_4462318, baseEnd_4462318] using wordTrace_append hprefix tailTrace_4462318
  have hstable : (prefixWord ++ tailWord_4462318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462318).length < 2 ^ (prefixWord ++ tailWord_4462318).sum := by decide
  have hdescent : baseEnd_4462318 < baseStart_4462318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462338 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_4462338 : Nat := 118140960795 + 4462338 * 2 ^ 59
def prefixEnd_4462338 : Nat := 4983230072969 + 3 ^ 40 * 4462338 * 2
def baseEnd_4462338 : Nat := 2291324236822867315753087

theorem tailTrace_4462338 : CollatzResearch.WordTrace tailWord_4462338 prefixEnd_4462338 2291324236822867315753087 := by
  unfold tailWord_4462338
  simp only [CollatzResearch.WordTrace]
  refine ⟨40688709426929751875274917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108503225138479338334066445 40688709426929751875274917)
  ·
    refine ⟨7629133017549328476614047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40688709426929751875274917 7629133017549328476614047)
    ·
      refine ⟨11443699526323992714921071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7629133017549328476614047 11443699526323992714921071)
      ·
        refine ⟨17165549289485989072381607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11443699526323992714921071 17165549289485989072381607)
        ·
          refine ⟨25748323934228983608572411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17165549289485989072381607 25748323934228983608572411)
          ·
            refine ⟨38622485901343475412858617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25748323934228983608572411 38622485901343475412858617)
            ·
              refine ⟨28966864426007606559643963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38622485901343475412858617 28966864426007606559643963)
              ·
                refine ⟨43450296639011409839465945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28966864426007606559643963 43450296639011409839465945)
                ·
                  refine ⟨32587722479258557379599459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43450296639011409839465945 32587722479258557379599459)
                  ·
                    refine ⟨48881583718887836069399189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32587722479258557379599459 48881583718887836069399189)
                    ·
                      refine ⟨2291324236822867315753087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48881583718887836069399189 2291324236822867315753087)
                      ·
                        rfl

theorem cell23_4462338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_4462338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462338 prefixEnd_4462338 := by exact prefixLift 4462338
  have htrace : WordTrace (prefixWord ++ tailWord_4462338) baseStart_4462338 baseEnd_4462338 := by
    simpa [prefixWord, tailWord_4462338, baseEnd_4462338] using wordTrace_append hprefix tailTrace_4462338
  have hstable : (prefixWord ++ tailWord_4462338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462338).length < 2 ^ (prefixWord ++ tailWord_4462338).sum := by decide
  have hdescent : baseEnd_4462338 < baseStart_4462338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462385 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 1, 5, 2]
def baseStart_4462385 : Nat := 118140960795 + 4462385 * 2 ^ 59
def prefixEnd_4462385 : Nat := 4983230072969 + 3 ^ 40 * 4462385 * 2
def baseEnd_4462385 : Nat := 2291348370413628631865371

theorem tailTrace_4462385 : CollatzResearch.WordTrace tailWord_4462385 prefixEnd_4462385 2291348370413628631865371 := by
  unfold tailWord_4462385
  simp only [CollatzResearch.WordTrace]
  refine ⟨162756551938548734528060609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108504367959032489685373739 162756551938548734528060609)
  ·
    refine ⟨122067413953911550896045457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162756551938548734528060609 122067413953911550896045457)
    ·
      refine ⟨91550560465433663172034093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122067413953911550896045457 91550560465433663172034093)
      ·
        refine ⟨34331460174537623689512785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91550560465433663172034093 34331460174537623689512785)
        ·
          refine ⟨25748595130903217767134589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34331460174537623689512785 25748595130903217767134589)
          ·
            refine ⟨9655723174088706662675471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25748595130903217767134589 9655723174088706662675471)
            ·
              refine ⟨14483584761133059994013207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9655723174088706662675471 14483584761133059994013207)
              ·
                refine ⟨21725377141699589991019811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14483584761133059994013207 21725377141699589991019811)
                ·
                  refine ⟨32588065712549384986529717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21725377141699589991019811 32588065712549384986529717)
                  ·
                    refine ⟨3055131160551504842487161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32588065712549384986529717 3055131160551504842487161)
                    ·
                      refine ⟨2291348370413628631865371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3055131160551504842487161 2291348370413628631865371)
                      ·
                        rfl

theorem cell23_4462385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_4462385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462385 prefixEnd_4462385 := by exact prefixLift 4462385
  have htrace : WordTrace (prefixWord ++ tailWord_4462385) baseStart_4462385 baseEnd_4462385 := by
    simpa [prefixWord, tailWord_4462385, baseEnd_4462385] using wordTrace_append hprefix tailTrace_4462385
  have hstable : (prefixWord ++ tailWord_4462385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462385).length < 2 ^ (prefixWord ++ tailWord_4462385).sum := by decide
  have hdescent : baseEnd_4462385 < baseStart_4462385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462391 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 3, 6]
def baseStart_4462391 : Nat := 118140960795 + 4462391 * 2 ^ 59
def prefixEnd_4462391 : Nat := 4983230072969 + 3 ^ 40 * 4462391 * 2
def baseEnd_4462391 : Nat := 763783817099185202796781

theorem tailTrace_4462391 : CollatzResearch.WordTrace tailWord_4462391 prefixEnd_4462391 763783817099185202796781 := by
  unfold tailWord_4462391
  simp only [CollatzResearch.WordTrace]
  refine ⟨162756770776526997552779027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108504513851017998368519351 162756770776526997552779027)
  ·
    refine ⟨244135156164790496329168541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162756770776526997552779027 244135156164790496329168541)
    ·
      refine ⟨91550683561796436123438203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244135156164790496329168541 91550683561796436123438203)
      ·
        refine ⟨137326025342694654185157305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91550683561796436123438203 137326025342694654185157305)
        ·
          refine ⟨102994519007020990638867979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137326025342694654185157305 102994519007020990638867979)
          ·
            refine ⟨154491778510531485958301969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102994519007020990638867979 154491778510531485958301969)
            ·
              refine ⟨115868833882898614468726477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154491778510531485958301969 115868833882898614468726477)
              ·
                refine ⟨43450812706086980425772429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115868833882898614468726477 43450812706086980425772429)
                ·
                  refine ⟨16294054764782617659664661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43450812706086980425772429 16294054764782617659664661)
                  ·
                    refine ⟨763783817099185202796781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16294054764782617659664661 763783817099185202796781)
                    ·
                      rfl

theorem cell23_4462391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_4462391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462391 prefixEnd_4462391 := by exact prefixLift 4462391
  have htrace : WordTrace (prefixWord ++ tailWord_4462391) baseStart_4462391 baseEnd_4462391 := by
    simpa [prefixWord, tailWord_4462391, baseEnd_4462391] using wordTrace_append hprefix tailTrace_4462391
  have hstable : (prefixWord ++ tailWord_4462391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462391).length < 2 ^ (prefixWord ++ tailWord_4462391).sum := by decide
  have hdescent : baseEnd_4462391 < baseStart_4462391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462392 : List Nat := [2, 1, 2, 1, 3, 3, 1, 5, 1, 1, 3]
def baseStart_4462392 : Nat := 118140960795 + 4462392 * 2 ^ 59
def prefixEnd_4462392 : Nat := 4983230072969 + 3 ^ 40 * 4462392 * 2
def baseEnd_4462392 : Nat := 2291351964778210104477839

theorem tailTrace_4462392 : CollatzResearch.WordTrace tailWord_4462392 prefixEnd_4462392 2291351964778210104477839 := by
  unfold tailWord_4462392
  simp only [CollatzResearch.WordTrace]
  refine ⟨81378403624761687361782715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108504538166348916482376953 81378403624761687361782715)
  ·
    refine ⟨122067605437142531042674073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81378403624761687361782715 122067605437142531042674073)
    ·
      refine ⟨91550704077856898282005555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122067605437142531042674073 91550704077856898282005555)
      ·
        refine ⟨137326056116785347423008333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91550704077856898282005555 137326056116785347423008333)
        ·
          refine ⟨51497271043794505283628125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137326056116785347423008333 51497271043794505283628125)
          ·
            refine ⟨19311476641422939481360547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51497271043794505283628125 19311476641422939481360547)
            ·
              refine ⟨28967214962134409222040821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19311476641422939481360547 28967214962134409222040821)
              ·
                refine ⟨2715676402700100864566327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28967214962134409222040821 2715676402700100864566327)
                ·
                  refine ⟨4073514604050151296849491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2715676402700100864566327 4073514604050151296849491)
                  ·
                    refine ⟨6110271906075226945274237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4073514604050151296849491 6110271906075226945274237)
                    ·
                      refine ⟨2291351964778210104477839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6110271906075226945274237 2291351964778210104477839)
                      ·
                        rfl

theorem cell23_4462392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 1, 1, 3].length) (baseStart_4462392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462392 prefixEnd_4462392 := by exact prefixLift 4462392
  have htrace : WordTrace (prefixWord ++ tailWord_4462392) baseStart_4462392 baseEnd_4462392 := by
    simpa [prefixWord, tailWord_4462392, baseEnd_4462392] using wordTrace_append hprefix tailTrace_4462392
  have hstable : (prefixWord ++ tailWord_4462392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462392).length < 2 ^ (prefixWord ++ tailWord_4462392).sum := by decide
  have hdescent : baseEnd_4462392 < baseStart_4462392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462411 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 4]
def baseStart_4462411 : Nat := 118140960795 + 4462411 * 2 ^ 59
def prefixEnd_4462411 : Nat := 4983230072969 + 3 ^ 40 * 4462411 * 2
def baseEnd_4462411 : Nat := 2291361720910645530140251

theorem tailTrace_4462411 : CollatzResearch.WordTrace tailWord_4462411 prefixEnd_4462411 2291361720910645530140251 := by
  unfold tailWord_4462411
  simp only [CollatzResearch.WordTrace]
  refine ⟨162757500236454540968507087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108505000157636360645671391 162757500236454540968507087)
  ·
    refine ⟨244136250354681811452760631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162757500236454540968507087 244136250354681811452760631)
    ·
      refine ⟨366204375532022717179140947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244136250354681811452760631 366204375532022717179140947)
      ·
        refine ⟨549306563298034075768711421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366204375532022717179140947 549306563298034075768711421)
        ·
          refine ⟨205989961236762778413266783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 549306563298034075768711421 205989961236762778413266783)
          ·
            refine ⟨308984941855144167619900175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205989961236762778413266783 308984941855144167619900175)
            ·
              refine ⟨463477412782716251429850263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308984941855144167619900175 463477412782716251429850263)
              ·
                refine ⟨695216119174074377144775395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463477412782716251429850263 695216119174074377144775395)
                ·
                  refine ⟨1042824178761111565717163093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 695216119174074377144775395 1042824178761111565717163093)
                  ·
                    refine ⟨12220595844856776160748005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1042824178761111565717163093 12220595844856776160748005)
                    ·
                      refine ⟨2291361720910645530140251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12220595844856776160748005 2291361720910645530140251)
                      ·
                        rfl

theorem cell23_4462411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 4].length) (baseStart_4462411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462411 prefixEnd_4462411 := by exact prefixLift 4462411
  have htrace : WordTrace (prefixWord ++ tailWord_4462411) baseStart_4462411 baseEnd_4462411 := by
    simpa [prefixWord, tailWord_4462411, baseEnd_4462411] using wordTrace_append hprefix tailTrace_4462411
  have hstable : (prefixWord ++ tailWord_4462411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462411).length < 2 ^ (prefixWord ++ tailWord_4462411).sum := by decide
  have hdescent : baseEnd_4462411 < baseStart_4462411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462418 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_4462418 : Nat := 118140960795 + 4462418 * 2 ^ 59
def prefixEnd_4462418 : Nat := 4983230072969 + 3 ^ 40 * 4462418 * 2
def baseEnd_4462418 : Nat := 2291365315275227002752719

theorem tailTrace_4462418 : CollatzResearch.WordTrace tailWord_4462418 prefixEnd_4462418 2291365315275227002752719 := by
  unfold tailWord_4462418
  simp only [CollatzResearch.WordTrace]
  refine ⟨40689438886857295291002977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108505170364952787442674605 40689438886857295291002977)
  ·
    refine ⟨30517079165142971468252233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40689438886857295291002977 30517079165142971468252233)
    ·
      refine ⟨22887809373857228601189175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30517079165142971468252233 22887809373857228601189175)
      ·
        refine ⟨34331714060785842901783763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22887809373857228601189175 34331714060785842901783763)
        ·
          refine ⟨51497571091178764352675645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34331714060785842901783763 51497571091178764352675645)
          ·
            refine ⟨19311589159192036632253367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51497571091178764352675645 19311589159192036632253367)
            ·
              refine ⟨28967383738788054948380051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19311589159192036632253367 28967383738788054948380051)
              ·
                refine ⟨43451075608182082422570077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28967383738788054948380051 43451075608182082422570077)
                ·
                  refine ⟨16294153353068280908463779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43451075608182082422570077 16294153353068280908463779)
                  ·
                    refine ⟨24441230029602421362695669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16294153353068280908463779 24441230029602421362695669)
                    ·
                      refine ⟨2291365315275227002752719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24441230029602421362695669 2291365315275227002752719)
                      ·
                        rfl

theorem cell23_4462418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_4462418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462418 prefixEnd_4462418 := by exact prefixLift 4462418
  have htrace : WordTrace (prefixWord ++ tailWord_4462418) baseStart_4462418 baseEnd_4462418 := by
    simpa [prefixWord, tailWord_4462418, baseEnd_4462418] using wordTrace_append hprefix tailTrace_4462418
  have hstable : (prefixWord ++ tailWord_4462418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462418).length < 2 ^ (prefixWord ++ tailWord_4462418).sum := by decide
  have hdescent : baseEnd_4462418 < baseStart_4462418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462432 : List Nat := [2, 1, 1, 3, 3, 2, 2, 2, 3, 2, 2]
def baseStart_4462432 : Nat := 118140960795 + 4462432 * 2 ^ 59
def prefixEnd_4462432 : Nat := 4983230072969 + 3 ^ 40 * 4462432 * 2
def baseEnd_4462432 : Nat := 2291372504004389947977655

theorem tailTrace_4462432 : CollatzResearch.WordTrace tailWord_4462432 prefixEnd_4462432 2291372504004389947977655 := by
  unfold tailWord_4462432
  simp only [CollatzResearch.WordTrace]
  refine ⟨81379133084689230777510775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108505510779585641036681033 81379133084689230777510775)
  ·
    refine ⟨122068699627033846166266163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81379133084689230777510775 122068699627033846166266163)
    ·
      refine ⟨183103049440550769249399245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122068699627033846166266163 183103049440550769249399245)
      ·
        refine ⟨68663643540206538468524717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183103049440550769249399245 68663643540206538468524717)
        ·
          refine ⟨25748866327577451925696769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68663643540206538468524717 25748866327577451925696769)
          ·
            refine ⟨19311649745683088944272577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25748866327577451925696769 19311649745683088944272577)
            ·
              refine ⟨14483737309262316708204433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19311649745683088944272577 14483737309262316708204433)
              ·
                refine ⟨10862802981946737531153325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14483737309262316708204433 10862802981946737531153325)
                ·
                  refine ⟨4073551118230026574182497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10862802981946737531153325 4073551118230026574182497)
                  ·
                    refine ⟨3055163338672519930636873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4073551118230026574182497 3055163338672519930636873)
                    ·
                      refine ⟨2291372504004389947977655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3055163338672519930636873 2291372504004389947977655)
                      ·
                        rfl

theorem cell23_4462432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_4462432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462432 prefixEnd_4462432 := by exact prefixLift 4462432
  have htrace : WordTrace (prefixWord ++ tailWord_4462432) baseStart_4462432 baseEnd_4462432 := by
    simpa [prefixWord, tailWord_4462432, baseEnd_4462432] using wordTrace_append hprefix tailTrace_4462432
  have hstable : (prefixWord ++ tailWord_4462432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462432).length < 2 ^ (prefixWord ++ tailWord_4462432).sum := by decide
  have hdescent : baseEnd_4462432 < baseStart_4462432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462441 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 1, 4, 6]
def baseStart_4462441 : Nat := 118140960795 + 4462441 * 2 ^ 59
def prefixEnd_4462441 : Nat := 4983230072969 + 3 ^ 40 * 4462441 * 2
def baseEnd_4462441 : Nat := 2291377125330280412765113

theorem tailTrace_4462441 : CollatzResearch.WordTrace tailWord_4462441 prefixEnd_4462441 2291377125330280412765113 := by
  unfold tailWord_4462441
  simp only [CollatzResearch.WordTrace]
  refine ⟨162758594426345856092099177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108505729617563904061399451 162758594426345856092099177)
  ·
    refine ⟨122068945819759392069074383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162758594426345856092099177 122068945819759392069074383)
    ·
      refine ⟨183103418729639088103611575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122068945819759392069074383 183103418729639088103611575)
      ·
        refine ⟨274655128094458632155417363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183103418729639088103611575 274655128094458632155417363)
        ·
          refine ⟨411982692141687948233126045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274655128094458632155417363 411982692141687948233126045)
          ·
            refine ⟨154493509553132980587422267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 411982692141687948233126045 154493509553132980587422267)
            ·
              refine ⟨231740264329699470881133401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154493509553132980587422267 231740264329699470881133401)
              ·
                refine ⟨173805198247274603160850051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231740264329699470881133401 173805198247274603160850051)
                ·
                  refine ⟨260707797370911904741275077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173805198247274603160850051 260707797370911904741275077)
                  ·
                    refine ⟨48882712007045982138989077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 260707797370911904741275077 48882712007045982138989077)
                    ·
                      refine ⟨2291377125330280412765113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48882712007045982138989077 2291377125330280412765113)
                      ·
                        rfl

theorem cell23_4462441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_4462441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462441 prefixEnd_4462441 := by exact prefixLift 4462441
  have htrace : WordTrace (prefixWord ++ tailWord_4462441) baseStart_4462441 baseEnd_4462441 := by
    simpa [prefixWord, tailWord_4462441, baseEnd_4462441] using wordTrace_append hprefix tailTrace_4462441
  have hstable : (prefixWord ++ tailWord_4462441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462441).length < 2 ^ (prefixWord ++ tailWord_4462441).sum := by decide
  have hdescent : baseEnd_4462441 < baseStart_4462441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462448 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 3]
def baseStart_4462448 : Nat := 118140960795 + 4462448 * 2 ^ 59
def prefixEnd_4462448 : Nat := 4983230072969 + 3 ^ 40 * 4462448 * 2
def baseEnd_4462448 : Nat := 2291380719694861885377581

theorem tailTrace_4462448 : CollatzResearch.WordTrace tailWord_4462448 prefixEnd_4462448 2291380719694861885377581 := by
  unfold tailWord_4462448
  simp only [CollatzResearch.WordTrace]
  refine ⟨81379424868660248143801999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108505899824880330858402665 81379424868660248143801999)
  ·
    refine ⟨122069137302990372215702999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81379424868660248143801999 122069137302990372215702999)
    ·
      refine ⟨183103705954485558323554499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122069137302990372215702999 183103705954485558323554499)
      ·
        refine ⟨274655558931728337485331749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183103705954485558323554499 274655558931728337485331749)
        ·
          refine ⟨51497917299699063278499703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 274655558931728337485331749 51497917299699063278499703)
          ·
            refine ⟨77246875949548594917749555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51497917299699063278499703 77246875949548594917749555)
            ·
              refine ⟨115870313924322892376624333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77246875949548594917749555 115870313924322892376624333)
              ·
                refine ⟨43451367721621084641234125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115870313924322892376624333 43451367721621084641234125)
                ·
                  refine ⟨16294262895607906740462797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43451367721621084641234125 16294262895607906740462797)
                  ·
                    refine ⟨6110348585852965027673549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16294262895607906740462797 6110348585852965027673549)
                    ·
                      refine ⟨2291380719694861885377581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6110348585852965027673549 2291380719694861885377581)
                      ·
                        rfl

theorem cell23_4462448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 3].length) (baseStart_4462448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462448 prefixEnd_4462448 := by exact prefixLift 4462448
  have htrace : WordTrace (prefixWord ++ tailWord_4462448) baseStart_4462448 baseEnd_4462448 := by
    simpa [prefixWord, tailWord_4462448, baseEnd_4462448] using wordTrace_append hprefix tailTrace_4462448
  have hstable : (prefixWord ++ tailWord_4462448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462448).length < 2 ^ (prefixWord ++ tailWord_4462448).sum := by decide
  have hdescent : baseEnd_4462448 < baseStart_4462448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462451 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 1, 9]
def baseStart_4462451 : Nat := 118140960795 + 4462451 * 2 ^ 59
def prefixEnd_4462451 : Nat := 4983230072969 + 3 ^ 40 * 4462451 * 2
def baseEnd_4462451 : Nat := 763794086712275124546689

theorem tailTrace_4462451 : CollatzResearch.WordTrace tailWord_4462451 prefixEnd_4462451 763794086712275124546689 := by
  unfold tailWord_4462451
  simp only [CollatzResearch.WordTrace]
  refine ⟨162758959156309627799963207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108505972770873085199975471 162758959156309627799963207)
  ·
    refine ⟨244138438734464441699944811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162758959156309627799963207 244138438734464441699944811)
    ·
      refine ⟨366207658101696662549917217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244138438734464441699944811 366207658101696662549917217)
      ·
        refine ⟨274655743576272496912437913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 366207658101696662549917217 274655743576272496912437913)
        ·
          refine ⟨205991807682204372684328435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274655743576272496912437913 205991807682204372684328435)
          ·
            refine ⟨308987711523306559026492653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205991807682204372684328435 308987711523306559026492653)
            ·
              refine ⟨115870391821239959634934745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 308987711523306559026492653 115870391821239959634934745)
              ·
                refine ⟨86902793865929969726201059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115870391821239959634934745 86902793865929969726201059)
                ·
                  refine ⟨130354190798894954589301589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86902793865929969726201059 130354190798894954589301589)
                  ·
                    refine ⟨763794086712275124546689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 130354190798894954589301589 763794086712275124546689)
                    ·
                      rfl

theorem cell23_4462451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 9].length) (baseStart_4462451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462451 prefixEnd_4462451 := by exact prefixLift 4462451
  have htrace : WordTrace (prefixWord ++ tailWord_4462451) baseStart_4462451 baseEnd_4462451 := by
    simpa [prefixWord, tailWord_4462451, baseEnd_4462451] using wordTrace_append hprefix tailTrace_4462451
  have hstable : (prefixWord ++ tailWord_4462451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462451).length < 2 ^ (prefixWord ++ tailWord_4462451).sum := by decide
  have hdescent : baseEnd_4462451 < baseStart_4462451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462475 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 3, 3, 2]
def baseStart_4462475 : Nat := 118140960795 + 4462475 * 2 ^ 59
def prefixEnd_4462475 : Nat := 4983230072969 + 3 ^ 40 * 4462475 * 2
def baseEnd_4462475 : Nat := 2291394583672533279739957

theorem tailTrace_4462475 : CollatzResearch.WordTrace tailWord_4462475 prefixEnd_4462475 2291394583672533279739957 := by
  unfold tailWord_4462475
  simp only [CollatzResearch.WordTrace]
  refine ⟨162759834508222679898836879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108506556338815119932557919 162759834508222679898836879)
  ·
    refine ⟨244139751762334019848255319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162759834508222679898836879 244139751762334019848255319)
    ·
      refine ⟨366209627643501029772382979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244139751762334019848255319 366209627643501029772382979)
      ·
        refine ⟨549314441465251544658574469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366209627643501029772382979 549314441465251544658574469)
        ·
          refine ⟨102996457774734664623482713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 549314441465251544658574469 102996457774734664623482713)
          ·
            refine ⟨77247343331050998467612035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102996457774734664623482713 77247343331050998467612035)
            ·
              refine ⟨115871014996576497701418053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77247343331050998467612035 115871014996576497701418053)
              ·
                refine ⟨21725815311858093319015885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115871014996576497701418053 21725815311858093319015885)
                ·
                  refine ⟨8147180741946784994630957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21725815311858093319015885 8147180741946784994630957)
                  ·
                    refine ⟨3055192778230044372986609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8147180741946784994630957 3055192778230044372986609)
                    ·
                      refine ⟨2291394583672533279739957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3055192778230044372986609 2291394583672533279739957)
                      ·
                        rfl

theorem cell23_4462475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 3, 2].length) (baseStart_4462475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462475 prefixEnd_4462475 := by exact prefixLift 4462475
  have htrace : WordTrace (prefixWord ++ tailWord_4462475) baseStart_4462475 baseEnd_4462475 := by
    simpa [prefixWord, tailWord_4462475, baseEnd_4462475] using wordTrace_append hprefix tailTrace_4462475
  have hstable : (prefixWord ++ tailWord_4462475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462475).length < 2 ^ (prefixWord ++ tailWord_4462475).sum := by decide
  have hdescent : baseEnd_4462475 < baseStart_4462475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462486 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_4462486 : Nat := 118140960795 + 4462486 * 2 ^ 59
def prefixEnd_4462486 : Nat := 4983230072969 + 3 ^ 40 * 4462486 * 2
def baseEnd_4462486 : Nat := 2291400231959732736702407

theorem tailTrace_4462486 : CollatzResearch.WordTrace tailWord_4462486 prefixEnd_4462486 2291400231959732736702407 := by
  unfold tailWord_4462486
  simp only [CollatzResearch.WordTrace]
  refine ⟨10172514731948926798592957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108506823807455219184991541 10172514731948926798592957)
  ·
    refine ⟨3814693024480847549472359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10172514731948926798592957 3814693024480847549472359)
    ·
      refine ⟨5722039536721271324208539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3814693024480847549472359 5722039536721271324208539)
      ·
        refine ⟨8583059305081906986312809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5722039536721271324208539 8583059305081906986312809)
        ·
          refine ⟨6437294478811430239734607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8583059305081906986312809 6437294478811430239734607)
          ·
            refine ⟨9655941718217145359601911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6437294478811430239734607 9655941718217145359601911)
            ·
              refine ⟨14483912577325718039402867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9655941718217145359601911 14483912577325718039402867)
              ·
                refine ⟨21725868865988577059104301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14483912577325718039402867 21725868865988577059104301)
                ·
                  refine ⟨8147200824745716397164113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21725868865988577059104301 8147200824745716397164113)
                  ·
                    refine ⟨6110400618559287297873085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8147200824745716397164113 6110400618559287297873085)
                    ·
                      refine ⟨2291400231959732736702407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6110400618559287297873085 2291400231959732736702407)
                      ·
                        rfl

theorem cell23_4462486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_4462486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462486 prefixEnd_4462486 := by exact prefixLift 4462486
  have htrace : WordTrace (prefixWord ++ tailWord_4462486) baseStart_4462486 baseEnd_4462486 := by
    simpa [prefixWord, tailWord_4462486, baseEnd_4462486] using wordTrace_append hprefix tailTrace_4462486
  have hstable : (prefixWord ++ tailWord_4462486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462486).length < 2 ^ (prefixWord ++ tailWord_4462486).sum := by decide
  have hdescent : baseEnd_4462486 < baseStart_4462486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462508 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 3]
def baseStart_4462508 : Nat := 118140960795 + 4462508 * 2 ^ 59
def prefixEnd_4462508 : Nat := 4983230072969 + 3 ^ 40 * 4462508 * 2
def baseEnd_4462508 : Nat := 2291411528534131650627305

theorem tailTrace_4462508 : CollatzResearch.WordTrace tailWord_4462508 prefixEnd_4462508 2291411528534131650627305 := by
  unfold tailWord_4462508
  simp only [CollatzResearch.WordTrace]
  refine ⟨81380519058551563267394089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108507358744735417689858785 81380519058551563267394089)
  ·
    refine ⟨61035389293913672450545567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81380519058551563267394089 61035389293913672450545567)
    ·
      refine ⟨91553083940870508675818351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61035389293913672450545567 91553083940870508675818351)
      ·
        refine ⟨137329625911305763013727527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91553083940870508675818351 137329625911305763013727527)
        ·
          refine ⟨205994438866958644520591291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137329625911305763013727527 205994438866958644520591291)
          ·
            refine ⟨308991658300437966780886937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205994438866958644520591291 308991658300437966780886937)
            ·
              refine ⟨231743743725328475085665203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308991658300437966780886937 231743743725328475085665203)
              ·
                refine ⟨347615615587992712628497805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231743743725328475085665203 347615615587992712628497805)
                ·
                  refine ⟨130355855845497267235686677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 347615615587992712628497805 130355855845497267235686677)
                  ·
                    refine ⟨6110430742757684401672813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 130355855845497267235686677 6110430742757684401672813)
                    ·
                      refine ⟨2291411528534131650627305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6110430742757684401672813 2291411528534131650627305)
                      ·
                        rfl

theorem cell23_4462508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 3].length) (baseStart_4462508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462508 prefixEnd_4462508 := by exact prefixLift 4462508
  have htrace : WordTrace (prefixWord ++ tailWord_4462508) baseStart_4462508 baseEnd_4462508 := by
    simpa [prefixWord, tailWord_4462508, baseEnd_4462508] using wordTrace_append hprefix tailTrace_4462508
  have hstable : (prefixWord ++ tailWord_4462508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462508).length < 2 ^ (prefixWord ++ tailWord_4462508).sum := by decide
  have hdescent : baseEnd_4462508 < baseStart_4462508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462525 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 2, 4, 3]
def baseStart_4462525 : Nat := 118140960795 + 4462525 * 2 ^ 59
def prefixEnd_4462525 : Nat := 4983230072969 + 3 ^ 40 * 4462525 * 2
def baseEnd_4462525 : Nat := 2291420257705258084114727

theorem tailTrace_4462525 : CollatzResearch.WordTrace tailWord_4462525 prefixEnd_4462525 2291420257705258084114727 := by
  unfold tailWord_4462525
  simp only [CollatzResearch.WordTrace]
  refine ⟨162761658158041538438157029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108507772105361025625438019 162761658158041538438157029)
  ·
    refine ⟨30517810904632788457154443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162761658158041538438157029 30517810904632788457154443)
    ·
      refine ⟨45776716356949182685731665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30517810904632788457154443 45776716356949182685731665)
      ·
        refine ⟨34332537267711887014298749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45776716356949182685731665 34332537267711887014298749)
        ·
          refine ⟨12874701475391957630362031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34332537267711887014298749 12874701475391957630362031)
          ·
            refine ⟨19312052213087936445543047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12874701475391957630362031 19312052213087936445543047)
            ·
              refine ⟨28968078319631904668314571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19312052213087936445543047 28968078319631904668314571)
              ·
                refine ⟨43452117479447857002471857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28968078319631904668314571 43452117479447857002471857)
                ·
                  refine ⟨32589088109585892751853893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43452117479447857002471857 32589088109585892751853893)
                  ·
                    refine ⟨6110454020547354890972605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32589088109585892751853893 6110454020547354890972605)
                    ·
                      refine ⟨2291420257705258084114727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6110454020547354890972605 2291420257705258084114727)
                      ·
                        rfl

theorem cell23_4462525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_4462525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462525 prefixEnd_4462525 := by exact prefixLift 4462525
  have htrace : WordTrace (prefixWord ++ tailWord_4462525) baseStart_4462525 baseEnd_4462525 := by
    simpa [prefixWord, tailWord_4462525, baseEnd_4462525] using wordTrace_append hprefix tailTrace_4462525
  have hstable : (prefixWord ++ tailWord_4462525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462525).length < 2 ^ (prefixWord ++ tailWord_4462525).sum := by decide
  have hdescent : baseEnd_4462525 < baseStart_4462525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462528 : List Nat := [2, 1, 1, 2, 3, 2, 2, 3, 7]
def baseStart_4462528 : Nat := 118140960795 + 4462528 * 2 ^ 59
def prefixEnd_4462528 : Nat := 4983230072969 + 3 ^ 40 * 4462528 * 2
def baseEnd_4462528 : Nat := 254602422016357952486357

theorem tailTrace_4462528 : CollatzResearch.WordTrace tailWord_4462528 prefixEnd_4462528 254602422016357952486357 := by
  unfold tailWord_4462528
  simp only [CollatzResearch.WordTrace]
  refine ⟨81380883788515334975258119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108507845051353779967010825 81380883788515334975258119)
  ·
    refine ⟨122071325682773002462887179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81380883788515334975258119 122071325682773002462887179)
    ·
      refine ⟨183106988524159503694330769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122071325682773002462887179 183106988524159503694330769)
      ·
        refine ⟨137330241393119627770748077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183106988524159503694330769 137330241393119627770748077)
        ·
          refine ⟨51498840522419860414030529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137330241393119627770748077 51498840522419860414030529)
          ·
            refine ⟨38624130391814895310522897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51498840522419860414030529 38624130391814895310522897)
            ·
              refine ⟨28968097793861171482892173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38624130391814895310522897 28968097793861171482892173)
              ·
                refine ⟨10863036672697939306084565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28968097793861171482892173 10863036672697939306084565)
                ·
                  refine ⟨254602422016357952486357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10863036672697939306084565 254602422016357952486357)
                  ·
                    rfl

theorem cell23_4462528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 7].length) (baseStart_4462528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462528 prefixEnd_4462528 := by exact prefixLift 4462528
  have htrace : WordTrace (prefixWord ++ tailWord_4462528) baseStart_4462528 baseEnd_4462528 := by
    simpa [prefixWord, tailWord_4462528, baseEnd_4462528] using wordTrace_append hprefix tailTrace_4462528
  have hstable : (prefixWord ++ tailWord_4462528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462528).length < 2 ^ (prefixWord ++ tailWord_4462528).sum := by decide
  have hdescent : baseEnd_4462528 < baseStart_4462528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462608 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 6]
def baseStart_4462608 : Nat := 118140960795 + 4462608 * 2 ^ 59
def prefixEnd_4462608 : Nat := 4983230072969 + 3 ^ 40 * 4462608 * 2
def baseEnd_4462608 : Nat := 2291462876599581259376845

theorem tailTrace_4462608 : CollatzResearch.WordTrace tailWord_4462608 prefixEnd_4462608 2291462876599581259376845 := by
  unfold tailWord_4462608
  simp only [CollatzResearch.WordTrace]
  refine ⟨81382342708370421806714239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108509790277827229075618985 81382342708370421806714239)
  ·
    refine ⟨122073514062555632710071359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81382342708370421806714239 122073514062555632710071359)
    ·
      refine ⟨183110271093833449065107039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122073514062555632710071359 183110271093833449065107039)
      ·
        refine ⟨274665406640750173597660559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183110271093833449065107039 274665406640750173597660559)
        ·
          refine ⟨411998109961125260396490839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274665406640750173597660559 411998109961125260396490839)
          ·
            refine ⟨617997164941687890594736259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 411998109961125260396490839 617997164941687890594736259)
            ·
              refine ⟨926995747412531835892104389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 617997164941687890594736259 926995747412531835892104389)
              ·
                refine ⟨173811702639849719229769573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 926995747412531835892104389 173811702639849719229769573)
                ·
                  refine ⟨32589694244971822355581795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 173811702639849719229769573 32589694244971822355581795)
                  ·
                    refine ⟨48884541367457733533372693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32589694244971822355581795 48884541367457733533372693)
                    ·
                      refine ⟨2291462876599581259376845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48884541367457733533372693 2291462876599581259376845)
                      ·
                        rfl

theorem cell23_4462608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_4462608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462608 prefixEnd_4462608 := by exact prefixLift 4462608
  have htrace : WordTrace (prefixWord ++ tailWord_4462608) baseStart_4462608 baseEnd_4462608 := by
    simpa [prefixWord, tailWord_4462608, baseEnd_4462608] using wordTrace_append hprefix tailTrace_4462608
  have hstable : (prefixWord ++ tailWord_4462608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462608).length < 2 ^ (prefixWord ++ tailWord_4462608).sum := by decide
  have hdescent : baseEnd_4462608 < baseStart_4462608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462665 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 3, 5]
def baseStart_4462665 : Nat := 118140960795 + 4462665 * 2 ^ 59
def prefixEnd_4462665 : Nat := 4983230072969 + 3 ^ 40 * 4462665 * 2
def baseEnd_4462665 : Nat := 763830714998962512121361

theorem tailTrace_4462665 : CollatzResearch.WordTrace tailWord_4462665 prefixEnd_4462665 763830714998962512121361 := by
  unfold tailWord_4462665
  simp only [CollatzResearch.WordTrace]
  refine ⟨162766764377534342348253449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108511176251689561565502299 162766764377534342348253449)
  ·
    refine ⟨122075073283150756761190087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162766764377534342348253449 122075073283150756761190087)
    ·
      refine ⟨183112609924726135141785131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122075073283150756761190087 183112609924726135141785131)
      ·
        refine ⟨274668914887089202712677697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183112609924726135141785131 274668914887089202712677697)
        ·
          refine ⟨206001686165316902034508273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274668914887089202712677697 206001686165316902034508273)
          ·
            refine ⟨154501264623987676525881205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206001686165316902034508273 154501264623987676525881205)
            ·
              refine ⟨14484493558498844674301363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 154501264623987676525881205 14484493558498844674301363)
              ·
                refine ⟨21726740337748267011452045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14484493558498844674301363 21726740337748267011452045)
                ·
                  refine ⟨8147527626655600129294517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21726740337748267011452045 8147527626655600129294517)
                  ·
                    refine ⟨763830714998962512121361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8147527626655600129294517 763830714998962512121361)
                    ·
                      rfl

theorem cell23_4462665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 5].length) (baseStart_4462665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462665 prefixEnd_4462665 := by exact prefixLift 4462665
  have htrace : WordTrace (prefixWord ++ tailWord_4462665) baseStart_4462665 baseEnd_4462665 := by
    simpa [prefixWord, tailWord_4462665, baseEnd_4462665] using wordTrace_append hprefix tailTrace_4462665
  have hstable : (prefixWord ++ tailWord_4462665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462665).length < 2 ^ (prefixWord ++ tailWord_4462665).sum := by decide
  have hdescent : baseEnd_4462665 < baseStart_4462665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462690 : List Nat := [3, 3, 2, 2, 2, 2, 2, 2, 1, 4]
def baseStart_4462690 : Nat := 118140960795 + 4462690 * 2 ^ 59
def prefixEnd_4462690 : Nat := 4983230072969 + 3 ^ 40 * 4462690 * 2
def baseEnd_4462690 : Nat := 763834994004416646183823

theorem tailTrace_4462690 : CollatzResearch.WordTrace tailWord_4462690 prefixEnd_4462690 763834994004416646183823 := by
  unfold tailWord_4462690
  simp only [CollatzResearch.WordTrace]
  refine ⟨40691919050610942904478381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108511784134962514411942349 40691919050610942904478381)
  ·
    refine ⟨15259469643979103589179393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40691919050610942904478381 15259469643979103589179393)
    ·
      refine ⟨11444602232984327691884545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15259469643979103589179393 11444602232984327691884545)
      ·
        refine ⟨8583451674738245768913409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11444602232984327691884545 8583451674738245768913409)
        ·
          refine ⟨6437588756053684326685057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8583451674738245768913409 6437588756053684326685057)
          ·
            refine ⟨4828191567040263245013793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6437588756053684326685057 4828191567040263245013793)
            ·
              refine ⟨3621143675280197433760345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4828191567040263245013793 3621143675280197433760345)
              ·
                refine ⟨2715857756460148075320259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3621143675280197433760345 2715857756460148075320259)
                ·
                  refine ⟨4073786634690222112980389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2715857756460148075320259 4073786634690222112980389)
                  ·
                    refine ⟨763834994004416646183823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4073786634690222112980389 763834994004416646183823)
                    ·
                      rfl

theorem cell23_4462690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_4462690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462690 prefixEnd_4462690 := by exact prefixLift 4462690
  have htrace : WordTrace (prefixWord ++ tailWord_4462690) baseStart_4462690 baseEnd_4462690 := by
    simpa [prefixWord, tailWord_4462690, baseEnd_4462690] using wordTrace_append hprefix tailTrace_4462690
  have hstable : (prefixWord ++ tailWord_4462690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462690).length < 2 ^ (prefixWord ++ tailWord_4462690).sum := by decide
  have hdescent : baseEnd_4462690 < baseStart_4462690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462695 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 3, 6]
def baseStart_4462695 : Nat := 118140960795 + 4462695 * 2 ^ 59
def prefixEnd_4462695 : Nat := 4983230072969 + 3 ^ 40 * 4462695 * 2
def baseEnd_4462695 : Nat := 763835849805507472996315

theorem tailTrace_4462695 : CollatzResearch.WordTrace tailWord_4462695 prefixEnd_4462695 763835849805507472996315 := by
  unfold tailWord_4462695
  simp only [CollatzResearch.WordTrace]
  refine ⟨162767858567425657471845539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108511905711617104981230359 162767858567425657471845539)
  ·
    refine ⟨244151787851138486207768309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162767858567425657471845539 244151787851138486207768309)
    ·
      refine ⟨22889230111044233081978279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 244151787851138486207768309 22889230111044233081978279)
      ·
        refine ⟨34333845166566349622967419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22889230111044233081978279 34333845166566349622967419)
        ·
          refine ⟨51500767749849524434451129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34333845166566349622967419 51500767749849524434451129)
          ·
            refine ⟨38625575812387143325838347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51500767749849524434451129 38625575812387143325838347)
            ·
              refine ⟨57938363718580714988757521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38625575812387143325838347 57938363718580714988757521)
              ·
                refine ⟨43453772788935536241568141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57938363718580714988757521 43453772788935536241568141)
                ·
                  refine ⟨16295164795850826090588053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43453772788935536241568141 16295164795850826090588053)
                  ·
                    refine ⟨763835849805507472996315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16295164795850826090588053 763835849805507472996315)
                    ·
                      rfl

theorem cell23_4462695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_4462695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462695 prefixEnd_4462695 := by exact prefixLift 4462695
  have htrace : WordTrace (prefixWord ++ tailWord_4462695) baseStart_4462695 baseEnd_4462695 := by
    simpa [prefixWord, tailWord_4462695, baseEnd_4462695] using wordTrace_append hprefix tailTrace_4462695
  have hstable : (prefixWord ++ tailWord_4462695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462695).length < 2 ^ (prefixWord ++ tailWord_4462695).sum := by decide
  have hdescent : baseEnd_4462695 < baseStart_4462695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462702 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_4462702 : Nat := 118140960795 + 4462702 * 2 ^ 59
def prefixEnd_4462702 : Nat := 4983230072969 + 3 ^ 40 * 4462702 * 2
def baseEnd_4462702 : Nat := 2291511143781103891601413

theorem tailTrace_4462702 : CollatzResearch.WordTrace tailWord_4462702 prefixEnd_4462702 2291511143781103891601413 := by
  unfold tailWord_4462702
  simp only [CollatzResearch.WordTrace]
  refine ⟨20346014234800037208418795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108512075918933531778233573 20346014234800037208418795)
  ·
    refine ⟨30519021352200055812628193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20346014234800037208418795 30519021352200055812628193)
    ·
      refine ⟨22889266014150041859471145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30519021352200055812628193 22889266014150041859471145)
      ·
        refine ⟨17166949510612531394603359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22889266014150041859471145 17166949510612531394603359)
        ·
          refine ⟨25750424265918797091905039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17166949510612531394603359 25750424265918797091905039)
          ·
            refine ⟨38625636398878195637857559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25750424265918797091905039 38625636398878195637857559)
            ·
              refine ⟨57938454598317293456786339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38625636398878195637857559 57938454598317293456786339)
              ·
                refine ⟨86907681897475940185179509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57938454598317293456786339 86907681897475940185179509)
                ·
                  refine ⟨8147595177888369392360579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86907681897475940185179509 8147595177888369392360579)
                  ·
                    refine ⟨12221392766832554088540869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8147595177888369392360579 12221392766832554088540869)
                    ·
                      refine ⟨2291511143781103891601413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12221392766832554088540869 2291511143781103891601413)
                      ·
                        rfl

theorem cell23_4462702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_4462702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462702 prefixEnd_4462702 := by exact prefixLift 4462702
  have htrace : WordTrace (prefixWord ++ tailWord_4462702) baseStart_4462702 baseEnd_4462702 := by
    simpa [prefixWord, tailWord_4462702, baseEnd_4462702] using wordTrace_append hprefix tailTrace_4462702
  have hstable : (prefixWord ++ tailWord_4462702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462702).length < 2 ^ (prefixWord ++ tailWord_4462702).sum := by decide
  have hdescent : baseEnd_4462702 < baseStart_4462702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462705 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 3, 1, 5]
def baseStart_4462705 : Nat := 118140960795 + 4462705 * 2 ^ 59
def prefixEnd_4462705 : Nat := 4983230072969 + 3 ^ 40 * 4462705 * 2
def baseEnd_4462705 : Nat := 2291512684223067379863899

theorem tailTrace_4462705 : CollatzResearch.WordTrace tailWord_4462705 prefixEnd_4462705 2291512684223067379863899 := by
  unfold tailWord_4462705
  simp only [CollatzResearch.WordTrace]
  refine ⟨162768223297389429179709569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108512148864926286119806379 162768223297389429179709569)
  ·
    refine ⟨122076167473042071884782177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162768223297389429179709569 122076167473042071884782177)
    ·
      refine ⟨91557125604781553913586633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122076167473042071884782177 91557125604781553913586633)
      ·
        refine ⟨68667844203586165435189975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91557125604781553913586633 68667844203586165435189975)
        ·
          refine ⟨103001766305379248152784963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68667844203586165435189975 103001766305379248152784963)
          ·
            refine ⟨154502649458068872229177445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103001766305379248152784963 154502649458068872229177445)
            ·
              refine ⟨28969246773387913542970771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154502649458068872229177445 28969246773387913542970771)
              ·
                refine ⟨43453870160081870314456157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28969246773387913542970771 43453870160081870314456157)
                ·
                  refine ⟨16295201310030701367921059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43453870160081870314456157 16295201310030701367921059)
                  ·
                    refine ⟨24442801965046052051881589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16295201310030701367921059 24442801965046052051881589)
                    ·
                      refine ⟨2291512684223067379863899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24442801965046052051881589 2291512684223067379863899)
                      ·
                        rfl

theorem cell23_4462705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_4462705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462705 prefixEnd_4462705 := by exact prefixLift 4462705
  have htrace : WordTrace (prefixWord ++ tailWord_4462705) baseStart_4462705 baseEnd_4462705 := by
    simpa [prefixWord, tailWord_4462705, baseEnd_4462705] using wordTrace_append hprefix tailTrace_4462705
  have hstable : (prefixWord ++ tailWord_4462705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462705).length < 2 ^ (prefixWord ++ tailWord_4462705).sum := by decide
  have hdescent : baseEnd_4462705 < baseStart_4462705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462753 : List Nat := [1, 2, 3, 3, 1, 2, 2, 4, 1, 2, 2]
def baseStart_4462753 : Nat := 118140960795 + 4462753 * 2 ^ 59
def prefixEnd_4462753 : Nat := 4983230072969 + 3 ^ 40 * 4462753 * 2
def baseEnd_4462753 : Nat := 2291537331294483192063679

theorem tailTrace_4462753 : CollatzResearch.WordTrace tailWord_4462753 prefixEnd_4462753 2291537331294483192063679 := by
  unfold tailWord_4462753
  simp only [CollatzResearch.WordTrace]
  refine ⟨162769974001215533377456913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108513316000810355584971275 162769974001215533377456913)
  ·
    refine ⟨122077480500911650033092685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162769974001215533377456913 122077480500911650033092685)
    ·
      refine ⟨45779055187841868762409757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122077480500911650033092685 45779055187841868762409757)
      ·
        refine ⟨17167145695440700785903659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45779055187841868762409757 17167145695440700785903659)
        ·
          refine ⟨25750718543161051178855489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17167145695440700785903659 25750718543161051178855489)
          ·
            refine ⟨19313038907370788384141617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25750718543161051178855489 19313038907370788384141617)
            ·
              refine ⟨14484779180528091288106213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19313038907370788384141617 14484779180528091288106213)
              ·
                refine ⟨2715896096349017116519915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14484779180528091288106213 2715896096349017116519915)
                ·
                  refine ⟨4073844144523525674779873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2715896096349017116519915 4073844144523525674779873)
                  ·
                    refine ⟨3055383108392644256084905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4073844144523525674779873 3055383108392644256084905)
                    ·
                      refine ⟨2291537331294483192063679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3055383108392644256084905 2291537331294483192063679)
                      ·
                        rfl

theorem cell23_4462753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_4462753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462753 prefixEnd_4462753 := by exact prefixLift 4462753
  have htrace : WordTrace (prefixWord ++ tailWord_4462753) baseStart_4462753 baseEnd_4462753 := by
    simpa [prefixWord, tailWord_4462753, baseEnd_4462753] using wordTrace_append hprefix tailTrace_4462753
  have hstable : (prefixWord ++ tailWord_4462753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462753).length < 2 ^ (prefixWord ++ tailWord_4462753).sum := by decide
  have hdescent : baseEnd_4462753 < baseStart_4462753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462766 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_4462766 : Nat := 118140960795 + 4462766 * 2 ^ 59
def prefixEnd_4462766 : Nat := 4983230072969 + 3 ^ 40 * 4462766 * 2
def baseEnd_4462766 : Nat := 2291544006542991641201119

theorem tailTrace_4462766 : CollatzResearch.WordTrace tailWord_4462766 prefixEnd_4462766 2291544006542991641201119 := by
  unfold tailWord_4462766
  simp only [CollatzResearch.WordTrace]
  refine ⟨20346306018771054574710019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108513632100112291065120101 20346306018771054574710019)
  ·
    refine ⟨30519459028156581862065029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20346306018771054574710019 30519459028156581862065029)
    ·
      refine ⟨5722398567779359099137193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30519459028156581862065029 5722398567779359099137193)
      ·
        refine ⟨4291798925834519324352895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5722398567779359099137193 4291798925834519324352895)
        ·
          refine ⟨6437698388751778986529343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4291798925834519324352895 6437698388751778986529343)
          ·
            refine ⟨9656547583127668479794015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6437698388751778986529343 9656547583127668479794015)
            ·
              refine ⟨14484821374691502719691023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9656547583127668479794015 14484821374691502719691023)
              ·
                refine ⟨21727232062037254079536535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14484821374691502719691023 21727232062037254079536535)
                ·
                  refine ⟨32590848093055881119304803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21727232062037254079536535 32590848093055881119304803)
                  ·
                    refine ⟨48886272139583821678957205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32590848093055881119304803 48886272139583821678957205)
                    ·
                      refine ⟨2291544006542991641201119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48886272139583821678957205 2291544006542991641201119)
                      ·
                        rfl

theorem cell23_4462766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_4462766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462766 prefixEnd_4462766 := by exact prefixLift 4462766
  have htrace : WordTrace (prefixWord ++ tailWord_4462766) baseStart_4462766 baseEnd_4462766 := by
    simpa [prefixWord, tailWord_4462766, baseEnd_4462766] using wordTrace_append hprefix tailTrace_4462766
  have hstable : (prefixWord ++ tailWord_4462766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462766).length < 2 ^ (prefixWord ++ tailWord_4462766).sum := by decide
  have hdescent : baseEnd_4462766 < baseStart_4462766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462773 : List Nat := [1, 3, 3, 4, 1, 1, 2, 2, 1, 2, 3]
def baseStart_4462773 : Nat := 118140960795 + 4462773 * 2 ^ 59
def prefixEnd_4462773 : Nat := 4983230072969 + 3 ^ 40 * 4462773 * 2
def baseEnd_4462773 : Nat := 2291547600907573113813587

theorem tailTrace_4462773 : CollatzResearch.WordTrace tailWord_4462773 prefixEnd_4462773 2291547600907573113813587 := by
  unfold tailWord_4462773
  simp only [CollatzResearch.WordTrace]
  refine ⟨162770703461143076793184973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108513802307428717862123315 162770703461143076793184973)
  ·
    refine ⟨61039013797928653797444365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162770703461143076793184973 61039013797928653797444365)
    ·
      refine ⟨22889630174223245174041637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61039013797928653797444365 22889630174223245174041637)
      ·
        refine ⟨4291805657666858470132807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22889630174223245174041637 4291805657666858470132807)
        ·
          refine ⟨6437708486500287705199211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4291805657666858470132807 6437708486500287705199211)
          ·
            refine ⟨9656562729750431557798817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6437708486500287705199211 9656562729750431557798817)
            ·
              refine ⟨7242422047312823668349113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9656562729750431557798817 7242422047312823668349113)
              ·
                refine ⟨5431816535484617751261835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7242422047312823668349113 5431816535484617751261835)
                ·
                  refine ⟨8147724803226926626892753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5431816535484617751261835 8147724803226926626892753)
                  ·
                    refine ⟨6110793602420194970169565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8147724803226926626892753 6110793602420194970169565)
                    ·
                      refine ⟨2291547600907573113813587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6110793602420194970169565 2291547600907573113813587)
                      ·
                        rfl

theorem cell23_4462773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_4462773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462773 prefixEnd_4462773 := by exact prefixLift 4462773
  have htrace : WordTrace (prefixWord ++ tailWord_4462773) baseStart_4462773 baseEnd_4462773 := by
    simpa [prefixWord, tailWord_4462773, baseEnd_4462773] using wordTrace_append hprefix tailTrace_4462773
  have hstable : (prefixWord ++ tailWord_4462773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462773).length < 2 ^ (prefixWord ++ tailWord_4462773).sum := by decide
  have hdescent : baseEnd_4462773 < baseStart_4462773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462825 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 9]
def baseStart_4462825 : Nat := 118140960795 + 4462825 * 2 ^ 59
def prefixEnd_4462825 : Nat := 4983230072969 + 3 ^ 40 * 4462825 * 2
def baseEnd_4462825 : Nat := 2291574301901606910363347

theorem tailTrace_4462825 : CollatzResearch.WordTrace tailWord_4462825 prefixEnd_4462825 2291574301901606910363347 := by
  unfold tailWord_4462825
  simp only [CollatzResearch.WordTrace]
  refine ⟨162772600056954689674077929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108515066704636459782718619 162772600056954689674077929)
  ·
    refine ⟨122079450042716017255558447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162772600056954689674077929 122079450042716017255558447)
    ·
      refine ⟨183119175064074025883337671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122079450042716017255558447 183119175064074025883337671)
      ·
        refine ⟨274678762596111038825006507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183119175064074025883337671 274678762596111038825006507)
        ·
          refine ⟨412018143894166558237509761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274678762596111038825006507 412018143894166558237509761)
          ·
            refine ⟨309013607920624918678132321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 412018143894166558237509761 309013607920624918678132321)
            ·
              refine ⟨231760205940468689008599241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309013607920624918678132321 231760205940468689008599241)
              ·
                refine ⟨173820154455351516756449431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231760205940468689008599241 173820154455351516756449431)
                ·
                  refine ⟨260730231683027275134674147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173820154455351516756449431 260730231683027275134674147)
                  ·
                    refine ⟨391095347524540912702011221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 260730231683027275134674147 391095347524540912702011221)
                    ·
                      refine ⟨2291574301901606910363347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 391095347524540912702011221 2291574301901606910363347)
                      ·
                        rfl

theorem cell23_4462825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_4462825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462825 prefixEnd_4462825 := by exact prefixLift 4462825
  have htrace : WordTrace (prefixWord ++ tailWord_4462825) baseStart_4462825 baseEnd_4462825 := by
    simpa [prefixWord, tailWord_4462825, baseEnd_4462825] using wordTrace_append hprefix tailTrace_4462825
  have hstable : (prefixWord ++ tailWord_4462825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462825).length < 2 ^ (prefixWord ++ tailWord_4462825).sum := by decide
  have hdescent : baseEnd_4462825 < baseStart_4462825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462849 : List Nat := [1, 2, 4, 1, 1, 2, 2, 5, 5]
def baseStart_4462849 : Nat := 118140960795 + 4462849 * 2 ^ 59
def prefixEnd_4462849 : Nat := 4983230072969 + 3 ^ 40 * 4462849 * 2
def baseEnd_4462849 : Nat := 254620736159701646273693

theorem tailTrace_4462849 : CollatzResearch.WordTrace tailWord_4462849 prefixEnd_4462849 254620736159701646273693 := by
  unfold tailWord_4462849
  simp only [CollatzResearch.WordTrace]
  refine ⟨162773475408867741772951601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108515650272578494515301067 162773475408867741772951601)
  ·
    refine ⟨122080106556650806329713701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162773475408867741772951601 122080106556650806329713701)
    ·
      refine ⟨22890019979372026186821319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122080106556650806329713701 22890019979372026186821319)
      ·
        refine ⟨34335029969058039280231979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22890019979372026186821319 34335029969058039280231979)
        ·
          refine ⟨51502544953587058920347969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34335029969058039280231979 51502544953587058920347969)
          ·
            refine ⟨38626908715190294190260977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51502544953587058920347969 38626908715190294190260977)
            ·
              refine ⟨28970181536392720642695733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38626908715190294190260977 28970181536392720642695733)
              ·
                refine ⟨2715954519036817560252725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28970181536392720642695733 2715954519036817560252725)
                ·
                  refine ⟨254620736159701646273693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2715954519036817560252725 254620736159701646273693)
                  ·
                    rfl

theorem cell23_4462849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 5].length) (baseStart_4462849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462849 prefixEnd_4462849 := by exact prefixLift 4462849
  have htrace : WordTrace (prefixWord ++ tailWord_4462849) baseStart_4462849 baseEnd_4462849 := by
    simpa [prefixWord, tailWord_4462849, baseEnd_4462849] using wordTrace_append hprefix tailTrace_4462849
  have hstable : (prefixWord ++ tailWord_4462849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462849).length < 2 ^ (prefixWord ++ tailWord_4462849).sum := by decide
  have hdescent : baseEnd_4462849 < baseStart_4462849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462869 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 2, 5, 2]
def baseStart_4462869 : Nat := 118140960795 + 4462869 * 2 ^ 59
def prefixEnd_4462869 : Nat := 4983230072969 + 3 ^ 40 * 4462869 * 2
def baseEnd_4462869 : Nat := 2291596895050404738213145

theorem tailTrace_4462869 : CollatzResearch.WordTrace tailWord_4462869 prefixEnd_4462869 2291596895050404738213145 := by
  unfold tailWord_4462869
  simp only [CollatzResearch.WordTrace]
  refine ⟨162774204868795285188679661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108516136579196856792453107 162774204868795285188679661)
  ·
    refine ⟨61040326825798231945754873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162774204868795285188679661 61040326825798231945754873)
    ·
      refine ⟨45780245119348673959316155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61040326825798231945754873 45780245119348673959316155)
      ·
        refine ⟨68670367679023010938974233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45780245119348673959316155 68670367679023010938974233)
        ·
          refine ⟨51502775759267258204230675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68670367679023010938974233 51502775759267258204230675)
          ·
            refine ⟨77254163638900887306346013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51502775759267258204230675 77254163638900887306346013)
            ·
              refine ⟨28970311364587832739879755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77254163638900887306346013 28970311364587832739879755)
              ·
                refine ⟨43455467046881749109819633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28970311364587832739879755 43455467046881749109819633)
                ·
                  refine ⟨32591600285161311832364725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43455467046881749109819633 32591600285161311832364725)
                  ·
                    refine ⟨3055462526733872984284193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32591600285161311832364725 3055462526733872984284193)
                    ·
                      refine ⟨2291596895050404738213145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3055462526733872984284193 2291596895050404738213145)
                      ·
                        rfl

theorem cell23_4462869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_4462869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462869 prefixEnd_4462869 := by exact prefixLift 4462869
  have htrace : WordTrace (prefixWord ++ tailWord_4462869) baseStart_4462869 baseEnd_4462869 := by
    simpa [prefixWord, tailWord_4462869, baseEnd_4462869] using wordTrace_append hprefix tailTrace_4462869
  have hstable : (prefixWord ++ tailWord_4462869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462869).length < 2 ^ (prefixWord ++ tailWord_4462869).sum := by decide
  have hdescent : baseEnd_4462869 < baseStart_4462869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462872 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 1, 2, 5]
def baseStart_4462872 : Nat := 118140960795 + 4462872 * 2 ^ 59
def prefixEnd_4462872 : Nat := 4983230072969 + 3 ^ 40 * 4462872 * 2
def baseEnd_4462872 : Nat := 2291598435492368226475631

theorem tailTrace_4462872 : CollatzResearch.WordTrace tailWord_4462872 prefixEnd_4462872 2291598435492368226475631 := by
  unfold tailWord_4462872
  simp only [CollatzResearch.WordTrace]
  refine ⟨81387157143892208350519435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108516209525189611134025913 81387157143892208350519435)
  ·
    refine ⟨122080735715838312525779153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81387157143892208350519435 122080735715838312525779153)
    ·
      refine ⟨91560551786878734394334365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122080735715838312525779153 91560551786878734394334365)
      ·
        refine ⟨34335206920079525397875387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91560551786878734394334365 34335206920079525397875387)
        ·
          refine ⟨51502810380119288096813081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34335206920079525397875387 51502810380119288096813081)
          ·
            refine ⟨38627107785089466072609811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51502810380119288096813081 38627107785089466072609811)
            ·
              refine ⟨57940661677634199108914717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38627107785089466072609811 57940661677634199108914717)
              ·
                refine ⟨21727748129112824665843019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57940661677634199108914717 21727748129112824665843019)
                ·
                  refine ⟨32591622193669236998764529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21727748129112824665843019 32591622193669236998764529)
                  ·
                    refine ⟨24443716645251927749073397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32591622193669236998764529 24443716645251927749073397)
                    ·
                      refine ⟨2291598435492368226475631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24443716645251927749073397 2291598435492368226475631)
                      ·
                        rfl

theorem cell23_4462872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_4462872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462872 prefixEnd_4462872 := by exact prefixLift 4462872
  have htrace : WordTrace (prefixWord ++ tailWord_4462872) baseStart_4462872 baseEnd_4462872 := by
    simpa [prefixWord, tailWord_4462872, baseEnd_4462872] using wordTrace_append hprefix tailTrace_4462872
  have hstable : (prefixWord ++ tailWord_4462872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462872).length < 2 ^ (prefixWord ++ tailWord_4462872).sum := by decide
  have hdescent : baseEnd_4462872 < baseStart_4462872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462899 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 1, 6, 2]
def baseStart_4462899 : Nat := 118140960795 + 4462899 * 2 ^ 59
def prefixEnd_4462899 : Nat := 4983230072969 + 3 ^ 40 * 4462899 * 2
def baseEnd_4462899 : Nat := 2291612299470039620838007

theorem tailTrace_4462899 : CollatzResearch.WordTrace tailWord_4462899 prefixEnd_4462899 2291612299470039620838007 := by
  unfold tailWord_4462899
  simp only [CollatzResearch.WordTrace]
  refine ⟨162775299058686600312271751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108516866039124400208181167 162775299058686600312271751)
  ·
    refine ⟨244162948588029900468407627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162775299058686600312271751 244162948588029900468407627)
    ·
      refine ⟨366244422882044850702611441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244162948588029900468407627 366244422882044850702611441)
      ·
        refine ⟨274683317161533638026958581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 366244422882044850702611441 274683317161533638026958581)
        ·
          refine ⟨25751560983893778565027367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 274683317161533638026958581 25751560983893778565027367)
          ·
            refine ⟨38627341475840667847541051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25751560983893778565027367 38627341475840667847541051)
            ·
              refine ⟨57941012213761001771311577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38627341475840667847541051 57941012213761001771311577)
              ·
                refine ⟨43455759160320751328483683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57941012213761001771311577 43455759160320751328483683)
                ·
                  refine ⟨65183638740481126992725525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43455759160320751328483683 65183638740481126992725525)
                  ·
                    refine ⟨3055483065960052827784009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65183638740481126992725525 3055483065960052827784009)
                    ·
                      refine ⟨2291612299470039620838007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3055483065960052827784009 2291612299470039620838007)
                      ·
                        rfl

theorem cell23_4462899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 6, 2].length) (baseStart_4462899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462899 prefixEnd_4462899 := by exact prefixLift 4462899
  have htrace : WordTrace (prefixWord ++ tailWord_4462899) baseStart_4462899 baseEnd_4462899 := by
    simpa [prefixWord, tailWord_4462899, baseEnd_4462899] using wordTrace_append hprefix tailTrace_4462899
  have hstable : (prefixWord ++ tailWord_4462899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462899).length < 2 ^ (prefixWord ++ tailWord_4462899).sum := by decide
  have hdescent : baseEnd_4462899 < baseStart_4462899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4462919 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 3]
def baseStart_4462919 : Nat := 118140960795 + 4462919 * 2 ^ 59
def prefixEnd_4462919 : Nat := 4983230072969 + 3 ^ 40 * 4462919 * 2
def baseEnd_4462919 : Nat := 2291622569083129542587915

theorem tailTrace_4462919 : CollatzResearch.WordTrace tailWord_4462919 prefixEnd_4462919 2291622569083129542587915 := by
  unfold tailWord_4462919
  simp only [CollatzResearch.WordTrace]
  refine ⟨162776028518614143727999811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108517352345742762485333207 162776028518614143727999811)
  ·
    refine ⟨244164042777921215591999717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162776028518614143727999811 244164042777921215591999717)
    ·
      refine ⟨45780758020860227923499947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 244164042777921215591999717 45780758020860227923499947)
      ·
        refine ⟨68671137031290341885249921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45780758020860227923499947 68671137031290341885249921)
        ·
          refine ⟨51503352773467756413937441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68671137031290341885249921 51503352773467756413937441)
          ·
            refine ⟨38627514580100817310453081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51503352773467756413937441 38627514580100817310453081)
            ·
              refine ⟨28970635935075612982839811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38627514580100817310453081 28970635935075612982839811)
              ·
                refine ⟨43455953902613419474259717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28970635935075612982839811 43455953902613419474259717)
                ·
                  refine ⟨8147991356740016151423697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43455953902613419474259717 8147991356740016151423697)
                  ·
                    refine ⟨6110993517555012113567773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8147991356740016151423697 6110993517555012113567773)
                    ·
                      refine ⟨2291622569083129542587915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6110993517555012113567773 2291622569083129542587915)
                      ·
                        rfl

theorem cell23_4462919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_4462919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4462919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4462919 prefixEnd_4462919 := by exact prefixLift 4462919
  have htrace : WordTrace (prefixWord ++ tailWord_4462919) baseStart_4462919 baseEnd_4462919 := by
    simpa [prefixWord, tailWord_4462919, baseEnd_4462919] using wordTrace_append hprefix tailTrace_4462919
  have hstable : (prefixWord ++ tailWord_4462919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4462919).length < 2 ^ (prefixWord ++ tailWord_4462919).sum := by decide
  have hdescent : baseEnd_4462919 < baseStart_4462919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4462919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463016 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 3, 6]
def baseStart_4463016 : Nat := 118140960795 + 4463016 * 2 ^ 59
def prefixEnd_4463016 : Nat := 4983230072969 + 3 ^ 40 * 4463016 * 2
def baseEnd_4463016 : Nat := 763890792235538554358323

theorem tailTrace_4463016 : CollatzResearch.WordTrace tailWord_4463016 prefixEnd_4463016 763890792235538554358323 := by
  unfold tailWord_4463016
  simp only [CollatzResearch.WordTrace]
  refine ⟨81389783199631364647140451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108519710932841819529520601 81389783199631364647140451)
  ·
    refine ⟨122084674799447046970710677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81389783199631364647140451 122084674799447046970710677)
    ·
      refine ⟨5722719131224080326752063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 122084674799447046970710677 5722719131224080326752063)
      ·
        refine ⟨8584078696836120490128095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5722719131224080326752063 8584078696836120490128095)
        ·
          refine ⟨12876118045254180735192143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8584078696836120490128095 12876118045254180735192143)
          ·
            refine ⟨19314177067881271102788215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12876118045254180735192143 19314177067881271102788215)
            ·
              refine ⟨28971265601821906654182323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19314177067881271102788215 28971265601821906654182323)
              ·
                refine ⟨43456898402732859981273485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28971265601821906654182323 43456898402732859981273485)
                ·
                  refine ⟨16296336901024822492977557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43456898402732859981273485 16296336901024822492977557)
                  ·
                    refine ⟨763890792235538554358323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16296336901024822492977557 763890792235538554358323)
                    ·
                      rfl

theorem cell23_4463016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_4463016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463016 prefixEnd_4463016 := by exact prefixLift 4463016
  have htrace : WordTrace (prefixWord ++ tailWord_4463016) baseStart_4463016 baseEnd_4463016 := by
    simpa [prefixWord, tailWord_4463016, baseEnd_4463016] using wordTrace_append hprefix tailTrace_4463016
  have hstable : (prefixWord ++ tailWord_4463016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463016).length < 2 ^ (prefixWord ++ tailWord_4463016).sum := by decide
  have hdescent : baseEnd_4463016 < baseStart_4463016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463029 : List Nat := [1, 3, 3, 2, 3, 11]
def baseStart_4463029 : Nat := 118140960795 + 4463029 * 2 ^ 59
def prefixEnd_4463029 : Nat := 4983230072969 + 3 ^ 40 * 4463029 * 2
def baseEnd_4463029 : Nat := 9430777991584872889763

theorem tailTrace_4463029 : CollatzResearch.WordTrace tailWord_4463029 prefixEnd_4463029 9430777991584872889763 := by
  unfold tailWord_4463029
  simp only [CollatzResearch.WordTrace]
  refine ⟨162780040548215632514504141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108520027032143755009669427 162780040548215632514504141)
  ·
    refine ⟨61042515205580862192939053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162780040548215632514504141 61042515205580862192939053)
    ·
      refine ⟨22890943202092823322352145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61042515205580862192939053 22890943202092823322352145)
      ·
        refine ⟨17168207401569617491764109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22890943202092823322352145 17168207401569617491764109)
        ·
          refine ⟨6438077775588606559411541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17168207401569617491764109 6438077775588606559411541)
          ·
            refine ⟨9430777991584872889763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6438077775588606559411541 9430777991584872889763)
            ·
              rfl

theorem cell23_4463029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 11].length) (baseStart_4463029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463029 prefixEnd_4463029 := by exact prefixLift 4463029
  have htrace : WordTrace (prefixWord ++ tailWord_4463029) baseStart_4463029 baseEnd_4463029 := by
    simpa [prefixWord, tailWord_4463029, baseEnd_4463029] using wordTrace_append hprefix tailTrace_4463029
  have hstable : (prefixWord ++ tailWord_4463029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463029).length < 2 ^ (prefixWord ++ tailWord_4463029).sum := by decide
  have hdescent : baseEnd_4463029 < baseStart_4463029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463033 : List Nat := [1, 2, 1, 4, 3, 2, 2, 2, 2, 4]
def baseStart_4463033 : Nat := 118140960795 + 4463033 * 2 ^ 59
def prefixEnd_4463033 : Nat := 4983230072969 + 3 ^ 40 * 4463033 * 2
def baseEnd_4463033 : Nat := 763893701959247365520797

theorem tailTrace_4463033 : CollatzResearch.WordTrace tailWord_4463033 prefixEnd_4463033 763893701959247365520797 := by
  unfold tailWord_4463033
  simp only [CollatzResearch.WordTrace]
  refine ⟨162780186440201141197649753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108520124293467427465099835 162780186440201141197649753)
  ·
    refine ⟨122085139830150855898237315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162780186440201141197649753 122085139830150855898237315)
    ·
      refine ⟨183127709745226283847355973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122085139830150855898237315 183127709745226283847355973)
      ·
        refine ⟨34336445577229928221379245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183127709745226283847355973 34336445577229928221379245)
        ·
          refine ⟨12876167091461223083017217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34336445577229928221379245 12876167091461223083017217)
          ·
            refine ⟨9657125318595917312262913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12876167091461223083017217 9657125318595917312262913)
            ·
              refine ⟨7242843988946937984197185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9657125318595917312262913 7242843988946937984197185)
              ·
                refine ⟨5432132991710203488147889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7242843988946937984197185 5432132991710203488147889)
                ·
                  refine ⟨4074099743782652616110917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5432132991710203488147889 4074099743782652616110917)
                  ·
                    refine ⟨763893701959247365520797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4074099743782652616110917 763893701959247365520797)
                    ·
                      rfl

theorem cell23_4463033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 4].length) (baseStart_4463033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463033 prefixEnd_4463033 := by exact prefixLift 4463033
  have htrace : WordTrace (prefixWord ++ tailWord_4463033) baseStart_4463033 baseEnd_4463033 := by
    simpa [prefixWord, tailWord_4463033, baseEnd_4463033] using wordTrace_append hprefix tailTrace_4463033
  have hstable : (prefixWord ++ tailWord_4463033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463033).length < 2 ^ (prefixWord ++ tailWord_4463033).sum := by decide
  have hdescent : baseEnd_4463033 < baseStart_4463033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463074 : List Nat := [3, 3, 3, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_4463074 : Nat := 118140960795 + 4463074 * 2 ^ 59
def prefixEnd_4463074 : Nat := 4983230072969 + 3 ^ 40 * 4463074 * 2
def baseEnd_4463074 : Nat := 2291702158584576436149703

theorem tailTrace_4463074 : CollatzResearch.WordTrace tailWord_4463074 prefixEnd_4463074 2291702158584576436149703 := by
  unfold tailWord_4463074
  simp only [CollatzResearch.WordTrace]
  refine ⟨40695420458263151299973069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108521121222035070133261517 40695420458263151299973069)
  ·
    refine ⟨15260782671848681737489901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40695420458263151299973069 15260782671848681737489901)
    ·
      refine ⟨5722793501943255651558713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15260782671848681737489901 5722793501943255651558713)
      ·
        refine ⟨4292095126457441738669035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5722793501943255651558713 4292095126457441738669035)
        ·
          refine ⟨6438142689686162608003553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4292095126457441738669035 6438142689686162608003553)
          ·
            refine ⟨4828607017264621956002665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6438142689686162608003553 4828607017264621956002665)
            ·
              refine ⟨3621455262948466467001999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4828607017264621956002665 3621455262948466467001999)
              ·
                refine ⟨5432182894422699700502999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3621455262948466467001999 5432182894422699700502999)
                ·
                  refine ⟨8148274341634049550754499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5432182894422699700502999 8148274341634049550754499)
                  ·
                    refine ⟨12222411512451074326131749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8148274341634049550754499 12222411512451074326131749)
                    ·
                      refine ⟨2291702158584576436149703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12222411512451074326131749 2291702158584576436149703)
                      ·
                        rfl

theorem cell23_4463074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_4463074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463074 prefixEnd_4463074 := by exact prefixLift 4463074
  have htrace : WordTrace (prefixWord ++ tailWord_4463074) baseStart_4463074 baseEnd_4463074 := by
    simpa [prefixWord, tailWord_4463074, baseEnd_4463074] using wordTrace_append hprefix tailTrace_4463074
  have hstable : (prefixWord ++ tailWord_4463074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463074).length < 2 ^ (prefixWord ++ tailWord_4463074).sum := by decide
  have hdescent : baseEnd_4463074 < baseStart_4463074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463077 : List Nat := [1, 3, 1, 5, 2, 2, 2, 1, 1, 2, 3]
def baseStart_4463077 : Nat := 118140960795 + 4463077 * 2 ^ 59
def prefixEnd_4463077 : Nat := 4983230072969 + 3 ^ 40 * 4463077 * 2
def baseEnd_4463077 : Nat := 2291703699026539924412189

theorem tailTrace_4463077 : CollatzResearch.WordTrace tailWord_4463077 prefixEnd_4463077 2291703699026539924412189 := by
  unfold tailWord_4463077
  simp only [CollatzResearch.WordTrace]
  refine ⟨162781791252041736712251485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108521194168027824474834323 162781791252041736712251485)
  ·
    refine ⟨61043171719515651267094307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162781791252041736712251485 61043171719515651267094307)
    ·
      refine ⟨91564757579273476900641461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61043171719515651267094307 91564757579273476900641461)
      ·
        refine ⟨8584196023056888459435137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91564757579273476900641461 8584196023056888459435137)
        ·
          refine ⟨6438147017292666344576353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8584196023056888459435137 6438147017292666344576353)
          ·
            refine ⟨4828610262969499758432265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6438147017292666344576353 4828610262969499758432265)
            ·
              refine ⟨3621457697227124818824199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4828610262969499758432265 3621457697227124818824199)
              ·
                refine ⟨5432186545840687228236299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3621457697227124818824199 5432186545840687228236299)
                ·
                  refine ⟨8148279818761030842354449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5432186545840687228236299 8148279818761030842354449)
                  ·
                    refine ⟨6111209864070773131765837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8148279818761030842354449 6111209864070773131765837)
                    ·
                      refine ⟨2291703699026539924412189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6111209864070773131765837 2291703699026539924412189)
                      ·
                        rfl

theorem cell23_4463077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_4463077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463077 prefixEnd_4463077 := by exact prefixLift 4463077
  have htrace : WordTrace (prefixWord ++ tailWord_4463077) baseStart_4463077 baseEnd_4463077 := by
    simpa [prefixWord, tailWord_4463077, baseEnd_4463077] using wordTrace_append hprefix tailTrace_4463077
  have hstable : (prefixWord ++ tailWord_4463077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463077).length < 2 ^ (prefixWord ++ tailWord_4463077).sum := by decide
  have hdescent : baseEnd_4463077 < baseStart_4463077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463083 : List Nat := [1, 1, 1, 1, 2, 3, 5, 3, 1, 3, 2]
def baseStart_4463083 : Nat := 118140960795 + 4463083 * 2 ^ 59
def prefixEnd_4463083 : Nat := 4983230072969 + 3 ^ 40 * 4463083 * 2
def baseEnd_4463083 : Nat := 2291706779910466900937161

theorem tailTrace_4463083 : CollatzResearch.WordTrace tailWord_4463083 prefixEnd_4463083 2291706779910466900937161 := by
  unfold tailWord_4463083
  simp only [CollatzResearch.WordTrace]
  refine ⟨162782010090019999736969903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108521340060013333157979935 162782010090019999736969903)
  ·
    refine ⟨244173015135029999605454855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162782010090019999736969903 244173015135029999605454855)
    ·
      refine ⟨366259522702544999408182283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244173015135029999605454855 366259522702544999408182283)
      ·
        refine ⟨549389284053817499112273425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366259522702544999408182283 549389284053817499112273425)
        ·
          refine ⟨412041963040363124334205069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 549389284053817499112273425 412041963040363124334205069)
          ·
            refine ⟨154515736140136171625326901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 412041963040363124334205069 154515736140136171625326901)
            ·
              refine ⟨14485850263137766089874397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 154515736140136171625326901 14485850263137766089874397)
              ·
                refine ⟨5432193848676662283702899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14485850263137766089874397 5432193848676662283702899)
                ·
                  refine ⟨8148290773014993425554349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5432193848676662283702899 8148290773014993425554349)
                  ·
                    refine ⟨3055609039880622534582881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8148290773014993425554349 3055609039880622534582881)
                    ·
                      refine ⟨2291706779910466900937161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3055609039880622534582881 2291706779910466900937161)
                      ·
                        rfl

theorem cell23_4463083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 3, 2].length) (baseStart_4463083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463083 prefixEnd_4463083 := by exact prefixLift 4463083
  have htrace : WordTrace (prefixWord ++ tailWord_4463083) baseStart_4463083 baseEnd_4463083 := by
    simpa [prefixWord, tailWord_4463083, baseEnd_4463083] using wordTrace_append hprefix tailTrace_4463083
  have hstable : (prefixWord ++ tailWord_4463083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463083).length < 2 ^ (prefixWord ++ tailWord_4463083).sum := by decide
  have hdescent : baseEnd_4463083 < baseStart_4463083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463089 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 4, 6]
def baseStart_4463089 : Nat := 118140960795 + 4463089 * 2 ^ 59
def prefixEnd_4463089 : Nat := 4983230072969 + 3 ^ 40 * 4463089 * 2
def baseEnd_4463089 : Nat := 763903286931464625820711

theorem tailTrace_4463089 : CollatzResearch.WordTrace tailWord_4463089 prefixEnd_4463089 763903286931464625820711 := by
  unfold tailWord_4463089
  simp only [CollatzResearch.WordTrace]
  refine ⟨162782228927998262761688321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108521485951998841841125547 162782228927998262761688321)
  ·
    refine ⟨122086671695998697071266241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162782228927998262761688321 122086671695998697071266241)
    ·
      refine ⟨91565003771999022803449681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122086671695998697071266241 91565003771999022803449681)
      ·
        refine ⟨68673752828999267102587261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91565003771999022803449681 68673752828999267102587261)
        ·
          refine ⟨25752657310874725163470223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68673752828999267102587261 25752657310874725163470223)
          ·
            refine ⟨38628985966312087745205335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25752657310874725163470223 38628985966312087745205335)
            ·
              refine ⟨57943478949468131617808003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38628985966312087745205335 57943478949468131617808003)
              ·
                refine ⟨86915218424202197426712005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57943478949468131617808003 86915218424202197426712005)
                ·
                  refine ⟨16296603454537912017508501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86915218424202197426712005 16296603454537912017508501)
                  ·
                    refine ⟨763903286931464625820711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16296603454537912017508501 763903286931464625820711)
                    ·
                      rfl

theorem cell23_4463089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_4463089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463089 prefixEnd_4463089 := by exact prefixLift 4463089
  have htrace : WordTrace (prefixWord ++ tailWord_4463089) baseStart_4463089 baseEnd_4463089 := by
    simpa [prefixWord, tailWord_4463089, baseEnd_4463089] using wordTrace_append hprefix tailTrace_4463089
  have hstable : (prefixWord ++ tailWord_4463089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463089).length < 2 ^ (prefixWord ++ tailWord_4463089).sum := by decide
  have hdescent : baseEnd_4463089 < baseStart_4463089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463090 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 4, 1, 3]
def baseStart_4463090 : Nat := 118140960795 + 4463090 * 2 ^ 59
def prefixEnd_4463090 : Nat := 4983230072969 + 3 ^ 40 * 4463090 * 2
def baseEnd_4463090 : Nat := 2291710374275048373549629

theorem tailTrace_4463090 : CollatzResearch.WordTrace tailWord_4463090 prefixEnd_4463090 2291710374275048373549629 := by
  unfold tailWord_4463090
  simp only [CollatzResearch.WordTrace]
  refine ⟨40695566350248659983118681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108521510267329759954983149 40695566350248659983118681)
  ·
    refine ⟨30521674762686494987339011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40695566350248659983118681 30521674762686494987339011)
    ·
      refine ⟨45782512144029742481008517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30521674762686494987339011 45782512144029742481008517)
      ·
        refine ⟨8584221027005576715189097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45782512144029742481008517 8584221027005576715189097)
        ·
          refine ⟨6438165770254182536391823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8584221027005576715189097 6438165770254182536391823)
          ·
            refine ⟨9657248655381273804587735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6438165770254182536391823 9657248655381273804587735)
            ·
              refine ⟨14485872983071910706881603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9657248655381273804587735 14485872983071910706881603)
              ·
                refine ⟨21728809474607866060322405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14485872983071910706881603 21728809474607866060322405)
                ·
                  refine ⟨4074151776488974886310451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21728809474607866060322405 4074151776488974886310451)
                  ·
                    refine ⟨6111227664733462329465677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4074151776488974886310451 6111227664733462329465677)
                    ·
                      refine ⟨2291710374275048373549629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6111227664733462329465677 2291710374275048373549629)
                      ·
                        rfl

theorem cell23_4463090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_4463090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463090 prefixEnd_4463090 := by exact prefixLift 4463090
  have htrace : WordTrace (prefixWord ++ tailWord_4463090) baseStart_4463090 baseEnd_4463090 := by
    simpa [prefixWord, tailWord_4463090, baseEnd_4463090] using wordTrace_append hprefix tailTrace_4463090
  have hstable : (prefixWord ++ tailWord_4463090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463090).length < 2 ^ (prefixWord ++ tailWord_4463090).sum := by decide
  have hdescent : baseEnd_4463090 < baseStart_4463090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463164 : List Nat := [2, 2, 2, 2, 3, 3, 2, 1, 2, 2, 2]
def baseStart_4463164 : Nat := 118140960795 + 4463164 * 2 ^ 59
def prefixEnd_4463164 : Nat := 4983230072969 + 3 ^ 40 * 4463164 * 2
def baseEnd_4463164 : Nat := 2291748371843481084024289

theorem tailTrace_4463164 : CollatzResearch.WordTrace tailWord_4463164 prefixEnd_4463164 2291748371843481084024289 := by
  unfold tailWord_4463164
  simp only [CollatzResearch.WordTrace]
  refine ⟨81392482201363275285334273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108523309601817700380445697 81392482201363275285334273)
  ·
    refine ⟨61044361651022456464000705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81392482201363275285334273 61044361651022456464000705)
    ·
      refine ⟨45783271238266842348000529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61044361651022456464000705 45783271238266842348000529)
      ·
        refine ⟨34337453428700131761000397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45783271238266842348000529 34337453428700131761000397)
        ·
          refine ⟨12876545035762549410375149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34337453428700131761000397 12876545035762549410375149)
          ·
            refine ⟨4828704388410956028890681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12876545035762549410375149 4828704388410956028890681)
            ·
              refine ⟨3621528291308217021668011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4828704388410956028890681 3621528291308217021668011)
              ·
                refine ⟨5432292436962325532502017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3621528291308217021668011 5432292436962325532502017)
                ·
                  refine ⟨4074219327721744149376513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5432292436962325532502017 4074219327721744149376513)
                  ·
                    refine ⟨3055664495791308112032385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4074219327721744149376513 3055664495791308112032385)
                    ·
                      refine ⟨2291748371843481084024289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3055664495791308112032385 2291748371843481084024289)
                      ·
                        rfl

theorem cell23_4463164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_4463164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463164 prefixEnd_4463164 := by exact prefixLift 4463164
  have htrace : WordTrace (prefixWord ++ tailWord_4463164) baseStart_4463164 baseEnd_4463164 := by
    simpa [prefixWord, tailWord_4463164, baseEnd_4463164] using wordTrace_append hprefix tailTrace_4463164
  have hstable : (prefixWord ++ tailWord_4463164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463164).length < 2 ^ (prefixWord ++ tailWord_4463164).sum := by decide
  have hdescent : baseEnd_4463164 < baseStart_4463164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463179 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 2, 8]
def baseStart_4463179 : Nat := 118140960795 + 4463179 * 2 ^ 59
def prefixEnd_4463179 : Nat := 4983230072969 + 3 ^ 40 * 4463179 * 2
def baseEnd_4463179 : Nat := 763918691351099508445573

theorem tailTrace_4463179 : CollatzResearch.WordTrace tailWord_4463179 prefixEnd_4463179 763918691351099508445573 := by
  unfold tailWord_4463179
  simp only [CollatzResearch.WordTrace]
  refine ⟨162785511497672208132464591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108523674331781472088309727 162785511497672208132464591)
  ·
    refine ⟨244178267246508312198696887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162785511497672208132464591 244178267246508312198696887)
    ·
      refine ⟨366267400869762468298045331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244178267246508312198696887 366267400869762468298045331)
      ·
        refine ⟨549401101304643702447067997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366267400869762468298045331 549401101304643702447067997)
        ·
          refine ⟨206025412989241388417650499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 549401101304643702447067997 206025412989241388417650499)
          ·
            refine ⟨309038119483862082626475749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206025412989241388417650499 309038119483862082626475749)
            ·
              refine ⟨57944647403224140492464203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 309038119483862082626475749 57944647403224140492464203)
              ·
                refine ⟨86916971104836210738696305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57944647403224140492464203 86916971104836210738696305)
                ·
                  refine ⟨65187728328627158054022229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86916971104836210738696305 65187728328627158054022229)
                  ·
                    refine ⟨763918691351099508445573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65187728328627158054022229 763918691351099508445573)
                    ·
                      rfl

theorem cell23_4463179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 8].length) (baseStart_4463179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463179 prefixEnd_4463179 := by exact prefixLift 4463179
  have htrace : WordTrace (prefixWord ++ tailWord_4463179) baseStart_4463179 baseEnd_4463179 := by
    simpa [prefixWord, tailWord_4463179, baseEnd_4463179] using wordTrace_append hprefix tailTrace_4463179
  have hstable : (prefixWord ++ tailWord_4463179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463179).length < 2 ^ (prefixWord ++ tailWord_4463179).sum := by decide
  have hdescent : baseEnd_4463179 < baseStart_4463179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463198 : List Nat := [4, 4, 1, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_4463198 : Nat := 118140960795 + 4463198 * 2 ^ 59
def prefixEnd_4463198 : Nat := 4983230072969 + 3 ^ 40 * 4463198 * 2
def baseEnd_4463198 : Nat := 2291765830185733950999133

theorem tailTrace_4463198 : CollatzResearch.WordTrace tailWord_4463198 prefixEnd_4463198 2291765830185733950999133 := by
  unfold tailWord_4463198
  simp only [CollatzResearch.WordTrace]
  refine ⟨20348275560575421797175781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108524136323068916251604165 20348275560575421797175781)
  ·
    refine ⟨3815301667607891586970459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20348275560575421797175781 3815301667607891586970459)
    ·
      refine ⟨5722952501411837380455689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3815301667607891586970459 5722952501411837380455689)
      ·
        refine ⟨4292214376058878035341767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5722952501411837380455689 4292214376058878035341767)
        ·
          refine ⟨6438321564088317053012651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4292214376058878035341767 6438321564088317053012651)
          ·
            refine ⟨9657482346132475579518977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6438321564088317053012651 9657482346132475579518977)
            ·
              refine ⟨7243111759599356684639233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9657482346132475579518977 7243111759599356684639233)
              ·
                refine ⟨5432333819699517513479425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7243111759599356684639233 5432333819699517513479425)
                ·
                  refine ⟨4074250364774638135109569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5432333819699517513479425 4074250364774638135109569)
                  ·
                    refine ⟨3055687773580978601332177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4074250364774638135109569 3055687773580978601332177)
                    ·
                      refine ⟨2291765830185733950999133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3055687773580978601332177 2291765830185733950999133)
                      ·
                        rfl

theorem cell23_4463198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_4463198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463198 prefixEnd_4463198 := by exact prefixLift 4463198
  have htrace : WordTrace (prefixWord ++ tailWord_4463198) baseStart_4463198 baseEnd_4463198 := by
    simpa [prefixWord, tailWord_4463198, baseEnd_4463198] using wordTrace_append hprefix tailTrace_4463198
  have hstable : (prefixWord ++ tailWord_4463198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463198).length < 2 ^ (prefixWord ++ tailWord_4463198).sum := by decide
  have hdescent : baseEnd_4463198 < baseStart_4463198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463203 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 2, 4, 2]
def baseStart_4463203 : Nat := 118140960795 + 4463203 * 2 ^ 59
def prefixEnd_4463203 : Nat := 4983230072969 + 3 ^ 40 * 4463203 * 2
def baseEnd_4463203 : Nat := 2291768397589006431436609

theorem tailTrace_4463203 : CollatzResearch.WordTrace tailWord_4463203 prefixEnd_4463203 2291768397589006431436609 := by
  unfold tailWord_4463203
  simp only [CollatzResearch.WordTrace]
  refine ⟨162786386849585260231338263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108524257899723506820892175 162786386849585260231338263)
  ·
    refine ⟨244179580274377890347007395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162786386849585260231338263 244179580274377890347007395)
    ·
      refine ⟨366269370411566835520511093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244179580274377890347007395 366269370411566835520511093)
      ·
        refine ⟨34337753476084390830047915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 366269370411566835520511093 34337753476084390830047915)
        ·
          refine ⟨51506630214126586245071873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34337753476084390830047915 51506630214126586245071873)
          ·
            refine ⟨38629972660594939683803905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51506630214126586245071873 38629972660594939683803905)
            ·
              refine ⟨28972479495446204762852929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38629972660594939683803905 28972479495446204762852929)
              ·
                refine ⟨21729359621584653572139697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28972479495446204762852929 21729359621584653572139697)
                ·
                  refine ⟨16297019716188490179104773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21729359621584653572139697 16297019716188490179104773)
                  ·
                    refine ⟨3055691196785341908582145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16297019716188490179104773 3055691196785341908582145)
                    ·
                      refine ⟨2291768397589006431436609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3055691196785341908582145 2291768397589006431436609)
                      ·
                        rfl

theorem cell23_4463203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_4463203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463203 prefixEnd_4463203 := by exact prefixLift 4463203
  have htrace : WordTrace (prefixWord ++ tailWord_4463203) baseStart_4463203 baseEnd_4463203 := by
    simpa [prefixWord, tailWord_4463203, baseEnd_4463203] using wordTrace_append hprefix tailTrace_4463203
  have hstable : (prefixWord ++ tailWord_4463203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463203).length < 2 ^ (prefixWord ++ tailWord_4463203).sum := by decide
  have hdescent : baseEnd_4463203 < baseStart_4463203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463260 : List Nat := [2, 2, 3, 2, 2, 3, 1, 2, 6]
def baseStart_4463260 : Nat := 118140960795 + 4463260 * 2 ^ 59
def prefixEnd_4463260 : Nat := 4983230072969 + 3 ^ 40 * 4463260 * 2
def baseEnd_4463260 : Nat := 254644185109590300935983

theorem tailTrace_4463260 : CollatzResearch.WordTrace tailWord_4463260 prefixEnd_4463260 254644185109590300935983 := by
  unfold tailWord_4463260
  simp only [CollatzResearch.WordTrace]
  refine ⟨81394232905189379483081617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108525643873585839310775489 81394232905189379483081617)
  ·
    refine ⟨61045674678892034612311213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81394232905189379483081617 61045674678892034612311213)
    ·
      refine ⟨22892128004584512979616705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61045674678892034612311213 22892128004584512979616705)
      ·
        refine ⟨17169096003438384734712529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22892128004584512979616705 17169096003438384734712529)
        ·
          refine ⟨12876822002578788551034397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17169096003438384734712529 12876822002578788551034397)
          ·
            refine ⟨4828808250967045706637899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12876822002578788551034397 4828808250967045706637899)
            ·
              refine ⟨7243212376450568559956849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4828808250967045706637899 7243212376450568559956849)
              ·
                refine ⟨5432409282337926419967637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7243212376450568559956849 5432409282337926419967637)
                ·
                  refine ⟨254644185109590300935983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5432409282337926419967637 254644185109590300935983)
                  ·
                    rfl

theorem cell23_4463260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 6].length) (baseStart_4463260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463260 prefixEnd_4463260 := by exact prefixLift 4463260
  have htrace : WordTrace (prefixWord ++ tailWord_4463260) baseStart_4463260 baseEnd_4463260 := by
    simpa [prefixWord, tailWord_4463260, baseEnd_4463260] using wordTrace_append hprefix tailTrace_4463260
  have hstable : (prefixWord ++ tailWord_4463260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463260).length < 2 ^ (prefixWord ++ tailWord_4463260).sum := by decide
  have hdescent : baseEnd_4463260 < baseStart_4463260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463304 : List Nat := [2, 1, 3, 1, 2, 5, 1, 3, 1, 1, 3]
def baseStart_4463304 : Nat := 118140960795 + 4463304 * 2 ^ 59
def prefixEnd_4463304 : Nat := 4983230072969 + 3 ^ 40 * 4463304 * 2
def baseEnd_4463304 : Nat := 2291820259135110536273645

theorem tailTrace_4463304 : CollatzResearch.WordTrace tailWord_4463304 prefixEnd_4463304 2291820259135110536273645 := by
  unfold tailWord_4463304
  simp only [CollatzResearch.WordTrace]
  refine ⟨81395035311109677240382483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108526713748146236320509977 81395035311109677240382483)
  ·
    refine ⟨122092552966664515860573725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81395035311109677240382483 122092552966664515860573725)
    ·
      refine ⟨45784707362499193447715147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122092552966664515860573725 45784707362499193447715147)
      ·
        refine ⟨68677061043748790171572721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45784707362499193447715147 68677061043748790171572721)
        ·
          refine ⟨51507795782811592628679541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68677061043748790171572721 51507795782811592628679541)
          ·
            refine ⟨4828855854638586808938707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51507795782811592628679541 4828855854638586808938707)
            ·
              refine ⟨7243283781957880213408061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4828855854638586808938707 7243283781957880213408061)
              ·
                refine ⟨2716231418234205080028023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7243283781957880213408061 2716231418234205080028023)
                ·
                  refine ⟨4074347127351307620042035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2716231418234205080028023 4074347127351307620042035)
                  ·
                    refine ⟨6111520691026961430063053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4074347127351307620042035 6111520691026961430063053)
                    ·
                      refine ⟨2291820259135110536273645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6111520691026961430063053 2291820259135110536273645)
                      ·
                        rfl

theorem cell23_4463304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 1, 1, 3].length) (baseStart_4463304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463304 prefixEnd_4463304 := by exact prefixLift 4463304
  have htrace : WordTrace (prefixWord ++ tailWord_4463304) baseStart_4463304 baseEnd_4463304 := by
    simpa [prefixWord, tailWord_4463304, baseEnd_4463304] using wordTrace_append hprefix tailTrace_4463304
  have hstable : (prefixWord ++ tailWord_4463304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463304).length < 2 ^ (prefixWord ++ tailWord_4463304).sum := by decide
  have hdescent : baseEnd_4463304 < baseStart_4463304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463310 : List Nat := [4, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4]
def baseStart_4463310 : Nat := 118140960795 + 4463310 * 2 ^ 59
def prefixEnd_4463310 : Nat := 4983230072969 + 3 ^ 40 * 4463310 * 2
def baseEnd_4463310 : Nat := 2291823340019037512798617

theorem tailTrace_4463310 : CollatzResearch.WordTrace tailWord_4463310 prefixEnd_4463310 2291823340019037512798617 := by
  unfold tailWord_4463310
  simp only [CollatzResearch.WordTrace]
  refine ⟨20348786182524702188185423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108526859640131745003655589 20348786182524702188185423)
  ·
    refine ⟨30523179273787053282278135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20348786182524702188185423 30523179273787053282278135)
    ·
      refine ⟨45784768910680579923417203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30523179273787053282278135 45784768910680579923417203)
      ·
        refine ⟨68677153366020869885125805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45784768910680579923417203 68677153366020869885125805)
        ·
          refine ⟨25753932512257826206922177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68677153366020869885125805 25753932512257826206922177)
          ·
            refine ⟨19315449384193369655191633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25753932512257826206922177 19315449384193369655191633)
            ·
              refine ⟨14486587038145027241393725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19315449384193369655191633 14486587038145027241393725)
              ·
                refine ⟨5432470139304385215522647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14486587038145027241393725 5432470139304385215522647)
                ·
                  refine ⟨8148705208956577823283971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5432470139304385215522647 8148705208956577823283971)
                  ·
                    refine ⟨12223057813434866734925957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8148705208956577823283971 12223057813434866734925957)
                    ·
                      refine ⟨2291823340019037512798617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12223057813434866734925957 2291823340019037512798617)
                      ·
                        rfl

theorem cell23_4463310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_4463310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463310 prefixEnd_4463310 := by exact prefixLift 4463310
  have htrace : WordTrace (prefixWord ++ tailWord_4463310) baseStart_4463310 baseEnd_4463310 := by
    simpa [prefixWord, tailWord_4463310, baseEnd_4463310] using wordTrace_append hprefix tailTrace_4463310
  have hstable : (prefixWord ++ tailWord_4463310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463310).length < 2 ^ (prefixWord ++ tailWord_4463310).sum := by decide
  have hdescent : baseEnd_4463310 < baseStart_4463310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463313 : List Nat := [1, 2, 2, 1, 2, 3, 4, 1, 1, 1, 5]
def baseStart_4463313 : Nat := 118140960795 + 4463313 * 2 ^ 59
def prefixEnd_4463313 : Nat := 4983230072969 + 3 ^ 40 * 4463313 * 2
def baseEnd_4463313 : Nat := 2291824880461001001061103

theorem tailTrace_4463313 : CollatzResearch.WordTrace tailWord_4463313 prefixEnd_4463313 2291824880461001001061103 := by
  unfold tailWord_4463313
  simp only [CollatzResearch.WordTrace]
  refine ⟨162790398879186749017842593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108526932586124499345228395 162790398879186749017842593)
  ·
    refine ⟨122092799159390061763381945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162790398879186749017842593 122092799159390061763381945)
    ·
      refine ⟨91569599369542546322536459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122092799159390061763381945 91569599369542546322536459)
      ·
        refine ⟨137354399054313819483804689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91569599369542546322536459 137354399054313819483804689)
        ·
          refine ⟨103015799290735364612853517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137354399054313819483804689 103015799290735364612853517)
          ·
            refine ⟨38630924734025761729820069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103015799290735364612853517 38630924734025761729820069)
            ·
              refine ⟨7243298387629830324341263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38630924734025761729820069 7243298387629830324341263)
              ·
                refine ⟨10864947581444745486511895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7243298387629830324341263 10864947581444745486511895)
                ·
                  refine ⟨16297421372167118229767843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10864947581444745486511895 16297421372167118229767843)
                  ·
                    refine ⟨24446132058250677344651765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16297421372167118229767843 24446132058250677344651765)
                    ·
                      refine ⟨2291824880461001001061103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24446132058250677344651765 2291824880461001001061103)
                      ·
                        rfl

theorem cell23_4463313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 1, 5].length) (baseStart_4463313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463313 prefixEnd_4463313 := by exact prefixLift 4463313
  have htrace : WordTrace (prefixWord ++ tailWord_4463313) baseStart_4463313 baseEnd_4463313 := by
    simpa [prefixWord, tailWord_4463313, baseEnd_4463313] using wordTrace_append hprefix tailTrace_4463313
  have hstable : (prefixWord ++ tailWord_4463313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463313).length < 2 ^ (prefixWord ++ tailWord_4463313).sum := by decide
  have hdescent : baseEnd_4463313 < baseStart_4463313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463327 : List Nat := [1, 1, 2, 3, 2, 3, 3, 1, 3, 2, 2]
def baseStart_4463327 : Nat := 118140960795 + 4463327 * 2 ^ 59
def prefixEnd_4463327 : Nat := 4983230072969 + 3 ^ 40 * 4463327 * 2
def baseEnd_4463327 : Nat := 2291832069190163946286039

theorem tailTrace_4463327 : CollatzResearch.WordTrace tailWord_4463327 prefixEnd_4463327 2291832069190163946286039 := by
  unfold tailWord_4463327
  simp only [CollatzResearch.WordTrace]
  refine ⟨162790909501136029408852235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108527273000757352939234823 162790909501136029408852235)
  ·
    refine ⟨244186364251704044113278353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162790909501136029408852235 244186364251704044113278353)
    ·
      refine ⟨183139773188778033084958765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244186364251704044113278353 183139773188778033084958765)
      ·
        refine ⟨68677414945791762406859537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183139773188778033084958765 68677414945791762406859537)
        ·
          refine ⟨51508061209343821805144653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68677414945791762406859537 51508061209343821805144653)
          ·
            refine ⟨19315522953503933176929245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51508061209343821805144653 19315522953503933176929245)
            ·
              refine ⟨7243321107563974941348467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19315522953503933176929245 7243321107563974941348467)
              ·
                refine ⟨10864981661345962412022701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7243321107563974941348467 10864981661345962412022701)
                ·
                  refine ⟨4074368123004735904508513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10864981661345962412022701 4074368123004735904508513)
                  ·
                    refine ⟨3055776092253551928381385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4074368123004735904508513 3055776092253551928381385)
                    ·
                      refine ⟨2291832069190163946286039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3055776092253551928381385 2291832069190163946286039)
                      ·
                        rfl

theorem cell23_4463327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_4463327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463327 prefixEnd_4463327 := by exact prefixLift 4463327
  have htrace : WordTrace (prefixWord ++ tailWord_4463327) baseStart_4463327 baseEnd_4463327 := by
    simpa [prefixWord, tailWord_4463327, baseEnd_4463327] using wordTrace_append hprefix tailTrace_4463327
  have hstable : (prefixWord ++ tailWord_4463327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463327).length < 2 ^ (prefixWord ++ tailWord_4463327).sum := by decide
  have hdescent : baseEnd_4463327 < baseStart_4463327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463333 : List Nat := [1, 3, 1, 4, 1, 3, 2, 8]
def baseStart_4463333 : Nat := 118140960795 + 4463333 * 2 ^ 59
def prefixEnd_4463333 : Nat := 4983230072969 + 3 ^ 40 * 4463333 * 2
def baseEnd_4463333 : Nat := 84882783336077441585593

theorem tailTrace_4463333 : CollatzResearch.WordTrace tailWord_4463333 prefixEnd_4463333 84882783336077441585593 := by
  unfold tailWord_4463333
  simp only [CollatzResearch.WordTrace]
  refine ⟨162791128339114292433570653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108527418892742861622380435 162791128339114292433570653)
  ·
    refine ⟨61046673127167859662588995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162791128339114292433570653 61046673127167859662588995)
    ·
      refine ⟨91570009690751789493883493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61046673127167859662588995 91570009690751789493883493)
      ·
        refine ⟨17169376817015960530103155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91570009690751789493883493 17169376817015960530103155)
        ·
          refine ⟨25754065225523940795154733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17169376817015960530103155 25754065225523940795154733)
          ·
            refine ⟨9657774459571477798183025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25754065225523940795154733 9657774459571477798183025)
            ·
              refine ⟨7243330844678608348637269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9657774459571477798183025 7243330844678608348637269)
              ·
                refine ⟨84882783336077441585593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7243330844678608348637269 84882783336077441585593)
                ·
                  rfl

theorem cell23_4463333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 8].length) (baseStart_4463333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463333 prefixEnd_4463333 := by exact prefixLift 4463333
  have htrace : WordTrace (prefixWord ++ tailWord_4463333) baseStart_4463333 baseEnd_4463333 := by
    simpa [prefixWord, tailWord_4463333, baseEnd_4463333] using wordTrace_append hprefix tailTrace_4463333
  have hstable : (prefixWord ++ tailWord_4463333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463333).length < 2 ^ (prefixWord ++ tailWord_4463333).sum := by decide
  have hdescent : baseEnd_4463333 < baseStart_4463333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463378 : List Nat := [3, 2, 4, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_4463378 : Nat := 118140960795 + 4463378 * 2 ^ 59
def prefixEnd_4463378 : Nat := 4983230072969 + 3 ^ 40 * 4463378 * 2
def baseEnd_4463378 : Nat := 2291858256703543246748305

theorem tailTrace_4463378 : CollatzResearch.WordTrace tailWord_4463378 prefixEnd_4463378 2291858256703543246748305 := by
  unfold tailWord_4463378
  simp only [CollatzResearch.WordTrace]
  refine ⟨40698192405987816279739697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108528513082634176745972525 40698192405987816279739697)
  ·
    refine ⟨30523644304490862209804773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40698192405987816279739697 30523644304490862209804773)
    ·
      refine ⟨5723183307092036664338395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30523644304490862209804773 5723183307092036664338395)
      ·
        refine ⟨8584774960638054996507593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5723183307092036664338395 8584774960638054996507593)
        ·
          refine ⟨6438581220478541247380695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8584774960638054996507593 6438581220478541247380695)
          ·
            refine ⟨9657871830717811871071043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6438581220478541247380695 9657871830717811871071043)
            ·
              refine ⟨14486807746076717806606565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9657871830717811871071043 14486807746076717806606565)
              ·
                refine ⟨2716276452389384588738731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14486807746076717806606565 2716276452389384588738731)
                ·
                  refine ⟨4074414678584076883108097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2716276452389384588738731 4074414678584076883108097)
                  ·
                    refine ⟨3055811008938057662331073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4074414678584076883108097 3055811008938057662331073)
                    ·
                      refine ⟨2291858256703543246748305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3055811008938057662331073 2291858256703543246748305)
                      ·
                        rfl

theorem cell23_4463378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_4463378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463378 prefixEnd_4463378 := by exact prefixLift 4463378
  have htrace : WordTrace (prefixWord ++ tailWord_4463378) baseStart_4463378 baseEnd_4463378 := by
    simpa [prefixWord, tailWord_4463378, baseEnd_4463378] using wordTrace_append hprefix tailTrace_4463378
  have hstable : (prefixWord ++ tailWord_4463378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463378).length < 2 ^ (prefixWord ++ tailWord_4463378).sum := by decide
  have hdescent : baseEnd_4463378 < baseStart_4463378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463393 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 2, 6]
def baseStart_4463393 : Nat := 118140960795 + 4463393 * 2 ^ 59
def prefixEnd_4463393 : Nat := 4983230072969 + 3 ^ 40 * 4463393 * 2
def baseEnd_4463393 : Nat := 763955319637786896020245

theorem tailTrace_4463393 : CollatzResearch.WordTrace tailWord_4463393 prefixEnd_4463393 763955319637786896020245 := by
  unfold tailWord_4463393
  simp only [CollatzResearch.WordTrace]
  refine ⟨162793316718896922680754833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108528877812597948453836555 162793316718896922680754833)
  ·
    refine ⟨122094987539172692010566125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162793316718896922680754833 122094987539172692010566125)
    ·
      refine ⟨45785620327189759503962297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122094987539172692010566125 45785620327189759503962297)
      ·
        refine ⟨34339215245392319627971723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45785620327189759503962297 34339215245392319627971723)
        ·
          refine ⟨51508822868088479441957585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34339215245392319627971723 51508822868088479441957585)
          ·
            refine ⟨38631617151066359581468189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51508822868088479441957585 38631617151066359581468189)
            ·
              refine ⟨14486856431649884843050571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38631617151066359581468189 14486856431649884843050571)
              ·
                refine ⟨21730284647474827264575857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14486856431649884843050571 21730284647474827264575857)
                ·
                  refine ⟨16297713485606120448431893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21730284647474827264575857 16297713485606120448431893)
                  ·
                    refine ⟨763955319637786896020245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16297713485606120448431893 763955319637786896020245)
                    ·
                      rfl

theorem cell23_4463393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_4463393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463393 prefixEnd_4463393 := by exact prefixLift 4463393
  have htrace : WordTrace (prefixWord ++ tailWord_4463393) baseStart_4463393 baseEnd_4463393 := by
    simpa [prefixWord, tailWord_4463393, baseEnd_4463393] using wordTrace_append hprefix tailTrace_4463393
  have hstable : (prefixWord ++ tailWord_4463393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463393).length < 2 ^ (prefixWord ++ tailWord_4463393).sum := by decide
  have hdescent : baseEnd_4463393 < baseStart_4463393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463428 : List Nat := [2, 3, 4, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_4463428 : Nat := 118140960795 + 4463428 * 2 ^ 59
def prefixEnd_4463428 : Nat := 4983230072969 + 3 ^ 40 * 4463428 * 2
def baseEnd_4463428 : Nat := 2291883930736268051123075

theorem tailTrace_4463428 : CollatzResearch.WordTrace tailWord_4463428 prefixEnd_4463428 2291883930736268051123075 := by
  unfold tailWord_4463428
  simp only [CollatzResearch.WordTrace]
  refine ⟨81397296636885061829139469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108529728849180082438852625 81397296636885061829139469)
  ·
    refine ⟨30523986238831898185927301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81397296636885061829139469 30523986238831898185927301)
    ·
      refine ⟨5723247419780980909861369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30523986238831898185927301 5723247419780980909861369)
      ·
        refine ⟨4292435564835735682396027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5723247419780980909861369 4292435564835735682396027)
        ·
          refine ⟨6438653347253603523594041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4292435564835735682396027 6438653347253603523594041)
          ·
            refine ⟨4828990010440202642695531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6438653347253603523594041 4828990010440202642695531)
            ·
              refine ⟨7243485015660303964043297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4828990010440202642695531 7243485015660303964043297)
              ·
                refine ⟨5432613761745227973032473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7243485015660303964043297 5432613761745227973032473)
                ·
                  refine ⟨4074460321308920979774355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5432613761745227973032473 4074460321308920979774355)
                  ·
                    refine ⟨6111690481963381469661533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4074460321308920979774355 6111690481963381469661533)
                    ·
                      refine ⟨2291883930736268051123075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6111690481963381469661533 2291883930736268051123075)
                      ·
                        rfl

theorem cell23_4463428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_4463428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463428 prefixEnd_4463428 := by exact prefixLift 4463428
  have htrace : WordTrace (prefixWord ++ tailWord_4463428) baseStart_4463428 baseEnd_4463428 := by
    simpa [prefixWord, tailWord_4463428, baseEnd_4463428] using wordTrace_append hprefix tailTrace_4463428
  have hstable : (prefixWord ++ tailWord_4463428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463428).length < 2 ^ (prefixWord ++ tailWord_4463428).sum := by decide
  have hdescent : baseEnd_4463428 < baseStart_4463428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463440 : List Nat := [2, 1, 1, 1, 1, 4, 4, 4, 5]
def baseStart_4463440 : Nat := 118140960795 + 4463440 * 2 ^ 59
def prefixEnd_4463440 : Nat := 4983230072969 + 3 ^ 40 * 4463440 * 2
def baseEnd_4463440 : Nat := 254654454722680222685891

theorem tailTrace_4463440 : CollatzResearch.WordTrace tailWord_4463440 prefixEnd_4463440 254654454722680222685891 := by
  unfold tailWord_4463440
  simp only [CollatzResearch.WordTrace]
  refine ⟨81397515474863324853857887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108530020633151099805143849 81397515474863324853857887)
  ·
    refine ⟨122096273212294987280786831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81397515474863324853857887 122096273212294987280786831)
    ·
      refine ⟨183144409818442480921180247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122096273212294987280786831 183144409818442480921180247)
      ·
        refine ⟨274716614727663721381770371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183144409818442480921180247 274716614727663721381770371)
        ·
          refine ⟨412074922091495582072655557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274716614727663721381770371 412074922091495582072655557)
          ·
            refine ⟨77264047892155421638622917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 412074922091495582072655557 77264047892155421638622917)
            ·
              refine ⟨14487008979779141557241797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77264047892155421638622917 14487008979779141557241797)
              ·
                refine ⟨2716314183708589041982837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14487008979779141557241797 2716314183708589041982837)
                ·
                  refine ⟨254654454722680222685891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2716314183708589041982837 254654454722680222685891)
                  ·
                    rfl

theorem cell23_4463440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 5].length) (baseStart_4463440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463440 prefixEnd_4463440 := by exact prefixLift 4463440
  have htrace : WordTrace (prefixWord ++ tailWord_4463440) baseStart_4463440 baseEnd_4463440 := by
    simpa [prefixWord, tailWord_4463440, baseEnd_4463440] using wordTrace_append hprefix tailTrace_4463440
  have hstable : (prefixWord ++ tailWord_4463440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463440).length < 2 ^ (prefixWord ++ tailWord_4463440).sum := by decide
  have hdescent : baseEnd_4463440 < baseStart_4463440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463450 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3]
def baseStart_4463450 : Nat := 118140960795 + 4463450 * 2 ^ 59
def prefixEnd_4463450 : Nat := 4983230072969 + 3 ^ 40 * 4463450 * 2
def baseEnd_4463450 : Nat := 2291895227310666965047973

theorem tailTrace_4463450 : CollatzResearch.WordTrace tailWord_4463450 prefixEnd_4463450 2291895227310666965047973 := by
  unfold tailWord_4463450
  simp only [CollatzResearch.WordTrace]
  refine ⟨40698848919922605353894951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108530263786460280943719869 40698848919922605353894951)
  ·
    refine ⟨61048273379883908030842427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40698848919922605353894951 61048273379883908030842427)
    ·
      refine ⟨91572410069825862046263641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61048273379883908030842427 91572410069825862046263641)
      ·
        refine ⟨68679307552369396534697731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91572410069825862046263641 68679307552369396534697731)
        ·
          refine ⟨103018961328554094802046597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68679307552369396534697731 103018961328554094802046597)
          ·
            refine ⟨19316055249103892775383737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103018961328554094802046597 19316055249103892775383737)
            ·
              refine ⟨14487041436827919581537803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19316055249103892775383737 14487041436827919581537803)
              ·
                refine ⟨21730562155241879372306705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14487041436827919581537803 21730562155241879372306705)
                ·
                  refine ⟨16297921616431409529230029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21730562155241879372306705 16297921616431409529230029)
                  ·
                    refine ⟨6111720606161778573461261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16297921616431409529230029 6111720606161778573461261)
                    ·
                      refine ⟨2291895227310666965047973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6111720606161778573461261 2291895227310666965047973)
                      ·
                        rfl

theorem cell23_4463450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_4463450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463450 prefixEnd_4463450 := by exact prefixLift 4463450
  have htrace : WordTrace (prefixWord ++ tailWord_4463450) baseStart_4463450 baseEnd_4463450 := by
    simpa [prefixWord, tailWord_4463450, baseEnd_4463450] using wordTrace_append hprefix tailTrace_4463450
  have hstable : (prefixWord ++ tailWord_4463450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463450).length < 2 ^ (prefixWord ++ tailWord_4463450).sum := by decide
  have hdescent : baseEnd_4463450 < baseStart_4463450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463542 : List Nat := [5, 1, 4, 1, 2, 1, 2, 2, 5]
def baseStart_4463542 : Nat := 118140960795 + 4463542 * 2 ^ 59
def prefixEnd_4463542 : Nat := 4983230072969 + 3 ^ 40 * 4463542 * 2
def baseEnd_4463542 : Nat := 254660274170097845010839

theorem tailTrace_4463542 : CollatzResearch.WordTrace tailWord_4463542 prefixEnd_4463542 254660274170097845010839 := by
  unfold tailWord_4463542
  simp only [CollatzResearch.WordTrace]
  refine ⟨10174921949709820070495555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108532500796904747418619253 10174921949709820070495555)
  ·
    refine ⟨15262382924564730105743333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10174921949709820070495555 15262382924564730105743333)
    ·
      refine ⟨2861696798355886894826875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15262382924564730105743333 2861696798355886894826875)
      ·
        refine ⟨4292545197533830342240313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2861696798355886894826875 4292545197533830342240313)
        ·
          refine ⟨3219408898150372756680235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4292545197533830342240313 3219408898150372756680235)
          ·
            refine ⟨4829113347225559135020353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3219408898150372756680235 4829113347225559135020353)
            ·
              refine ⟨3621835010419169351265265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4829113347225559135020353 3621835010419169351265265)
              ·
                refine ⟨2716376257814377013448949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3621835010419169351265265 2716376257814377013448949)
                ·
                  refine ⟨254660274170097845010839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2716376257814377013448949 254660274170097845010839)
                  ·
                    rfl

theorem cell23_4463542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_4463542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463542 prefixEnd_4463542 := by exact prefixLift 4463542
  have htrace : WordTrace (prefixWord ++ tailWord_4463542) baseStart_4463542 baseEnd_4463542 := by
    simpa [prefixWord, tailWord_4463542, baseEnd_4463542] using wordTrace_append hprefix tailTrace_4463542
  have hstable : (prefixWord ++ tailWord_4463542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463542).length < 2 ^ (prefixWord ++ tailWord_4463542).sum := by decide
  have hdescent : baseEnd_4463542 < baseStart_4463542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463550 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_4463550 : Nat := 118140960795 + 4463550 * 2 ^ 59
def prefixEnd_4463550 : Nat := 4983230072969 + 3 ^ 40 * 4463550 * 2
def baseEnd_4463550 : Nat := 2291946575376116573797513

theorem tailTrace_4463550 : CollatzResearch.WordTrace tailWord_4463550 prefixEnd_4463550 2291946575376116573797513 := by
  unfold tailWord_4463550
  simp only [CollatzResearch.WordTrace]
  refine ⟨20349880372416017311777513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108532695319552092329480069 20349880372416017311777513)
  ·
    refine ⟨15262410279312012983833135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20349880372416017311777513 15262410279312012983833135)
    ·
      refine ⟨22893615418968019475749703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15262410279312012983833135 22893615418968019475749703)
      ·
        refine ⟨34340423128452029213624555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22893615418968019475749703 34340423128452029213624555)
        ·
          refine ⟨51510634692678043820436833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34340423128452029213624555 51510634692678043820436833)
          ·
            refine ⟨38632976019508532865327625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51510634692678043820436833 38632976019508532865327625)
            ·
              refine ⟨28974732014631399648995719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38632976019508532865327625 28974732014631399648995719)
              ·
                refine ⟨43462098021947099473493579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28974732014631399648995719 43462098021947099473493579)
                ·
                  refine ⟨65193147032920649210240369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43462098021947099473493579 65193147032920649210240369)
                  ·
                    refine ⟨48894860274690486907680277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65193147032920649210240369 48894860274690486907680277)
                    ·
                      refine ⟨2291946575376116573797513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48894860274690486907680277 2291946575376116573797513)
                      ·
                        rfl

theorem cell23_4463550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_4463550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463550 prefixEnd_4463550 := by exact prefixLift 4463550
  have htrace : WordTrace (prefixWord ++ tailWord_4463550) baseStart_4463550 baseEnd_4463550 := by
    simpa [prefixWord, tailWord_4463550, baseEnd_4463550] using wordTrace_append hprefix tailTrace_4463550
  have hstable : (prefixWord ++ tailWord_4463550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463550).length < 2 ^ (prefixWord ++ tailWord_4463550).sum := by decide
  have hdescent : baseEnd_4463550 < baseStart_4463550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463591 : List Nat := [1, 1, 5, 2, 2, 1, 1, 5, 1, 1, 3]
def baseStart_4463591 : Nat := 118140960795 + 4463591 * 2 ^ 59
def prefixEnd_4463591 : Nat := 4983230072969 + 3 ^ 40 * 4463591 * 2
def baseEnd_4463591 : Nat := 2291967628082950913384825

theorem tailTrace_4463591 : CollatzResearch.WordTrace tailWord_4463591 prefixEnd_4463591 2291967628082950913384825 := by
  unfold tailWord_4463591
  simp only [CollatzResearch.WordTrace]
  refine ⟨162800538372179602496462627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108533692248119734997641751 162800538372179602496462627)
  ·
    refine ⟨244200807558269403744693941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162800538372179602496462627 244200807558269403744693941)
    ·
      refine ⟨22893825708587756601065057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 244200807558269403744693941 22893825708587756601065057)
      ·
        refine ⟨17170369281440817450798793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22893825708587756601065057 17170369281440817450798793)
        ·
          refine ⟨12877776961080613088099095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17170369281440817450798793 12877776961080613088099095)
          ·
            refine ⟨19316665441620919632148643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12877776961080613088099095 19316665441620919632148643)
            ·
              refine ⟨28974998162431379448222965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19316665441620919632148643 28974998162431379448222965)
              ·
                refine ⟨2716406077727941823270903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28974998162431379448222965 2716406077727941823270903)
                ·
                  refine ⟨4074609116591912734906355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2716406077727941823270903 4074609116591912734906355)
                  ·
                    refine ⟨6111913674887869102359533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4074609116591912734906355 6111913674887869102359533)
                    ·
                      refine ⟨2291967628082950913384825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6111913674887869102359533 2291967628082950913384825)
                      ·
                        rfl

theorem cell23_4463591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_4463591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463591 prefixEnd_4463591 := by exact prefixLift 4463591
  have htrace : WordTrace (prefixWord ++ tailWord_4463591) baseStart_4463591 baseEnd_4463591 := by
    simpa [prefixWord, tailWord_4463591, baseEnd_4463591] using wordTrace_append hprefix tailTrace_4463591
  have hstable : (prefixWord ++ tailWord_4463591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463591).length < 2 ^ (prefixWord ++ tailWord_4463591).sum := by decide
  have hdescent : baseEnd_4463591 < baseStart_4463591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463594 : List Nat := [3, 1, 3, 1, 2, 2, 4, 1, 1, 5]
def baseStart_4463594 : Nat := 118140960795 + 4463594 * 2 ^ 59
def prefixEnd_4463594 : Nat := 4983230072969 + 3 ^ 40 * 4463594 * 2
def baseEnd_4463594 : Nat := 763989722841638133882437

theorem tailTrace_4463594 : CollatzResearch.WordTrace tailWord_4463594 prefixEnd_4463594 763989722841638133882437 := by
  unfold tailWord_4463594
  simp only [CollatzResearch.WordTrace]
  refine ⟨40700161947792183502205459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108533765194112489339214557 40700161947792183502205459)
  ·
    refine ⟨61050242921688275253308189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40700161947792183502205459 61050242921688275253308189)
    ·
      refine ⟨22893841095633103219990571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61050242921688275253308189 22893841095633103219990571)
      ·
        refine ⟨34340761643449654829985857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22893841095633103219990571 34340761643449654829985857)
        ·
          refine ⟨25755571232587241122489393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34340761643449654829985857 25755571232587241122489393)
          ·
            refine ⟨19316678424440430841867045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25755571232587241122489393 19316678424440430841867045)
            ·
              refine ⟨3621877204582580782850071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19316678424440430841867045 3621877204582580782850071)
              ·
                refine ⟨5432815806873871174275107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3621877204582580782850071 5432815806873871174275107)
                ·
                  refine ⟨8149223710310806761412661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5432815806873871174275107 8149223710310806761412661)
                  ·
                    refine ⟨763989722841638133882437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8149223710310806761412661 763989722841638133882437)
                    ·
                      rfl

theorem cell23_4463594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_4463594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463594 prefixEnd_4463594 := by exact prefixLift 4463594
  have htrace : WordTrace (prefixWord ++ tailWord_4463594) baseStart_4463594 baseEnd_4463594 := by
    simpa [prefixWord, tailWord_4463594, baseEnd_4463594] using wordTrace_append hprefix tailTrace_4463594
  have hstable : (prefixWord ++ tailWord_4463594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463594).length < 2 ^ (prefixWord ++ tailWord_4463594).sum := by decide
  have hdescent : baseEnd_4463594 < baseStart_4463594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463600 : List Nat := [2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 5]
def baseStart_4463600 : Nat := 118140960795 + 4463600 * 2 ^ 59
def prefixEnd_4463600 : Nat := 4983230072969 + 3 ^ 40 * 4463600 * 2
def baseEnd_4463600 : Nat := 2291972249408841378172283

theorem tailTrace_4463600 : CollatzResearch.WordTrace tailWord_4463600 prefixEnd_4463600 2291972249408841378172283 := by
  unfold tailWord_4463600
  simp only [CollatzResearch.WordTrace]
  refine ⟨81400433314573498516770127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108533911086097998022360169 81400433314573498516770127)
  ·
    refine ⟨122100649971860247775155191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81400433314573498516770127 122100649971860247775155191)
    ·
      refine ⟨183150974957790371662732787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122100649971860247775155191 183150974957790371662732787)
      ·
        refine ⟨274726462436685557494099181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183150974957790371662732787 274726462436685557494099181)
        ·
          refine ⟨103022423413757084060287193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274726462436685557494099181 103022423413757084060287193)
          ·
            refine ⟨77266817560317813045215395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103022423413757084060287193 77266817560317813045215395)
            ·
              refine ⟨115900226340476719567823093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77266817560317813045215395 115900226340476719567823093)
              ·
                refine ⟨10865646219419692459483415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115900226340476719567823093 10865646219419692459483415)
                ·
                  refine ⟨16298469329129538689225123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10865646219419692459483415 16298469329129538689225123)
                  ·
                    refine ⟨24447703993694308033837685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16298469329129538689225123 24447703993694308033837685)
                    ·
                      refine ⟨2291972249408841378172283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24447703993694308033837685 2291972249408841378172283)
                      ·
                        rfl

theorem cell23_4463600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 5].length) (baseStart_4463600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463600 prefixEnd_4463600 := by exact prefixLift 4463600
  have htrace : WordTrace (prefixWord ++ tailWord_4463600) baseStart_4463600 baseEnd_4463600 := by
    simpa [prefixWord, tailWord_4463600, baseEnd_4463600] using wordTrace_append hprefix tailTrace_4463600
  have hstable : (prefixWord ++ tailWord_4463600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463600).length < 2 ^ (prefixWord ++ tailWord_4463600).sum := by decide
  have hdescent : baseEnd_4463600 < baseStart_4463600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463610 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4]
def baseStart_4463610 : Nat := 118140960795 + 4463610 * 2 ^ 59
def prefixEnd_4463610 : Nat := 4983230072969 + 3 ^ 40 * 4463610 * 2
def baseEnd_4463610 : Nat := 2291977384215386339047237

theorem tailTrace_4463610 : CollatzResearch.WordTrace tailWord_4463610 prefixEnd_4463610 2291977384215386339047237 := by
  unfold tailWord_4463610
  simp only [CollatzResearch.WordTrace]
  refine ⟨40700307839777692185351071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108534154239407179160936189 40700307839777692185351071)
  ·
    refine ⟨61050461759666538278026607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40700307839777692185351071 61050461759666538278026607)
    ·
      refine ⟨91575692639499807417039911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61050461759666538278026607 91575692639499807417039911)
      ·
        refine ⟨137363538959249711125559867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91575692639499807417039911 137363538959249711125559867)
        ·
          refine ⟨206045308438874566688339801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137363538959249711125559867 206045308438874566688339801)
          ·
            refine ⟨154533981329155925016254851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206045308438874566688339801 154533981329155925016254851)
            ·
              refine ⟨231800971993733887524382277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154533981329155925016254851 231800971993733887524382277)
              ·
                refine ⟨43462682248825103910821677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 231800971993733887524382277 43462682248825103910821677)
                ·
                  refine ⟨16298505843309413966558129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43462682248825103910821677 16298505843309413966558129)
                  ·
                    refine ⟨12223879382482060474918597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16298505843309413966558129 12223879382482060474918597)
                    ·
                      refine ⟨2291977384215386339047237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12223879382482060474918597 2291977384215386339047237)
                      ·
                        rfl

theorem cell23_4463610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_4463610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463610 prefixEnd_4463610 := by exact prefixLift 4463610
  have htrace : WordTrace (prefixWord ++ tailWord_4463610) baseStart_4463610 baseEnd_4463610 := by
    simpa [prefixWord, tailWord_4463610, baseEnd_4463610] using wordTrace_append hprefix tailTrace_4463610
  have hstable : (prefixWord ++ tailWord_4463610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463610).length < 2 ^ (prefixWord ++ tailWord_4463610).sum := by decide
  have hdescent : baseEnd_4463610 < baseStart_4463610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463617 : List Nat := [1, 2, 4, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_4463617 : Nat := 118140960795 + 4463617 * 2 ^ 59
def prefixEnd_4463617 : Nat := 4983230072969 + 3 ^ 40 * 4463617 * 2
def baseEnd_4463617 : Nat := 2291980978579967811659705

theorem tailTrace_4463617 : CollatzResearch.WordTrace tailWord_4463617 prefixEnd_4463617 2291980978579967811659705 := by
  unfold tailWord_4463617
  simp only [CollatzResearch.WordTrace]
  refine ⟨162801486670085408936909105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108534324446723605957939403 162801486670085408936909105)
  ·
    refine ⟨122101115002564056702681829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162801486670085408936909105 122101115002564056702681829)
    ·
      refine ⟨22893959062980760631752843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122101115002564056702681829 22893959062980760631752843)
      ·
        refine ⟨34340938594471140947629265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22893959062980760631752843 34340938594471140947629265)
        ·
          refine ⟨25755703945853355710721949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34340938594471140947629265 25755703945853355710721949)
          ·
            refine ⟨9658388979695008391520731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25755703945853355710721949 9658388979695008391520731)
            ·
              refine ⟨14487583469542512587281097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9658388979695008391520731 14487583469542512587281097)
              ·
                refine ⟨10865687602156884440460823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14487583469542512587281097 10865687602156884440460823)
                ·
                  refine ⟨16298531403235326660691235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10865687602156884440460823 16298531403235326660691235)
                  ·
                    refine ⟨24447797104852989991036853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16298531403235326660691235 24447797104852989991036853)
                    ·
                      refine ⟨2291980978579967811659705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24447797104852989991036853 2291980978579967811659705)
                      ·
                        rfl

theorem cell23_4463617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_4463617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463617 prefixEnd_4463617 := by exact prefixLift 4463617
  have htrace : WordTrace (prefixWord ++ tailWord_4463617) baseStart_4463617 baseEnd_4463617 := by
    simpa [prefixWord, tailWord_4463617, baseEnd_4463617] using wordTrace_append hprefix tailTrace_4463617
  have hstable : (prefixWord ++ tailWord_4463617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463617).length < 2 ^ (prefixWord ++ tailWord_4463617).sum := by decide
  have hdescent : baseEnd_4463617 < baseStart_4463617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463627 : List Nat := [1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 4]
def baseStart_4463627 : Nat := 118140960795 + 4463627 * 2 ^ 59
def prefixEnd_4463627 : Nat := 4983230072969 + 3 ^ 40 * 4463627 * 2
def baseEnd_4463627 : Nat := 2291986113386512772534659

theorem tailTrace_4463627 : CollatzResearch.WordTrace tailWord_4463627 prefixEnd_4463627 2291986113386512772534659 := by
  unfold tailWord_4463627
  simp only [CollatzResearch.WordTrace]
  refine ⟨162801851400049180644773135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108534567600032787096515423 162801851400049180644773135)
  ·
    refine ⟨244202777100073770967159703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162801851400049180644773135 244202777100073770967159703)
    ·
      refine ⟨366304165650110656450739555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244202777100073770967159703 366304165650110656450739555)
      ·
        refine ⟨549456248475165984676109333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366304165650110656450739555 549456248475165984676109333)
        ·
          refine ⟨25755761647273405531692625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 549456248475165984676109333 25755761647273405531692625)
          ·
            refine ⟨19316821235455054148769469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25755761647273405531692625 19316821235455054148769469)
            ·
              refine ⟨7243807963295645305788551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19316821235455054148769469 7243807963295645305788551)
              ·
                refine ⟨10865711944943467958682827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7243807963295645305788551 10865711944943467958682827)
                ·
                  refine ⟨16298567917415201938024241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10865711944943467958682827 16298567917415201938024241)
                  ·
                    refine ⟨12223925938061401453518181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16298567917415201938024241 12223925938061401453518181)
                    ·
                      refine ⟨2291986113386512772534659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12223925938061401453518181 2291986113386512772534659)
                      ·
                        rfl

theorem cell23_4463627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 4].length) (baseStart_4463627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463627 prefixEnd_4463627 := by exact prefixLift 4463627
  have htrace : WordTrace (prefixWord ++ tailWord_4463627) baseStart_4463627 baseEnd_4463627 := by
    simpa [prefixWord, tailWord_4463627, baseEnd_4463627] using wordTrace_append hprefix tailTrace_4463627
  have hstable : (prefixWord ++ tailWord_4463627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463627).length < 2 ^ (prefixWord ++ tailWord_4463627).sum := by decide
  have hdescent : baseEnd_4463627 < baseStart_4463627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463637 : List Nat := [1, 3, 2, 1, 4, 1, 4, 7]
def baseStart_4463637 : Nat := 118140960795 + 4463637 * 2 ^ 59
def prefixEnd_4463637 : Nat := 4983230072969 + 3 ^ 40 * 4463637 * 2
def baseEnd_4463637 : Nat := 84888564747891027163319

theorem tailTrace_4463637 : CollatzResearch.WordTrace tailWord_4463637 prefixEnd_4463637 84888564747891027163319 := by
  unfold tailWord_4463637
  simp only [CollatzResearch.WordTrace]
  refine ⟨162802216130012952352637165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108534810753341968235091443 162802216130012952352637165)
  ·
    refine ⟨61050831048754857132238937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162802216130012952352637165 61050831048754857132238937)
    ·
      refine ⟨45788123286566142849179203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61050831048754857132238937 45788123286566142849179203)
      ·
        refine ⟨68682184929849214273768805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45788123286566142849179203 68682184929849214273768805)
        ·
          refine ⟨12877909674346727676331651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68682184929849214273768805 12877909674346727676331651)
          ·
            refine ⟨19316864511520091514497477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12877909674346727676331651 19316864511520091514497477)
            ·
              refine ⟨3621912095910017158968277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19316864511520091514497477 3621912095910017158968277)
              ·
                refine ⟨84888564747891027163319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3621912095910017158968277 84888564747891027163319)
                ·
                  rfl

theorem cell23_4463637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 7].length) (baseStart_4463637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463637 prefixEnd_4463637 := by exact prefixLift 4463637
  have htrace : WordTrace (prefixWord ++ tailWord_4463637) baseStart_4463637 baseEnd_4463637 := by
    simpa [prefixWord, tailWord_4463637, baseEnd_4463637] using wordTrace_append hprefix tailTrace_4463637
  have hstable : (prefixWord ++ tailWord_4463637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463637).length < 2 ^ (prefixWord ++ tailWord_4463637).sum := by decide
  have hdescent : baseEnd_4463637 < baseStart_4463637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463660 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 5]
def baseStart_4463660 : Nat := 118140960795 + 4463660 * 2 ^ 59
def prefixEnd_4463660 : Nat := 4983230072969 + 3 ^ 40 * 4463660 * 2
def baseEnd_4463660 : Nat := 2292003058248111143422007

theorem tailTrace_4463660 : CollatzResearch.WordTrace tailWord_4463660 prefixEnd_4463660 2292003058248111143422007 := by
  unfold tailWord_4463660
  simp only [CollatzResearch.WordTrace]
  refine ⟨81401527504464813640362217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108535370005953084853816289 81401527504464813640362217)
  ·
    refine ⟨61051145628348610230271663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81401527504464813640362217 61051145628348610230271663)
    ·
      refine ⟨91576718442522915345407495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61051145628348610230271663 91576718442522915345407495)
      ·
        refine ⟨137365077663784373018111243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91576718442522915345407495 137365077663784373018111243)
        ·
          refine ⟨206047616495676559527166865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137365077663784373018111243 206047616495676559527166865)
          ·
            refine ⟨154535712371757419645375149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206047616495676559527166865 154535712371757419645375149)
            ·
              refine ⟨57950892139409032367015681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154535712371757419645375149 57950892139409032367015681)
              ·
                refine ⟨43463169104556774275261761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57950892139409032367015681 43463169104556774275261761)
                ·
                  refine ⟨32597376828417580706446321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43463169104556774275261761 32597376828417580706446321)
                  ·
                    refine ⟨24448032621313185529834741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32597376828417580706446321 24448032621313185529834741)
                    ·
                      refine ⟨2292003058248111143422007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24448032621313185529834741 2292003058248111143422007)
                      ·
                        rfl

theorem cell23_4463660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_4463660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463660 prefixEnd_4463660 := by exact prefixLift 4463660
  have htrace : WordTrace (prefixWord ++ tailWord_4463660) baseStart_4463660 baseEnd_4463660 := by
    simpa [prefixWord, tailWord_4463660, baseEnd_4463660] using wordTrace_append hprefix tailTrace_4463660
  have hstable : (prefixWord ++ tailWord_4463660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463660).length < 2 ^ (prefixWord ++ tailWord_4463660).sum := by decide
  have hdescent : baseEnd_4463660 < baseStart_4463660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463664 : List Nat := [2, 1, 1, 1, 2, 4, 2, 4, 2, 1, 3]
def baseStart_4463664 : Nat := 118140960795 + 4463664 * 2 ^ 59
def prefixEnd_4463664 : Nat := 4983230072969 + 3 ^ 40 * 4463664 * 2
def baseEnd_4463664 : Nat := 2292005112170729127771989

theorem tailTrace_4463664 : CollatzResearch.WordTrace tailWord_4463664 prefixEnd_4463664 2292005112170729127771989 := by
  unfold tailWord_4463664
  simp only [CollatzResearch.WordTrace]
  refine ⟨81401600450457567981935023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108535467267276757309246697 81401600450457567981935023)
  ·
    refine ⟨122102400675686351972902535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81401600450457567981935023 122102400675686351972902535)
    ·
      refine ⟨183153601013529527959353803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122102400675686351972902535 183153601013529527959353803)
      ·
        refine ⟨274730401520294291939030705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183153601013529527959353803 274730401520294291939030705)
        ·
          refine ⟨206047801140220718954273029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274730401520294291939030705 206047801140220718954273029)
          ·
            refine ⟨38633962713791384803926193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 206047801140220718954273029 38633962713791384803926193)
            ·
              refine ⟨28975472035343538602944645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38633962713791384803926193 28975472035343538602944645)
              ·
                refine ⟨5432901006626913488052121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28975472035343538602944645 5432901006626913488052121)
                ·
                  refine ⟨4074675754970185116039091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5432901006626913488052121 4074675754970185116039091)
                  ·
                    refine ⟨6112013632455277674058637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4074675754970185116039091 6112013632455277674058637)
                    ·
                      refine ⟨2292005112170729127771989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6112013632455277674058637 2292005112170729127771989)
                      ·
                        rfl

theorem cell23_4463664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 2, 1, 3].length) (baseStart_4463664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463664 prefixEnd_4463664 := by exact prefixLift 4463664
  have htrace : WordTrace (prefixWord ++ tailWord_4463664) baseStart_4463664 baseEnd_4463664 := by
    simpa [prefixWord, tailWord_4463664, baseEnd_4463664] using wordTrace_append hprefix tailTrace_4463664
  have hstable : (prefixWord ++ tailWord_4463664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463664).length < 2 ^ (prefixWord ++ tailWord_4463664).sum := by decide
  have hdescent : baseEnd_4463664 < baseStart_4463664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463680 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 1, 8]
def baseStart_4463680 : Nat := 118140960795 + 4463680 * 2 ^ 59
def prefixEnd_4463680 : Nat := 4983230072969 + 3 ^ 40 * 4463680 * 2
def baseEnd_4463680 : Nat := 764004442620400355057305

theorem tailTrace_4463680 : CollatzResearch.WordTrace tailWord_4463680 prefixEnd_4463680 764004442620400355057305 := by
  unfold tailWord_4463680
  simp only [CollatzResearch.WordTrace]
  refine ⟨81401892234428585348226247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108535856312571447130968329 81401892234428585348226247)
  ·
    refine ⟨122102838351642878022339371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81401892234428585348226247 122102838351642878022339371)
    ·
      refine ⟨183154257527464317033509057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122102838351642878022339371 183154257527464317033509057)
      ·
        refine ⟨137365693145598237775131793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183154257527464317033509057 137365693145598237775131793)
        ·
          refine ⟨103024269859198678331348845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137365693145598237775131793 103024269859198678331348845)
          ·
            refine ⟨38634101197199504374255817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103024269859198678331348845 38634101197199504374255817)
            ·
              refine ⟨28975575897899628280691863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38634101197199504374255817 28975575897899628280691863)
              ·
                refine ⟨43463363846849442421037795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28975575897899628280691863 43463363846849442421037795)
                ·
                  refine ⟨65195045770274163631556693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43463363846849442421037795 65195045770274163631556693)
                  ·
                    refine ⟨764004442620400355057305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65195045770274163631556693 764004442620400355057305)
                    ·
                      rfl

theorem cell23_4463680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 1, 8].length) (baseStart_4463680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463680 prefixEnd_4463680 := by exact prefixLift 4463680
  have htrace : WordTrace (prefixWord ++ tailWord_4463680) baseStart_4463680 baseEnd_4463680 := by
    simpa [prefixWord, tailWord_4463680, baseEnd_4463680] using wordTrace_append hprefix tailTrace_4463680
  have hstable : (prefixWord ++ tailWord_4463680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463680).length < 2 ^ (prefixWord ++ tailWord_4463680).sum := by decide
  have hdescent : baseEnd_4463680 < baseStart_4463680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463704 : List Nat := [2, 1, 2, 2, 1, 3, 3, 2, 1, 4, 2]
def baseStart_4463704 : Nat := 118140960795 + 4463704 * 2 ^ 59
def prefixEnd_4463704 : Nat := 4983230072969 + 3 ^ 40 * 4463704 * 2
def baseEnd_4463704 : Nat := 2292025651396908971271805

theorem tailTrace_4463704 : CollatzResearch.WordTrace tailWord_4463704 prefixEnd_4463704 2292025651396908971271805 := by
  unfold tailWord_4463704
  simp only [CollatzResearch.WordTrace]
  refine ⟨81402329910385111397663083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108536439880513481863550777 81402329910385111397663083)
  ·
    refine ⟨122103494865577667096494625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81402329910385111397663083 122103494865577667096494625)
    ·
      refine ⟨91577621149183250322370969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122103494865577667096494625 91577621149183250322370969)
      ·
        refine ⟨68683215861887437741778227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91577621149183250322370969 68683215861887437741778227)
        ·
          refine ⟨103024823792831156612667341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68683215861887437741778227 103024823792831156612667341)
          ·
            refine ⟨38634308922311683729750253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103024823792831156612667341 38634308922311683729750253)
            ·
              refine ⟨14487865845866881398656345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38634308922311683729750253 14487865845866881398656345)
              ·
                refine ⟨10865899384400161048992259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14487865845866881398656345 10865899384400161048992259)
                ·
                  refine ⟨16298849076600241573488389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10865899384400161048992259 16298849076600241573488389)
                  ·
                    refine ⟨3056034201862545295029073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16298849076600241573488389 3056034201862545295029073)
                    ·
                      refine ⟨2292025651396908971271805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3056034201862545295029073 2292025651396908971271805)
                      ·
                        rfl

theorem cell23_4463704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_4463704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463704 prefixEnd_4463704 := by exact prefixLift 4463704
  have htrace : WordTrace (prefixWord ++ tailWord_4463704) baseStart_4463704 baseEnd_4463704 := by
    simpa [prefixWord, tailWord_4463704, baseEnd_4463704] using wordTrace_append hprefix tailTrace_4463704
  have hstable : (prefixWord ++ tailWord_4463704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463704).length < 2 ^ (prefixWord ++ tailWord_4463704).sum := by decide
  have hdescent : baseEnd_4463704 < baseStart_4463704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463708 : List Nat := [2, 2, 4, 1, 1, 1, 5, 1, 1, 3, 2]
def baseStart_4463708 : Nat := 118140960795 + 4463708 * 2 ^ 59
def prefixEnd_4463708 : Nat := 4983230072969 + 3 ^ 40 * 4463708 * 2
def baseEnd_4463708 : Nat := 2292027705319526955621787

theorem tailTrace_4463708 : CollatzResearch.WordTrace tailWord_4463708 prefixEnd_4463708 2292027705319526955621787 := by
  unfold tailWord_4463708
  simp only [CollatzResearch.WordTrace]
  refine ⟨81402402856377865739235889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108536537141837154318981185 81402402856377865739235889)
  ·
    refine ⟨61051802142283399304426917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81402402856377865739235889 61051802142283399304426917)
    ·
      refine ⟨11447212901678137369580047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61051802142283399304426917 11447212901678137369580047)
      ·
        refine ⟨17170819352517206054370071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11447212901678137369580047 17170819352517206054370071)
        ·
          refine ⟨25756229028775809081555107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17170819352517206054370071 25756229028775809081555107)
          ·
            refine ⟨38634343543163713622332661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25756229028775809081555107 38634343543163713622332661)
            ·
              refine ⟨3621969707171598152093687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38634343543163713622332661 3621969707171598152093687)
              ·
                refine ⟨5432954560757397228140531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3621969707171598152093687 5432954560757397228140531)
                ·
                  refine ⟨8149431841136095842210797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5432954560757397228140531 8149431841136095842210797)
                  ·
                    refine ⟨3056036940426035940829049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8149431841136095842210797 3056036940426035940829049)
                    ·
                      refine ⟨2292027705319526955621787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3056036940426035940829049 2292027705319526955621787)
                      ·
                        rfl

theorem cell23_4463708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_4463708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463708 prefixEnd_4463708 := by exact prefixLift 4463708
  have htrace : WordTrace (prefixWord ++ tailWord_4463708) baseStart_4463708 baseEnd_4463708 := by
    simpa [prefixWord, tailWord_4463708, baseEnd_4463708] using wordTrace_append hprefix tailTrace_4463708
  have hstable : (prefixWord ++ tailWord_4463708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463708).length < 2 ^ (prefixWord ++ tailWord_4463708).sum := by decide
  have hdescent : baseEnd_4463708 < baseStart_4463708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463717 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 2, 2, 4]
def baseStart_4463717 : Nat := 118140960795 + 4463717 * 2 ^ 59
def prefixEnd_4463717 : Nat := 4983230072969 + 3 ^ 40 * 4463717 * 2
def baseEnd_4463717 : Nat := 2292032326645417420409245

theorem tailTrace_4463717 : CollatzResearch.WordTrace tailWord_4463717 prefixEnd_4463717 2292032326645417420409245 := by
  unfold tailWord_4463717
  simp only [CollatzResearch.WordTrace]
  refine ⟨162805133969723126015549405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108536755979815417343699603 162805133969723126015549405)
  ·
    refine ⟨61051925238646172255831027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162805133969723126015549405 61051925238646172255831027)
    ·
      refine ⟨91577887857969258383746541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61051925238646172255831027 91577887857969258383746541)
      ·
        refine ⟨34341707946738471893904953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91577887857969258383746541 34341707946738471893904953)
        ·
          refine ⟨25756280960053853920428715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34341707946738471893904953 25756280960053853920428715)
          ·
            refine ⟨38634421440080780880643073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25756280960053853920428715 38634421440080780880643073)
            ·
              refine ⟨28975816080060585660482305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38634421440080780880643073 28975816080060585660482305)
              ·
                refine ⟨21731862060045439245361729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28975816080060585660482305 21731862060045439245361729)
                ·
                  refine ⟨16298896545034079434021297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21731862060045439245361729 16298896545034079434021297)
                  ·
                    refine ⟨12224172408775559575515973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16298896545034079434021297 12224172408775559575515973)
                    ·
                      refine ⟨2292032326645417420409245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12224172408775559575515973 2292032326645417420409245)
                      ·
                        rfl

theorem cell23_4463717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_4463717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463717 prefixEnd_4463717 := by exact prefixLift 4463717
  have htrace : WordTrace (prefixWord ++ tailWord_4463717) baseStart_4463717 baseEnd_4463717 := by
    simpa [prefixWord, tailWord_4463717, baseEnd_4463717] using wordTrace_append hprefix tailTrace_4463717
  have hstable : (prefixWord ++ tailWord_4463717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463717).length < 2 ^ (prefixWord ++ tailWord_4463717).sum := by decide
  have hdescent : baseEnd_4463717 < baseStart_4463717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463721 : List Nat := [1, 2, 1, 1, 1, 6, 1, 4, 2, 2, 2]
def baseStart_4463721 : Nat := 118140960795 + 4463721 * 2 ^ 59
def prefixEnd_4463721 : Nat := 4983230072969 + 3 ^ 40 * 4463721 * 2
def baseEnd_4463721 : Nat := 2292034380568035404759227

theorem tailTrace_4463721 : CollatzResearch.WordTrace tailWord_4463721 prefixEnd_4463721 2292034380568035404759227 := by
  unfold tailWord_4463721
  simp only [CollatzResearch.WordTrace]
  refine ⟨162805279861708634698695017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108536853241139089799130011 162805279861708634698695017)
  ·
    refine ⟨122103959896281476024021263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162805279861708634698695017 122103959896281476024021263)
    ·
      refine ⟨183155939844422214036031895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122103959896281476024021263 183155939844422214036031895)
      ·
        refine ⟨274733909766633321054047843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183155939844422214036031895 274733909766633321054047843)
        ·
          refine ⟨412100864649949981581071765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274733909766633321054047843 412100864649949981581071765)
          ·
            refine ⟨19317228030466405386612739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 412100864649949981581071765 19317228030466405386612739)
            ·
              refine ⟨28975842045699608079919109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19317228030466405386612739 28975842045699608079919109)
              ·
                refine ⟨5432970383568676514984833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28975842045699608079919109 5432970383568676514984833)
                ·
                  refine ⟨4074727787676507386238625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5432970383568676514984833 4074727787676507386238625)
                  ·
                    refine ⟨3056045840757380539678969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4074727787676507386238625 3056045840757380539678969)
                    ·
                      refine ⟨2292034380568035404759227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3056045840757380539678969 2292034380568035404759227)
                      ·
                        rfl

theorem cell23_4463721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 2, 2].length) (baseStart_4463721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463721 prefixEnd_4463721 := by exact prefixLift 4463721
  have htrace : WordTrace (prefixWord ++ tailWord_4463721) baseStart_4463721 baseEnd_4463721 := by
    simpa [prefixWord, tailWord_4463721, baseEnd_4463721] using wordTrace_append hprefix tailTrace_4463721
  have hstable : (prefixWord ++ tailWord_4463721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463721).length < 2 ^ (prefixWord ++ tailWord_4463721).sum := by decide
  have hdescent : baseEnd_4463721 < baseStart_4463721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463734 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_4463734 : Nat := 118140960795 + 4463734 * 2 ^ 59
def prefixEnd_4463734 : Nat := 4983230072969 + 3 ^ 40 * 4463734 * 2
def baseEnd_4463734 : Nat := 2292041055816543853896667

theorem tailTrace_4463734 : CollatzResearch.WordTrace tailWord_4463734 prefixEnd_4463734 2292041055816543853896667 := by
  unfold tailWord_4463734
  simp only [CollatzResearch.WordTrace]
  refine ⟨10175359625666346119932391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108537169340441025279278837 10175359625666346119932391)
  ·
    refine ⟨15263039438499519179898587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10175359625666346119932391 15263039438499519179898587)
    ·
      refine ⟨22894559157749278769847881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15263039438499519179898587 22894559157749278769847881)
      ·
        refine ⟨17170919368311959077385911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22894559157749278769847881 17170919368311959077385911)
        ·
          refine ⟨25756379052467938616078867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17170919368311959077385911 25756379052467938616078867)
          ·
            refine ⟨38634568578701907924118301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25756379052467938616078867 38634568578701907924118301)
            ·
              refine ⟨14487963217013215471544363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38634568578701907924118301 14487963217013215471544363)
              ·
                refine ⟨21731944825519823207316545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14487963217013215471544363 21731944825519823207316545)
                ·
                  refine ⟨16298958619139867405487409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21731944825519823207316545 16298958619139867405487409)
                  ·
                    refine ⟨12224218964354900554115557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16298958619139867405487409 12224218964354900554115557)
                    ·
                      refine ⟨2292041055816543853896667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12224218964354900554115557 2292041055816543853896667)
                      ·
                        rfl

theorem cell23_4463734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_4463734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463734 prefixEnd_4463734 := by exact prefixLift 4463734
  have htrace : WordTrace (prefixWord ++ tailWord_4463734) baseStart_4463734 baseEnd_4463734 := by
    simpa [prefixWord, tailWord_4463734, baseEnd_4463734] using wordTrace_append hprefix tailTrace_4463734
  have hstable : (prefixWord ++ tailWord_4463734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463734).length < 2 ^ (prefixWord ++ tailWord_4463734).sum := by decide
  have hdescent : baseEnd_4463734 < baseStart_4463734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463827 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 3]
def baseStart_4463827 : Nat := 118140960795 + 4463827 * 2 ^ 59
def prefixEnd_4463827 : Nat := 4983230072969 + 3 ^ 40 * 4463827 * 2
def baseEnd_4463827 : Nat := 2292088809517411990033739

theorem tailTrace_4463827 : CollatzResearch.WordTrace tailWord_4463827 prefixEnd_4463827 2292088809517411990033739 := by
  unfold tailWord_4463827
  simp only [CollatzResearch.WordTrace]
  refine ⟨162809145999324614802053735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108539430666216409868035823 162809145999324614802053735)
  ·
    refine ⟨244213718998986922203080603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162809145999324614802053735 244213718998986922203080603)
    ·
      refine ⟨366320578498480383304620905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244213718998986922203080603 366320578498480383304620905)
      ·
        refine ⟨274740433873860287478465679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 366320578498480383304620905 274740433873860287478465679)
        ·
          refine ⟨412110650810790431217698519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274740433873860287478465679 412110650810790431217698519)
          ·
            refine ⟨618165976216185646826547779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412110650810790431217698519 618165976216185646826547779)
            ·
              refine ⟨927248964324278470239821669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 618165976216185646826547779 927248964324278470239821669)
              ·
                refine ⟨173859180810802213169966563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 927248964324278470239821669 173859180810802213169966563)
                ·
                  refine ⟨260788771216203319754949845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173859180810802213169966563 260788771216203319754949845)
                  ·
                    refine ⟨6112236825379765306756637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 260788771216203319754949845 6112236825379765306756637)
                    ·
                      refine ⟨2292088809517411990033739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6112236825379765306756637 2292088809517411990033739)
                      ·
                        rfl

theorem cell23_4463827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 3].length) (baseStart_4463827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463827 prefixEnd_4463827 := by exact prefixLift 4463827
  have htrace : WordTrace (prefixWord ++ tailWord_4463827) baseStart_4463827 baseEnd_4463827 := by
    simpa [prefixWord, tailWord_4463827, baseEnd_4463827] using wordTrace_append hprefix tailTrace_4463827
  have hstable : (prefixWord ++ tailWord_4463827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463827).length < 2 ^ (prefixWord ++ tailWord_4463827).sum := by decide
  have hdescent : baseEnd_4463827 < baseStart_4463827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463828 : List Nat := [2, 4, 1, 4, 1, 1, 1, 2, 2, 1, 4]
def baseStart_4463828 : Nat := 118140960795 + 4463828 * 2 ^ 59
def prefixEnd_4463828 : Nat := 4983230072969 + 3 ^ 40 * 4463828 * 2
def baseEnd_4463828 : Nat := 2292089322998066486121235

theorem tailTrace_4463828 : CollatzResearch.WordTrace tailWord_4463828 prefixEnd_4463828 2292089322998066486121235 := by
  unfold tailWord_4463828
  simp only [CollatzResearch.WordTrace]
  refine ⟨81404591236160495986420069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108539454981547327981893425 81404591236160495986420069)
  ·
    refine ⟨15263360856780092997453763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81404591236160495986420069 15263360856780092997453763)
    ·
      refine ⟨22895041285170139496180645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15263360856780092997453763 22895041285170139496180645)
      ·
        refine ⟨4292820240969401155533871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22895041285170139496180645 4292820240969401155533871)
        ·
          refine ⟨6439230361454101733300807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4292820240969401155533871 6439230361454101733300807)
          ·
            refine ⟨9658845542181152599951211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6439230361454101733300807 9658845542181152599951211)
            ·
              refine ⟨14488268313271728899926817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9658845542181152599951211 14488268313271728899926817)
              ·
                refine ⟨10866201234953796674945113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14488268313271728899926817 10866201234953796674945113)
                ·
                  refine ⟨8149650926215347506208835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10866201234953796674945113 8149650926215347506208835)
                  ·
                    refine ⟨12224476389323021259313253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8149650926215347506208835 12224476389323021259313253)
                    ·
                      refine ⟨2292089322998066486121235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12224476389323021259313253 2292089322998066486121235)
                      ·
                        rfl

theorem cell23_4463828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_4463828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463828 prefixEnd_4463828 := by exact prefixLift 4463828
  have htrace : WordTrace (prefixWord ++ tailWord_4463828) baseStart_4463828 baseEnd_4463828 := by
    simpa [prefixWord, tailWord_4463828, baseEnd_4463828] using wordTrace_append hprefix tailTrace_4463828
  have hstable : (prefixWord ++ tailWord_4463828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463828).length < 2 ^ (prefixWord ++ tailWord_4463828).sum := by decide
  have hdescent : baseEnd_4463828 < baseStart_4463828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463851 : List Nat := [1, 1, 1, 1, 2, 8, 2, 1, 6]
def baseStart_4463851 : Nat := 118140960795 + 4463851 * 2 ^ 59
def prefixEnd_4463851 : Nat := 4983230072969 + 3 ^ 40 * 4463851 * 2
def baseEnd_4463851 : Nat := 254677903672568877348181

theorem tailTrace_4463851 : CollatzResearch.WordTrace tailWord_4463851 prefixEnd_4463851 254677903672568877348181 := by
  unfold tailWord_4463851
  simp only [CollatzResearch.WordTrace]
  refine ⟨162810021351237666900927407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108540014234158444600618271 162810021351237666900927407)
  ·
    refine ⟨244215032026856500351391111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162810021351237666900927407 244215032026856500351391111)
    ·
      refine ⟨366322548040284750527086667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244215032026856500351391111 366322548040284750527086667)
      ·
        refine ⟨549483822060427125790630001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366322548040284750527086667 549483822060427125790630001)
        ·
          refine ⟨412112866545320344342972501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 549483822060427125790630001 412112866545320344342972501)
          ·
            refine ⟨4829447654827972785269209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 412112866545320344342972501 4829447654827972785269209)
            ·
              refine ⟨3622085741120979588951907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4829447654827972785269209 3622085741120979588951907)
              ·
                refine ⟨5433128611681469383427861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3622085741120979588951907 5433128611681469383427861)
                ·
                  refine ⟨254677903672568877348181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5433128611681469383427861 254677903672568877348181)
                  ·
                    rfl

theorem cell23_4463851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 6].length) (baseStart_4463851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463851 prefixEnd_4463851 := by exact prefixLift 4463851
  have htrace : WordTrace (prefixWord ++ tailWord_4463851) baseStart_4463851 baseEnd_4463851 := by
    simpa [prefixWord, tailWord_4463851, baseEnd_4463851] using wordTrace_append hprefix tailTrace_4463851
  have hstable : (prefixWord ++ tailWord_4463851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463851).length < 2 ^ (prefixWord ++ tailWord_4463851).sum := by decide
  have hdescent : baseEnd_4463851 < baseStart_4463851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463871 : List Nat := [1, 1, 2, 2, 1, 5, 1, 3, 2, 3, 2]
def baseStart_4463871 : Nat := 118140960795 + 4463871 * 2 ^ 59
def prefixEnd_4463871 : Nat := 4983230072969 + 3 ^ 40 * 4463871 * 2
def baseEnd_4463871 : Nat := 2292111402666209817883537

theorem tailTrace_4463871 : CollatzResearch.WordTrace tailWord_4463871 prefixEnd_4463871 2292111402666209817883537 := by
  unfold tailWord_4463871
  simp only [CollatzResearch.WordTrace]
  refine ⟨162810750811165210316655467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108540500540776806877770311 162810750811165210316655467)
  ·
    refine ⟨244216126216747815474983201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162810750811165210316655467 244216126216747815474983201)
    ·
      refine ⟨183162094662560861606237401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244216126216747815474983201 183162094662560861606237401)
      ·
        refine ⟨137371570996920646204678051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183162094662560861606237401 137371570996920646204678051)
        ·
          refine ⟨206057356495380969307017077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137371570996920646204678051 206057356495380969307017077)
          ·
            refine ⟨19317877171441965872532851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 206057356495380969307017077 19317877171441965872532851)
            ·
              refine ⟨28976815757162948808799277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19317877171441965872532851 28976815757162948808799277)
              ·
                refine ⟨10866305908936105803299729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28976815757162948808799277 10866305908936105803299729)
                ·
                  refine ⟨8149729431702079352474797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10866305908936105803299729 8149729431702079352474797)
                  ·
                    refine ⟨3056148536888279757178049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8149729431702079352474797 3056148536888279757178049)
                    ·
                      refine ⟨2292111402666209817883537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3056148536888279757178049 2292111402666209817883537)
                      ·
                        rfl

theorem cell23_4463871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 3, 2].length) (baseStart_4463871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463871 prefixEnd_4463871 := by exact prefixLift 4463871
  have htrace : WordTrace (prefixWord ++ tailWord_4463871) baseStart_4463871 baseEnd_4463871 := by
    simpa [prefixWord, tailWord_4463871, baseEnd_4463871] using wordTrace_append hprefix tailTrace_4463871
  have hstable : (prefixWord ++ tailWord_4463871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463871).length < 2 ^ (prefixWord ++ tailWord_4463871).sum := by decide
  have hdescent : baseEnd_4463871 < baseStart_4463871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463881 : List Nat := [1, 2, 1, 1, 3, 3, 5, 1, 1, 5]
def baseStart_4463881 : Nat := 118140960795 + 4463881 * 2 ^ 59
def prefixEnd_4463881 : Nat := 4983230072969 + 3 ^ 40 * 4463881 * 2
def baseEnd_4463881 : Nat := 764038845824251592919497

theorem tailTrace_4463881 : CollatzResearch.WordTrace tailWord_4463881 prefixEnd_4463881 764038845824251592919497 := by
  unfold tailWord_4463881
  simp only [CollatzResearch.WordTrace]
  refine ⟨162811115541128982024519497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108540743694085988016346331 162811115541128982024519497)
  ·
    refine ⟨122108336655846736518389623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162811115541128982024519497 122108336655846736518389623)
    ·
      refine ⟨183162504983770104777584435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122108336655846736518389623 183162504983770104777584435)
      ·
        refine ⟨274743757475655157166376653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183162504983770104777584435 274743757475655157166376653)
        ·
          refine ⟨103028909053370683937391245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274743757475655157166376653 103028909053370683937391245)
          ·
            refine ⟨38635840895014006476521717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103028909053370683937391245 38635840895014006476521717)
            ·
              refine ⟨3622110083907563107173911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38635840895014006476521717 3622110083907563107173911)
              ·
                refine ⟨5433165125861344660760867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3622110083907563107173911 5433165125861344660760867)
                ·
                  refine ⟨8149747688792016991141301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5433165125861344660760867 8149747688792016991141301)
                  ·
                    refine ⟨764038845824251592919497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8149747688792016991141301 764038845824251592919497)
                    ·
                      rfl

theorem cell23_4463881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 1, 5].length) (baseStart_4463881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463881 prefixEnd_4463881 := by exact prefixLift 4463881
  have htrace : WordTrace (prefixWord ++ tailWord_4463881) baseStart_4463881 baseEnd_4463881 := by
    simpa [prefixWord, tailWord_4463881, baseEnd_4463881] using wordTrace_append hprefix tailTrace_4463881
  have hstable : (prefixWord ++ tailWord_4463881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463881).length < 2 ^ (prefixWord ++ tailWord_4463881).sum := by decide
  have hdescent : baseEnd_4463881 < baseStart_4463881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463901 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_4463901 : Nat := 118140960795 + 4463901 * 2 ^ 59
def prefixEnd_4463901 : Nat := 4983230072969 + 3 ^ 40 * 4463901 * 2
def baseEnd_4463901 : Nat := 2292126807085844700508399

theorem tailTrace_4463901 : CollatzResearch.WordTrace tailWord_4463901 prefixEnd_4463901 2292126807085844700508399 := by
  unfold tailWord_4463901
  simp only [CollatzResearch.WordTrace]
  refine ⟨162811845001056525440247557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108541230000704350293498371 162811845001056525440247557)
  ·
    refine ⟨30527220937698098520046417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162811845001056525440247557 30527220937698098520046417)
    ·
      refine ⟨22895415703273573890034813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30527220937698098520046417 22895415703273573890034813)
      ·
        refine ⟨8585780888727590208763055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22895415703273573890034813 8585780888727590208763055)
        ·
          refine ⟨12878671333091385313144583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8585780888727590208763055 12878671333091385313144583)
          ·
            refine ⟨19318006999637077969716875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12878671333091385313144583 19318006999637077969716875)
            ·
              refine ⟨28977010499455616954575313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19318006999637077969716875 28977010499455616954575313)
              ·
                refine ⟨21732757874591712715931485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28977010499455616954575313 21732757874591712715931485)
                ·
                  refine ⟨8149784202971892268474307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21732757874591712715931485 8149784202971892268474307)
                  ·
                    refine ⟨12224676304457838402711461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8149784202971892268474307 12224676304457838402711461)
                    ·
                      refine ⟨2292126807085844700508399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12224676304457838402711461 2292126807085844700508399)
                      ·
                        rfl

theorem cell23_4463901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_4463901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463901 prefixEnd_4463901 := by exact prefixLift 4463901
  have htrace : WordTrace (prefixWord ++ tailWord_4463901) baseStart_4463901 baseEnd_4463901 := by
    simpa [prefixWord, tailWord_4463901, baseEnd_4463901] using wordTrace_append hprefix tailTrace_4463901
  have hstable : (prefixWord ++ tailWord_4463901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463901).length < 2 ^ (prefixWord ++ tailWord_4463901).sum := by decide
  have hdescent : baseEnd_4463901 < baseStart_4463901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463921 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 3, 2, 3]
def baseStart_4463921 : Nat := 118140960795 + 4463921 * 2 ^ 59
def prefixEnd_4463921 : Nat := 4983230072969 + 3 ^ 40 * 4463921 * 2
def baseEnd_4463921 : Nat := 2292137076698934622258307

theorem tailTrace_4463921 : CollatzResearch.WordTrace tailWord_4463921 prefixEnd_4463921 2292137076698934622258307 := by
  unfold tailWord_4463921
  simp only [CollatzResearch.WordTrace]
  refine ⟨162812574460984068855975617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108541716307322712570650411 162812574460984068855975617)
  ·
    refine ⟨122109430845738051641981713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162812574460984068855975617 122109430845738051641981713)
    ·
      refine ⟨91582073134303538731486285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122109430845738051641981713 91582073134303538731486285)
      ·
        refine ⟨34343277425363827024307357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91582073134303538731486285 34343277425363827024307357)
        ·
          refine ⟨12878729034511435134115259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34343277425363827024307357 12878729034511435134115259)
          ·
            refine ⟨19318093551767152701172889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12878729034511435134115259 19318093551767152701172889)
            ·
              refine ⟨14488570163825364525879667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19318093551767152701172889 14488570163825364525879667)
              ·
                refine ⟨21732855245738046788819501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14488570163825364525879667 21732855245738046788819501)
                ·
                  refine ⟨8149820717151767545807313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21732855245738046788819501 8149820717151767545807313)
                  ·
                    refine ⟨6112365537863825659355485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8149820717151767545807313 6112365537863825659355485)
                    ·
                      refine ⟨2292137076698934622258307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6112365537863825659355485 2292137076698934622258307)
                      ·
                        rfl

theorem cell23_4463921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_4463921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463921 prefixEnd_4463921 := by exact prefixLift 4463921
  have htrace : WordTrace (prefixWord ++ tailWord_4463921) baseStart_4463921 baseEnd_4463921 := by
    simpa [prefixWord, tailWord_4463921, baseEnd_4463921] using wordTrace_append hprefix tailTrace_4463921
  have hstable : (prefixWord ++ tailWord_4463921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463921).length < 2 ^ (prefixWord ++ tailWord_4463921).sum := by decide
  have hdescent : baseEnd_4463921 < baseStart_4463921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463935 : List Nat := [1, 1, 2, 2, 4, 2, 1, 5, 1, 2, 2]
def baseStart_4463935 : Nat := 118140960795 + 4463935 * 2 ^ 59
def prefixEnd_4463935 : Nat := 4983230072969 + 3 ^ 40 * 4463935 * 2
def baseEnd_4463935 : Nat := 2292144265428097567483243

theorem tailTrace_4463935 : CollatzResearch.WordTrace tailWord_4463935 prefixEnd_4463935 2292144265428097567483243 := by
  unfold tailWord_4463935
  simp only [CollatzResearch.WordTrace]
  refine ⟨162813085082933349246985259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108542056721955566164656839 162813085082933349246985259)
  ·
    refine ⟨244219627624400023870477889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162813085082933349246985259 244219627624400023870477889)
    ·
      refine ⟨183164720718300017902858417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244219627624400023870477889 183164720718300017902858417)
      ·
        refine ⟨137373540538725013427143813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183164720718300017902858417 137373540538725013427143813)
        ·
          refine ⟨25757538851010940017589465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137373540538725013427143813 25757538851010940017589465)
          ·
            refine ⟨19318154138258205013192099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25757538851010940017589465 19318154138258205013192099)
            ·
              refine ⟨28977231207387307519788149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19318154138258205013192099 28977231207387307519788149)
              ·
                refine ⟨2716615425692560079980139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28977231207387307519788149 2716615425692560079980139)
                ·
                  refine ⟨4074923138538840119970209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2716615425692560079980139 4074923138538840119970209)
                  ·
                    refine ⟨3056192353904130089977657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4074923138538840119970209 3056192353904130089977657)
                    ·
                      refine ⟨2292144265428097567483243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3056192353904130089977657 2292144265428097567483243)
                      ·
                        rfl

theorem cell23_4463935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 1, 2, 2].length) (baseStart_4463935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463935 prefixEnd_4463935 := by exact prefixLift 4463935
  have htrace : WordTrace (prefixWord ++ tailWord_4463935) baseStart_4463935 baseEnd_4463935 := by
    simpa [prefixWord, tailWord_4463935, baseEnd_4463935] using wordTrace_append hprefix tailTrace_4463935
  have hstable : (prefixWord ++ tailWord_4463935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463935).length < 2 ^ (prefixWord ++ tailWord_4463935).sum := by decide
  have hdescent : baseEnd_4463935 < baseStart_4463935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463961 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 5, 3, 2]
def baseStart_4463961 : Nat := 118140960795 + 4463961 * 2 ^ 59
def prefixEnd_4463961 : Nat := 4983230072969 + 3 ^ 40 * 4463961 * 2
def baseEnd_4463961 : Nat := 2292157615925114465758123

theorem tailTrace_4463961 : CollatzResearch.WordTrace tailWord_4463961 prefixEnd_4463961 2292157615925114465758123 := by
  unfold tailWord_4463961
  simp only [CollatzResearch.WordTrace]
  refine ⟨162814033380839155687431737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108542688920559437124954491 162814033380839155687431737)
  ·
    refine ⟨122110525035629366765573803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162814033380839155687431737 122110525035629366765573803)
    ·
      refine ⟨183165787553444050148360705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122110525035629366765573803 183165787553444050148360705)
      ·
        refine ⟨137374340665083037611270529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183165787553444050148360705 137374340665083037611270529)
        ·
          refine ⟨103030755498812278208452897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137374340665083037611270529 103030755498812278208452897)
          ·
            refine ⟨77273066624109208656339673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103030755498812278208452897 77273066624109208656339673)
            ·
              refine ⟨57954799968081906492254755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77273066624109208656339673 57954799968081906492254755)
              ·
                refine ⟨86932199952122859738382133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57954799968081906492254755 86932199952122859738382133)
                ·
                  refine ⟨8149893745511518100473325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86932199952122859738382133 8149893745511518100473325)
                  ·
                    refine ⟨3056210154566819287677497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8149893745511518100473325 3056210154566819287677497)
                    ·
                      refine ⟨2292157615925114465758123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3056210154566819287677497 2292157615925114465758123)
                      ·
                        rfl

theorem cell23_4463961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 3, 2].length) (baseStart_4463961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463961 prefixEnd_4463961 := by exact prefixLift 4463961
  have htrace : WordTrace (prefixWord ++ tailWord_4463961) baseStart_4463961 baseEnd_4463961 := by
    simpa [prefixWord, tailWord_4463961, baseEnd_4463961] using wordTrace_append hprefix tailTrace_4463961
  have hstable : (prefixWord ++ tailWord_4463961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463961).length < 2 ^ (prefixWord ++ tailWord_4463961).sum := by decide
  have hdescent : baseEnd_4463961 < baseStart_4463961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463965 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_4463965 : Nat := 118140960795 + 4463965 * 2 ^ 59
def prefixEnd_4463965 : Nat := 4983230072969 + 3 ^ 40 * 4463965 * 2
def baseEnd_4463965 : Nat := 2292159669847732450108105

theorem tailTrace_4463965 : CollatzResearch.WordTrace tailWord_4463965 prefixEnd_4463965 2292159669847732450108105 := by
  unfold tailWord_4463965
  simp only [CollatzResearch.WordTrace]
  refine ⟨162814179272824664370577349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108542786181883109580384899 162814179272824664370577349)
  ·
    refine ⟨30527658613654624569483253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162814179272824664370577349 30527658613654624569483253)
    ·
      refine ⟨2861967995030121053389055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30527658613654624569483253 2861967995030121053389055)
      ·
        refine ⟨4292951992545181580083583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2861967995030121053389055 4292951992545181580083583)
        ·
          refine ⟨6439427988817772370125375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4292951992545181580083583 6439427988817772370125375)
          ·
            refine ⟨9659141983226658555188063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6439427988817772370125375 9659141983226658555188063)
            ·
              refine ⟨14488712974839987832782095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9659141983226658555188063 14488712974839987832782095)
              ·
                refine ⟨21733069462259981749173143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14488712974839987832782095 21733069462259981749173143)
                ·
                  refine ⟨32599604193389972623759715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21733069462259981749173143 32599604193389972623759715)
                  ·
                    refine ⟨48899406290084958935639573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32599604193389972623759715 48899406290084958935639573)
                    ·
                      refine ⟨2292159669847732450108105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48899406290084958935639573 2292159669847732450108105)
                      ·
                        rfl

theorem cell23_4463965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_4463965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463965 prefixEnd_4463965 := by exact prefixLift 4463965
  have htrace : WordTrace (prefixWord ++ tailWord_4463965) baseStart_4463965 baseEnd_4463965 := by
    simpa [prefixWord, tailWord_4463965, baseEnd_4463965] using wordTrace_append hprefix tailTrace_4463965
  have hstable : (prefixWord ++ tailWord_4463965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463965).length < 2 ^ (prefixWord ++ tailWord_4463965).sum := by decide
  have hdescent : baseEnd_4463965 < baseStart_4463965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463968 : List Nat := [2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 3]
def baseStart_4463968 : Nat := 118140960795 + 4463968 * 2 ^ 59
def prefixEnd_4463968 : Nat := 4983230072969 + 3 ^ 40 * 4463968 * 2
def baseEnd_4463968 : Nat := 2292161210289695938370591

theorem tailTrace_4463968 : CollatzResearch.WordTrace tailWord_4463968 prefixEnd_4463968 2292161210289695938370591 := by
  unfold tailWord_4463968
  simp only [CollatzResearch.WordTrace]
  refine ⟨81407144345906897941468279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108542859127875863921957705 81407144345906897941468279)
  ·
    refine ⟨122110716518860346912202419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81407144345906897941468279 122110716518860346912202419)
    ·
      refine ⟨183166074778290520368303629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122110716518860346912202419 183166074778290520368303629)
      ·
        refine ⟨68687278041858945138113861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183166074778290520368303629 68687278041858945138113861)
        ·
          refine ⟨12878864632848552213396349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68687278041858945138113861 12878864632848552213396349)
          ·
            refine ⟨4829574237318207080023631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12878864632848552213396349 4829574237318207080023631)
            ·
              refine ⟨7244361355977310620035447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4829574237318207080023631 7244361355977310620035447)
              ·
                refine ⟨10866542033965965930053171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7244361355977310620035447 10866542033965965930053171)
                ·
                  refine ⟨16299813050948948895079757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10866542033965965930053171 16299813050948948895079757)
                  ·
                    refine ⟨6112429894105855835654909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16299813050948948895079757 6112429894105855835654909)
                    ·
                      refine ⟨2292161210289695938370591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6112429894105855835654909 2292161210289695938370591)
                      ·
                        rfl

theorem cell23_4463968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_4463968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463968 prefixEnd_4463968 := by exact prefixLift 4463968
  have htrace : WordTrace (prefixWord ++ tailWord_4463968) baseStart_4463968 baseEnd_4463968 := by
    simpa [prefixWord, tailWord_4463968, baseEnd_4463968] using wordTrace_append hprefix tailTrace_4463968
  have hstable : (prefixWord ++ tailWord_4463968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463968).length < 2 ^ (prefixWord ++ tailWord_4463968).sum := by decide
  have hdescent : baseEnd_4463968 < baseStart_4463968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463991 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 3, 4, 2]
def baseStart_4463991 : Nat := 118140960795 + 4463991 * 2 ^ 59
def prefixEnd_4463991 : Nat := 4983230072969 + 3 ^ 40 * 4463991 * 2
def baseEnd_4463991 : Nat := 2292173020344749348382985

theorem tailTrace_4463991 : CollatzResearch.WordTrace tailWord_4463991 prefixEnd_4463991 2292173020344749348382985 := by
  unfold tailWord_4463991
  simp only [CollatzResearch.WordTrace]
  refine ⟨162815127570730470811023827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108543418380486980540682551 162815127570730470811023827)
  ·
    refine ⟨244222691356095706216535741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162815127570730470811023827 244222691356095706216535741)
    ·
      refine ⟨91583509258535889831200903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244222691356095706216535741 91583509258535889831200903)
      ·
        refine ⟨137375263887803834746801355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91583509258535889831200903 137375263887803834746801355)
        ·
          refine ⟨206062895831705752120202033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137375263887803834746801355 206062895831705752120202033)
          ·
            refine ⟨154547171873779314090151525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206062895831705752120202033 154547171873779314090151525)
            ·
              refine ⟨28977594726333621391903411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154547171873779314090151525 28977594726333621391903411)
              ·
                refine ⟨43466392089500432087855117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28977594726333621391903411 43466392089500432087855117)
                ·
                  refine ⟨16299897033562662032945669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43466392089500432087855117 16299897033562662032945669)
                  ·
                    refine ⟨3056230693792999131177313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16299897033562662032945669 3056230693792999131177313)
                    ·
                      refine ⟨2292173020344749348382985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3056230693792999131177313 2292173020344749348382985)
                      ·
                        rfl

theorem cell23_4463991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 4, 2].length) (baseStart_4463991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463991 prefixEnd_4463991 := by exact prefixLift 4463991
  have htrace : WordTrace (prefixWord ++ tailWord_4463991) baseStart_4463991 baseEnd_4463991 := by
    simpa [prefixWord, tailWord_4463991, baseEnd_4463991] using wordTrace_append hprefix tailTrace_4463991
  have hstable : (prefixWord ++ tailWord_4463991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463991).length < 2 ^ (prefixWord ++ tailWord_4463991).sum := by decide
  have hdescent : baseEnd_4463991 < baseStart_4463991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4463994 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5]
def baseStart_4463994 : Nat := 118140960795 + 4463994 * 2 ^ 59
def prefixEnd_4463994 : Nat := 4983230072969 + 3 ^ 40 * 4463994 * 2
def baseEnd_4463994 : Nat := 2292174560786712836645471

theorem tailTrace_4463994 : CollatzResearch.WordTrace tailWord_4463994 prefixEnd_4463994 2292174560786712836645471 := by
  unfold tailWord_4463994
  simp only [CollatzResearch.WordTrace]
  refine ⟨40703809247429900580845759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108543491326479734882255357 40703809247429900580845759)
  ·
    refine ⟨61055713871144850871268639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40703809247429900580845759 61055713871144850871268639)
    ·
      refine ⟨91583570806717276306902959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61055713871144850871268639 91583570806717276306902959)
      ·
        refine ⟨137375356210075914460354439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91583570806717276306902959 137375356210075914460354439)
        ·
          refine ⟨206063034315113871690531659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137375356210075914460354439 206063034315113871690531659)
          ·
            refine ⟨309094551472670807535797489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206063034315113871690531659 309094551472670807535797489)
            ·
              refine ⟨231820913604503105651848117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309094551472670807535797489 231820913604503105651848117)
              ·
                refine ⟨21733210650422166154860761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 231820913604503105651848117 21733210650422166154860761)
                ·
                  refine ⟨16299907987816624616145571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21733210650422166154860761 16299907987816624616145571)
                  ·
                    refine ⟨24449861981724936924218357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16299907987816624616145571 24449861981724936924218357)
                    ·
                      refine ⟨2292174560786712836645471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24449861981724936924218357 2292174560786712836645471)
                      ·
                        rfl

theorem cell23_4463994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_4463994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4463994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4463994 prefixEnd_4463994 := by exact prefixLift 4463994
  have htrace : WordTrace (prefixWord ++ tailWord_4463994) baseStart_4463994 baseEnd_4463994 := by
    simpa [prefixWord, tailWord_4463994, baseEnd_4463994] using wordTrace_append hprefix tailTrace_4463994
  have hstable : (prefixWord ++ tailWord_4463994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4463994).length < 2 ^ (prefixWord ++ tailWord_4463994).sum := by decide
  have hdescent : baseEnd_4463994 < baseStart_4463994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4463994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464025 : List Nat := [1, 2, 1, 2, 1, 6, 1, 3, 2, 2, 2]
def baseStart_4464025 : Nat := 118140960795 + 4464025 * 2 ^ 59
def prefixEnd_4464025 : Nat := 4983230072969 + 3 ^ 40 * 4464025 * 2
def baseEnd_4464025 : Nat := 2292190478687002215357829

theorem tailTrace_4464025 : CollatzResearch.WordTrace tailWord_4464025 prefixEnd_4464025 2292190478687002215357829 := by
  unfold tailWord_4464025
  simp only [CollatzResearch.WordTrace]
  refine ⟨162816367652607294617761529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108544245101738196411841019 162816367652607294617761529)
  ·
    refine ⟨122112275739455470963321147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162816367652607294617761529 122112275739455470963321147)
    ·
      refine ⟨183168413609183206444981721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122112275739455470963321147 183168413609183206444981721)
      ·
        refine ⟨137376310206887404833736291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183168413609183206444981721 137376310206887404833736291)
        ·
          refine ⟨206064465310331107250604437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137376310206887404833736291 206064465310331107250604437)
          ·
            refine ⟨9659271811421770652372083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 206064465310331107250604437 9659271811421770652372083)
            ·
              refine ⟨14488907717132655978558125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9659271811421770652372083 14488907717132655978558125)
              ·
                refine ⟨5433340393924745991959297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14488907717132655978558125 5433340393924745991959297)
                ·
                  refine ⟨4075005295443559493969473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5433340393924745991959297 4075005295443559493969473)
                  ·
                    refine ⟨3056253971582669620477105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4075005295443559493969473 3056253971582669620477105)
                    ·
                      refine ⟨2292190478687002215357829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3056253971582669620477105 2292190478687002215357829)
                      ·
                        rfl

theorem cell23_4464025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 2, 2].length) (baseStart_4464025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464025 prefixEnd_4464025 := by exact prefixLift 4464025
  have htrace : WordTrace (prefixWord ++ tailWord_4464025) baseStart_4464025 baseEnd_4464025 := by
    simpa [prefixWord, tailWord_4464025, baseEnd_4464025] using wordTrace_append hprefix tailTrace_4464025
  have hstable : (prefixWord ++ tailWord_4464025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464025).length < 2 ^ (prefixWord ++ tailWord_4464025).sum := by decide
  have hdescent : baseEnd_4464025 < baseStart_4464025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464044 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 1, 7]
def baseStart_4464044 : Nat := 118140960795 + 4464044 * 2 ^ 59
def prefixEnd_4464044 : Nat := 4983230072969 + 3 ^ 40 * 4464044 * 2
def baseEnd_4464044 : Nat := 764066744939812547006747

theorem tailTrace_4464044 : CollatzResearch.WordTrace tailWord_4464044 prefixEnd_4464044 764066744939812547006747 := by
  unfold tailWord_4464044
  simp only [CollatzResearch.WordTrace]
  refine ⟨81408530319769230431351593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108544707093025640575135457 81408530319769230431351593)
  ·
    refine ⟨61056397739826922823513695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81408530319769230431351593 61056397739826922823513695)
    ·
      refine ⟨91584596609740384235270543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61056397739826922823513695 91584596609740384235270543)
      ·
        refine ⟨137376894914610576352905815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91584596609740384235270543 137376894914610576352905815)
        ·
          refine ⟨206065342371915864529358723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137376894914610576352905815 206065342371915864529358723)
          ·
            refine ⟨309098013557873796794038085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206065342371915864529358723 309098013557873796794038085)
            ·
              refine ⟨57955877542101336898882141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 309098013557873796794038085 57955877542101336898882141)
              ·
                refine ⟨21733454078288001337080803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57955877542101336898882141 21733454078288001337080803)
                ·
                  refine ⟨32600181117432002005621205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21733454078288001337080803 32600181117432002005621205)
                  ·
                    refine ⟨764066744939812547006747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32600181117432002005621205 764066744939812547006747)
                    ·
                      rfl

theorem cell23_4464044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_4464044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464044 prefixEnd_4464044 := by exact prefixLift 4464044
  have htrace : WordTrace (prefixWord ++ tailWord_4464044) baseStart_4464044 baseEnd_4464044 := by
    simpa [prefixWord, tailWord_4464044, baseEnd_4464044] using wordTrace_append hprefix tailTrace_4464044
  have hstable : (prefixWord ++ tailWord_4464044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464044).length < 2 ^ (prefixWord ++ tailWord_4464044).sum := by decide
  have hdescent : baseEnd_4464044 < baseStart_4464044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464051 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 4, 5, 2]
def baseStart_4464051 : Nat := 118140960795 + 4464051 * 2 ^ 59
def prefixEnd_4464051 : Nat := 4983230072969 + 3 ^ 40 * 4464051 * 2
def baseEnd_4464051 : Nat := 2292203829184019113632709

theorem tailTrace_4464051 : CollatzResearch.WordTrace tailWord_4464051 prefixEnd_4464051 2292203829184019113632709 := by
  unfold tailWord_4464051
  simp only [CollatzResearch.WordTrace]
  refine ⟨162817315950513101058208007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108544877300342067372138671 162817315950513101058208007)
  ·
    refine ⟨244225973925769651587312011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162817315950513101058208007 244225973925769651587312011)
    ·
      refine ⟨366338960888654477380968017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244225973925769651587312011 366338960888654477380968017)
      ·
        refine ⟨274754220666490858035726013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 366338960888654477380968017 274754220666490858035726013)
        ·
          refine ⟨103032832749934071763397255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274754220666490858035726013 103032832749934071763397255)
          ·
            refine ⟨154549249124901107645095883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103032832749934071763397255 154549249124901107645095883)
            ·
              refine ⟨231823873687351661467643825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154549249124901107645095883 231823873687351661467643825)
              ·
                refine ⟨173867905265513746100732869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231823873687351661467643825 173867905265513746100732869)
                ·
                  refine ⟨32600232237283827393887413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 173867905265513746100732869 32600232237283827393887413)
                  ·
                    refine ⟨3056271772245358818176945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32600232237283827393887413 3056271772245358818176945)
                    ·
                      refine ⟨2292203829184019113632709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3056271772245358818176945 2292203829184019113632709)
                      ·
                        rfl

theorem cell23_4464051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 5, 2].length) (baseStart_4464051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464051 prefixEnd_4464051 := by exact prefixLift 4464051
  have htrace : WordTrace (prefixWord ++ tailWord_4464051) baseStart_4464051 baseEnd_4464051 := by
    simpa [prefixWord, tailWord_4464051, baseEnd_4464051] using wordTrace_append hprefix tailTrace_4464051
  have hstable : (prefixWord ++ tailWord_4464051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464051).length < 2 ^ (prefixWord ++ tailWord_4464051).sum := by decide
  have hdescent : baseEnd_4464051 < baseStart_4464051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464061 : List Nat := [1, 4, 1, 2, 2, 1, 1, 4, 2, 5]
def baseStart_4464061 : Nat := 118140960795 + 4464061 * 2 ^ 59
def prefixEnd_4464061 : Nat := 4983230072969 + 3 ^ 40 * 4464061 * 2
def baseEnd_4464061 : Nat := 764069654663521358169221

theorem tailTrace_4464061 : CollatzResearch.WordTrace tailWord_4464061 prefixEnd_4464061 764069654663521358169221 := by
  unfold tailWord_4464061
  simp only [CollatzResearch.WordTrace]
  refine ⟨162817680680476872766072037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108545120453651248510714691 162817680680476872766072037)
  ·
    refine ⟨30528315127589413643638507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162817680680476872766072037 30528315127589413643638507)
    ·
      refine ⟨45792472691384120465457761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30528315127589413643638507 45792472691384120465457761)
      ·
        refine ⟨34344354518538090349093321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45792472691384120465457761 34344354518538090349093321)
        ·
          refine ⟨25758265888903567761819991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34344354518538090349093321 25758265888903567761819991)
          ·
            refine ⟨38637398833355351642729987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25758265888903567761819991 38637398833355351642729987)
            ·
              refine ⟨57956098250033027464094981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38637398833355351642729987 57956098250033027464094981)
              ·
                refine ⟨10866768421881192649517809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57956098250033027464094981 10866768421881192649517809)
                ·
                  refine ⟨8150076316410894487138357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10866768421881192649517809 8150076316410894487138357)
                  ·
                    refine ⟨764069654663521358169221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8150076316410894487138357 764069654663521358169221)
                    ·
                      rfl

theorem cell23_4464061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_4464061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464061 prefixEnd_4464061 := by exact prefixLift 4464061
  have htrace : WordTrace (prefixWord ++ tailWord_4464061) baseStart_4464061 baseEnd_4464061 := by
    simpa [prefixWord, tailWord_4464061, baseEnd_4464061] using wordTrace_append hprefix tailTrace_4464061
  have hstable : (prefixWord ++ tailWord_4464061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464061).length < 2 ^ (prefixWord ++ tailWord_4464061).sum := by decide
  have hdescent : baseEnd_4464061 < baseStart_4464061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464125 : List Nat := [1, 4, 1, 1, 1, 4, 2, 4, 1, 4]
def baseStart_4464125 : Nat := 118140960795 + 4464125 * 2 ^ 59
def prefixEnd_4464125 : Nat := 4983230072969 + 3 ^ 40 * 4464125 * 2
def baseEnd_4464125 : Nat := 764080608917483941369123

theorem tailTrace_4464125 : CollatzResearch.WordTrace tailWord_4464125 prefixEnd_4464125 764080608917483941369123 := by
  unfold tailWord_4464125
  simp only [CollatzResearch.WordTrace]
  refine ⟨162820014952245011696401829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108546676634830007797601219 162820014952245011696401829)
  ·
    refine ⟨30528752803545939693075343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162820014952245011696401829 30528752803545939693075343)
    ·
      refine ⟨45793129205318909539613015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30528752803545939693075343 45793129205318909539613015)
      ·
        refine ⟨68689693807978364309419523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45793129205318909539613015 68689693807978364309419523)
        ·
          refine ⟨103034540711967546464129285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68689693807978364309419523 103034540711967546464129285)
          ·
            refine ⟨19318976383493914962024241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103034540711967546464129285 19318976383493914962024241)
            ·
              refine ⟨14489232287620436221518181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19318976383493914962024241 14489232287620436221518181)
              ·
                refine ⟨2716731053928831791534659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14489232287620436221518181 2716731053928831791534659)
                ·
                  refine ⟨4075096580893247687301989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2716731053928831791534659 4075096580893247687301989)
                  ·
                    refine ⟨764080608917483941369123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4075096580893247687301989 764080608917483941369123)
                    ·
                      rfl

theorem cell23_4464125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_4464125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464125 prefixEnd_4464125 := by exact prefixLift 4464125
  have htrace : WordTrace (prefixWord ++ tailWord_4464125) baseStart_4464125 baseEnd_4464125 := by
    simpa [prefixWord, tailWord_4464125, baseEnd_4464125] using wordTrace_append hprefix tailTrace_4464125
  have hstable : (prefixWord ++ tailWord_4464125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464125).length < 2 ^ (prefixWord ++ tailWord_4464125).sum := by decide
  have hdescent : baseEnd_4464125 < baseStart_4464125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464171 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 4]
def baseStart_4464171 : Nat := 118140960795 + 4464171 * 2 ^ 59
def prefixEnd_4464171 : Nat := 4983230072969 + 3 ^ 40 * 4464171 * 2
def baseEnd_4464171 : Nat := 2292265446862558644132157

theorem tailTrace_4464171 : CollatzResearch.WordTrace tailWord_4464171 prefixEnd_4464171 2292265446862558644132157 := by
  unfold tailWord_4464171
  simp only [CollatzResearch.WordTrace]
  refine ⟨162821692710078361552576367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108547795140052241035050911 162821692710078361552576367)
  ·
    refine ⟨244232539065117542328864551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162821692710078361552576367 244232539065117542328864551)
    ·
      refine ⟨366348808597676313493296827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244232539065117542328864551 366348808597676313493296827)
      ·
        refine ⟨549523212896514470239945241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366348808597676313493296827 549523212896514470239945241)
        ·
          refine ⟨412142409672385852679958931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 549523212896514470239945241 412142409672385852679958931)
          ·
            refine ⟨618213614508578779019938397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412142409672385852679958931 618213614508578779019938397)
            ·
              refine ⟨231830105440717042132476899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 618213614508578779019938397 231830105440717042132476899)
              ·
                refine ⟨347745158161075563198715349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231830105440717042132476899 347745158161075563198715349)
                ·
                  refine ⟨8150277144400208512469891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 347745158161075563198715349 8150277144400208512469891)
                  ·
                    refine ⟨12225415716600312768704837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8150277144400208512469891 12225415716600312768704837)
                    ·
                      refine ⟨2292265446862558644132157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12225415716600312768704837 2292265446862558644132157)
                      ·
                        rfl

theorem cell23_4464171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 4].length) (baseStart_4464171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464171 prefixEnd_4464171 := by exact prefixLift 4464171
  have htrace : WordTrace (prefixWord ++ tailWord_4464171) baseStart_4464171 baseEnd_4464171 := by
    simpa [prefixWord, tailWord_4464171, baseEnd_4464171] using wordTrace_append hprefix tailTrace_4464171
  have hstable : (prefixWord ++ tailWord_4464171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464171).length < 2 ^ (prefixWord ++ tailWord_4464171).sum := by decide
  have hdescent : baseEnd_4464171 < baseStart_4464171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464201 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 5, 2, 4]
def baseStart_4464201 : Nat := 118140960795 + 4464201 * 2 ^ 59
def prefixEnd_4464201 : Nat := 4983230072969 + 3 ^ 40 * 4464201 * 2
def baseEnd_4464201 : Nat := 2292280851282193526757019

theorem tailTrace_4464201 : CollatzResearch.WordTrace tailWord_4464201 prefixEnd_4464201 2292280851282193526757019 := by
  unfold tailWord_4464201
  simp only [CollatzResearch.WordTrace]
  refine ⟨162822786899969676676168457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108548524599979784450778971 162822786899969676676168457)
  ·
    refine ⟨122117090174977257507126343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162822786899969676676168457 122117090174977257507126343)
    ·
      refine ⟨183175635262465886260689515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122117090174977257507126343 183175635262465886260689515)
      ·
        refine ⟨274763452893698829391034273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183175635262465886260689515 274763452893698829391034273)
        ·
          refine ⟨206072589670274122043275705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274763452893698829391034273 206072589670274122043275705)
          ·
            refine ⟨154554442252705591532456779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206072589670274122043275705 154554442252705591532456779)
            ·
              refine ⟨231831663379058387298685169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154554442252705591532456779 231831663379058387298685169)
              ·
                refine ⟨173873747534293790474013877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231831663379058387298685169 173873747534293790474013877)
                ·
                  refine ⟨16300663831340042856938801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 173873747534293790474013877 16300663831340042856938801)
                  ·
                    refine ⟨12225497873505032142704101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16300663831340042856938801 12225497873505032142704101)
                    ·
                      refine ⟨2292280851282193526757019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12225497873505032142704101 2292280851282193526757019)
                      ·
                        rfl

theorem cell23_4464201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 2, 4].length) (baseStart_4464201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464201 prefixEnd_4464201 := by exact prefixLift 4464201
  have htrace : WordTrace (prefixWord ++ tailWord_4464201) baseStart_4464201 baseEnd_4464201 := by
    simpa [prefixWord, tailWord_4464201, baseEnd_4464201] using wordTrace_append hprefix tailTrace_4464201
  have hstable : (prefixWord ++ tailWord_4464201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464201).length < 2 ^ (prefixWord ++ tailWord_4464201).sum := by decide
  have hdescent : baseEnd_4464201 < baseStart_4464201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464208 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 3]
def baseStart_4464208 : Nat := 118140960795 + 4464208 * 2 ^ 59
def prefixEnd_4464208 : Nat := 4983230072969 + 3 ^ 40 * 4464208 * 2
def baseEnd_4464208 : Nat := 2292284445646774999369487

theorem tailTrace_4464208 : CollatzResearch.WordTrace tailWord_4464208 prefixEnd_4464208 2292284445646774999369487 := by
  unfold tailWord_4464208
  simp only [CollatzResearch.WordTrace]
  refine ⟨81411521105472158435836639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108548694807296211247782185 81411521105472158435836639)
  ·
    refine ⟨122117281658208237653754959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81411521105472158435836639 122117281658208237653754959)
    ·
      refine ⟨183175922487312356480632439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122117281658208237653754959 183175922487312356480632439)
      ·
        refine ⟨274763883730968534720948659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183175922487312356480632439 274763883730968534720948659)
        ·
          refine ⟨412145825596452802081422989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274763883730968534720948659 412145825596452802081422989)
          ·
            refine ⟨154554684598669800780533621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 412145825596452802081422989 154554684598669800780533621)
            ·
              refine ⟨14489501681125293823175027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 154554684598669800780533621 14489501681125293823175027)
              ·
                refine ⟨21734252521687940734762541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14489501681125293823175027 21734252521687940734762541)
                ·
                  refine ⟨8150344695632977775535953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21734252521687940734762541 8150344695632977775535953)
                  ·
                    refine ⟨6112758521724733331651965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8150344695632977775535953 6112758521724733331651965)
                    ·
                      refine ⟨2292284445646774999369487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6112758521724733331651965 2292284445646774999369487)
                      ·
                        rfl

theorem cell23_4464208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 3].length) (baseStart_4464208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464208 prefixEnd_4464208 := by exact prefixLift 4464208
  have htrace : WordTrace (prefixWord ++ tailWord_4464208) baseStart_4464208 baseEnd_4464208 := by
    simpa [prefixWord, tailWord_4464208, baseEnd_4464208] using wordTrace_append hprefix tailTrace_4464208
  have hstable : (prefixWord ++ tailWord_4464208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464208).length < 2 ^ (prefixWord ++ tailWord_4464208).sum := by decide
  have hdescent : baseEnd_4464208 < baseStart_4464208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464232 : List Nat := [2, 1, 4, 3, 1, 2, 2, 2, 2, 4]
def baseStart_4464232 : Nat := 118140960795 + 4464232 * 2 ^ 59
def prefixEnd_4464232 : Nat := 4983230072969 + 3 ^ 40 * 4464232 * 2
def baseEnd_4464232 : Nat := 764098923060827635156459

theorem tailTrace_4464232 : CollatzResearch.WordTrace tailWord_4464232 prefixEnd_4464232 764098923060827635156459 := by
  unfold tailWord_4464232
  simp only [CollatzResearch.WordTrace]
  refine ⟨81411958781428684485273475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108549278375238245980364633 81411958781428684485273475)
  ·
    refine ⟨122117938172143026727910213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81411958781428684485273475 122117938172143026727910213)
    ·
      refine ⟨22897113407276817511483165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122117938172143026727910213 22897113407276817511483165)
      ·
        refine ⟨8586417527728806566806187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22897113407276817511483165 8586417527728806566806187)
        ·
          refine ⟨12879626291593209850209281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8586417527728806566806187 12879626291593209850209281)
          ·
            refine ⟨9659719718694907387656961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12879626291593209850209281 9659719718694907387656961)
            ·
              refine ⟨7244789789021180540742721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9659719718694907387656961 7244789789021180540742721)
              ·
                refine ⟨5433592341765885405557041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7244789789021180540742721 5433592341765885405557041)
                ·
                  refine ⟨4075194256324414054167781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5433592341765885405557041 4075194256324414054167781)
                  ·
                    refine ⟨764098923060827635156459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4075194256324414054167781 764098923060827635156459)
                    ·
                      rfl

theorem cell23_4464232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_4464232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464232 prefixEnd_4464232 := by exact prefixLift 4464232
  have htrace : WordTrace (prefixWord ++ tailWord_4464232) baseStart_4464232 baseEnd_4464232 := by
    simpa [prefixWord, tailWord_4464232, baseEnd_4464232] using wordTrace_append hprefix tailTrace_4464232
  have hstable : (prefixWord ++ tailWord_4464232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464232).length < 2 ^ (prefixWord ++ tailWord_4464232).sum := by decide
  have hdescent : baseEnd_4464232 < baseStart_4464232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464245 : List Nat := [1, 3, 4, 2, 1, 3, 1, 8]
def baseStart_4464245 : Nat := 118140960795 + 4464245 * 2 ^ 59
def prefixEnd_4464245 : Nat := 4983230072969 + 3 ^ 40 * 4464245 * 2
def baseEnd_4464245 : Nat := 84900127571518198318771

theorem tailTrace_4464245 : CollatzResearch.WordTrace tailWord_4464245 prefixEnd_4464245 84900127571518198318771 := by
  unfold tailWord_4464245
  simp only [CollatzResearch.WordTrace]
  refine ⟨162824391711810272190770189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108549594474540181460513459 162824391711810272190770189)
  ·
    refine ⟨61059146891928852071538821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162824391711810272190770189 61059146891928852071538821)
    ·
      refine ⟨11448590042236659763413529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61059146891928852071538821 11448590042236659763413529)
      ·
        refine ⟨8586442531677494822560147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11448590042236659763413529 8586442531677494822560147)
        ·
          refine ⟨12879663797516242233840221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8586442531677494822560147 12879663797516242233840221)
          ·
            refine ⟨4829873924068590837690083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12879663797516242233840221 4829873924068590837690083)
            ·
              refine ⟨7244810886102886256535125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4829873924068590837690083 7244810886102886256535125)
              ·
                refine ⟨84900127571518198318771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7244810886102886256535125 84900127571518198318771)
                ·
                  rfl

theorem cell23_4464245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 8].length) (baseStart_4464245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464245 prefixEnd_4464245 := by exact prefixLift 4464245
  have htrace : WordTrace (prefixWord ++ tailWord_4464245) baseStart_4464245 baseEnd_4464245 := by
    simpa [prefixWord, tailWord_4464245, baseEnd_4464245] using wordTrace_append hprefix tailTrace_4464245
  have hstable : (prefixWord ++ tailWord_4464245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464245).length < 2 ^ (prefixWord ++ tailWord_4464245).sum := by decide
  have hdescent : baseEnd_4464245 < baseStart_4464245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464248 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 1, 9, 2]
def baseStart_4464248 : Nat := 118140960795 + 4464248 * 2 ^ 59
def prefixEnd_4464248 : Nat := 4983230072969 + 3 ^ 40 * 4464248 * 2
def baseEnd_4464248 : Nat := 2292304984872954842869303

theorem tailTrace_4464248 : CollatzResearch.WordTrace tailWord_4464248 prefixEnd_4464248 2292304984872954842869303 := by
  unfold tailWord_4464248
  simp only [CollatzResearch.WordTrace]
  refine ⟨81412250565399701851564699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108549667420532935802086265 81412250565399701851564699)
  ·
    refine ⟨122118375848099552777347049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81412250565399701851564699 122118375848099552777347049)
    ·
      refine ⟨91588781886074664583010287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122118375848099552777347049 91588781886074664583010287)
      ·
        refine ⟨137383172829111996874515431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91588781886074664583010287 137383172829111996874515431)
        ·
          refine ⟨206074759243667995311773147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137383172829111996874515431 206074759243667995311773147)
          ·
            refine ⟨309112138865501992967659721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206074759243667995311773147 309112138865501992967659721)
            ·
              refine ⟨231834104149126494725744791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309112138865501992967659721 231834104149126494725744791)
              ·
                refine ⟨347751156223689742088617187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231834104149126494725744791 347751156223689742088617187)
                ·
                  refine ⟨521626734335534613132925781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 347751156223689742088617187 521626734335534613132925781)
                  ·
                    refine ⟨3056406646497273123825737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 521626734335534613132925781 3056406646497273123825737)
                    ·
                      refine ⟨2292304984872954842869303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3056406646497273123825737 2292304984872954842869303)
                      ·
                        rfl

theorem cell23_4464248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 9, 2].length) (baseStart_4464248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464248 prefixEnd_4464248 := by exact prefixLift 4464248
  have htrace : WordTrace (prefixWord ++ tailWord_4464248) baseStart_4464248 baseEnd_4464248 := by
    simpa [prefixWord, tailWord_4464248, baseEnd_4464248] using wordTrace_append hprefix tailTrace_4464248
  have hstable : (prefixWord ++ tailWord_4464248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464248).length < 2 ^ (prefixWord ++ tailWord_4464248).sum := by decide
  have hdescent : baseEnd_4464248 < baseStart_4464248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464265 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 3, 3, 2]
def baseStart_4464265 : Nat := 118140960795 + 4464265 * 2 ^ 59
def prefixEnd_4464265 : Nat := 4983230072969 + 3 ^ 40 * 4464265 * 2
def baseEnd_4464265 : Nat := 2292313714044081276356725

theorem tailTrace_4464265 : CollatzResearch.WordTrace tailWord_4464265 prefixEnd_4464265 2292313714044081276356725 := by
  unfold tailWord_4464265
  simp only [CollatzResearch.WordTrace]
  refine ⟨162825121171737815606498249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108550080781158543737665499 162825121171737815606498249)
  ·
    refine ⟨122118840878803361704873687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162825121171737815606498249 122118840878803361704873687)
    ·
      refine ⟨183178261318205042557310531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122118840878803361704873687 183178261318205042557310531)
      ·
        refine ⟨274767391977307563835965797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183178261318205042557310531 274767391977307563835965797)
        ·
          refine ⟨51518885995745168219243587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 274767391977307563835965797 51518885995745168219243587)
          ·
            refine ⟨77278328993617752328865381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51518885995745168219243587 77278328993617752328865381)
            ·
              refine ⟨14489686686303328561662259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77278328993617752328865381 14489686686303328561662259)
              ·
                refine ⟨21734530029454992842493389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14489686686303328561662259 21734530029454992842493389)
                ·
                  refine ⟨8150448761045622315935021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21734530029454992842493389 8150448761045622315935021)
                  ·
                    refine ⟨3056418285392108368475633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8150448761045622315935021 3056418285392108368475633)
                    ·
                      refine ⟨2292313714044081276356725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3056418285392108368475633 2292313714044081276356725)
                      ·
                        rfl

theorem cell23_4464265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 3, 2].length) (baseStart_4464265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464265 prefixEnd_4464265 := by exact prefixLift 4464265
  have htrace : WordTrace (prefixWord ++ tailWord_4464265) baseStart_4464265 baseEnd_4464265 := by
    simpa [prefixWord, tailWord_4464265, baseEnd_4464265] using wordTrace_append hprefix tailTrace_4464265
  have hstable : (prefixWord ++ tailWord_4464265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464265).length < 2 ^ (prefixWord ++ tailWord_4464265).sum := by decide
  have hdescent : baseEnd_4464265 < baseStart_4464265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464271 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 6, 6]
def baseStart_4464271 : Nat := 118140960795 + 4464271 * 2 ^ 59
def prefixEnd_4464271 : Nat := 4983230072969 + 3 ^ 40 * 4464271 * 2
def baseEnd_4464271 : Nat := 764105598309336084293899

theorem tailTrace_4464271 : CollatzResearch.WordTrace tailWord_4464271 prefixEnd_4464271 764105598309336084293899 := by
  unfold tailWord_4464271
  simp only [CollatzResearch.WordTrace]
  refine ⟨162825340009716078631216667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108550226673144052420811111 162825340009716078631216667)
  ·
    refine ⟨244238010014574117946825001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162825340009716078631216667 244238010014574117946825001)
    ·
      refine ⟨183178507510930588460118751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244238010014574117946825001 183178507510930588460118751)
      ·
        refine ⟨274767761266395882690178127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183178507510930588460118751 274767761266395882690178127)
        ·
          refine ⟨412151641899593824035267191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274767761266395882690178127 412151641899593824035267191)
          ·
            refine ⟨618227462849390736052900787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412151641899593824035267191 618227462849390736052900787)
            ·
              refine ⟨927341194274086104079351181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 618227462849390736052900787 927341194274086104079351181)
              ·
                refine ⟨347752947852782289029756693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 927341194274086104079351181 347752947852782289029756693)
                ·
                  refine ⟨16300919430599169798269845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 347752947852782289029756693 16300919430599169798269845)
                  ·
                    refine ⟨764105598309336084293899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16300919430599169798269845 764105598309336084293899)
                    ·
                      rfl

theorem cell23_4464271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 6].length) (baseStart_4464271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464271 prefixEnd_4464271 := by exact prefixLift 4464271
  have htrace : WordTrace (prefixWord ++ tailWord_4464271) baseStart_4464271 baseEnd_4464271 := by
    simpa [prefixWord, tailWord_4464271, baseEnd_4464271] using wordTrace_append hprefix tailTrace_4464271
  have hstable : (prefixWord ++ tailWord_4464271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464271).length < 2 ^ (prefixWord ++ tailWord_4464271).sum := by decide
  have hdescent : baseEnd_4464271 < baseStart_4464271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464276 : List Nat := [2, 4, 2, 2, 2, 2, 2, 1, 1, 2, 3]
def baseStart_4464276 : Nat := 118140960795 + 4464276 * 2 ^ 59
def prefixEnd_4464276 : Nat := 4983230072969 + 3 ^ 40 * 4464276 * 2
def baseEnd_4464276 : Nat := 2292319362331280733319175

theorem tailTrace_4464276 : CollatzResearch.WordTrace tailWord_4464276 prefixEnd_4464276 2292319362331280733319175 := by
  unfold tailWord_4464276
  simp only [CollatzResearch.WordTrace]
  refine ⟨81412761187348982242574341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108550348249798642990099121 81412761187348982242574341)
  ·
    refine ⟨15264892722627934170482689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81412761187348982242574341 15264892722627934170482689)
    ·
      refine ⟨11448669541970950627862017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15264892722627934170482689 11448669541970950627862017)
      ·
        refine ⟨8586502156478212970896513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11448669541970950627862017 8586502156478212970896513)
        ·
          refine ⟨6439876617358659728172385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8586502156478212970896513 6439876617358659728172385)
          ·
            refine ⟨4829907463018994796129289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6439876617358659728172385 4829907463018994796129289)
            ·
              refine ⟨3622430597264246097096967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4829907463018994796129289 3622430597264246097096967)
              ·
                refine ⟨5433645895896369145645451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3622430597264246097096967 5433645895896369145645451)
                ·
                  refine ⟨8150468843844553718468177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5433645895896369145645451 8150468843844553718468177)
                  ·
                    refine ⟨6112851632883415288851133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8150468843844553718468177 6112851632883415288851133)
                    ·
                      refine ⟨2292319362331280733319175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6112851632883415288851133 2292319362331280733319175)
                      ·
                        rfl

theorem cell23_4464276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_4464276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464276 prefixEnd_4464276 := by exact prefixLift 4464276
  have htrace : WordTrace (prefixWord ++ tailWord_4464276) baseStart_4464276 baseEnd_4464276 := by
    simpa [prefixWord, tailWord_4464276, baseEnd_4464276] using wordTrace_append hprefix tailTrace_4464276
  have hstable : (prefixWord ++ tailWord_4464276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464276).length < 2 ^ (prefixWord ++ tailWord_4464276).sum := by decide
  have hdescent : baseEnd_4464276 < baseStart_4464276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464288 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 2, 6]
def baseStart_4464288 : Nat := 118140960795 + 4464288 * 2 ^ 59
def prefixEnd_4464288 : Nat := 4983230072969 + 3 ^ 40 * 4464288 * 2
def baseEnd_4464288 : Nat := 764108508033044895456373

theorem tailTrace_4464288 : CollatzResearch.WordTrace tailWord_4464288 prefixEnd_4464288 764108508033044895456373 := by
  unfold tailWord_4464288
  simp only [CollatzResearch.WordTrace]
  refine ⟨81412980025327245267292759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108550640033769660356390345 81412980025327245267292759)
  ·
    refine ⟨122119470037990867900939139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81412980025327245267292759 122119470037990867900939139)
    ·
      refine ⟨183179205056986301851408709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122119470037990867900939139 183179205056986301851408709)
      ·
        refine ⟨34346100948184931597139133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183179205056986301851408709 34346100948184931597139133)
        ·
          refine ⟨12879787855569349348927175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34346100948184931597139133 12879787855569349348927175)
          ·
            refine ⟨19319681783354024023390763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12879787855569349348927175 19319681783354024023390763)
            ·
              refine ⟨28979522675031036035086145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19319681783354024023390763 28979522675031036035086145)
              ·
                refine ⟨21734642006273277026314609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28979522675031036035086145 21734642006273277026314609)
                ·
                  refine ⟨16300981504704957769735957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21734642006273277026314609 16300981504704957769735957)
                  ·
                    refine ⟨764108508033044895456373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16300981504704957769735957 764108508033044895456373)
                    ·
                      rfl

theorem cell23_4464288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 2, 6].length) (baseStart_4464288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464288 prefixEnd_4464288 := by exact prefixLift 4464288
  have htrace : WordTrace (prefixWord ++ tailWord_4464288) baseStart_4464288 baseEnd_4464288 := by
    simpa [prefixWord, tailWord_4464288, baseEnd_4464288] using wordTrace_append hprefix tailTrace_4464288
  have hstable : (prefixWord ++ tailWord_4464288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464288).length < 2 ^ (prefixWord ++ tailWord_4464288).sum := by decide
  have hdescent : baseEnd_4464288 < baseStart_4464288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
