import V185TrunkScan23Chunk0445

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2636918 : List Nat := [5, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4]
def baseStart_2636918 : Nat := 118140960795 + 2636918 * 2 ^ 59
def prefixEnd_2636918 : Nat := 4983230072969 + 3 ^ 40 * 2636918 * 2
def baseEnd_2636918 : Nat := 1354006380492619279898041

theorem tailTrace_2636918 : CollatzResearch.WordTrace tailWord_2636918 prefixEnd_2636918 1354006380492619279898041 := by
  unfold tailWord_2636918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6011018791306494411583463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64117533773935940390223605 6011018791306494411583463)
  ·
    refine ⟨9016528186959741617375195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6011018791306494411583463 9016528186959741617375195)
    ·
      refine ⟨13524792280439612426062793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9016528186959741617375195 13524792280439612426062793)
      ·
        refine ⟨10143594210329709319547095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13524792280439612426062793 10143594210329709319547095)
        ·
          refine ⟨15215391315494563979320643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10143594210329709319547095 15215391315494563979320643)
          ·
            refine ⟨22823086973241845968980965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15215391315494563979320643 22823086973241845968980965)
            ·
              refine ⟨4279328807482846119183931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22823086973241845968980965 4279328807482846119183931)
              ·
                refine ⟨6418993211224269178775897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4279328807482846119183931 6418993211224269178775897)
                ·
                  refine ⟨4814244908418201884081923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6418993211224269178775897 4814244908418201884081923)
                  ·
                    refine ⟨7221367362627302826122885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4814244908418201884081923 7221367362627302826122885)
                    ·
                      refine ⟨1354006380492619279898041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7221367362627302826122885 1354006380492619279898041)
                      ·
                        rfl

theorem cell23_2636918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_2636918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636918 prefixEnd_2636918 := by exact prefixLift 2636918
  have htrace : WordTrace (prefixWord ++ tailWord_2636918) baseStart_2636918 baseEnd_2636918 := by
    simpa [prefixWord, tailWord_2636918, baseEnd_2636918] using wordTrace_append hprefix tailTrace_2636918
  have hstable : (prefixWord ++ tailWord_2636918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636918).length < 2 ^ (prefixWord ++ tailWord_2636918).sum := by decide
  have hdescent : baseEnd_2636918 < baseStart_2636918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636958 : List Nat := [4, 3, 1, 1, 2, 1, 2, 3, 6]
def baseStart_2636958 : Nat := 118140960795 + 2636958 * 2 ^ 59
def prefixEnd_2636958 : Nat := 4983230072969 + 3 ^ 40 * 2636958 * 2
def baseEnd_2636958 : Nat := 150447435524311013710873

theorem tailTrace_2636958 : CollatzResearch.WordTrace tailWord_2636958 prefixEnd_2636958 150447435524311013710873 := by
  unfold tailWord_2636958
  simp only [CollatzResearch.WordTrace]
  refine ⟨12022219947594874677098941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64118506387172664944527685 12022219947594874677098941)
  ·
    refine ⟨4508332480348078003912103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12022219947594874677098941 4508332480348078003912103)
    ·
      refine ⟨6762498720522117005868155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4508332480348078003912103 6762498720522117005868155)
      ·
        refine ⟨10143748080783175508802233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6762498720522117005868155 10143748080783175508802233)
        ·
          refine ⟨7607811060587381631601675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10143748080783175508802233 7607811060587381631601675)
          ·
            refine ⟨11411716590881072447402513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7607811060587381631601675 11411716590881072447402513)
            ·
              refine ⟨8558787443160804335551885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11411716590881072447402513 8558787443160804335551885)
              ·
                refine ⟨3209545291185301625831957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8558787443160804335551885 3209545291185301625831957)
                ·
                  refine ⟨150447435524311013710873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3209545291185301625831957 150447435524311013710873)
                  ·
                    rfl

theorem cell23_2636958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_2636958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636958 prefixEnd_2636958 := by exact prefixLift 2636958
  have htrace : WordTrace (prefixWord ++ tailWord_2636958) baseStart_2636958 baseEnd_2636958 := by
    simpa [prefixWord, tailWord_2636958, baseEnd_2636958] using wordTrace_append hprefix tailTrace_2636958
  have hstable : (prefixWord ++ tailWord_2636958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636958).length < 2 ^ (prefixWord ++ tailWord_2636958).sum := by decide
  have hdescent : baseEnd_2636958 < baseStart_2636958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636978 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2]
def baseStart_2636978 : Nat := 118140960795 + 2636978 * 2 ^ 59
def prefixEnd_2636978 : Nat := 4983230072969 + 3 ^ 40 * 2636978 * 2
def baseEnd_2636978 : Nat := 1354037189331889045147765

theorem tailTrace_2636978 : CollatzResearch.WordTrace tailWord_2636978 prefixEnd_2636978 1354037189331889045147765 := by
  unfold tailWord_2636978
  simp only [CollatzResearch.WordTrace]
  refine ⟨24044622260171635208129897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64118992693791027221679725 24044622260171635208129897)
  ·
    refine ⟨18033466695128726406097423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24044622260171635208129897 18033466695128726406097423)
    ·
      refine ⟨27050200042693089609146135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18033466695128726406097423 27050200042693089609146135)
      ·
        refine ⟨40575300064039634413719203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27050200042693089609146135 40575300064039634413719203)
        ·
          refine ⟨60862950096059451620578805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40575300064039634413719203 60862950096059451620578805)
          ·
            refine ⟨5705901571505573589429263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60862950096059451620578805 5705901571505573589429263)
            ·
              refine ⟨8558852357258360384143895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5705901571505573589429263 8558852357258360384143895)
              ·
                refine ⟨12838278535887540576215843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8558852357258360384143895 12838278535887540576215843)
                ·
                  refine ⟨19257417803831310864323765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12838278535887540576215843 19257417803831310864323765)
                  ·
                    refine ⟨1805382919109185393530353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19257417803831310864323765 1805382919109185393530353)
                    ·
                      refine ⟨1354037189331889045147765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1805382919109185393530353 1354037189331889045147765)
                      ·
                        rfl

theorem cell23_2636978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_2636978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636978 prefixEnd_2636978 := by exact prefixLift 2636978
  have htrace : WordTrace (prefixWord ++ tailWord_2636978) baseStart_2636978 baseEnd_2636978 := by
    simpa [prefixWord, tailWord_2636978, baseEnd_2636978] using wordTrace_append hprefix tailTrace_2636978
  have hstable : (prefixWord ++ tailWord_2636978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636978).length < 2 ^ (prefixWord ++ tailWord_2636978).sum := by decide
  have hdescent : baseEnd_2636978 < baseStart_2636978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636984 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 3, 6]
def baseStart_2636984 : Nat := 118140960795 + 2636984 * 2 ^ 59
def prefixEnd_2636984 : Nat := 4983230072969 + 3 ^ 40 * 2636984 * 2
def baseEnd_2636984 : Nat := 451346756738605340557579

theorem tailTrace_2636984 : CollatzResearch.WordTrace tailWord_2636984 prefixEnd_2636984 451346756738605340557579 := by
  unfold tailWord_2636984
  simp only [CollatzResearch.WordTrace]
  refine ⟨48089353939332401928619003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64119138585776535904825337 48089353939332401928619003)
  ·
    refine ⟨72134030908998602892928505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48089353939332401928619003 72134030908998602892928505)
    ·
      refine ⟨54100523181748952169696379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72134030908998602892928505 54100523181748952169696379)
      ·
        refine ⟨81150784772623428254544569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54100523181748952169696379 81150784772623428254544569)
        ·
          refine ⟨60863088579467571190908427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81150784772623428254544569 60863088579467571190908427)
          ·
            refine ⟨91294632869201356786362641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60863088579467571190908427 91294632869201356786362641)
            ·
              refine ⟨68470974651901017589771981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91294632869201356786362641 68470974651901017589771981)
              ·
                refine ⟨25676615494462881596164493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68470974651901017589771981 25676615494462881596164493)
                ·
                  refine ⟨9628730810423580598561685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25676615494462881596164493 9628730810423580598561685)
                  ·
                    refine ⟨451346756738605340557579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9628730810423580598561685 451346756738605340557579)
                    ·
                      rfl

theorem cell23_2636984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_2636984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636984 prefixEnd_2636984 := by exact prefixLift 2636984
  have htrace : WordTrace (prefixWord ++ tailWord_2636984) baseStart_2636984 baseEnd_2636984 := by
    simpa [prefixWord, tailWord_2636984, baseEnd_2636984] using wordTrace_append hprefix tailTrace_2636984
  have hstable : (prefixWord ++ tailWord_2636984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636984).length < 2 ^ (prefixWord ++ tailWord_2636984).sum := by decide
  have hdescent : baseEnd_2636984 < baseStart_2636984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636985 : List Nat := [1, 2, 1, 4, 1, 3, 1, 5, 1, 1, 3]
def baseStart_2636985 : Nat := 118140960795 + 2636985 * 2 ^ 59
def prefixEnd_2636985 : Nat := 4983230072969 + 3 ^ 40 * 2636985 * 2
def baseEnd_2636985 : Nat := 1354040783696470517760233

theorem tailTrace_2636985 : CollatzResearch.WordTrace tailWord_2636985 prefixEnd_2636985 1354040783696470517760233 := by
  unfold tailWord_2636985
  simp only [CollatzResearch.WordTrace]
  refine ⟨96178744351661181028024409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64119162901107454018682939 96178744351661181028024409)
  ·
    refine ⟨72134058263745885771018307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96178744351661181028024409 72134058263745885771018307)
    ·
      refine ⟨108201087395618828656527461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72134058263745885771018307 108201087395618828656527461)
      ·
        refine ⟨20287703886678530373098899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108201087395618828656527461 20287703886678530373098899)
        ·
          refine ⟨30431555830017795559648349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20287703886678530373098899 30431555830017795559648349)
          ·
            refine ⟨11411833436256673334868131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30431555830017795559648349 11411833436256673334868131)
            ·
              refine ⟨17117750154385010002302197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11411833436256673334868131 17117750154385010002302197)
              ·
                refine ⟨1604789076973594687715831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17117750154385010002302197 1604789076973594687715831)
                ·
                  refine ⟨2407183615460392031573747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1604789076973594687715831 2407183615460392031573747)
                  ·
                    refine ⟨3610775423190588047360621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2407183615460392031573747 3610775423190588047360621)
                    ·
                      refine ⟨1354040783696470517760233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3610775423190588047360621 1354040783696470517760233)
                      ·
                        rfl

theorem cell23_2636985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_2636985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636985 prefixEnd_2636985 := by exact prefixLift 2636985
  have htrace : WordTrace (prefixWord ++ tailWord_2636985) baseStart_2636985 baseEnd_2636985 := by
    simpa [prefixWord, tailWord_2636985, baseEnd_2636985] using wordTrace_append hprefix tailTrace_2636985
  have hstable : (prefixWord ++ tailWord_2636985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636985).length < 2 ^ (prefixWord ++ tailWord_2636985).sum := by decide
  have hdescent : baseEnd_2636985 < baseStart_2636985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2636988 : List Nat := [2, 2, 2, 3, 2, 2, 1, 3, 1, 5]
def baseStart_2636988 : Nat := 118140960795 + 2636988 * 2 ^ 59
def prefixEnd_2636988 : Nat := 4983230072969 + 3 ^ 40 * 2636988 * 2
def baseEnd_2636988 : Nat := 451347441379478002007573

theorem tailTrace_2636988 : CollatzResearch.WordTrace tailWord_2636988 prefixEnd_2636988 451347441379478002007573 := by
  unfold tailWord_2636988
  simp only [CollatzResearch.WordTrace]
  refine ⟨48089426885325156270191809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64119235847100208360255745 48089426885325156270191809)
  ·
    refine ⟨36067070163993867202643857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48089426885325156270191809 36067070163993867202643857)
    ·
      refine ⟨27050302622995400401982893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36067070163993867202643857 27050302622995400401982893)
      ·
        refine ⟨10143863483623275150743585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27050302622995400401982893 10143863483623275150743585)
        ·
          refine ⟨7607897612717456363057689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10143863483623275150743585 7607897612717456363057689)
          ·
            refine ⟨5705923209538092272293267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7607897612717456363057689 5705923209538092272293267)
            ·
              refine ⟨8558884814307138408439901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5705923209538092272293267 8558884814307138408439901)
              ·
                refine ⟨3209581805365176903164963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8558884814307138408439901 3209581805365176903164963)
                ·
                  refine ⟨4814372708047765354747445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3209581805365176903164963 4814372708047765354747445)
                  ·
                    refine ⟨451347441379478002007573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4814372708047765354747445 451347441379478002007573)
                    ·
                      rfl

theorem cell23_2636988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_2636988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2636988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2636988 prefixEnd_2636988 := by exact prefixLift 2636988
  have htrace : WordTrace (prefixWord ++ tailWord_2636988) baseStart_2636988 baseEnd_2636988 := by
    simpa [prefixWord, tailWord_2636988, baseEnd_2636988] using wordTrace_append hprefix tailTrace_2636988
  have hstable : (prefixWord ++ tailWord_2636988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2636988).length < 2 ^ (prefixWord ++ tailWord_2636988).sum := by decide
  have hdescent : baseEnd_2636988 < baseStart_2636988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2636988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637025 : List Nat := [1, 2, 3, 1, 3, 2, 2, 2, 3, 2, 2]
def baseStart_2637025 : Nat := 118140960795 + 2637025 * 2 ^ 59
def prefixEnd_2637025 : Nat := 4983230072969 + 3 ^ 40 * 2637025 * 2
def baseEnd_2637025 : Nat := 1354061322922650361260049

theorem tailTrace_2637025 : CollatzResearch.WordTrace tailWord_2637025 prefixEnd_2637025 1354061322922650361260049 := by
  unfold tailWord_2637025
  simp only [CollatzResearch.WordTrace]
  refine ⟨96180203271516267859480529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64120135514344178572987019 96180203271516267859480529)
  ·
    refine ⟨72135152453637200894610397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96180203271516267859480529 72135152453637200894610397)
    ·
      refine ⟨27050682170113950335478899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72135152453637200894610397 27050682170113950335478899)
      ·
        refine ⟨40576023255170925503218349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27050682170113950335478899 40576023255170925503218349)
        ·
          refine ⟨15216008720689097063706881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40576023255170925503218349 15216008720689097063706881)
          ·
            refine ⟨11412006540516822797780161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15216008720689097063706881 11412006540516822797780161)
            ·
              refine ⟨8559004905387617098335121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11412006540516822797780161 8559004905387617098335121)
              ·
                refine ⟨6419253679040712823751341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8559004905387617098335121 6419253679040712823751341)
                ·
                  refine ⟨2407220129640267308906753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6419253679040712823751341 2407220129640267308906753)
                  ·
                    refine ⟨1805415097230200481680065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2407220129640267308906753 1805415097230200481680065)
                    ·
                      refine ⟨1354061322922650361260049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1805415097230200481680065 1354061322922650361260049)
                      ·
                        rfl

theorem cell23_2637025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_2637025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637025 prefixEnd_2637025 := by exact prefixLift 2637025
  have htrace : WordTrace (prefixWord ++ tailWord_2637025) baseStart_2637025 baseEnd_2637025 := by
    simpa [prefixWord, tailWord_2637025, baseEnd_2637025] using wordTrace_append hprefix tailTrace_2637025
  have hstable : (prefixWord ++ tailWord_2637025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637025).length < 2 ^ (prefixWord ++ tailWord_2637025).sum := by decide
  have hdescent : baseEnd_2637025 < baseStart_2637025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637028 : List Nat := [2, 3, 1, 1, 1, 2, 3, 4, 1, 2, 3]
def baseStart_2637028 : Nat := 118140960795 + 2637028 * 2 ^ 59
def prefixEnd_2637028 : Nat := 4983230072969 + 3 ^ 40 * 2637028 * 2
def baseEnd_2637028 : Nat := 1354062863364613849522535

theorem tailTrace_2637028 : CollatzResearch.WordTrace tailWord_2637028 prefixEnd_2637028 1354062863364613849522535 := by
  unfold tailWord_2637028
  simp only [CollatzResearch.WordTrace]
  refine ⟨48090156345252699685919869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64120208460336932914559825 48090156345252699685919869)
  ·
    refine ⟨18033808629469762382219951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48090156345252699685919869 18033808629469762382219951)
    ·
      refine ⟨27050712944204643573329927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18033808629469762382219951 27050712944204643573329927)
      ·
        refine ⟨40576069416306965359994891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27050712944204643573329927 40576069416306965359994891)
        ·
          refine ⟨60864104124460448039992337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40576069416306965359994891 60864104124460448039992337)
          ·
            refine ⟨45648078093345336029994253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60864104124460448039992337 45648078093345336029994253)
            ·
              refine ⟨17118029285004501011247845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45648078093345336029994253 17118029285004501011247845)
              ·
                refine ⟨3209630490938343939608971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17118029285004501011247845 3209630490938343939608971)
                ·
                  refine ⟨4814445736407515909413457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3209630490938343939608971 4814445736407515909413457)
                  ·
                    refine ⟨3610834302305636932060093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4814445736407515909413457 3610834302305636932060093)
                    ·
                      refine ⟨1354062863364613849522535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3610834302305636932060093 1354062863364613849522535)
                      ·
                        rfl

theorem cell23_2637028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_2637028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637028 prefixEnd_2637028 := by exact prefixLift 2637028
  have htrace : WordTrace (prefixWord ++ tailWord_2637028) baseStart_2637028 baseEnd_2637028 := by
    simpa [prefixWord, tailWord_2637028, baseEnd_2637028] using wordTrace_append hprefix tailTrace_2637028
  have hstable : (prefixWord ++ tailWord_2637028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637028).length < 2 ^ (prefixWord ++ tailWord_2637028).sum := by decide
  have hdescent : baseEnd_2637028 < baseStart_2637028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637041 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 3, 3, 3]
def baseStart_2637041 : Nat := 118140960795 + 2637041 * 2 ^ 59
def prefixEnd_2637041 : Nat := 4983230072969 + 3 ^ 40 * 2637041 * 2
def baseEnd_2637041 : Nat := 1354069538613122298659975

theorem tailTrace_2637041 : CollatzResearch.WordTrace tailWord_2637041 prefixEnd_2637041 1354069538613122298659975 := by
  unfold tailWord_2637041
  simp only [CollatzResearch.WordTrace]
  refine ⟨96180786839458302592062977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64120524559638868394708651 96180786839458302592062977)
  ·
    refine ⟨72135590129593726944047233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96180786839458302592062977 72135590129593726944047233)
    ·
      refine ⟨54101692597195295208035425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72135590129593726944047233 54101692597195295208035425)
      ·
        refine ⟨40576269447896471406026569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54101692597195295208035425 40576269447896471406026569)
        ·
          refine ⟨30432202085922353554519927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40576269447896471406026569 30432202085922353554519927)
          ·
            refine ⟨45648303128883530331779891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30432202085922353554519927 45648303128883530331779891)
            ·
              refine ⟨68472454693325295497669837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45648303128883530331779891 68472454693325295497669837)
              ·
                refine ⟨25677170509996985811626189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68472454693325295497669837 25677170509996985811626189)
                ·
                  refine ⟨9628938941248869679359821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25677170509996985811626189 9628938941248869679359821)
                  ·
                    refine ⟨3610852102968326129759933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9628938941248869679359821 3610852102968326129759933)
                    ·
                      refine ⟨1354069538613122298659975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3610852102968326129759933 1354069538613122298659975)
                      ·
                        rfl

theorem cell23_2637041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_2637041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637041 prefixEnd_2637041 := by exact prefixLift 2637041
  have htrace : WordTrace (prefixWord ++ tailWord_2637041) baseStart_2637041 baseEnd_2637041 := by
    simpa [prefixWord, tailWord_2637041, baseEnd_2637041] using wordTrace_append hprefix tailTrace_2637041
  have hstable : (prefixWord ++ tailWord_2637041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637041).length < 2 ^ (prefixWord ++ tailWord_2637041).sum := by decide
  have hdescent : baseEnd_2637041 < baseStart_2637041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637059 : List Nat := [1, 1, 1, 3, 2, 5, 3, 2, 1, 2, 2]
def baseStart_2637059 : Nat := 118140960795 + 2637059 * 2 ^ 59
def prefixEnd_2637059 : Nat := 4983230072969 + 3 ^ 40 * 2637059 * 2
def baseEnd_2637059 : Nat := 1354078781264903228234893

theorem tailTrace_2637059 : CollatzResearch.WordTrace tailWord_2637059 prefixEnd_2637059 1354078781264903228234893 := by
  unfold tailWord_2637059
  simp only [CollatzResearch.WordTrace]
  refine ⟨96181443353393091666218231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64120962235595394444145487 96181443353393091666218231)
  ·
    refine ⟨144272165030089637499327347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96181443353393091666218231 144272165030089637499327347)
    ·
      refine ⟨216408247545134456248991021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144272165030089637499327347 216408247545134456248991021)
      ·
        refine ⟨81153092829425421093371633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216408247545134456248991021 81153092829425421093371633)
        ·
          refine ⟨60864819622069065820028725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81153092829425421093371633 60864819622069065820028725)
          ·
            refine ⟨5706076839568974920627693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60864819622069065820028725 5706076839568974920627693)
            ·
              refine ⟨2139778814838365595235385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5706076839568974920627693 2139778814838365595235385)
              ·
                refine ⟨1604834111128774196426539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2139778814838365595235385 1604834111128774196426539)
                ·
                  refine ⟨2407251166693161294639809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1604834111128774196426539 2407251166693161294639809)
                  ·
                    refine ⟨1805438375019870970979857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2407251166693161294639809 1805438375019870970979857)
                    ·
                      refine ⟨1354078781264903228234893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1805438375019870970979857 1354078781264903228234893)
                      ·
                        rfl

theorem cell23_2637059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 1, 2, 2].length) (baseStart_2637059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637059 prefixEnd_2637059 := by exact prefixLift 2637059
  have htrace : WordTrace (prefixWord ++ tailWord_2637059) baseStart_2637059 baseEnd_2637059 := by
    simpa [prefixWord, tailWord_2637059, baseEnd_2637059] using wordTrace_append hprefix tailTrace_2637059
  have hstable : (prefixWord ++ tailWord_2637059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637059).length < 2 ^ (prefixWord ++ tailWord_2637059).sum := by decide
  have hdescent : baseEnd_2637059 < baseStart_2637059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637108 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_2637108 : Nat := 118140960795 + 2637108 * 2 ^ 59
def prefixEnd_2637108 : Nat := 4983230072969 + 3 ^ 40 * 2637108 * 2
def baseEnd_2637108 : Nat := 451367980605657845507389

theorem tailTrace_2637108 : CollatzResearch.WordTrace tailWord_2637108 prefixEnd_2637108 451367980605657845507389 := by
  unfold tailWord_2637108
  simp only [CollatzResearch.WordTrace]
  refine ⟨48091615265107786517375989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64122153686810382023167985 48091615265107786517375989)
  ·
    refine ⟨4508588931103854986003999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48091615265107786517375989 4508588931103854986003999)
    ·
      refine ⟨6762883396655782479005999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4508588931103854986003999 6762883396655782479005999)
      ·
        refine ⟨10144325094983673718508999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6762883396655782479005999 10144325094983673718508999)
        ·
          refine ⟨15216487642475510577763499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10144325094983673718508999 15216487642475510577763499)
          ·
            refine ⟨22824731463713265866645249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15216487642475510577763499 22824731463713265866645249)
            ·
              refine ⟨17118548597784949399983937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22824731463713265866645249 17118548597784949399983937)
              ·
                refine ⟨12838911448338712049987953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17118548597784949399983937 12838911448338712049987953)
                ·
                  refine ⟨9629183586254034037490965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12838911448338712049987953 9629183586254034037490965)
                  ·
                    refine ⟨451367980605657845507389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9629183586254034037490965 451367980605657845507389)
                    ·
                      rfl

theorem cell23_2637108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_2637108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637108 prefixEnd_2637108 := by exact prefixLift 2637108
  have htrace : WordTrace (prefixWord ++ tailWord_2637108) baseStart_2637108 baseEnd_2637108 := by
    simpa [prefixWord, tailWord_2637108, baseEnd_2637108] using wordTrace_append hprefix tailTrace_2637108
  have hstable : (prefixWord ++ tailWord_2637108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637108).length < 2 ^ (prefixWord ++ tailWord_2637108).sum := by decide
  have hdescent : baseEnd_2637108 < baseStart_2637108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637110 : List Nat := [5, 1, 2, 3, 1, 2, 2, 2, 1, 2, 2]
def baseStart_2637110 : Nat := 118140960795 + 2637110 * 2 ^ 59
def prefixEnd_2637110 : Nat := 4983230072969 + 3 ^ 40 * 2637110 * 2
def baseEnd_2637110 : Nat := 1354104968778282528697159

theorem tailTrace_2637110 : CollatzResearch.WordTrace tailWord_2637110 prefixEnd_2637110 1354104968778282528697159 := by
  unfold tailWord_2637110
  simp only [CollatzResearch.WordTrace]
  refine ⟨6011456467263020461020299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64122202317472218250883189 6011456467263020461020299)
  ·
    refine ⟨9017184700894530691530449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6011456467263020461020299 9017184700894530691530449)
    ·
      refine ⟨6762888525670898018647837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9017184700894530691530449 6762888525670898018647837)
      ·
        refine ⟨2536083197126586756992939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6762888525670898018647837 2536083197126586756992939)
        ·
          refine ⟨3804124795689880135489409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2536083197126586756992939 3804124795689880135489409)
          ·
            refine ⟨2853093596767410101617057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3804124795689880135489409 2853093596767410101617057)
            ·
              refine ⟨2139820197575557576212793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2853093596767410101617057 2139820197575557576212793)
              ·
                refine ⟨1604865148181668182159595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2139820197575557576212793 1604865148181668182159595)
                ·
                  refine ⟨2407297722272502273239393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1604865148181668182159595 2407297722272502273239393)
                  ·
                    refine ⟨1805473291704376704929545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2407297722272502273239393 1805473291704376704929545)
                    ·
                      refine ⟨1354104968778282528697159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1805473291704376704929545 1354104968778282528697159)
                      ·
                        rfl

theorem cell23_2637110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_2637110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637110 prefixEnd_2637110 := by exact prefixLift 2637110
  have htrace : WordTrace (prefixWord ++ tailWord_2637110) baseStart_2637110 baseEnd_2637110 := by
    simpa [prefixWord, tailWord_2637110, baseEnd_2637110] using wordTrace_append hprefix tailTrace_2637110
  have hstable : (prefixWord ++ tailWord_2637110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637110).length < 2 ^ (prefixWord ++ tailWord_2637110).sum := by decide
  have hdescent : baseEnd_2637110 < baseStart_2637110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637118 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 1, 6, 3]
def baseStart_2637118 : Nat := 118140960795 + 2637118 * 2 ^ 59
def prefixEnd_2637118 : Nat := 4983230072969 + 3 ^ 40 * 2637118 * 2
def baseEnd_2637118 : Nat := 1354109076623518497397121

theorem tailTrace_2637118 : CollatzResearch.WordTrace tailWord_2637118 prefixEnd_2637118 1354109076623518497397121 := by
  unfold tailWord_2637118
  simp only [CollatzResearch.WordTrace]
  refine ⟨12022949407522418092827001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64122396840119563161744005 12022949407522418092827001)
  ·
    refine ⟨9017212055641813569620251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12022949407522418092827001 9017212055641813569620251)
    ·
      refine ⟨13525818083462720354430377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9017212055641813569620251 13525818083462720354430377)
      ·
        refine ⟨10144363562597040265822783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13525818083462720354430377 10144363562597040265822783)
        ·
          refine ⟨15216545343895560398734175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10144363562597040265822783 15216545343895560398734175)
          ·
            refine ⟨22824818015843340598101263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15216545343895560398734175 22824818015843340598101263)
            ·
              refine ⟨34237227023765010897151895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22824818015843340598101263 34237227023765010897151895)
              ·
                refine ⟨51355840535647516345727843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34237227023765010897151895 51355840535647516345727843)
                ·
                  refine ⟨77033760803471274518591765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51355840535647516345727843 77033760803471274518591765)
                  ·
                    refine ⟨3610957537662715993058989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77033760803471274518591765 3610957537662715993058989)
                    ·
                      refine ⟨1354109076623518497397121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3610957537662715993058989 1354109076623518497397121)
                      ·
                        rfl

theorem cell23_2637118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_2637118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637118 prefixEnd_2637118 := by exact prefixLift 2637118
  have htrace : WordTrace (prefixWord ++ tailWord_2637118) baseStart_2637118 baseEnd_2637118 := by
    simpa [prefixWord, tailWord_2637118, baseEnd_2637118] using wordTrace_append hprefix tailTrace_2637118
  have hstable : (prefixWord ++ tailWord_2637118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637118).length < 2 ^ (prefixWord ++ tailWord_2637118).sum := by decide
  have hdescent : baseEnd_2637118 < baseStart_2637118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637132 : List Nat := [2, 2, 1, 3, 2, 2, 2, 3, 2, 2, 2]
def baseStart_2637132 : Nat := 118140960795 + 2637132 * 2 ^ 59
def prefixEnd_2637132 : Nat := 4983230072969 + 3 ^ 40 * 2637132 * 2
def baseEnd_2637132 : Nat := 1354116265352681442622057

theorem tailTrace_2637132 : CollatzResearch.WordTrace tailWord_2637132 prefixEnd_2637132 1354116265352681442622057 := by
  unfold tailWord_2637132
  simp only [CollatzResearch.WordTrace]
  refine ⟨48092052941064312566812825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64122737254752416755750433 48092052941064312566812825)
  ·
    refine ⟨36069039705798234425109619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48092052941064312566812825 36069039705798234425109619)
    ·
      refine ⟨54103559558697351637664429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36069039705798234425109619 54103559558697351637664429)
      ·
        refine ⟨20288834834511506864124161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54103559558697351637664429 20288834834511506864124161)
        ·
          refine ⟨15216626125883630148093121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20288834834511506864124161 15216626125883630148093121)
          ·
            refine ⟨11412469594412722611069841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15216626125883630148093121 11412469594412722611069841)
            ·
              refine ⟨8559352195809541958302381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11412469594412722611069841 8559352195809541958302381)
              ·
                refine ⟨3209757073428578234363393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8559352195809541958302381 3209757073428578234363393)
                ·
                  refine ⟨2407317805071433675772545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3209757073428578234363393 2407317805071433675772545)
                  ·
                    refine ⟨1805488353803575256829409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2407317805071433675772545 1805488353803575256829409)
                    ·
                      refine ⟨1354116265352681442622057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1805488353803575256829409 1354116265352681442622057)
                      ·
                        rfl

theorem cell23_2637132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_2637132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637132 prefixEnd_2637132 := by exact prefixLift 2637132
  have htrace : WordTrace (prefixWord ++ tailWord_2637132) baseStart_2637132 baseEnd_2637132 := by
    simpa [prefixWord, tailWord_2637132, baseEnd_2637132] using wordTrace_append hprefix tailTrace_2637132
  have hstable : (prefixWord ++ tailWord_2637132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637132).length < 2 ^ (prefixWord ++ tailWord_2637132).sum := by decide
  have hdescent : baseEnd_2637132 < baseStart_2637132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637155 : List Nat := [1, 1, 1, 5, 2, 3, 2, 3, 5]
def baseStart_2637155 : Nat := 118140960795 + 2637155 * 2 ^ 59
def prefixEnd_2637155 : Nat := 4983230072969 + 3 ^ 40 * 2637155 * 2
def baseEnd_2637155 : Nat := 150458675045303872514939

theorem tailTrace_2637155 : CollatzResearch.WordTrace tailWord_2637155 prefixEnd_2637155 150458675045303872514939 := by
  unfold tailWord_2637155
  simp only [CollatzResearch.WordTrace]
  refine ⟨96184944761045300061712919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64123296507363533374475279 96184944761045300061712919)
  ·
    refine ⟨144277417141567950092569379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96184944761045300061712919 144277417141567950092569379)
    ·
      refine ⟨216416125712351925138854069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144277417141567950092569379 216416125712351925138854069)
      ·
        refine ⟨20289011785532992981767569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 216416125712351925138854069 20289011785532992981767569)
        ·
          refine ⟨15216758839149744736325677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20289011785532992981767569 15216758839149744736325677)
          ·
            refine ⟨5706284564681154276122129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15216758839149744736325677 5706284564681154276122129)
            ·
              refine ⟨4279713423510865707091597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5706284564681154276122129 4279713423510865707091597)
              ·
                refine ⟨1604892533816574640159349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4279713423510865707091597 1604892533816574640159349)
                ·
                  refine ⟨150458675045303872514939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1604892533816574640159349 150458675045303872514939)
                  ·
                    rfl

theorem cell23_2637155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 5].length) (baseStart_2637155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637155 prefixEnd_2637155 := by exact prefixLift 2637155
  have htrace : WordTrace (prefixWord ++ tailWord_2637155) baseStart_2637155 baseEnd_2637155 := by
    simpa [prefixWord, tailWord_2637155, baseEnd_2637155] using wordTrace_append hprefix tailTrace_2637155
  have hstable : (prefixWord ++ tailWord_2637155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637155).length < 2 ^ (prefixWord ++ tailWord_2637155).sum := by decide
  have hdescent : baseEnd_2637155 < baseStart_2637155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637161 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 1, 2, 5]
def baseStart_2637161 : Nat := 118140960795 + 2637161 * 2 ^ 59
def prefixEnd_2637161 : Nat := 4983230072969 + 3 ^ 40 * 2637161 * 2
def baseEnd_2637161 : Nat := 1354131156291661829159423

theorem tailTrace_2637161 : CollatzResearch.WordTrace tailWord_2637161 prefixEnd_2637161 1354131156291661829159423 := by
  unfold tailWord_2637161
  simp only [CollatzResearch.WordTrace]
  refine ⟨96185163599023563086431337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64123442399349042057620891 96185163599023563086431337)
  ·
    refine ⟨72138872699267672314823503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96185163599023563086431337 72138872699267672314823503)
    ·
      refine ⟨108208309048901508472235255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72138872699267672314823503 108208309048901508472235255)
      ·
        refine ⟨162312463573352262708352883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108208309048901508472235255 162312463573352262708352883)
        ·
          refine ⟨243468695360028394062529325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162312463573352262708352883 243468695360028394062529325)
          ·
            refine ⟨91300760760010647773448497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243468695360028394062529325 91300760760010647773448497)
            ·
              refine ⟨68475570570007985830086373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91300760760010647773448497 68475570570007985830086373)
              ·
                refine ⟨12839169481876497343141195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68475570570007985830086373 12839169481876497343141195)
                ·
                  refine ⟨19258754222814746014711793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12839169481876497343141195 19258754222814746014711793)
                  ·
                    refine ⟨14444065667111059511033845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19258754222814746014711793 14444065667111059511033845)
                    ·
                      refine ⟨1354131156291661829159423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14444065667111059511033845 1354131156291661829159423)
                      ·
                        rfl

theorem cell23_2637161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 2, 5].length) (baseStart_2637161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637161 prefixEnd_2637161 := by exact prefixLift 2637161
  have htrace : WordTrace (prefixWord ++ tailWord_2637161) baseStart_2637161 baseEnd_2637161 := by
    simpa [prefixWord, tailWord_2637161, baseEnd_2637161] using wordTrace_append hprefix tailTrace_2637161
  have hstable : (prefixWord ++ tailWord_2637161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637161).length < 2 ^ (prefixWord ++ tailWord_2637161).sum := by decide
  have hdescent : baseEnd_2637161 < baseStart_2637161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637171 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 4]
def baseStart_2637171 : Nat := 118140960795 + 2637171 * 2 ^ 59
def prefixEnd_2637171 : Nat := 4983230072969 + 3 ^ 40 * 2637171 * 2
def baseEnd_2637171 : Nat := 1354136291098206790034377

theorem tailTrace_2637171 : CollatzResearch.WordTrace tailWord_2637171 prefixEnd_2637171 1354136291098206790034377 := by
  unfold tailWord_2637171
  simp only [CollatzResearch.WordTrace]
  refine ⟨96185528328987334794295367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64123685552658223196196911 96185528328987334794295367)
  ·
    refine ⟨144278292493481002191443051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96185528328987334794295367 144278292493481002191443051)
    ·
      refine ⟨216417438740221503287164577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144278292493481002191443051 216417438740221503287164577)
      ·
        refine ⟨162313079055166127465373433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216417438740221503287164577 162313079055166127465373433)
        ·
          refine ⟨121734809291374595599030075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162313079055166127465373433 121734809291374595599030075)
          ·
            refine ⟨182602213937061893398545113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121734809291374595599030075 182602213937061893398545113)
            ·
              refine ⟨136951660452796420048908835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182602213937061893398545113 136951660452796420048908835)
              ·
                refine ⟨205427490679194630073363253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136951660452796420048908835 205427490679194630073363253)
                ·
                  refine ⟨19258827251174496569377805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 205427490679194630073363253 19258827251174496569377805)
                  ·
                    refine ⟨7222060219190436213516677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19258827251174496569377805 7222060219190436213516677)
                    ·
                      refine ⟨1354136291098206790034377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7222060219190436213516677 1354136291098206790034377)
                      ·
                        rfl

theorem cell23_2637171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 4].length) (baseStart_2637171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637171 prefixEnd_2637171 := by exact prefixLift 2637171
  have htrace : WordTrace (prefixWord ++ tailWord_2637171) baseStart_2637171 baseEnd_2637171 := by
    simpa [prefixWord, tailWord_2637171, baseEnd_2637171] using wordTrace_append hprefix tailTrace_2637171
  have hstable : (prefixWord ++ tailWord_2637171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637171).length < 2 ^ (prefixWord ++ tailWord_2637171).sum := by decide
  have hdescent : baseEnd_2637171 < baseStart_2637171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637188 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_2637188 : Nat := 118140960795 + 2637188 * 2 ^ 59
def prefixEnd_2637188 : Nat := 4983230072969 + 3 ^ 40 * 2637188 * 2
def baseEnd_2637188 : Nat := 1354145020269333223521799

theorem tailTrace_2637188 : CollatzResearch.WordTrace tailWord_2637188 prefixEnd_2637188 1354145020269333223521799 := by
  unfold tailWord_2637188
  simp only [CollatzResearch.WordTrace]
  refine ⟨48093074184962873348832109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64124098913283831131776145 48093074184962873348832109)
  ·
    refine ⟨18034902819361077505812041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48093074184962873348832109 18034902819361077505812041)
    ·
      refine ⟨13526177114520808129359031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18034902819361077505812041 13526177114520808129359031)
      ·
        refine ⟨20289265671781212194038547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13526177114520808129359031 20289265671781212194038547)
        ·
          refine ⟨30433898507671818291057821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20289265671781212194038547 30433898507671818291057821)
          ·
            refine ⟨11412711940376931859146683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30433898507671818291057821 11412711940376931859146683)
            ·
              refine ⟨17119067910565397788720025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11412711940376931859146683 17119067910565397788720025)
              ·
                refine ⟨12839300932924048341540019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17119067910565397788720025 12839300932924048341540019)
                ·
                  refine ⟨19258951399386072512310029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12839300932924048341540019 19258951399386072512310029)
                  ·
                    refine ⟨7222106774769777192116261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19258951399386072512310029 7222106774769777192116261)
                    ·
                      refine ⟨1354145020269333223521799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7222106774769777192116261 1354145020269333223521799)
                      ·
                        rfl

theorem cell23_2637188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_2637188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637188 prefixEnd_2637188 := by exact prefixLift 2637188
  have htrace : WordTrace (prefixWord ++ tailWord_2637188) baseStart_2637188 baseEnd_2637188 := by
    simpa [prefixWord, tailWord_2637188, baseEnd_2637188] using wordTrace_append hprefix tailTrace_2637188
  have hstable : (prefixWord ++ tailWord_2637188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637188).length < 2 ^ (prefixWord ++ tailWord_2637188).sum := by decide
  have hdescent : baseEnd_2637188 < baseStart_2637188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637201 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 6]
def baseStart_2637201 : Nat := 118140960795 + 2637201 * 2 ^ 59
def prefixEnd_2637201 : Nat := 4983230072969 + 3 ^ 40 * 2637201 * 2
def baseEnd_2637201 : Nat := 1354151695517841672659239

theorem tailTrace_2637201 : CollatzResearch.WordTrace tailWord_2637201 prefixEnd_2637201 1354151695517841672659239 := by
  unfold tailWord_2637201
  simp only [CollatzResearch.WordTrace]
  refine ⟨96186622518878649917887457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64124415012585766611924971 96186622518878649917887457)
  ·
    refine ⟨72139966889158987438415593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96186622518878649917887457 72139966889158987438415593)
    ·
      refine ⟨54104975166869240578811695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72139966889158987438415593 54104975166869240578811695)
      ·
        refine ⟨81157462750303860868217543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54104975166869240578811695 81157462750303860868217543)
        ·
          refine ⟨121736194125455791302326315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81157462750303860868217543 121736194125455791302326315)
          ·
            refine ⟨182604291188183686953489473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121736194125455791302326315 182604291188183686953489473)
            ·
              refine ⟨136953218391137765215117105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182604291188183686953489473 136953218391137765215117105)
              ·
                refine ⟨102714913793353323911337829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136953218391137765215117105 102714913793353323911337829)
                ·
                  refine ⟨19259046336253748233375843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102714913793353323911337829 19259046336253748233375843)
                  ·
                    refine ⟨28888569504380622350063765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19259046336253748233375843 28888569504380622350063765)
                    ·
                      refine ⟨1354151695517841672659239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28888569504380622350063765 1354151695517841672659239)
                      ·
                        rfl

theorem cell23_2637201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_2637201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637201 prefixEnd_2637201 := by exact prefixLift 2637201
  have htrace : WordTrace (prefixWord ++ tailWord_2637201) baseStart_2637201 baseEnd_2637201 := by
    simpa [prefixWord, tailWord_2637201, baseEnd_2637201] using wordTrace_append hprefix tailTrace_2637201
  have hstable : (prefixWord ++ tailWord_2637201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637201).length < 2 ^ (prefixWord ++ tailWord_2637201).sum := by decide
  have hdescent : baseEnd_2637201 < baseStart_2637201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637231 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 8]
def baseStart_2637231 : Nat := 118140960795 + 2637231 * 2 ^ 59
def prefixEnd_2637231 : Nat := 4983230072969 + 3 ^ 40 * 2637231 * 2
def baseEnd_2637231 : Nat := 1354167099937476555284101

theorem tailTrace_2637231 : CollatzResearch.WordTrace tailWord_2637231 prefixEnd_2637231 1354167099937476555284101 := by
  unfold tailWord_2637231
  simp only [CollatzResearch.WordTrace]
  refine ⟨96187716708769965041479547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64125144472513310027653031 96187716708769965041479547)
  ·
    refine ⟨144281575063154947562219321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96187716708769965041479547 144281575063154947562219321)
    ·
      refine ⟨108211181297366210671664491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144281575063154947562219321 108211181297366210671664491)
      ·
        refine ⟨162316771946049316007496737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108211181297366210671664491 162316771946049316007496737)
        ·
          refine ⟨121737578959536987005622553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162316771946049316007496737 121737578959536987005622553)
          ·
            refine ⟨91303184219652740254216915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121737578959536987005622553 91303184219652740254216915)
            ·
              refine ⟨136954776329479110381325373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91303184219652740254216915 136954776329479110381325373)
              ·
                refine ⟨51358041123554666392997015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136954776329479110381325373 51358041123554666392997015)
                ·
                  refine ⟨77037061685331999589495523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51358041123554666392997015 77037061685331999589495523)
                  ·
                    refine ⟨115555592527997999384243285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77037061685331999589495523 115555592527997999384243285)
                    ·
                      refine ⟨1354167099937476555284101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 115555592527997999384243285 1354167099937476555284101)
                      ·
                        rfl

theorem cell23_2637231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_2637231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637231 prefixEnd_2637231 := by exact prefixLift 2637231
  have htrace : WordTrace (prefixWord ++ tailWord_2637231) baseStart_2637231 baseEnd_2637231 := by
    simpa [prefixWord, tailWord_2637231, baseEnd_2637231] using wordTrace_append hprefix tailTrace_2637231
  have hstable : (prefixWord ++ tailWord_2637231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637231).length < 2 ^ (prefixWord ++ tailWord_2637231).sum := by decide
  have hdescent : baseEnd_2637231 < baseStart_2637231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637255 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 5, 1, 3]
def baseStart_2637255 : Nat := 118140960795 + 2637255 * 2 ^ 59
def prefixEnd_2637255 : Nat := 4983230072969 + 3 ^ 40 * 2637255 * 2
def baseEnd_2637255 : Nat := 1354179423473184461383991

theorem tailTrace_2637255 : CollatzResearch.WordTrace tailWord_2637255 prefixEnd_2637255 1354179423473184461383991 := by
  unfold tailWord_2637255
  simp only [CollatzResearch.WordTrace]
  refine ⟨96188592060683017140353219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64125728040455344760235479 96188592060683017140353219)
  ·
    refine ⟨144282888091024525710529829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96188592060683017140353219 144282888091024525710529829)
    ·
      refine ⟨27053041517067098570724343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144282888091024525710529829 27053041517067098570724343)
      ·
        refine ⟨40579562275600647856086515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27053041517067098570724343 40579562275600647856086515)
        ·
          refine ⟨60869343413400971784129773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40579562275600647856086515 60869343413400971784129773)
          ·
            refine ⟨22826003780025364419048665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60869343413400971784129773 22826003780025364419048665)
            ·
              refine ⟨17119502835019023314286499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22826003780025364419048665 17119502835019023314286499)
              ·
                refine ⟨25679254252528534971429749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17119502835019023314286499 25679254252528534971429749)
                ·
                  refine ⟨2407430086174550153571539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25679254252528534971429749 2407430086174550153571539)
                  ·
                    refine ⟨3611145129261825230357309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2407430086174550153571539 3611145129261825230357309)
                    ·
                      refine ⟨1354179423473184461383991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3611145129261825230357309 1354179423473184461383991)
                      ·
                        rfl

theorem cell23_2637255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_2637255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637255 prefixEnd_2637255 := by exact prefixLift 2637255
  have htrace : WordTrace (prefixWord ++ tailWord_2637255) baseStart_2637255 baseEnd_2637255 := by
    simpa [prefixWord, tailWord_2637255, baseEnd_2637255] using wordTrace_append hprefix tailTrace_2637255
  have hstable : (prefixWord ++ tailWord_2637255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637255).length < 2 ^ (prefixWord ++ tailWord_2637255).sum := by decide
  have hdescent : baseEnd_2637255 < baseStart_2637255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637288 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 3, 6]
def baseStart_2637288 : Nat := 118140960795 + 2637288 * 2 ^ 59
def prefixEnd_2637288 : Nat := 4983230072969 + 3 ^ 40 * 2637288 * 2
def baseEnd_2637288 : Nat := 451398789444927610757113

theorem tailTrace_2637288 : CollatzResearch.WordTrace tailWord_2637288 prefixEnd_2637288 451398789444927610757113 := by
  unfold tailWord_2637288
  simp only [CollatzResearch.WordTrace]
  refine ⟨48094897834781731888152259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64126530446375642517536345 48094897834781731888152259)
  ·
    refine ⟨72142346752172597832228389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48094897834781731888152259 72142346752172597832228389)
    ·
      refine ⟨13526690016032362093542823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72142346752172597832228389 13526690016032362093542823)
      ·
        refine ⟨20290035024048543140314235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13526690016032362093542823 20290035024048543140314235)
        ·
          refine ⟨30435052536072814710471353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20290035024048543140314235 30435052536072814710471353)
          ·
            refine ⟨22826289402054611032853515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30435052536072814710471353 22826289402054611032853515)
            ·
              refine ⟨34239434103081916549280273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22826289402054611032853515 34239434103081916549280273)
              ·
                refine ⟨25679575577311437411960205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34239434103081916549280273 25679575577311437411960205)
                ·
                  refine ⟨9629840841491789029485077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25679575577311437411960205 9629840841491789029485077)
                  ·
                    refine ⟨451398789444927610757113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9629840841491789029485077 451398789444927610757113)
                    ·
                      rfl

theorem cell23_2637288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_2637288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637288 prefixEnd_2637288 := by exact prefixLift 2637288
  have htrace : WordTrace (prefixWord ++ tailWord_2637288) baseStart_2637288 baseEnd_2637288 := by
    simpa [prefixWord, tailWord_2637288, baseEnd_2637288] using wordTrace_append hprefix tailTrace_2637288
  have hstable : (prefixWord ++ tailWord_2637288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637288).length < 2 ^ (prefixWord ++ tailWord_2637288).sum := by decide
  have hdescent : baseEnd_2637288 < baseStart_2637288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637308 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 1, 1, 6]
def baseStart_2637308 : Nat := 118140960795 + 2637308 * 2 ^ 59
def prefixEnd_2637308 : Nat := 4983230072969 + 3 ^ 40 * 2637308 * 2
def baseEnd_2637308 : Nat := 1354206637947872754021247

theorem tailTrace_2637308 : CollatzResearch.WordTrace tailWord_2637308 prefixEnd_2637308 1354206637947872754021247 := by
  unfold tailWord_2637308
  simp only [CollatzResearch.WordTrace]
  refine ⟨48095262564745503596016289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64127016752994004794688385 48095262564745503596016289)
  ·
    refine ⟨36071446923559127697012217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48095262564745503596016289 36071446923559127697012217)
    ·
      refine ⟨27053585192669345772759163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36071446923559127697012217 27053585192669345772759163)
      ·
        refine ⟨40580377789004018659138745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27053585192669345772759163 40580377789004018659138745)
        ·
          refine ⟨30435283341753013994354059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40580377789004018659138745 30435283341753013994354059)
          ·
            refine ⟨45652925012629520991531089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30435283341753013994354059 45652925012629520991531089)
            ·
              refine ⟨34239693759472140743648317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45652925012629520991531089 34239693759472140743648317)
              ·
                refine ⟨12839885159802052778868119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34239693759472140743648317 12839885159802052778868119)
                ·
                  refine ⟨19259827739703079168302179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12839885159802052778868119 19259827739703079168302179)
                  ·
                    refine ⟨28889741609554618752453269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19259827739703079168302179 28889741609554618752453269)
                    ·
                      refine ⟨1354206637947872754021247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28889741609554618752453269 1354206637947872754021247)
                      ·
                        rfl

theorem cell23_2637308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_2637308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637308 prefixEnd_2637308 := by exact prefixLift 2637308
  have htrace : WordTrace (prefixWord ++ tailWord_2637308) baseStart_2637308 baseEnd_2637308 := by
    simpa [prefixWord, tailWord_2637308, baseEnd_2637308] using wordTrace_append hprefix tailTrace_2637308
  have hstable : (prefixWord ++ tailWord_2637308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637308).length < 2 ^ (prefixWord ++ tailWord_2637308).sum := by decide
  have hdescent : baseEnd_2637308 < baseStart_2637308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637316 : List Nat := [2, 3, 2, 3, 2, 2, 1, 1, 2, 3, 2]
def baseStart_2637316 : Nat := 118140960795 + 2637316 * 2 ^ 59
def prefixEnd_2637316 : Nat := 4983230072969 + 3 ^ 40 * 2637316 * 2
def baseEnd_2637316 : Nat := 1354210745793108722721211

theorem tailTrace_2637316 : CollatzResearch.WordTrace tailWord_2637316 prefixEnd_2637316 1354210745793108722721211 := by
  unfold tailWord_2637316
  simp only [CollatzResearch.WordTrace]
  refine ⟨48095408456731012279161901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64127211275641349705549201 48095408456731012279161901)
  ·
    refine ⟨18035778171274129604685713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48095408456731012279161901 18035778171274129604685713)
    ·
      refine ⟨13526833628455597203514285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18035778171274129604685713 13526833628455597203514285)
      ·
        refine ⟨5072562610670848951317857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13526833628455597203514285 5072562610670848951317857)
        ·
          refine ⟨3804421958003136713488393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5072562610670848951317857 3804421958003136713488393)
          ·
            refine ⟨2853316468502352535116295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3804421958003136713488393 2853316468502352535116295)
            ·
              refine ⟨4279974702753528802674443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2853316468502352535116295 4279974702753528802674443)
              ·
                refine ⟨6419962054130293204011665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4279974702753528802674443 6419962054130293204011665)
                ·
                  refine ⟨4814971540597719903008749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6419962054130293204011665 4814971540597719903008749)
                  ·
                    refine ⟨1805614327724144963628281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4814971540597719903008749 1805614327724144963628281)
                    ·
                      refine ⟨1354210745793108722721211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1805614327724144963628281 1354210745793108722721211)
                      ·
                        rfl

theorem cell23_2637316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_2637316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637316 prefixEnd_2637316 := by exact prefixLift 2637316
  have htrace : WordTrace (prefixWord ++ tailWord_2637316) baseStart_2637316 baseEnd_2637316 := by
    simpa [prefixWord, tailWord_2637316, baseEnd_2637316] using wordTrace_append hprefix tailTrace_2637316
  have hstable : (prefixWord ++ tailWord_2637316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637316).length < 2 ^ (prefixWord ++ tailWord_2637316).sum := by decide
  have hdescent : baseEnd_2637316 < baseStart_2637316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637326 : List Nat := [4, 1, 1, 2, 5, 1, 2, 1, 1, 5]
def baseStart_2637326 : Nat := 118140960795 + 2637326 * 2 ^ 59
def prefixEnd_2637326 : Nat := 4983230072969 + 3 ^ 40 * 2637326 * 2
def baseEnd_2637326 : Nat := 451405293533217894532055

theorem tailTrace_2637326 : CollatzResearch.WordTrace tailWord_2637326 prefixEnd_2637326 451405293533217894532055 := by
  unfold tailWord_2637326
  simp only [CollatzResearch.WordTrace]
  refine ⟨12023897705428224533273479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64127454428950530844125221 12023897705428224533273479)
  ·
    refine ⟨18035846558142336799910219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12023897705428224533273479 18035846558142336799910219)
    ·
      refine ⟨27053769837213505199865329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18035846558142336799910219 27053769837213505199865329)
      ·
        refine ⟨20290327377910128899898997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27053769837213505199865329 20290327377910128899898997)
        ·
          refine ⟨1902218191679074584365531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20290327377910128899898997 1902218191679074584365531)
          ·
            refine ⟨2853327287518611876548297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1902218191679074584365531 2853327287518611876548297)
            ·
              refine ⟨2139995465638958907411223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2853327287518611876548297 2139995465638958907411223)
              ·
                refine ⟨3209993198458438361116835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2139995465638958907411223 3209993198458438361116835)
                ·
                  refine ⟨4814989797687657541675253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3209993198458438361116835 4814989797687657541675253)
                  ·
                    refine ⟨451405293533217894532055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4814989797687657541675253 451405293533217894532055)
                    ·
                      rfl

theorem cell23_2637326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_2637326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637326 prefixEnd_2637326 := by exact prefixLift 2637326
  have htrace : WordTrace (prefixWord ++ tailWord_2637326) baseStart_2637326 baseEnd_2637326 := by
    simpa [prefixWord, tailWord_2637326, baseEnd_2637326] using wordTrace_append hprefix tailTrace_2637326
  have hstable : (prefixWord ++ tailWord_2637326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637326).length < 2 ^ (prefixWord ++ tailWord_2637326).sum := by decide
  have hdescent : baseEnd_2637326 < baseStart_2637326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637338 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6]
def baseStart_2637338 : Nat := 118140960795 + 2637338 * 2 ^ 59
def prefixEnd_2637338 : Nat := 4983230072969 + 3 ^ 40 * 2637338 * 2
def baseEnd_2637338 : Nat := 1354222042367507636646109

theorem tailTrace_2637338 : CollatzResearch.WordTrace tailWord_2637338 prefixEnd_2637338 1354222042367507636646109 := by
  unfold tailWord_2637338
  simp only [CollatzResearch.WordTrace]
  refine ⟨24047904829845580578906167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64127746212921548210416445 24047904829845580578906167)
  ·
    refine ⟨36071857244768370868359251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24047904829845580578906167 36071857244768370868359251)
    ·
      refine ⟨54107785867152556302538877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36071857244768370868359251 54107785867152556302538877)
      ·
        refine ⟨20290419700182208613452079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54107785867152556302538877 20290419700182208613452079)
        ·
          refine ⟨30435629550273312920178119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20290419700182208613452079 30435629550273312920178119)
          ·
            refine ⟨45653444325409969380267179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30435629550273312920178119 45653444325409969380267179)
            ·
              refine ⟨68480166488114954070400769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45653444325409969380267179 68480166488114954070400769)
              ·
                refine ⟨51360124866086215552800577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68480166488114954070400769 51360124866086215552800577)
                ·
                  refine ⟨38520093649564661664600433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51360124866086215552800577 38520093649564661664600433)
                  ·
                    refine ⟨28890070237173496248450325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38520093649564661664600433 28890070237173496248450325)
                    ·
                      refine ⟨1354222042367507636646109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28890070237173496248450325 1354222042367507636646109)
                      ·
                        rfl

theorem cell23_2637338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_2637338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637338 prefixEnd_2637338 := by exact prefixLift 2637338
  have htrace : WordTrace (prefixWord ++ tailWord_2637338) baseStart_2637338 baseEnd_2637338 := by
    simpa [prefixWord, tailWord_2637338, baseEnd_2637338] using wordTrace_append hprefix tailTrace_2637338
  have hstable : (prefixWord ++ tailWord_2637338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637338).length < 2 ^ (prefixWord ++ tailWord_2637338).sum := by decide
  have hdescent : baseEnd_2637338 < baseStart_2637338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637346 : List Nat := [3, 3, 1, 1, 1, 1, 4, 4, 1, 2, 2]
def baseStart_2637346 : Nat := 118140960795 + 2637346 * 2 ^ 59
def prefixEnd_2637346 : Nat := 4983230072969 + 3 ^ 40 * 2637346 * 2
def baseEnd_2637346 : Nat := 1354226150212743605346073

theorem tailTrace_2637346 : CollatzResearch.WordTrace tailWord_2637346 prefixEnd_2637346 1354226150212743605346073 := by
  unfold tailWord_2637346
  simp only [CollatzResearch.WordTrace]
  refine ⟨24047977775838334920478973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64127940735568893121277261 24047977775838334920478973)
  ·
    refine ⟨9017991665939375595179615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24047977775838334920478973 9017991665939375595179615)
    ·
      refine ⟨13526987498909063392769423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9017991665939375595179615 13526987498909063392769423)
      ·
        refine ⟨20290481248363595089154135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13526987498909063392769423 20290481248363595089154135)
        ·
          refine ⟨30435721872545392633731203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20290481248363595089154135 30435721872545392633731203)
          ·
            refine ⟨45653582808818088950596805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30435721872545392633731203 45653582808818088950596805)
            ·
              refine ⟨8560046776653391678236901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45653582808818088950596805 8560046776653391678236901)
              ·
                refine ⟨1605008770622510939669419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8560046776653391678236901 1605008770622510939669419)
                ·
                  refine ⟨2407513155933766409504129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1605008770622510939669419 2407513155933766409504129)
                  ·
                    refine ⟨1805634866950324807128097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2407513155933766409504129 1805634866950324807128097)
                    ·
                      refine ⟨1354226150212743605346073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1805634866950324807128097 1354226150212743605346073)
                      ·
                        rfl

theorem cell23_2637346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_2637346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637346 prefixEnd_2637346 := by exact prefixLift 2637346
  have htrace : WordTrace (prefixWord ++ tailWord_2637346) baseStart_2637346 baseEnd_2637346 := by
    simpa [prefixWord, tailWord_2637346, baseEnd_2637346] using wordTrace_append hprefix tailTrace_2637346
  have hstable : (prefixWord ++ tailWord_2637346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637346).length < 2 ^ (prefixWord ++ tailWord_2637346).sum := by decide
  have hdescent : baseEnd_2637346 < baseStart_2637346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637366 : List Nat := [5, 1, 2, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_2637366 : Nat := 118140960795 + 2637366 * 2 ^ 59
def prefixEnd_2637366 : Nat := 4983230072969 + 3 ^ 40 * 2637366 * 2
def baseEnd_2637366 : Nat := 1354236419825833527095981

theorem tailTrace_2637366 : CollatzResearch.WordTrace tailWord_2637366 prefixEnd_2637366 1354236419825833527095981 := by
  unfold tailWord_2637366
  simp only [CollatzResearch.WordTrace]
  refine ⟨6012040035205055193602747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64128427042187255398429301 6012040035205055193602747)
  ·
    refine ⟨9018060052807582790404121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6012040035205055193602747 9018060052807582790404121)
    ·
      refine ⟨6763545039605687092803091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9018060052807582790404121 6763545039605687092803091)
      ·
        refine ⟨10145317559408530639204637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6763545039605687092803091 10145317559408530639204637)
        ·
          refine ⟨3804494084778198989701739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10145317559408530639204637 3804494084778198989701739)
          ·
            refine ⟨5706741127167298484552609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3804494084778198989701739 5706741127167298484552609)
            ·
              refine ⟨4280055845375473863414457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5706741127167298484552609 4280055845375473863414457)
              ·
                refine ⟨3210041884031605397560843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4280055845375473863414457 3210041884031605397560843)
                ·
                  refine ⟨4815062826047408096341265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3210041884031605397560843 4815062826047408096341265)
                  ·
                    refine ⟨3611297119535556072255949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4815062826047408096341265 3611297119535556072255949)
                    ·
                      refine ⟨1354236419825833527095981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3611297119535556072255949 1354236419825833527095981)
                      ·
                        rfl

theorem cell23_2637366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_2637366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637366 prefixEnd_2637366 := by exact prefixLift 2637366
  have htrace : WordTrace (prefixWord ++ tailWord_2637366) baseStart_2637366 baseEnd_2637366 := by
    simpa [prefixWord, tailWord_2637366, baseEnd_2637366] using wordTrace_append hprefix tailTrace_2637366
  have hstable : (prefixWord ++ tailWord_2637366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637366).length < 2 ^ (prefixWord ++ tailWord_2637366).sum := by decide
  have hdescent : baseEnd_2637366 < baseStart_2637366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637415 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_2637415 : Nat := 118140960795 + 2637415 * 2 ^ 59
def prefixEnd_2637415 : Nat := 4983230072969 + 3 ^ 40 * 2637415 * 2
def baseEnd_2637415 : Nat := 1354261580377903835383255

theorem tailTrace_2637415 : CollatzResearch.WordTrace tailWord_2637415 prefixEnd_2637415 1354261580377903835383255 := by
  unfold tailWord_2637415
  simp only [CollatzResearch.WordTrace]
  refine ⟨96194427740103364466177699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64129618493402242977451799 96194427740103364466177699)
  ·
    refine ⟨144291641610155046699266549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96194427740103364466177699 144291641610155046699266549)
    ·
      refine ⟨13527341400952035628056239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144291641610155046699266549 13527341400952035628056239)
      ·
        refine ⟨20291012101428053442084359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13527341400952035628056239 20291012101428053442084359)
        ·
          refine ⟨30436518152142080163126539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20291012101428053442084359 30436518152142080163126539)
          ·
            refine ⟨45654777228213120244689809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30436518152142080163126539 45654777228213120244689809)
            ·
              refine ⟨34241082921159840183517357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45654777228213120244689809 34241082921159840183517357)
              ·
                refine ⟨12840406095434940068819009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34241082921159840183517357 12840406095434940068819009)
                ·
                  refine ⟨9630304571576205051614257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12840406095434940068819009 9630304571576205051614257)
                  ·
                    refine ⟨7222728428682153788710693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9630304571576205051614257 7222728428682153788710693)
                    ·
                      refine ⟨1354261580377903835383255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7222728428682153788710693 1354261580377903835383255)
                      ·
                        rfl

theorem cell23_2637415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_2637415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637415 prefixEnd_2637415 := by exact prefixLift 2637415
  have htrace : WordTrace (prefixWord ++ tailWord_2637415) baseStart_2637415 baseEnd_2637415 := by
    simpa [prefixWord, tailWord_2637415, baseEnd_2637415] using wordTrace_append hprefix tailTrace_2637415
  have hstable : (prefixWord ++ tailWord_2637415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637415).length < 2 ^ (prefixWord ++ tailWord_2637415).sum := by decide
  have hdescent : baseEnd_2637415 < baseStart_2637415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637475 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 4]
def baseStart_2637475 : Nat := 118140960795 + 2637475 * 2 ^ 59
def prefixEnd_2637475 : Nat := 4983230072969 + 3 ^ 40 * 2637475 * 2
def baseEnd_2637475 : Nat := 1354292389217173600632979

theorem tailTrace_2637475 : CollatzResearch.WordTrace tailWord_2637475 prefixEnd_2637475 1354292389217173600632979 := by
  unfold tailWord_2637475
  simp only [CollatzResearch.WordTrace]
  refine ⟨96196616119885994713361879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64131077413257329808907919 96196616119885994713361879)
  ·
    refine ⟨144294924179828992070042819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96196616119885994713361879 144294924179828992070042819)
    ·
      refine ⟨216442386269743488105064229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144294924179828992070042819 216442386269743488105064229)
      ·
        refine ⟨40582947425576904019699543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216442386269743488105064229 40582947425576904019699543)
        ·
          refine ⟨60874421138365356029549315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40582947425576904019699543 60874421138365356029549315)
          ·
            refine ⟨91311631707548034044323973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60874421138365356029549315 91311631707548034044323973)
            ·
              refine ⟨17120930945165256383310745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91311631707548034044323973 17120930945165256383310745)
              ·
                refine ⟨12840698208873942287483059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17120930945165256383310745 12840698208873942287483059)
                ·
                  refine ⟨19261047313310913431224589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12840698208873942287483059 19261047313310913431224589)
                  ·
                    refine ⟨7222892742491592536709221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19261047313310913431224589 7222892742491592536709221)
                    ·
                      refine ⟨1354292389217173600632979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7222892742491592536709221 1354292389217173600632979)
                      ·
                        rfl

theorem cell23_2637475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_2637475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637475 prefixEnd_2637475 := by exact prefixLift 2637475
  have htrace : WordTrace (prefixWord ++ tailWord_2637475) baseStart_2637475 baseEnd_2637475 := by
    simpa [prefixWord, tailWord_2637475, baseEnd_2637475] using wordTrace_append hprefix tailTrace_2637475
  have hstable : (prefixWord ++ tailWord_2637475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637475).length < 2 ^ (prefixWord ++ tailWord_2637475).sum := by decide
  have hdescent : baseEnd_2637475 < baseStart_2637475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637512 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 4, 2, 3]
def baseStart_2637512 : Nat := 118140960795 + 2637512 * 2 ^ 59
def prefixEnd_2637512 : Nat := 4983230072969 + 3 ^ 40 * 2637512 * 2
def baseEnd_2637512 : Nat := 1354311388001389955870309

theorem tailTrace_2637512 : CollatzResearch.WordTrace tailWord_2637512 prefixEnd_2637512 1354311388001389955870309 := by
  unfold tailWord_2637512
  simp only [CollatzResearch.WordTrace]
  refine ⟨48098982810375975016229395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64131977080501300021639193 48098982810375975016229395)
  ·
    refine ⟨72148474215563962524344093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48098982810375975016229395 72148474215563962524344093)
    ·
      refine ⟨27055677830836485946629035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72148474215563962524344093 27055677830836485946629035)
      ·
        refine ⟨40583516746254728919943553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27055677830836485946629035 40583516746254728919943553)
        ·
          refine ⟨30437637559691046689957665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40583516746254728919943553 30437637559691046689957665)
          ·
            refine ⟨22828228169768285017468249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30437637559691046689957665 22828228169768285017468249)
            ·
              refine ⟨17121171127326213763101187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22828228169768285017468249 17121171127326213763101187)
              ·
                refine ⟨25681756690989320644651781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17121171127326213763101187 25681756690989320644651781)
                ·
                  refine ⟨4815329379560497620872209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25681756690989320644651781 4815329379560497620872209)
                  ·
                    refine ⟨3611497034670373215654157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4815329379560497620872209 3611497034670373215654157)
                    ·
                      refine ⟨1354311388001389955870309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3611497034670373215654157 1354311388001389955870309)
                      ·
                        rfl

theorem cell23_2637512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_2637512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637512 prefixEnd_2637512 := by exact prefixLift 2637512
  have htrace : WordTrace (prefixWord ++ tailWord_2637512) baseStart_2637512 baseEnd_2637512 := by
    simpa [prefixWord, tailWord_2637512, baseEnd_2637512] using wordTrace_append hprefix tailTrace_2637512
  have hstable : (prefixWord ++ tailWord_2637512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637512).length < 2 ^ (prefixWord ++ tailWord_2637512).sum := by decide
  have hdescent : baseEnd_2637512 < baseStart_2637512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637535 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 6]
def baseStart_2637535 : Nat := 118140960795 + 2637535 * 2 ^ 59
def prefixEnd_2637535 : Nat := 4983230072969 + 3 ^ 40 * 2637535 * 2
def baseEnd_2637535 : Nat := 1354323198056443365882703

theorem tailTrace_2637535 : CollatzResearch.WordTrace tailWord_2637535 prefixEnd_2637535 1354323198056443365882703 := by
  unfold tailWord_2637535
  simp only [CollatzResearch.WordTrace]
  refine ⟨96198804499668624960546059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64132536333112416640364039 96198804499668624960546059)
  ·
    refine ⟨144298206749502937440819089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96198804499668624960546059 144298206749502937440819089)
    ·
      refine ⟨108223655062127203080614317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144298206749502937440819089 108223655062127203080614317)
      ·
        refine ⟨40583870648297701155230369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108223655062127203080614317 40583870648297701155230369)
        ·
          refine ⟨30437902986223275866422777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40583870648297701155230369 30437902986223275866422777)
          ·
            refine ⟨22828427239667456899817083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30437902986223275866422777 22828427239667456899817083)
            ·
              refine ⟨34242640859501185349725625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22828427239667456899817083 34242640859501185349725625)
              ·
                refine ⟨25681980644625889012294219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34242640859501185349725625 25681980644625889012294219)
                ·
                  refine ⟨38522970966938833518441329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25681980644625889012294219 38522970966938833518441329)
                  ·
                    refine ⟨28892228225204125138830997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38522970966938833518441329 28892228225204125138830997)
                    ·
                      refine ⟨1354323198056443365882703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28892228225204125138830997 1354323198056443365882703)
                      ·
                        rfl

theorem cell23_2637535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_2637535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637535 prefixEnd_2637535 := by exact prefixLift 2637535
  have htrace : WordTrace (prefixWord ++ tailWord_2637535) baseStart_2637535 baseEnd_2637535 := by
    simpa [prefixWord, tailWord_2637535, baseEnd_2637535] using wordTrace_append hprefix tailTrace_2637535
  have hstable : (prefixWord ++ tailWord_2637535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637535).length < 2 ^ (prefixWord ++ tailWord_2637535).sum := by decide
  have hdescent : baseEnd_2637535 < baseStart_2637535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637569 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 4, 3, 2]
def baseStart_2637569 : Nat := 118140960795 + 2637569 * 2 ^ 59
def prefixEnd_2637569 : Nat := 4983230072969 + 3 ^ 40 * 2637569 * 2
def baseEnd_2637569 : Nat := 1354340656398696232857547

theorem tailTrace_2637569 : CollatzResearch.WordTrace tailWord_2637569 prefixEnd_2637569 1354340656398696232857547 := by
  unfold tailWord_2637569
  simp only [CollatzResearch.WordTrace]
  refine ⟨96200044581545448767283761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64133363054363632511522507 96200044581545448767283761)
  ·
    refine ⟨72150033436159086575462821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96200044581545448767283761 72150033436159086575462821)
    ·
      refine ⟨13528131269279828732899279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72150033436159086575462821 13528131269279828732899279)
      ·
        refine ⟨20292196903919743099348919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13528131269279828732899279 20292196903919743099348919)
        ·
          refine ⟨30438295355879614649023379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20292196903919743099348919 30438295355879614649023379)
          ·
            refine ⟨45657443033819421973535069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30438295355879614649023379 45657443033819421973535069)
            ·
              refine ⟨17121541137682283240075651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45657443033819421973535069 17121541137682283240075651)
              ·
                refine ⟨25682311706523424860113477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17121541137682283240075651 25682311706523424860113477)
                ·
                  refine ⟨4815433444973142161271277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25682311706523424860113477 4815433444973142161271277)
                  ·
                    refine ⟨1805787541864928310476729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4815433444973142161271277 1805787541864928310476729)
                    ·
                      refine ⟨1354340656398696232857547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1805787541864928310476729 1354340656398696232857547)
                      ·
                        rfl

theorem cell23_2637569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_2637569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637569 prefixEnd_2637569 := by exact prefixLift 2637569
  have htrace : WordTrace (prefixWord ++ tailWord_2637569) baseStart_2637569 baseEnd_2637569 := by
    simpa [prefixWord, tailWord_2637569, baseEnd_2637569] using wordTrace_append hprefix tailTrace_2637569
  have hstable : (prefixWord ++ tailWord_2637569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637569).length < 2 ^ (prefixWord ++ tailWord_2637569).sum := by decide
  have hdescent : baseEnd_2637569 < baseStart_2637569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637612 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 4]
def baseStart_2637612 : Nat := 118140960795 + 2637612 * 2 ^ 59
def prefixEnd_2637612 : Nat := 4983230072969 + 3 ^ 40 * 2637612 * 2
def baseEnd_2637612 : Nat := 1354362736066839564619849

theorem tailTrace_2637612 : CollatzResearch.WordTrace tailWord_2637612 prefixEnd_2637612 1354362736066839564619849 := by
  unfold tailWord_2637612
  simp only [CollatzResearch.WordTrace]
  refine ⟨48100806460194833555549545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64134408613593111407399393 48100806460194833555549545)
  ·
    refine ⟨36075604845146125166662159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48100806460194833555549545 36075604845146125166662159)
    ·
      refine ⟨54113407267719187749993239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36075604845146125166662159 54113407267719187749993239)
      ·
        refine ⟨81170110901578781624989859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54113407267719187749993239 81170110901578781624989859)
        ·
          refine ⟨121755166352368172437484789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81170110901578781624989859 121755166352368172437484789)
          ·
            refine ⟨11414546845534516166014199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121755166352368172437484789 11414546845534516166014199)
            ·
              refine ⟨17121820268301774249021299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11414546845534516166014199 17121820268301774249021299)
              ·
                refine ⟨25682730402452661373531949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17121820268301774249021299 25682730402452661373531949)
                ·
                  refine ⟨9631023900919748015074481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25682730402452661373531949 9631023900919748015074481)
                  ·
                    refine ⟨7223267925689811011305861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9631023900919748015074481 7223267925689811011305861)
                    ·
                      refine ⟨1354362736066839564619849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7223267925689811011305861 1354362736066839564619849)
                      ·
                        rfl

theorem cell23_2637612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_2637612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637612 prefixEnd_2637612 := by exact prefixLift 2637612
  have htrace : WordTrace (prefixWord ++ tailWord_2637612) baseStart_2637612 baseEnd_2637612 := by
    simpa [prefixWord, tailWord_2637612, baseEnd_2637612] using wordTrace_append hprefix tailTrace_2637612
  have hstable : (prefixWord ++ tailWord_2637612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637612).length < 2 ^ (prefixWord ++ tailWord_2637612).sum := by decide
  have hdescent : baseEnd_2637612 < baseStart_2637612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637626 : List Nat := [3, 1, 1, 1, 5, 2, 2, 2, 2, 4]
def baseStart_2637626 : Nat := 118140960795 + 2637626 * 2 ^ 59
def prefixEnd_2637626 : Nat := 4983230072969 + 3 ^ 40 * 2637626 * 2
def baseEnd_2637626 : Nat := 451456641598667503281595

theorem tailTrace_2637626 : CollatzResearch.WordTrace tailWord_2637626 prefixEnd_2637626 451456641598667503281595 := by
  unfold tailWord_2637626
  simp only [CollatzResearch.WordTrace]
  refine ⟨24050530885584736875527183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64134749028225965001405821 24050530885584736875527183)
  ·
    refine ⟨36075796328377105313290775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24050530885584736875527183 36075796328377105313290775)
    ·
      refine ⟨54113694492565657969936163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36075796328377105313290775 54113694492565657969936163)
      ·
        refine ⟨81170541738848486954904245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54113694492565657969936163 81170541738848486954904245)
        ·
          refine ⟨7609738288017045652022273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81170541738848486954904245 7609738288017045652022273)
          ·
            refine ⟨5707303716012784239016705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7609738288017045652022273 5707303716012784239016705)
            ·
              refine ⟨4280477787009588179262529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5707303716012784239016705 4280477787009588179262529)
              ·
                refine ⟨3210358340257191134446897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4280477787009588179262529 3210358340257191134446897)
                ·
                  refine ⟨2407768755192893350835173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3210358340257191134446897 2407768755192893350835173)
                  ·
                    refine ⟨451456641598667503281595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2407768755192893350835173 451456641598667503281595)
                    ·
                      rfl

theorem cell23_2637626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 2, 4].length) (baseStart_2637626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637626 prefixEnd_2637626 := by exact prefixLift 2637626
  have htrace : WordTrace (prefixWord ++ tailWord_2637626) baseStart_2637626 baseEnd_2637626 := by
    simpa [prefixWord, tailWord_2637626, baseEnd_2637626] using wordTrace_append hprefix tailTrace_2637626
  have hstable : (prefixWord ++ tailWord_2637626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637626).length < 2 ^ (prefixWord ++ tailWord_2637626).sum := by decide
  have hdescent : baseEnd_2637626 < baseStart_2637626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637649 : List Nat := [1, 2, 2, 1, 5, 1, 1, 3, 1, 3, 3]
def baseStart_2637649 : Nat := 118140960795 + 2637649 * 2 ^ 59
def prefixEnd_2637649 : Nat := 4983230072969 + 3 ^ 40 * 2637649 * 2
def baseEnd_2637649 : Nat := 1354381734851055919857179

theorem tailTrace_2637649 : CollatzResearch.WordTrace tailWord_2637649 prefixEnd_2637649 1354381734851055919857179 := by
  unfold tailWord_2637649
  simp only [CollatzResearch.WordTrace]
  refine ⟨96202962421255622430196001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64135308280837081620130667 96202962421255622430196001)
  ·
    refine ⟨72152221815941716822647001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96202962421255622430196001 72152221815941716822647001)
    ·
      refine ⟨54114166361956287616985251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72152221815941716822647001 54114166361956287616985251)
      ·
        refine ⟨81171249542934431425477877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54114166361956287616985251 81171249542934431425477877)
        ·
          refine ⟨7609804644650102946138551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81171249542934431425477877 7609804644650102946138551)
          ·
            refine ⟨11414706966975154419207827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7609804644650102946138551 11414706966975154419207827)
            ·
              refine ⟨17122060450462731628811741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11414706966975154419207827 17122060450462731628811741)
              ·
                refine ⟨6420772668923524360804403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17122060450462731628811741 6420772668923524360804403)
                ·
                  refine ⟨9631159003385286541206605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6420772668923524360804403 9631159003385286541206605)
                  ·
                    refine ⟨3611684626269482452952477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9631159003385286541206605 3611684626269482452952477)
                    ·
                      refine ⟨1354381734851055919857179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3611684626269482452952477 1354381734851055919857179)
                      ·
                        rfl

theorem cell23_2637649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 3, 3].length) (baseStart_2637649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637649 prefixEnd_2637649 := by exact prefixLift 2637649
  have htrace : WordTrace (prefixWord ++ tailWord_2637649) baseStart_2637649 baseEnd_2637649 := by
    simpa [prefixWord, tailWord_2637649, baseEnd_2637649] using wordTrace_append hprefix tailTrace_2637649
  have hstable : (prefixWord ++ tailWord_2637649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637649).length < 2 ^ (prefixWord ++ tailWord_2637649).sum := by decide
  have hdescent : baseEnd_2637649 < baseStart_2637649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637666 : List Nat := [3, 3, 2, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_2637666 : Nat := 118140960795 + 2637666 * 2 ^ 59
def prefixEnd_2637666 : Nat := 4983230072969 + 3 ^ 40 * 2637666 * 2
def baseEnd_2637666 : Nat := 1354390464022182353344601

theorem tailTrace_2637666 : CollatzResearch.WordTrace tailWord_2637666 prefixEnd_2637666 1354390464022182353344601 := by
  unfold tailWord_2637666
  simp only [CollatzResearch.WordTrace]
  refine ⟨24050895615548508583391213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64135721641462689555709901 24050895615548508583391213)
  ·
    refine ⟨9019085855830690718771705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24050895615548508583391213 9019085855830690718771705)
    ·
      refine ⟨6764314391873018039078779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9019085855830690718771705 6764314391873018039078779)
      ·
        refine ⟨10146471587809527058618169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6764314391873018039078779 10146471587809527058618169)
        ·
          refine ⟨7609853690857145293963627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10146471587809527058618169 7609853690857145293963627)
          ·
            refine ⟨11414780536285717940945441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7609853690857145293963627 11414780536285717940945441)
            ·
              refine ⟨8561085402214288455709081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11414780536285717940945441 8561085402214288455709081)
              ·
                refine ⟨6420814051660716341781811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8561085402214288455709081 6420814051660716341781811)
                ·
                  refine ⟨9631221077491074512672717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6420814051660716341781811 9631221077491074512672717)
                  ·
                    refine ⟨3611707904059152942252269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9631221077491074512672717 3611707904059152942252269)
                    ·
                      refine ⟨1354390464022182353344601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3611707904059152942252269 1354390464022182353344601)
                      ·
                        rfl

theorem cell23_2637666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_2637666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637666 prefixEnd_2637666 := by exact prefixLift 2637666
  have htrace : WordTrace (prefixWord ++ tailWord_2637666) baseStart_2637666 baseEnd_2637666 := by
    simpa [prefixWord, tailWord_2637666, baseEnd_2637666] using wordTrace_append hprefix tailTrace_2637666
  have hstable : (prefixWord ++ tailWord_2637666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637666).length < 2 ^ (prefixWord ++ tailWord_2637666).sum := by decide
  have hdescent : baseEnd_2637666 < baseStart_2637666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637692 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 6, 1, 5]
def baseStart_2637692 : Nat := 118140960795 + 2637692 * 2 ^ 59
def prefixEnd_2637692 : Nat := 4983230072969 + 3 ^ 40 * 2637692 * 2
def baseEnd_2637692 : Nat := 1354403814519199251619481

theorem tailTrace_2637692 : CollatzResearch.WordTrace tailWord_2637692 prefixEnd_2637692 1354403814519199251619481 := by
  unfold tailWord_2637692
  simp only [CollatzResearch.WordTrace]
  refine ⟨48102265380049920387005665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64136353840066560516007553 48102265380049920387005665)
  ·
    refine ⟨36076699035037440290254249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48102265380049920387005665 36076699035037440290254249)
    ·
      refine ⟨27057524276278080217690687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36076699035037440290254249 27057524276278080217690687)
      ·
        refine ⟨40586286414417120326536031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27057524276278080217690687 40586286414417120326536031)
        ·
          refine ⟨60879429621625680489804047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40586286414417120326536031 60879429621625680489804047)
          ·
            refine ⟨91319144432438520734706071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60879429621625680489804047 91319144432438520734706071)
            ·
              refine ⟨136978716648657781102059107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91319144432438520734706071 136978716648657781102059107)
              ·
                refine ⟨205468074972986671653088661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136978716648657781102059107 205468074972986671653088661)
                ·
                  refine ⟨9631316014358750233738531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 205468074972986671653088661 9631316014358750233738531)
                  ·
                    refine ⟨14446974021538125350607797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9631316014358750233738531 14446974021538125350607797)
                    ·
                      refine ⟨1354403814519199251619481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14446974021538125350607797 1354403814519199251619481)
                      ·
                        rfl

theorem cell23_2637692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_2637692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637692 prefixEnd_2637692 := by exact prefixLift 2637692
  have htrace : WordTrace (prefixWord ++ tailWord_2637692) baseStart_2637692 baseEnd_2637692 := by
    simpa [prefixWord, tailWord_2637692, baseEnd_2637692] using wordTrace_append hprefix tailTrace_2637692
  have hstable : (prefixWord ++ tailWord_2637692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637692).length < 2 ^ (prefixWord ++ tailWord_2637692).sum := by decide
  have hdescent : baseEnd_2637692 < baseStart_2637692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637718 : List Nat := [5, 3, 1, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_2637718 : Nat := 118140960795 + 2637718 * 2 ^ 59
def prefixEnd_2637718 : Nat := 4983230072969 + 3 ^ 40 * 2637718 * 2
def baseEnd_2637718 : Nat := 1354417165016216149894363

theorem tailTrace_2637718 : CollatzResearch.WordTrace tailWord_2637718 prefixEnd_2637718 1354417165016216149894363 := by
  unfold tailWord_2637718
  simp only [CollatzResearch.WordTrace]
  refine ⟨6012842441125352950903613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64136986038670431476305205 6012842441125352950903613)
  ·
    refine ⟨2254815915422007356588855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6012842441125352950903613 2254815915422007356588855)
    ·
      refine ⟨3382223873133011034883283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2254815915422007356588855 3382223873133011034883283)
      ·
        refine ⟨5073335809699516552324925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3382223873133011034883283 5073335809699516552324925)
        ·
          refine ⟨1902500928637318707121847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5073335809699516552324925 1902500928637318707121847)
          ·
            refine ⟨2853751392955978060682771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1902500928637318707121847 2853751392955978060682771)
            ·
              refine ⟨4280627089433967091024157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2853751392955978060682771 4280627089433967091024157)
              ·
                refine ⟨1605235158537737659134059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4280627089433967091024157 1605235158537737659134059)
                ·
                  refine ⟨2407852737806606488701089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1605235158537737659134059 2407852737806606488701089)
                  ·
                    refine ⟨1805889553354954866525817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2407852737806606488701089 1805889553354954866525817)
                    ·
                      refine ⟨1354417165016216149894363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1805889553354954866525817 1354417165016216149894363)
                      ·
                        rfl

theorem cell23_2637718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_2637718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637718 prefixEnd_2637718 := by exact prefixLift 2637718
  have htrace : WordTrace (prefixWord ++ tailWord_2637718) baseStart_2637718 baseEnd_2637718 := by
    simpa [prefixWord, tailWord_2637718, baseEnd_2637718] using wordTrace_append hprefix tailTrace_2637718
  have hstable : (prefixWord ++ tailWord_2637718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637718).length < 2 ^ (prefixWord ++ tailWord_2637718).sum := by decide
  have hdescent : baseEnd_2637718 < baseStart_2637718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637757 : List Nat := [1, 4, 1, 2, 3, 3, 2, 1, 2, 2, 2]
def baseStart_2637757 : Nat := 118140960795 + 2637757 * 2 ^ 59
def prefixEnd_2637757 : Nat := 4983230072969 + 3 ^ 40 * 2637757 * 2
def baseEnd_2637757 : Nat := 1354437190761741497306683

theorem tailTrace_2637757 : CollatzResearch.WordTrace tailWord_2637757 prefixEnd_2637757 1354437190761741497306683 := by
  unfold tailWord_2637757
  simp only [CollatzResearch.WordTrace]
  refine ⟨96206901504864356875127525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64137934336576237916751683 96206901504864356875127525)
  ·
    refine ⟨18038794032162066914086411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96206901504864356875127525 18038794032162066914086411)
    ·
      refine ⟨27058191048243100371129617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18038794032162066914086411 27058191048243100371129617)
      ·
        refine ⟨20293643286182325278347213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27058191048243100371129617 20293643286182325278347213)
        ·
          refine ⟨7610116232318371979380205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20293643286182325278347213 7610116232318371979380205)
          ·
            refine ⟨2853793587119389492267577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7610116232318371979380205 2853793587119389492267577)
            ·
              refine ⟨2140345190339542119200683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2853793587119389492267577 2140345190339542119200683)
              ·
                refine ⟨3210517785509313178801025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2140345190339542119200683 3210517785509313178801025)
                ·
                  refine ⟨2407888339131984884100769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3210517785509313178801025 2407888339131984884100769)
                  ·
                    refine ⟨1805916254348988663075577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2407888339131984884100769 1805916254348988663075577)
                    ·
                      refine ⟨1354437190761741497306683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1805916254348988663075577 1354437190761741497306683)
                      ·
                        rfl

theorem cell23_2637757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_2637757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637757 prefixEnd_2637757 := by exact prefixLift 2637757
  have htrace : WordTrace (prefixWord ++ tailWord_2637757) baseStart_2637757 baseEnd_2637757 := by
    simpa [prefixWord, tailWord_2637757, baseEnd_2637757] using wordTrace_append hprefix tailTrace_2637757
  have hstable : (prefixWord ++ tailWord_2637757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637757).length < 2 ^ (prefixWord ++ tailWord_2637757).sum := by decide
  have hdescent : baseEnd_2637757 < baseStart_2637757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637796 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 2, 4, 2]
def baseStart_2637796 : Nat := 118140960795 + 2637796 * 2 ^ 59
def prefixEnd_2637796 : Nat := 4983230072969 + 3 ^ 40 * 2637796 * 2
def baseEnd_2637796 : Nat := 1354457216507266844719003

theorem tailTrace_2637796 : CollatzResearch.WordTrace tailWord_2637796 prefixEnd_2637796 1354457216507266844719003 := by
  unfold tailWord_2637796
  simp only [CollatzResearch.WordTrace]
  refine ⟨48104161975861533267898621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64138882634482044357198161 48104161975861533267898621)
  ·
    refine ⟨18039060740948074975461983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48104161975861533267898621 18039060740948074975461983)
    ·
      refine ⟨27058591111422112463192975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18039060740948074975461983 27058591111422112463192975)
      ·
        refine ⟨40587886667133168694789463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27058591111422112463192975 40587886667133168694789463)
        ·
          refine ⟨60881830000699753042184195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40587886667133168694789463 60881830000699753042184195)
          ·
            refine ⟨91322745001049629563276293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60881830000699753042184195 91322745001049629563276293)
            ·
              refine ⟨17123014687696805543114305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91322745001049629563276293 17123014687696805543114305)
              ·
                refine ⟨12842261015772604157335729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17123014687696805543114305 12842261015772604157335729)
                ·
                  refine ⟨9631695761829453118001797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12842261015772604157335729 9631695761829453118001797)
                  ·
                    refine ⟨1805942955343022459625337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9631695761829453118001797 1805942955343022459625337)
                    ·
                      refine ⟨1354457216507266844719003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1805942955343022459625337 1354457216507266844719003)
                      ·
                        rfl

theorem cell23_2637796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_2637796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637796 prefixEnd_2637796 := by exact prefixLift 2637796
  have htrace : WordTrace (prefixWord ++ tailWord_2637796) baseStart_2637796 baseEnd_2637796 := by
    simpa [prefixWord, tailWord_2637796, baseEnd_2637796] using wordTrace_append hprefix tailTrace_2637796
  have hstable : (prefixWord ++ tailWord_2637796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637796).length < 2 ^ (prefixWord ++ tailWord_2637796).sum := by decide
  have hdescent : baseEnd_2637796 < baseStart_2637796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637819 : List Nat := [1, 1, 1, 1, 1, 3, 6, 3, 6]
def baseStart_2637819 : Nat := 118140960795 + 2637819 * 2 ^ 59
def prefixEnd_2637819 : Nat := 4983230072969 + 3 ^ 40 * 2637819 * 2
def baseEnd_2637819 : Nat := 150496558506924472747933

theorem tailTrace_2637819 : CollatzResearch.WordTrace tailWord_2637819 prefixEnd_2637819 150496558506924472747933 := by
  unfold tailWord_2637819
  simp only [CollatzResearch.WordTrace]
  refine ⟨96209162830639741463884511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64139441887093160975923007 96209162830639741463884511)
  ·
    refine ⟨144313744245959612195826767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96209162830639741463884511 144313744245959612195826767)
    ·
      refine ⟨216470616368939418293740151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144313744245959612195826767 216470616368939418293740151)
      ·
        refine ⟨324705924553409127440610227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216470616368939418293740151 324705924553409127440610227)
        ·
          refine ⟨487058886830113691160915341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324705924553409127440610227 487058886830113691160915341)
          ·
            refine ⟨182647082561292634185343253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 487058886830113691160915341 182647082561292634185343253)
            ·
              refine ⟨8561581995060592227437965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 182647082561292634185343253 8561581995060592227437965)
              ·
                refine ⟨3210593248147722085289237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8561581995060592227437965 3210593248147722085289237)
                ·
                  refine ⟨150496558506924472747933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3210593248147722085289237 150496558506924472747933)
                  ·
                    rfl

theorem cell23_2637819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 6].length) (baseStart_2637819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637819 prefixEnd_2637819 := by exact prefixLift 2637819
  have htrace : WordTrace (prefixWord ++ tailWord_2637819) baseStart_2637819 baseEnd_2637819 := by
    simpa [prefixWord, tailWord_2637819, baseEnd_2637819] using wordTrace_append hprefix tailTrace_2637819
  have hstable : (prefixWord ++ tailWord_2637819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637819).length < 2 ^ (prefixWord ++ tailWord_2637819).sum := by decide
  have hdescent : baseEnd_2637819 < baseStart_2637819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637853 : List Nat := [1, 4, 2, 2, 2, 3, 1, 2, 6]
def baseStart_2637853 : Nat := 118140960795 + 2637853 * 2 ^ 59
def prefixEnd_2637853 : Nat := 4983230072969 + 3 ^ 40 * 2637853 * 2
def baseEnd_2637853 : Nat := 150498498322730346856249

theorem tailTrace_2637853 : CollatzResearch.WordTrace tailWord_2637853 prefixEnd_2637853 150498498322730346856249 := by
  unfold tailWord_2637853
  simp only [CollatzResearch.WordTrace]
  refine ⟨96210402912516565270622213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64140268608344376847081475 96210402912516565270622213)
  ·
    refine ⟨18039450546096855988241665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96210402912516565270622213 18039450546096855988241665)
    ·
      refine ⟨13529587909572641991181249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18039450546096855988241665 13529587909572641991181249)
      ·
        refine ⟨10147190932179481493385937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13529587909572641991181249 10147190932179481493385937)
        ·
          refine ⟨7610393199134611120039453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10147190932179481493385937 7610393199134611120039453)
          ·
            refine ⟨2853897449675479170014795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7610393199134611120039453 2853897449675479170014795)
            ·
              refine ⟨4280846174513218755022193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2853897449675479170014795 4280846174513218755022193)
              ·
                refine ⟨3210634630884914066266645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4280846174513218755022193 3210634630884914066266645)
                ·
                  refine ⟨150498498322730346856249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3210634630884914066266645 150498498322730346856249)
                  ·
                    rfl

theorem cell23_2637853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_2637853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637853 prefixEnd_2637853 := by exact prefixLift 2637853
  have htrace : WordTrace (prefixWord ++ tailWord_2637853) baseStart_2637853 baseEnd_2637853 := by
    simpa [prefixWord, tailWord_2637853, baseEnd_2637853] using wordTrace_append hprefix tailTrace_2637853
  have hstable : (prefixWord ++ tailWord_2637853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637853).length < 2 ^ (prefixWord ++ tailWord_2637853).sum := by decide
  have hdescent : baseEnd_2637853 < baseStart_2637853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637909 : List Nat := [1, 3, 2, 2, 1, 3, 11]
def baseStart_2637909 : Nat := 118140960795 + 2637909 * 2 ^ 59
def prefixEnd_2637909 : Nat := 4983230072969 + 3 ^ 40 * 2637909 * 2
def baseEnd_2637909 : Nat := 16722410368163270402543

theorem tailTrace_2637909 : CollatzResearch.WordTrace tailWord_2637909 prefixEnd_2637909 16722410368163270402543 := by
  unfold tailWord_2637909
  simp only [CollatzResearch.WordTrace]
  refine ⟨96212445400313686834660781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64141630266875791223107187 96212445400313686834660781)
  ·
    refine ⟨36079667025117632562997793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96212445400313686834660781 36079667025117632562997793)
    ·
      refine ⟨27059750268838224422248345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36079667025117632562997793 27059750268838224422248345)
      ·
        refine ⟨20294812701628668316686259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27059750268838224422248345 20294812701628668316686259)
        ·
          refine ⟨30442219052443002475029389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20294812701628668316686259 30442219052443002475029389)
          ·
            refine ⟨11415832144666125928136021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30442219052443002475029389 11415832144666125928136021)
            ·
              refine ⟨16722410368163270402543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11415832144666125928136021 16722410368163270402543)
              ·
                rfl

theorem cell23_2637909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 11].length) (baseStart_2637909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637909 prefixEnd_2637909 := by exact prefixLift 2637909
  have htrace : WordTrace (prefixWord ++ tailWord_2637909) baseStart_2637909 baseEnd_2637909 := by
    simpa [prefixWord, tailWord_2637909, baseEnd_2637909] using wordTrace_append hprefix tailTrace_2637909
  have hstable : (prefixWord ++ tailWord_2637909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637909).length < 2 ^ (prefixWord ++ tailWord_2637909).sum := by decide
  have hdescent : baseEnd_2637909 < baseStart_2637909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637916 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_2637916 : Nat := 118140960795 + 2637916 * 2 ^ 59
def prefixEnd_2637916 : Nat := 4983230072969 + 3 ^ 40 * 2637916 * 2
def baseEnd_2637916 : Nat := 1354518834185806375218451

theorem tailTrace_2637916 : CollatzResearch.WordTrace tailWord_2637916 prefixEnd_2637916 1354518834185806375218451 := by
  unfold tailWord_2637916
  simp only [CollatzResearch.WordTrace]
  refine ⟨48106350355644163515082801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64141800474192218020110401 48106350355644163515082801)
  ·
    refine ⟨36079762766733122636312101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48106350355644163515082801 36079762766733122636312101)
    ·
      refine ⟨6764955518762460494308519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36079762766733122636312101 6764955518762460494308519)
      ·
        refine ⟨10147433278143690741462779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6764955518762460494308519 10147433278143690741462779)
        ·
          refine ⟨15221149917215536112194169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10147433278143690741462779 15221149917215536112194169)
          ·
            refine ⟨11415862437911652084145627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15221149917215536112194169 11415862437911652084145627)
            ·
              refine ⟨17123793656867478126218441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11415862437911652084145627 17123793656867478126218441)
              ·
                refine ⟨12842845242650608594663831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17123793656867478126218441 12842845242650608594663831)
                ·
                  refine ⟨19264267863975912891995747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12842845242650608594663831 19264267863975912891995747)
                  ·
                    refine ⟨28896401795963869337993621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19264267863975912891995747 28896401795963869337993621)
                    ·
                      refine ⟨1354518834185806375218451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28896401795963869337993621 1354518834185806375218451)
                      ·
                        rfl

theorem cell23_2637916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_2637916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637916 prefixEnd_2637916 := by exact prefixLift 2637916
  have htrace : WordTrace (prefixWord ++ tailWord_2637916) baseStart_2637916 baseEnd_2637916 := by
    simpa [prefixWord, tailWord_2637916, baseEnd_2637916] using wordTrace_append hprefix tailTrace_2637916
  have hstable : (prefixWord ++ tailWord_2637916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637916).length < 2 ^ (prefixWord ++ tailWord_2637916).sum := by decide
  have hdescent : baseEnd_2637916 < baseStart_2637916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637920 : List Nat := [2, 1, 1, 3, 2, 3, 3, 1, 3, 2, 2]
def baseStart_2637920 : Nat := 118140960795 + 2637920 * 2 ^ 59
def prefixEnd_2637920 : Nat := 4983230072969 + 3 ^ 40 * 2637920 * 2
def baseEnd_2637920 : Nat := 1354520888108424359568433

theorem tailTrace_2637920 : CollatzResearch.WordTrace tailWord_2637920 prefixEnd_2637920 1354520888108424359568433 := by
  unfold tailWord_2637920
  simp only [CollatzResearch.WordTrace]
  refine ⟨48106423301636917856655607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64141897735515890475540809 48106423301636917856655607)
  ·
    refine ⟨72159634952455376784983411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48106423301636917856655607 72159634952455376784983411)
    ·
      refine ⟨108239452428683065177475117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72159634952455376784983411 108239452428683065177475117)
      ·
        refine ⟨40589794660756149441553169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108239452428683065177475117 40589794660756149441553169)
        ·
          refine ⟨30442345995567112081164877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40589794660756149441553169 30442345995567112081164877)
          ·
            refine ⟨11415879748337667030436829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30442345995567112081164877 11415879748337667030436829)
            ·
              refine ⟨4280954905626625136413811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11415879748337667030436829 4280954905626625136413811)
              ·
                refine ⟨6421432358439937704620717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4280954905626625136413811 6421432358439937704620717)
                ·
                  refine ⟨2408037134414976639232769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6421432358439937704620717 2408037134414976639232769)
                  ·
                    refine ⟨1806027850811232479424577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2408037134414976639232769 1806027850811232479424577)
                    ·
                      refine ⟨1354520888108424359568433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1806027850811232479424577 1354520888108424359568433)
                      ·
                        rfl

theorem cell23_2637920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_2637920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637920 prefixEnd_2637920 := by exact prefixLift 2637920
  have htrace : WordTrace (prefixWord ++ tailWord_2637920) baseStart_2637920 baseEnd_2637920 := by
    simpa [prefixWord, tailWord_2637920, baseEnd_2637920] using wordTrace_append hprefix tailTrace_2637920
  have hstable : (prefixWord ++ tailWord_2637920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637920).length < 2 ^ (prefixWord ++ tailWord_2637920).sum := by decide
  have hdescent : baseEnd_2637920 < baseStart_2637920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637929 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 2, 2, 6]
def baseStart_2637929 : Nat := 118140960795 + 2637929 * 2 ^ 59
def prefixEnd_2637929 : Nat := 4983230072969 + 3 ^ 40 * 2637929 * 2
def baseEnd_2637929 : Nat := 1354525509434314824355891

theorem tailTrace_2637929 : CollatzResearch.WordTrace tailWord_2637929 prefixEnd_2637929 1354525509434314824355891 := by
  unfold tailWord_2637929
  simp only [CollatzResearch.WordTrace]
  refine ⟨96213174860241230250388841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64142116573494153500259227 96213174860241230250388841)
  ·
    refine ⟨72159881145180922687791631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96213174860241230250388841 72159881145180922687791631)
    ·
      refine ⟨108239821717771384031687447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72159881145180922687791631 108239821717771384031687447)
      ·
        refine ⟨162359732576657076047531171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108239821717771384031687447 162359732576657076047531171)
        ·
          refine ⟨243539598864985614071296757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162359732576657076047531171 243539598864985614071296757)
          ·
            refine ⟨22831837393592401319184071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 243539598864985614071296757 22831837393592401319184071)
            ·
              refine ⟨34247756090388601978776107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22831837393592401319184071 34247756090388601978776107)
              ·
                refine ⟨51371634135582902968164161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34247756090388601978776107 51371634135582902968164161)
                ·
                  refine ⟨38528725601687177226123121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51371634135582902968164161 38528725601687177226123121)
                  ·
                    refine ⟨28896544201265382919592341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38528725601687177226123121 28896544201265382919592341)
                    ·
                      refine ⟨1354525509434314824355891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28896544201265382919592341 1354525509434314824355891)
                      ·
                        rfl

theorem cell23_2637929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_2637929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637929 prefixEnd_2637929 := by exact prefixLift 2637929
  have htrace : WordTrace (prefixWord ++ tailWord_2637929) baseStart_2637929 baseEnd_2637929 := by
    simpa [prefixWord, tailWord_2637929, baseEnd_2637929] using wordTrace_append hprefix tailTrace_2637929
  have hstable : (prefixWord ++ tailWord_2637929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637929).length < 2 ^ (prefixWord ++ tailWord_2637929).sum := by decide
  have hdescent : baseEnd_2637929 < baseStart_2637929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637930 : List Nat := [3, 1, 3, 2, 3, 1, 1, 3, 2, 4]
def baseStart_2637930 : Nat := 118140960795 + 2637930 * 2 ^ 59
def prefixEnd_2637930 : Nat := 4983230072969 + 3 ^ 40 * 2637930 * 2
def baseEnd_2637930 : Nat := 451508674304989773481129

theorem tailTrace_2637930 : CollatzResearch.WordTrace tailWord_2637930 prefixEnd_2637930 451508674304989773481129 := by
  unfold tailWord_2637930
  simp only [CollatzResearch.WordTrace]
  refine ⟨24053302833309401855293811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64142140888825071614116829 24053302833309401855293811)
  ·
    refine ⟨36079954249964102782940717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24053302833309401855293811 36079954249964102782940717)
    ·
      refine ⟨13529982843736538543602769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36079954249964102782940717 13529982843736538543602769)
      ·
        refine ⟨10147487132802403907702077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13529982843736538543602769 10147487132802403907702077)
        ·
          refine ⟨3805307674800901465388279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10147487132802403907702077 3805307674800901465388279)
          ·
            refine ⟨5707961512201352198082419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3805307674800901465388279 5707961512201352198082419)
            ·
              refine ⟨8561942268302028297123629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5707961512201352198082419 8561942268302028297123629)
              ·
                refine ⟨3210728350613260611421361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8561942268302028297123629 3210728350613260611421361)
                ·
                  refine ⟨2408046262959945458566021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3210728350613260611421361 2408046262959945458566021)
                  ·
                    refine ⟨451508674304989773481129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2408046262959945458566021 451508674304989773481129)
                    ·
                      rfl

theorem cell23_2637930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_2637930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637930 prefixEnd_2637930 := by exact prefixLift 2637930
  have htrace : WordTrace (prefixWord ++ tailWord_2637930) baseStart_2637930 baseEnd_2637930 := by
    simpa [prefixWord, tailWord_2637930, baseEnd_2637930] using wordTrace_append hprefix tailTrace_2637930
  have hstable : (prefixWord ++ tailWord_2637930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637930).length < 2 ^ (prefixWord ++ tailWord_2637930).sum := by decide
  have hdescent : baseEnd_2637930 < baseStart_2637930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2637969 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 5, 8]
def baseStart_2637969 : Nat := 118140960795 + 2637969 * 2 ^ 59
def prefixEnd_2637969 : Nat := 4983230072969 + 3 ^ 40 * 2637969 * 2
def baseEnd_2637969 : Nat := 451515349553498222618569

theorem tailTrace_2637969 : CollatzResearch.WordTrace tailWord_2637969 prefixEnd_2637969 451515349553498222618569 := by
  unfold tailWord_2637969
  simp only [CollatzResearch.WordTrace]
  refine ⟨96214633780096317081844961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64143089186730878054563307 96214633780096317081844961)
  ·
    refine ⟨72160975335072237811383721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96214633780096317081844961 72160975335072237811383721)
    ·
      refine ⟨54120731501304178358537791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72160975335072237811383721 54120731501304178358537791)
      ·
        refine ⟨81181097251956267537806687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54120731501304178358537791 81181097251956267537806687)
        ·
          refine ⟨121771645877934401306710031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81181097251956267537806687 121771645877934401306710031)
          ·
            refine ⟨182657468816901601960065047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121771645877934401306710031 182657468816901601960065047)
            ·
              refine ⟨273986203225352402940097571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182657468816901601960065047 273986203225352402940097571)
              ·
                refine ⟨410979304838028604410146357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273986203225352402940097571 410979304838028604410146357)
                ·
                  refine ⟨38529309828565181663451221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 410979304838028604410146357 38529309828565181663451221)
                  ·
                    refine ⟨451515349553498222618569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38529309828565181663451221 451515349553498222618569)
                    ·
                      rfl

theorem cell23_2637969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_2637969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2637969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2637969 prefixEnd_2637969 := by exact prefixLift 2637969
  have htrace : WordTrace (prefixWord ++ tailWord_2637969) baseStart_2637969 baseEnd_2637969 := by
    simpa [prefixWord, tailWord_2637969, baseEnd_2637969] using wordTrace_append hprefix tailTrace_2637969
  have hstable : (prefixWord ++ tailWord_2637969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2637969).length < 2 ^ (prefixWord ++ tailWord_2637969).sum := by decide
  have hdescent : baseEnd_2637969 < baseStart_2637969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2637969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638033 : List Nat := [1, 2, 2, 1, 2, 2, 4, 4, 5]
def baseStart_2638033 : Nat := 118140960795 + 2638033 * 2 ^ 59
def prefixEnd_2638033 : Nat := 4983230072969 + 3 ^ 40 * 2638033 * 2
def baseEnd_2638033 : Nat := 150508767935820268606157

theorem tailTrace_2638033 : CollatzResearch.WordTrace tailWord_2638033 prefixEnd_2638033 150508767935820268606157 := by
  unfold tailWord_2638033
  simp only [CollatzResearch.WordTrace]
  refine ⟨96216968051864456012174753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64144645367909637341449835 96216968051864456012174753)
  ·
    refine ⟨72162726038898342009131065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96216968051864456012174753 72162726038898342009131065)
    ·
      refine ⟨54122044529173756506848299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72162726038898342009131065 54122044529173756506848299)
      ·
        refine ⟨81183066793760634760272449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54122044529173756506848299 81183066793760634760272449)
        ·
          refine ⟨60887300095320476070204337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81183066793760634760272449 60887300095320476070204337)
          ·
            refine ⟨45665475071490357052653253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60887300095320476070204337 45665475071490357052653253)
            ·
              refine ⟨8562276575904441947372485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45665475071490357052653253 8562276575904441947372485)
              ·
                refine ⟨1605426857982082865132341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8562276575904441947372485 1605426857982082865132341)
                ·
                  refine ⟨150508767935820268606157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1605426857982082865132341 150508767935820268606157)
                  ·
                    rfl

theorem cell23_2638033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 5].length) (baseStart_2638033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638033 prefixEnd_2638033 := by exact prefixLift 2638033
  have htrace : WordTrace (prefixWord ++ tailWord_2638033) baseStart_2638033 baseEnd_2638033 := by
    simpa [prefixWord, tailWord_2638033, baseEnd_2638033] using wordTrace_append hprefix tailTrace_2638033
  have hstable : (prefixWord ++ tailWord_2638033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638033).length < 2 ^ (prefixWord ++ tailWord_2638033).sum := by decide
  have hdescent : baseEnd_2638033 < baseStart_2638033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638083 : List Nat := [1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 4]
def baseStart_2638083 : Nat := 118140960795 + 2638083 * 2 ^ 59
def prefixEnd_2638083 : Nat := 4983230072969 + 3 ^ 40 * 2638083 * 2
def baseEnd_2638083 : Nat := 1354604585455107221830183

theorem tailTrace_2638083 : CollatzResearch.WordTrace tailWord_2638083 prefixEnd_2638083 1354604585455107221830183 := by
  unfold tailWord_2638083
  simp only [CollatzResearch.WordTrace]
  refine ⟨96218791701683314551494903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64145861134455543034329935 96218791701683314551494903)
  ·
    refine ⟨144328187552524971827242355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96218791701683314551494903 144328187552524971827242355)
    ·
      refine ⟨216492281328787457740863533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144328187552524971827242355 216492281328787457740863533)
      ·
        refine ⟨81184605498295296652823825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216492281328787457740863533 81184605498295296652823825)
        ·
          refine ⟨60888454123721472489617869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81184605498295296652823825 60888454123721472489617869)
          ·
            refine ⟨22833170296395552183606701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60888454123721472489617869 22833170296395552183606701)
            ·
              refine ⟨8562438861148332068852513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22833170296395552183606701 8562438861148332068852513)
              ·
                refine ⟨6421829145861249051639385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8562438861148332068852513 6421829145861249051639385)
                ·
                  refine ⟨4816371859395936788729539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6421829145861249051639385 4816371859395936788729539)
                  ·
                    refine ⟨7224557789093905183094309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4816371859395936788729539 7224557789093905183094309)
                    ·
                      refine ⟨1354604585455107221830183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7224557789093905183094309 1354604585455107221830183)
                      ·
                        rfl

theorem cell23_2638083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_2638083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638083 prefixEnd_2638083 := by exact prefixLift 2638083
  have htrace : WordTrace (prefixWord ++ tailWord_2638083) baseStart_2638083 baseEnd_2638083 := by
    simpa [prefixWord, tailWord_2638083, baseEnd_2638083] using wordTrace_append hprefix tailTrace_2638083
  have hstable : (prefixWord ++ tailWord_2638083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638083).length < 2 ^ (prefixWord ++ tailWord_2638083).sum := by decide
  have hdescent : baseEnd_2638083 < baseStart_2638083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638184 : List Nat := [2, 1, 4, 2, 2, 1, 1, 5, 1, 1, 3]
def baseStart_2638184 : Nat := 118140960795 + 2638184 * 2 ^ 59
def prefixEnd_2638184 : Nat := 4983230072969 + 3 ^ 40 * 2638184 * 2
def baseEnd_2638184 : Nat := 1354656447001211326667219

theorem tailTrace_2638184 : CollatzResearch.WordTrace tailWord_2638184 prefixEnd_2638184 1354656447001211326667219 := by
  unfold tailWord_2638184
  simp only [CollatzResearch.WordTrace]
  refine ⟨48111237737158704400460803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64148316982878272533947737 48111237737158704400460803)
  ·
    refine ⟨72166856605738056600691205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48111237737158704400460803 72166856605738056600691205)
    ·
      refine ⟨13531285613575885612629601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72166856605738056600691205 13531285613575885612629601)
      ·
        refine ⟨10148464210181914209472201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13531285613575885612629601 10148464210181914209472201)
        ·
          refine ⟨7611348157636435657104151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10148464210181914209472201 7611348157636435657104151)
          ·
            refine ⟨11417022236454653485656227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7611348157636435657104151 11417022236454653485656227)
            ·
              refine ⟨17125533354681980228484341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11417022236454653485656227 17125533354681980228484341)
              ·
                refine ⟨1605518752001435646420407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17125533354681980228484341 1605518752001435646420407)
                ·
                  refine ⟨2408278128002153469630611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1605518752001435646420407 2408278128002153469630611)
                  ·
                    refine ⟨3612417192003230204445917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2408278128002153469630611 3612417192003230204445917)
                    ·
                      refine ⟨1354656447001211326667219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3612417192003230204445917 1354656447001211326667219)
                      ·
                        rfl

theorem cell23_2638184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_2638184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638184 prefixEnd_2638184 := by exact prefixLift 2638184
  have htrace : WordTrace (prefixWord ++ tailWord_2638184) baseStart_2638184 baseEnd_2638184 := by
    simpa [prefixWord, tailWord_2638184, baseEnd_2638184] using wordTrace_append hprefix tailTrace_2638184
  have hstable : (prefixWord ++ tailWord_2638184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638184).length < 2 ^ (prefixWord ++ tailWord_2638184).sum := by decide
  have hdescent : baseEnd_2638184 < baseStart_2638184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638193 : List Nat := [1, 2, 2, 2, 1, 2, 1, 5, 1, 1, 5]
def baseStart_2638193 : Nat := 118140960795 + 2638193 * 2 ^ 59
def prefixEnd_2638193 : Nat := 4983230072969 + 3 ^ 40 * 2638193 * 2
def baseEnd_2638193 : Nat := 1354661068327101791454677

theorem tailTrace_2638193 : CollatzResearch.WordTrace tailWord_2638193 prefixEnd_2638193 1354661068327101791454677 := by
  unfold tailWord_2638193
  simp only [CollatzResearch.WordTrace]
  refine ⟨96222803731284803337999233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64148535820856535558666155 96222803731284803337999233)
  ·
    refine ⟨72167102798463602503499425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96222803731284803337999233 72167102798463602503499425)
    ·
      refine ⟨54125327098847701877624569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72167102798463602503499425 54125327098847701877624569)
      ·
        refine ⟨40593995324135776408218427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54125327098847701877624569 40593995324135776408218427)
        ·
          refine ⟨60890992986203664612327641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40593995324135776408218427 60890992986203664612327641)
          ·
            refine ⟨45668244739652748459245731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60890992986203664612327641 45668244739652748459245731)
            ·
              refine ⟨68502367109479122688868597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45668244739652748459245731 68502367109479122688868597)
              ·
                refine ⟨6422096916513667752081431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68502367109479122688868597 6422096916513667752081431)
                ·
                  refine ⟨9633145374770501628122147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6422096916513667752081431 9633145374770501628122147)
                  ·
                    refine ⟨14449718062155752442183221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9633145374770501628122147 14449718062155752442183221)
                    ·
                      refine ⟨1354661068327101791454677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14449718062155752442183221 1354661068327101791454677)
                      ·
                        rfl

theorem cell23_2638193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_2638193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638193 prefixEnd_2638193 := by exact prefixLift 2638193
  have htrace : WordTrace (prefixWord ++ tailWord_2638193) baseStart_2638193 baseEnd_2638193 := by
    simpa [prefixWord, tailWord_2638193, baseEnd_2638193] using wordTrace_append hprefix tailTrace_2638193
  have hstable : (prefixWord ++ tailWord_2638193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638193).length < 2 ^ (prefixWord ++ tailWord_2638193).sum := by decide
  have hdescent : baseEnd_2638193 < baseStart_2638193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638220 : List Nat := [2, 2, 1, 2, 1, 4, 3, 1, 1, 2, 4]
def baseStart_2638220 : Nat := 118140960795 + 2638220 * 2 ^ 59
def prefixEnd_2638220 : Nat := 4983230072969 + 3 ^ 40 * 2638220 * 2
def baseEnd_2638220 : Nat := 1354674932304773185817053

theorem tailTrace_2638220 : CollatzResearch.WordTrace tailWord_2638220 prefixEnd_2638220 1354674932304773185817053 := by
  unfold tailWord_2638220
  simp only [CollatzResearch.WordTrace]
  refine ⟨48111894251093493474616057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64149192334791324632821409 48111894251093493474616057)
  ·
    refine ⟨36083920688320120105962043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48111894251093493474616057 36083920688320120105962043)
    ·
      refine ⟨54125881032480180158943065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36083920688320120105962043 54125881032480180158943065)
      ·
        refine ⟨40594410774360135119207299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54125881032480180158943065 40594410774360135119207299)
        ·
          refine ⟨60891616161540202678810949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40594410774360135119207299 60891616161540202678810949)
          ·
            refine ⟨11417178030288788002277053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60891616161540202678810949 11417178030288788002277053)
            ·
              refine ⟨4281441761358295500853895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11417178030288788002277053 4281441761358295500853895)
              ·
                refine ⟨6422162642037443251280843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4281441761358295500853895 6422162642037443251280843)
                ·
                  refine ⟨9633243963056164876921265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6422162642037443251280843 9633243963056164876921265)
                  ·
                    refine ⟨7224932972292123657690949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9633243963056164876921265 7224932972292123657690949)
                    ·
                      refine ⟨1354674932304773185817053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7224932972292123657690949 1354674932304773185817053)
                      ·
                        rfl

theorem cell23_2638220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_2638220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638220 prefixEnd_2638220 := by exact prefixLift 2638220
  have htrace : WordTrace (prefixWord ++ tailWord_2638220) baseStart_2638220 baseEnd_2638220 := by
    simpa [prefixWord, tailWord_2638220, baseEnd_2638220] using wordTrace_append hprefix tailTrace_2638220
  have hstable : (prefixWord ++ tailWord_2638220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638220).length < 2 ^ (prefixWord ++ tailWord_2638220).sum := by decide
  have hdescent : baseEnd_2638220 < baseStart_2638220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638257 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 4, 1, 3]
def baseStart_2638257 : Nat := 118140960795 + 2638257 * 2 ^ 59
def prefixEnd_2638257 : Nat := 4983230072969 + 3 ^ 40 * 2638257 * 2
def baseEnd_2638257 : Nat := 1354693931088989541054383

theorem tailTrace_2638257 : CollatzResearch.WordTrace tailWord_2638257 prefixEnd_2638257 1354693931088989541054383 := by
  unfold tailWord_2638257
  simp only [CollatzResearch.WordTrace]
  refine ⟨96225138003052942268329025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64150092002035294845552683 96225138003052942268329025)
  ·
    refine ⟨72168853502289706701246769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96225138003052942268329025 72168853502289706701246769)
    ·
      refine ⟨54126640126717280025935077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72168853502289706701246769 54126640126717280025935077)
      ·
        refine ⟨10148745023759490004862827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54126640126717280025935077 10148745023759490004862827)
        ·
          refine ⟨15223117535639235007294241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10148745023759490004862827 15223117535639235007294241)
          ·
            refine ⟨11417338151729426255470681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15223117535639235007294241 11417338151729426255470681)
            ·
              refine ⟨8563003613797069691603011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11417338151729426255470681 8563003613797069691603011)
              ·
                refine ⟨12844505420695604537404517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8563003613797069691603011 12844505420695604537404517)
                ·
                  refine ⟨2408344766380425850763347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12844505420695604537404517 2408344766380425850763347)
                  ·
                    refine ⟨3612517149570638776145021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2408344766380425850763347 3612517149570638776145021)
                    ·
                      refine ⟨1354693931088989541054383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3612517149570638776145021 1354693931088989541054383)
                      ·
                        rfl

theorem cell23_2638257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_2638257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638257 prefixEnd_2638257 := by exact prefixLift 2638257
  have htrace : WordTrace (prefixWord ++ tailWord_2638257) baseStart_2638257 baseEnd_2638257 := by
    simpa [prefixWord, tailWord_2638257, baseEnd_2638257] using wordTrace_append hprefix tailTrace_2638257
  have hstable : (prefixWord ++ tailWord_2638257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638257).length < 2 ^ (prefixWord ++ tailWord_2638257).sum := by decide
  have hdescent : baseEnd_2638257 < baseStart_2638257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638284 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 3, 3, 2]
def baseStart_2638284 : Nat := 118140960795 + 2638284 * 2 ^ 59
def prefixEnd_2638284 : Nat := 4983230072969 + 3 ^ 40 * 2638284 * 2
def baseEnd_2638284 : Nat := 1354707795066660935416759

theorem tailTrace_2638284 : CollatzResearch.WordTrace tailWord_2638284 prefixEnd_2638284 1354707795066660935416759 := by
  unfold tailWord_2638284
  simp only [CollatzResearch.WordTrace]
  refine ⟨48113061386977562939780953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64150748515970083919707937 48113061386977562939780953)
  ·
    refine ⟨36084796040233172204835715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48113061386977562939780953 36084796040233172204835715)
    ·
      refine ⟨54127194060349758307253573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36084796040233172204835715 54127194060349758307253573)
      ·
        refine ⟨10148848886315579682610045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54127194060349758307253573 10148848886315579682610045)
        ·
          refine ⟨3805818332368342380978767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10148848886315579682610045 3805818332368342380978767)
          ·
            refine ⟨5708727498552513571468151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3805818332368342380978767 5708727498552513571468151)
            ·
              refine ⟨8563091247828770357202227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5708727498552513571468151 8563091247828770357202227)
              ·
                refine ⟨12844636871743155535803341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8563091247828770357202227 12844636871743155535803341)
                ·
                  refine ⟨4816738826903683325926253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12844636871743155535803341 4816738826903683325926253)
                  ·
                    refine ⟨1806277060088881247222345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4816738826903683325926253 1806277060088881247222345)
                    ·
                      refine ⟨1354707795066660935416759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1806277060088881247222345 1354707795066660935416759)
                      ·
                        rfl

theorem cell23_2638284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_2638284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638284 prefixEnd_2638284 := by exact prefixLift 2638284
  have htrace : WordTrace (prefixWord ++ tailWord_2638284) baseStart_2638284 baseEnd_2638284 := by
    simpa [prefixWord, tailWord_2638284, baseEnd_2638284] using wordTrace_append hprefix tailTrace_2638284
  have hstable : (prefixWord ++ tailWord_2638284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638284).length < 2 ^ (prefixWord ++ tailWord_2638284).sum := by decide
  have hdescent : baseEnd_2638284 < baseStart_2638284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638297 : List Nat := [1, 2, 1, 2, 4, 1, 3, 2, 1, 4, 2]
def baseStart_2638297 : Nat := 118140960795 + 2638297 * 2 ^ 59
def prefixEnd_2638297 : Nat := 4983230072969 + 3 ^ 40 * 2638297 * 2
def baseEnd_2638297 : Nat := 1354714470315169384554199

theorem tailTrace_2638297 : CollatzResearch.WordTrace tailWord_2638297 prefixEnd_2638297 1354714470315169384554199 := by
  unfold tailWord_2638297
  simp only [CollatzResearch.WordTrace]
  refine ⟨96226596922908029099785145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64151064615272019399856763 96226596922908029099785145)
  ·
    refine ⟨72169947692181021824838859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96226596922908029099785145 72169947692181021824838859)
    ·
      refine ⟨108254921538271532737258289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72169947692181021824838859 108254921538271532737258289)
      ·
        refine ⟨81191191153703649552943717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108254921538271532737258289 81191191153703649552943717)
        ·
          refine ⟨15223348341319434291176947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81191191153703649552943717 15223348341319434291176947)
          ·
            refine ⟨22835022511979151436765421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15223348341319434291176947 22835022511979151436765421)
            ·
              refine ⟨8563133441992181788787033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22835022511979151436765421 8563133441992181788787033)
              ·
                refine ⟨6422350081494136341590275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8563133441992181788787033 6422350081494136341590275)
                ·
                  refine ⟨9633525122241204512385413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6422350081494136341590275 9633525122241204512385413)
                  ·
                    refine ⟨1806285960420225846072265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9633525122241204512385413 1806285960420225846072265)
                    ·
                      refine ⟨1354714470315169384554199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1806285960420225846072265 1354714470315169384554199)
                      ·
                        rfl

theorem cell23_2638297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 4, 2].length) (baseStart_2638297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638297 prefixEnd_2638297 := by exact prefixLift 2638297
  have htrace : WordTrace (prefixWord ++ tailWord_2638297) baseStart_2638297 baseEnd_2638297 := by
    simpa [prefixWord, tailWord_2638297, baseEnd_2638297] using wordTrace_append hprefix tailTrace_2638297
  have hstable : (prefixWord ++ tailWord_2638297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638297).length < 2 ^ (prefixWord ++ tailWord_2638297).sum := by decide
  have hdescent : baseEnd_2638297 < baseStart_2638297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638301 : List Nat := [1, 4, 3, 1, 1, 1, 5, 1, 1, 3, 2]
def baseStart_2638301 : Nat := 118140960795 + 2638301 * 2 ^ 59
def prefixEnd_2638301 : Nat := 4983230072969 + 3 ^ 40 * 2638301 * 2
def baseEnd_2638301 : Nat := 1354716524237787368904181

theorem tailTrace_2638301 : CollatzResearch.WordTrace tailWord_2638301 prefixEnd_2638301 1354716524237787368904181 := by
  unfold tailWord_2638301
  simp only [CollatzResearch.WordTrace]
  refine ⟨96226742814893537782930757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64151161876595691855287171 96226742814893537782930757)
  ·
    refine ⟨18042514277792538334299517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96226742814893537782930757 18042514277792538334299517)
    ·
      refine ⟨6765942854172201875362319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18042514277792538334299517 6765942854172201875362319)
      ·
        refine ⟨10148914281258302813043479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6765942854172201875362319 10148914281258302813043479)
        ·
          refine ⟨15223371421887454219565219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10148914281258302813043479 15223371421887454219565219)
          ·
            refine ⟨22835057132831181329347829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15223371421887454219565219 22835057132831181329347829)
            ·
              refine ⟨2140786606202923249626359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22835057132831181329347829 2140786606202923249626359)
              ·
                refine ⟨3211179909304384874439539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2140786606202923249626359 3211179909304384874439539)
                ·
                  refine ⟨4816769863956577311659309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3211179909304384874439539 4816769863956577311659309)
                  ·
                    refine ⟨1806288698983716491872241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4816769863956577311659309 1806288698983716491872241)
                    ·
                      refine ⟨1354716524237787368904181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1806288698983716491872241 1354716524237787368904181)
                      ·
                        rfl

theorem cell23_2638301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_2638301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638301 prefixEnd_2638301 := by exact prefixLift 2638301
  have htrace : WordTrace (prefixWord ++ tailWord_2638301) baseStart_2638301 baseEnd_2638301 := by
    simpa [prefixWord, tailWord_2638301, baseEnd_2638301] using wordTrace_append hprefix tailTrace_2638301
  have hstable : (prefixWord ++ tailWord_2638301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638301).length < 2 ^ (prefixWord ++ tailWord_2638301).sum := by decide
  have hdescent : baseEnd_2638301 < baseStart_2638301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638317 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 2, 4, 3]
def baseStart_2638317 : Nat := 118140960795 + 2638317 * 2 ^ 59
def prefixEnd_2638317 : Nat := 4983230072969 + 3 ^ 40 * 2638317 * 2
def baseEnd_2638317 : Nat := 1354724739928259306304107

theorem tailTrace_2638317 : CollatzResearch.WordTrace tailWord_2638317 prefixEnd_2638317 1354724739928259306304107 := by
  unfold tailWord_2638317
  simp only [CollatzResearch.WordTrace]
  refine ⟨96227326382835572515513205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64151550921890381677008803 96227326382835572515513205)
  ·
    refine ⟨9021311848390834923329363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96227326382835572515513205 9021311848390834923329363)
    ·
      refine ⟨13531967772586252384994045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9021311848390834923329363 13531967772586252384994045)
      ·
        refine ⟨5074487914719844644372767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13531967772586252384994045 5074487914719844644372767)
        ·
          refine ⟨7611731872079766966559151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5074487914719844644372767 7611731872079766966559151)
          ·
            refine ⟨11417597808119650449838727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7611731872079766966559151 11417597808119650449838727)
            ·
              refine ⟨17126396712179475674758091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11417597808119650449838727 17126396712179475674758091)
              ·
                refine ⟨25689595068269213512137137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17126396712179475674758091 25689595068269213512137137)
                ·
                  refine ⟨19267196301201910134102853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25689595068269213512137137 19267196301201910134102853)
                  ·
                    refine ⟨3612599306475358150144285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19267196301201910134102853 3612599306475358150144285)
                    ·
                      refine ⟨1354724739928259306304107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3612599306475358150144285 1354724739928259306304107)
                      ·
                        rfl

theorem cell23_2638317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_2638317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638317 prefixEnd_2638317 := by exact prefixLift 2638317
  have htrace : WordTrace (prefixWord ++ tailWord_2638317) baseStart_2638317 baseEnd_2638317 := by
    simpa [prefixWord, tailWord_2638317, baseEnd_2638317] using wordTrace_append hprefix tailTrace_2638317
  have hstable : (prefixWord ++ tailWord_2638317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638317).length < 2 ^ (prefixWord ++ tailWord_2638317).sum := by decide
  have hdescent : baseEnd_2638317 < baseStart_2638317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638363 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 3, 10]
def baseStart_2638363 : Nat := 118140960795 + 2638363 * 2 ^ 59
def prefixEnd_2638363 : Nat := 4983230072969 + 3 ^ 40 * 2638363 * 2
def baseEnd_2638363 : Nat := 451582786679455375442965

theorem tailTrace_2638363 : CollatzResearch.WordTrace tailWord_2638363 prefixEnd_2638363 451582786679455375442965 := by
  unfold tailWord_2638363
  simp only [CollatzResearch.WordTrace]
  refine ⟨96229004140668922371687743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64152669427112614914458495 96229004140668922371687743)
  ·
    refine ⟨144343506211003383557531615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96229004140668922371687743 144343506211003383557531615)
    ·
      refine ⟨216515259316505075336297423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144343506211003383557531615 216515259316505075336297423)
      ·
        refine ⟨324772888974757613004446135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216515259316505075336297423 324772888974757613004446135)
        ·
          refine ⟨487159333462136419506669203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324772888974757613004446135 487159333462136419506669203)
          ·
            refine ⟨730739000193204629260003805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487159333462136419506669203 730739000193204629260003805)
            ·
              refine ⟨274027125072451735972501427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 730739000193204629260003805 274027125072451735972501427)
              ·
                refine ⟨411040687608677603958752141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274027125072451735972501427 411040687608677603958752141)
                ·
                  refine ⟨154140257853254101484532053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 411040687608677603958752141 154140257853254101484532053)
                  ·
                    refine ⟨451582786679455375442965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 154140257853254101484532053 451582786679455375442965)
                    ·
                      rfl

theorem cell23_2638363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 10].length) (baseStart_2638363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638363 prefixEnd_2638363 := by exact prefixLift 2638363
  have htrace : WordTrace (prefixWord ++ tailWord_2638363) baseStart_2638363 baseEnd_2638363 := by
    simpa [prefixWord, tailWord_2638363, baseEnd_2638363] using wordTrace_append hprefix tailTrace_2638363
  have hstable : (prefixWord ++ tailWord_2638363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638363).length < 2 ^ (prefixWord ++ tailWord_2638363).sum := by decide
  have hdescent : baseEnd_2638363 < baseStart_2638363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638387 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 2, 4, 2]
def baseStart_2638387 : Nat := 118140960795 + 2638387 * 2 ^ 59
def prefixEnd_2638387 : Nat := 4983230072969 + 3 ^ 40 * 2638387 * 2
def baseEnd_2638387 : Nat := 1354760683574074032428785

theorem tailTrace_2638387 : CollatzResearch.WordTrace tailWord_2638387 prefixEnd_2638387 1354760683574074032428785 := by
  unfold tailWord_2638387
  simp only [CollatzResearch.WordTrace]
  refine ⟨96229879492581974470561415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64153252995054649647040943 96229879492581974470561415)
  ·
    refine ⟨144344819238872961705842123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96229879492581974470561415 144344819238872961705842123)
    ·
      refine ⟨216517228858309442558763185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144344819238872961705842123 216517228858309442558763185)
      ·
        refine ⟨162387921643732081919072389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216517228858309442558763185 162387921643732081919072389)
        ·
          refine ⟨30447735308199765359826073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162387921643732081919072389 30447735308199765359826073)
          ·
            refine ⟨22835801481149824019869555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30447735308199765359826073 22835801481149824019869555)
            ·
              refine ⟨34253702221724736029804333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22835801481149824019869555 34253702221724736029804333)
              ·
                refine ⟨12845138333146776011176625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34253702221724736029804333 12845138333146776011176625)
                ·
                  refine ⟨9633853749860082008382469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12845138333146776011176625 9633853749860082008382469)
                  ·
                    refine ⟨1806347578098765376571713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9633853749860082008382469 1806347578098765376571713)
                    ·
                      refine ⟨1354760683574074032428785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1806347578098765376571713 1354760683574074032428785)
                      ·
                        rfl

theorem cell23_2638387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 4, 2].length) (baseStart_2638387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638387 prefixEnd_2638387 := by exact prefixLift 2638387
  have htrace : WordTrace (prefixWord ++ tailWord_2638387) baseStart_2638387 baseEnd_2638387 := by
    simpa [prefixWord, tailWord_2638387, baseEnd_2638387] using wordTrace_append hprefix tailTrace_2638387
  have hstable : (prefixWord ++ tailWord_2638387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638387).length < 2 ^ (prefixWord ++ tailWord_2638387).sum := by decide
  have hdescent : baseEnd_2638387 < baseStart_2638387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638407 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 3]
def baseStart_2638407 : Nat := 118140960795 + 2638407 * 2 ^ 59
def prefixEnd_2638407 : Nat := 4983230072969 + 3 ^ 40 * 2638407 * 2
def baseEnd_2638407 : Nat := 1354770953187163954178693

theorem tailTrace_2638407 : CollatzResearch.WordTrace tailWord_2638407 prefixEnd_2638407 1354770953187163954178693 := by
  unfold tailWord_2638407
  simp only [CollatzResearch.WordTrace]
  refine ⟨96230608952509517886289475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64153739301673011924192983 96230608952509517886289475)
  ·
    refine ⟨144345913428764276829434213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96230608952509517886289475 144345913428764276829434213)
    ·
      refine ⟨27064858767893301905518915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144345913428764276829434213 27064858767893301905518915)
      ·
        refine ⟨40597288151839952858278373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27064858767893301905518915 40597288151839952858278373)
        ·
          refine ⟨7611991528469991160927195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40597288151839952858278373 7611991528469991160927195)
          ·
            refine ⟨11417987292704986741390793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7611991528469991160927195 11417987292704986741390793)
            ·
              refine ⟨8563490469528740056043095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11417987292704986741390793 8563490469528740056043095)
              ·
                refine ⟨12845235704293110084064643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8563490469528740056043095 12845235704293110084064643)
                ·
                  refine ⟨19267853556439665126096965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12845235704293110084064643 19267853556439665126096965)
                  ·
                    refine ⟨3612722541832437211143181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19267853556439665126096965 3612722541832437211143181)
                    ·
                      refine ⟨1354770953187163954178693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3612722541832437211143181 1354770953187163954178693)
                      ·
                        rfl

theorem cell23_2638407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_2638407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638407 prefixEnd_2638407 := by exact prefixLift 2638407
  have htrace : WordTrace (prefixWord ++ tailWord_2638407) baseStart_2638407 baseEnd_2638407 := by
    simpa [prefixWord, tailWord_2638407, baseEnd_2638407] using wordTrace_append hprefix tailTrace_2638407
  have hstable : (prefixWord ++ tailWord_2638407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638407).length < 2 ^ (prefixWord ++ tailWord_2638407).sum := by decide
  have hdescent : baseEnd_2638407 < baseStart_2638407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638410 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 8]
def baseStart_2638410 : Nat := 118140960795 + 2638410 * 2 ^ 59
def prefixEnd_2638410 : Nat := 4983230072969 + 3 ^ 40 * 2638410 * 2
def baseEnd_2638410 : Nat := 150530277069903049160131

theorem tailTrace_2638410 : CollatzResearch.WordTrace tailWord_2638410 prefixEnd_2638410 150530277069903049160131 := by
  unfold tailWord_2638410
  simp only [CollatzResearch.WordTrace]
  refine ⟨24057679592874662349662171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64153812247665766265765789 24057679592874662349662171)
  ·
    refine ⟨36086519389311993524493257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24057679592874662349662171 36086519389311993524493257)
    ·
      refine ⟨27064889541983995143369943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36086519389311993524493257 27064889541983995143369943)
      ·
        refine ⟨40597334312975992715054915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27064889541983995143369943 40597334312975992715054915)
        ·
          refine ⟨60896001469463989072582373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40597334312975992715054915 60896001469463989072582373)
          ·
            refine ⟨11418000275524497951109195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60896001469463989072582373 11418000275524497951109195)
            ·
              refine ⟨17127000413286746926663793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11418000275524497951109195 17127000413286746926663793)
              ·
                refine ⟨12845250309965060194997845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17127000413286746926663793 12845250309965060194997845)
                ·
                  refine ⟨150530277069903049160131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12845250309965060194997845 150530277069903049160131)
                  ·
                    rfl

theorem cell23_2638410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 8].length) (baseStart_2638410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638410 prefixEnd_2638410 := by exact prefixLift 2638410
  have htrace : WordTrace (prefixWord ++ tailWord_2638410) baseStart_2638410 baseEnd_2638410 := by
    simpa [prefixWord, tailWord_2638410, baseEnd_2638410] using wordTrace_append hprefix tailTrace_2638410
  have hstable : (prefixWord ++ tailWord_2638410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638410).length < 2 ^ (prefixWord ++ tailWord_2638410).sum := by decide
  have hdescent : baseEnd_2638410 < baseStart_2638410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638447 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 3, 5, 2]
def baseStart_2638447 : Nat := 118140960795 + 2638447 * 2 ^ 59
def prefixEnd_2638447 : Nat := 4983230072969 + 3 ^ 40 * 2638447 * 2
def baseEnd_2638447 : Nat := 1354791492413343797678509

theorem tailTrace_2638447 : CollatzResearch.WordTrace tailWord_2638447 prefixEnd_2638447 1354791492413343797678509 := by
  unfold tailWord_2638447
  simp only [CollatzResearch.WordTrace]
  refine ⟨96232067872364604717745595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64154711914909736478497063 96232067872364604717745595)
  ·
    refine ⟨144348101808546907076618393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96232067872364604717745595 144348101808546907076618393)
    ·
      refine ⟨108261076356410180307463795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144348101808546907076618393 108261076356410180307463795)
      ·
        refine ⟨162391614534615270461195693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108261076356410180307463795 162391614534615270461195693)
        ·
          refine ⟨60896855450480726422948385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162391614534615270461195693 60896855450480726422948385)
          ·
            refine ⟨45672641587860544817211289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60896855450480726422948385 45672641587860544817211289)
            ·
              refine ⟨34254481190895408612908467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45672641587860544817211289 34254481190895408612908467)
              ·
                refine ⟨51381721786343112919362701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34254481190895408612908467 51381721786343112919362701)
                ·
                  refine ⟨19268145669878667344761013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51381721786343112919362701 19268145669878667344761013)
                  ·
                    refine ⟨1806388656551125063571345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19268145669878667344761013 1806388656551125063571345)
                    ·
                      refine ⟨1354791492413343797678509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1806388656551125063571345 1354791492413343797678509)
                      ·
                        rfl

theorem cell23_2638447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 5, 2].length) (baseStart_2638447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638447 prefixEnd_2638447 := by exact prefixLift 2638447
  have htrace : WordTrace (prefixWord ++ tailWord_2638447) baseStart_2638447 baseEnd_2638447 := by
    simpa [prefixWord, tailWord_2638447, baseEnd_2638447] using wordTrace_append hprefix tailTrace_2638447
  have hstable : (prefixWord ++ tailWord_2638447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638447).length < 2 ^ (prefixWord ++ tailWord_2638447).sum := by decide
  have hdescent : baseEnd_2638447 < baseStart_2638447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638457 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 3, 5]
def baseStart_2638457 : Nat := 118140960795 + 2638457 * 2 ^ 59
def prefixEnd_2638457 : Nat := 4983230072969 + 3 ^ 40 * 2638457 * 2
def baseEnd_2638457 : Nat := 451598875739962919517821

theorem tailTrace_2638457 : CollatzResearch.WordTrace tailWord_2638457 prefixEnd_2638457 451598875739962919517821 := by
  unfold tailWord_2638457
  simp only [CollatzResearch.WordTrace]
  refine ⟨96232432602328376425609625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64154955068218917617073083 96232432602328376425609625)
  ·
    refine ⟨72174324451746282319207219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96232432602328376425609625 72174324451746282319207219)
    ·
      refine ⟨108261486677619423478810829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72174324451746282319207219 108261486677619423478810829)
      ·
        refine ⟨40598057504107283804554061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108261486677619423478810829 40598057504107283804554061)
        ·
          refine ⟨15224271564040231426707773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40598057504107283804554061 15224271564040231426707773)
          ·
            refine ⟨5709101836515086785015415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15224271564040231426707773 5709101836515086785015415)
            ·
              refine ⟨8563652754772630177523123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5709101836515086785015415 8563652754772630177523123)
              ·
                refine ⟨12845479132158945266284685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8563652754772630177523123 12845479132158945266284685)
                ·
                  refine ⟨4817054674559604474856757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12845479132158945266284685 4817054674559604474856757)
                  ·
                    refine ⟨451598875739962919517821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4817054674559604474856757 451598875739962919517821)
                    ·
                      rfl

theorem cell23_2638457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 5].length) (baseStart_2638457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638457 prefixEnd_2638457 := by exact prefixLift 2638457
  have htrace : WordTrace (prefixWord ++ tailWord_2638457) baseStart_2638457 baseEnd_2638457 := by
    simpa [prefixWord, tailWord_2638457, baseEnd_2638457] using wordTrace_append hprefix tailTrace_2638457
  have hstable : (prefixWord ++ tailWord_2638457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638457).length < 2 ^ (prefixWord ++ tailWord_2638457).sum := by decide
  have hdescent : baseEnd_2638457 < baseStart_2638457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638464 : List Nat := [2, 1, 1, 2, 1, 5, 1, 3, 2, 3, 2]
def baseStart_2638464 : Nat := 118140960795 + 2638464 * 2 ^ 59
def prefixEnd_2638464 : Nat := 4983230072969 + 3 ^ 40 * 2638464 * 2
def baseEnd_2638464 : Nat := 1354800221584470231165931

theorem tailTrace_2638464 : CollatzResearch.WordTrace tailWord_2638464 prefixEnd_2638464 1354800221584470231165931 := by
  unfold tailWord_2638464
  simp only [CollatzResearch.WordTrace]
  refine ⟨48116343956651508310557223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64155125275535344414076297 48116343956651508310557223)
  ·
    refine ⟨72174515934977262465835835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48116343956651508310557223 72174515934977262465835835)
    ·
      refine ⟨108261773902465893698753753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72174515934977262465835835 108261773902465893698753753)
      ·
        refine ⟨81196330426849420274065315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108261773902465893698753753 81196330426849420274065315)
        ·
          refine ⟨121794495640274130411097973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81196330426849420274065315 121794495640274130411097973)
          ·
            refine ⟨11418233966275699726040435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121794495640274130411097973 11418233966275699726040435)
            ·
              refine ⟨17127350949413549589060653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11418233966275699726040435 17127350949413549589060653)
              ·
                refine ⟨6422756606030081095897745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17127350949413549589060653 6422756606030081095897745)
                ·
                  refine ⟨4817067454522560821923309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6422756606030081095897745 4817067454522560821923309)
                  ·
                    refine ⟨1806400295445960308221241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4817067454522560821923309 1806400295445960308221241)
                    ·
                      refine ⟨1354800221584470231165931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1806400295445960308221241 1354800221584470231165931)
                      ·
                        rfl

theorem cell23_2638464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 2, 3, 2].length) (baseStart_2638464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638464 prefixEnd_2638464 := by exact prefixLift 2638464
  have htrace : WordTrace (prefixWord ++ tailWord_2638464) baseStart_2638464 baseEnd_2638464 := by
    simpa [prefixWord, tailWord_2638464, baseEnd_2638464] using wordTrace_append hprefix tailTrace_2638464
  have hstable : (prefixWord ++ tailWord_2638464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638464).length < 2 ^ (prefixWord ++ tailWord_2638464).sum := by decide
  have hdescent : baseEnd_2638464 < baseStart_2638464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638471 : List Nat := [1, 1, 4, 2, 1, 2, 2, 5, 1, 1, 3]
def baseStart_2638471 : Nat := 118140960795 + 2638471 * 2 ^ 59
def prefixEnd_2638471 : Nat := 4983230072969 + 3 ^ 40 * 2638471 * 2
def baseEnd_2638471 : Nat := 1354803815949051703778399

theorem tailTrace_2638471 : CollatzResearch.WordTrace tailWord_2638471 prefixEnd_2638471 1354803815949051703778399 := by
  unfold tailWord_2638471
  simp only [CollatzResearch.WordTrace]
  refine ⟨96232943224277656816619267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64155295482851771211079511 96232943224277656816619267)
  ·
    refine ⟨144349414836416485224928901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96232943224277656816619267 144349414836416485224928901)
    ·
      refine ⟨27065515281828090979674169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144349414836416485224928901 27065515281828090979674169)
      ·
        refine ⟨20299136461371068234755627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27065515281828090979674169 20299136461371068234755627)
        ·
          refine ⟨30448704692056602352133441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20299136461371068234755627 30448704692056602352133441)
          ·
            refine ⟨22836528519042451764100081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30448704692056602352133441 22836528519042451764100081)
            ·
              refine ⟨17127396389281838823075061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22836528519042451764100081 17127396389281838823075061)
              ·
                refine ⟨1605693411495172389663287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17127396389281838823075061 1605693411495172389663287)
                ·
                  refine ⟨2408540117242758584494931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1605693411495172389663287 2408540117242758584494931)
                  ·
                    refine ⟨3612810175864137876742397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2408540117242758584494931 3612810175864137876742397)
                    ·
                      refine ⟨1354803815949051703778399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3612810175864137876742397 1354803815949051703778399)
                      ·
                        rfl

theorem cell23_2638471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_2638471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638471 prefixEnd_2638471 := by exact prefixLift 2638471
  have htrace : WordTrace (prefixWord ++ tailWord_2638471) baseStart_2638471 baseEnd_2638471 := by
    simpa [prefixWord, tailWord_2638471, baseEnd_2638471] using wordTrace_append hprefix tailTrace_2638471
  have hstable : (prefixWord ++ tailWord_2638471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638471).length < 2 ^ (prefixWord ++ tailWord_2638471).sum := by decide
  have hdescent : baseEnd_2638471 < baseStart_2638471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638494 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_2638494 : Nat := 118140960795 + 2638494 * 2 ^ 59
def prefixEnd_2638494 : Nat := 4983230072969 + 3 ^ 40 * 2638494 * 2
def baseEnd_2638494 : Nat := 1354815626004105113790793

theorem tailTrace_2638494 : CollatzResearch.WordTrace tailWord_2638494 prefixEnd_2638494 1354815626004105113790793 := by
  unfold tailWord_2638494
  simp only [CollatzResearch.WordTrace]
  refine ⟨12029222762899291468088317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64155854735462887829804357 12029222762899291468088317)
  ·
    refine ⟨4510958536087234300533119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12029222762899291468088317 4510958536087234300533119)
    ·
      refine ⟨6766437804130851450799679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4510958536087234300533119 6766437804130851450799679)
      ·
        refine ⟨10149656706196277176199519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6766437804130851450799679 10149656706196277176199519)
        ·
          refine ⟨15224485059294415764299279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10149656706196277176199519 15224485059294415764299279)
          ·
            refine ⟨22836727588941623646448919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15224485059294415764299279 22836727588941623646448919)
            ·
              refine ⟨34255091383412435469673379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22836727588941623646448919 34255091383412435469673379)
              ·
                refine ⟨51382637075118653204510069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34255091383412435469673379 51382637075118653204510069)
                ·
                  refine ⟨4817122225792373737922819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51382637075118653204510069 4817122225792373737922819)
                  ·
                    refine ⟨7225683338688560606884229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4817122225792373737922819 7225683338688560606884229)
                    ·
                      refine ⟨1354815626004105113790793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7225683338688560606884229 1354815626004105113790793)
                      ·
                        rfl

theorem cell23_2638494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_2638494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638494 prefixEnd_2638494 := by exact prefixLift 2638494
  have htrace : WordTrace (prefixWord ++ tailWord_2638494) baseStart_2638494 baseEnd_2638494 := by
    simpa [prefixWord, tailWord_2638494, baseEnd_2638494] using wordTrace_append hprefix tailTrace_2638494
  have hstable : (prefixWord ++ tailWord_2638494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638494).length < 2 ^ (prefixWord ++ tailWord_2638494).sum := by decide
  have hdescent : baseEnd_2638494 < baseStart_2638494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638511 : List Nat := [1, 1, 2, 1, 2, 6, 1, 2, 3, 2, 2]
def baseStart_2638511 : Nat := 118140960795 + 2638511 * 2 ^ 59
def prefixEnd_2638511 : Nat := 4983230072969 + 3 ^ 40 * 2638511 * 2
def baseEnd_2638511 : Nat := 1354824355175231547278215

theorem tailTrace_2638511 : CollatzResearch.WordTrace tailWord_2638511 prefixEnd_2638511 1354824355175231547278215 := by
  unfold tailWord_2638511
  simp only [CollatzResearch.WordTrace]
  refine ⟨96234402144132743648075387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64156268096088495765383591 96234402144132743648075387)
  ·
    refine ⟨144351603216199115472113081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96234402144132743648075387 144351603216199115472113081)
    ·
      refine ⟨108263702412149336604084811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144351603216199115472113081 108263702412149336604084811)
      ·
        refine ⟨162395553618224004906127217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108263702412149336604084811 162395553618224004906127217)
        ·
          refine ⟨121796665213668003679595413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162395553618224004906127217 121796665213668003679595413)
          ·
            refine ⟨5709218681890687672481035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 121796665213668003679595413 5709218681890687672481035)
            ·
              refine ⟨8563828022836031508721553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5709218681890687672481035 8563828022836031508721553)
              ·
                refine ⟨6422871017127023631541165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8563828022836031508721553 6422871017127023631541165)
                ·
                  refine ⟨2408576631422633861827937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6422871017127023631541165 2408576631422633861827937)
                  ·
                    refine ⟨1806432473566975396370953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2408576631422633861827937 1806432473566975396370953)
                    ·
                      refine ⟨1354824355175231547278215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1806432473566975396370953 1354824355175231547278215)
                      ·
                        rfl

theorem cell23_2638511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 2, 2].length) (baseStart_2638511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638511 prefixEnd_2638511 := by exact prefixLift 2638511
  have htrace : WordTrace (prefixWord ++ tailWord_2638511) baseStart_2638511 baseEnd_2638511 := by
    simpa [prefixWord, tailWord_2638511, baseEnd_2638511] using wordTrace_append hprefix tailTrace_2638511
  have hstable : (prefixWord ++ tailWord_2638511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638511).length < 2 ^ (prefixWord ++ tailWord_2638511).sum := by decide
  have hdescent : baseEnd_2638511 < baseStart_2638511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638514 : List Nat := [3, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3]
def baseStart_2638514 : Nat := 118140960795 + 2638514 * 2 ^ 59
def prefixEnd_2638514 : Nat := 4983230072969 + 3 ^ 40 * 2638514 * 2
def baseEnd_2638514 : Nat := 1354825895617195035540701

theorem tailTrace_2638514 : CollatzResearch.WordTrace tailWord_2638514 prefixEnd_2638514 1354825895617195035540701 := by
  unfold tailWord_2638514
  simp only [CollatzResearch.WordTrace]
  refine ⟨24058627890780468790108649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64156341042081250106956397 24058627890780468790108649)
  ·
    refine ⟨18043970918085351592581487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24058627890780468790108649 18043970918085351592581487)
    ·
      refine ⟨27065956377128027388872231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18043970918085351592581487 27065956377128027388872231)
      ·
        refine ⟨40598934565692041083308347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27065956377128027388872231 40598934565692041083308347)
        ·
          refine ⟨60898401848538061624962521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40598934565692041083308347 60898401848538061624962521)
          ·
            refine ⟨45673801386403546218721891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60898401848538061624962521 45673801386403546218721891)
            ·
              refine ⟨68510702079605319328082837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45673801386403546218721891 68510702079605319328082837)
              ·
                refine ⟨3211439159981499343503883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68510702079605319328082837 3211439159981499343503883)
                ·
                  refine ⟨4817158739972249015255825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3211439159981499343503883 4817158739972249015255825)
                  ·
                    refine ⟨3612869054979186761441869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4817158739972249015255825 3612869054979186761441869)
                    ·
                      refine ⟨1354825895617195035540701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3612869054979186761441869 1354825895617195035540701)
                      ·
                        rfl

theorem cell23_2638514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_2638514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638514 prefixEnd_2638514 := by exact prefixLift 2638514
  have htrace : WordTrace (prefixWord ++ tailWord_2638514) baseStart_2638514 baseEnd_2638514 := by
    simpa [prefixWord, tailWord_2638514, baseEnd_2638514] using wordTrace_append hprefix tailTrace_2638514
  have hstable : (prefixWord ++ tailWord_2638514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638514).length < 2 ^ (prefixWord ++ tailWord_2638514).sum := by decide
  have hdescent : baseEnd_2638514 < baseStart_2638514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638528 : List Nat := [2, 1, 1, 2, 4, 2, 1, 5, 1, 2, 2]
def baseStart_2638528 : Nat := 118140960795 + 2638528 * 2 ^ 59
def prefixEnd_2638528 : Nat := 4983230072969 + 3 ^ 40 * 2638528 * 2
def baseEnd_2638528 : Nat := 1354833084346357980765637

theorem tailTrace_2638528 : CollatzResearch.WordTrace tailWord_2638528 prefixEnd_2638528 1354833084346357980765637 := by
  unfold tailWord_2638528
  simp only [CollatzResearch.WordTrace]
  refine ⟨48117511092535577775722119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64156681456714103700962825 48117511092535577775722119)
  ·
    refine ⟨72176266638803366663583179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48117511092535577775722119 72176266638803366663583179)
    ·
      refine ⟨108264399958205049995374769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72176266638803366663583179 108264399958205049995374769)
      ·
        refine ⟨81198299968653787496531077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108264399958205049995374769 81198299968653787496531077)
        ·
          refine ⟨15224681244122585155599577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81198299968653787496531077 15224681244122585155599577)
          ·
            refine ⟨11418510933091938866699683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15224681244122585155599577 11418510933091938866699683)
            ·
              refine ⟨17127766399637908300049525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11418510933091938866699683 17127766399637908300049525)
              ·
                refine ⟨1605728099966053903129643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17127766399637908300049525 1605728099966053903129643)
                ·
                  refine ⟨2408592149949080854694465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1605728099966053903129643 2408592149949080854694465)
                  ·
                    refine ⟨1806444112461810641020849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2408592149949080854694465 1806444112461810641020849)
                    ·
                      refine ⟨1354833084346357980765637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1806444112461810641020849 1354833084346357980765637)
                      ·
                        rfl

theorem cell23_2638528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 1, 2, 2].length) (baseStart_2638528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638528 prefixEnd_2638528 := by exact prefixLift 2638528
  have htrace : WordTrace (prefixWord ++ tailWord_2638528) baseStart_2638528 baseEnd_2638528 := by
    simpa [prefixWord, tailWord_2638528, baseEnd_2638528] using wordTrace_append hprefix tailTrace_2638528
  have hstable : (prefixWord ++ tailWord_2638528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638528).length < 2 ^ (prefixWord ++ tailWord_2638528).sum := by decide
  have hdescent : baseEnd_2638528 < baseStart_2638528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638561 : List Nat := [1, 2, 3, 1, 4, 3, 1, 1, 1, 3, 3]
def baseStart_2638561 : Nat := 118140960795 + 2638561 * 2 ^ 59
def prefixEnd_2638561 : Nat := 4983230072969 + 3 ^ 40 * 2638561 * 2
def baseEnd_2638561 : Nat := 1354850029207956351652985

theorem tailTrace_2638561 : CollatzResearch.WordTrace tailWord_2638561 prefixEnd_2638561 1354850029207956351652985 := by
  unfold tailWord_2638561
  simp only [CollatzResearch.WordTrace]
  refine ⟨96236225793951602187395537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64157483862634401458263691 96236225793951602187395537)
  ·
    refine ⟨72177169345463701640546653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96236225793951602187395537 72177169345463701640546653)
    ·
      refine ⟨27066438504548888115204995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72177169345463701640546653 27066438504548888115204995)
      ·
        refine ⟨40599657756823332172807493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27066438504548888115204995 40599657756823332172807493)
        ·
          refine ⟨7612435829404374782401405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40599657756823332172807493 7612435829404374782401405)
          ·
            refine ⟨2854663436026640543400527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7612435829404374782401405 2854663436026640543400527)
            ·
              refine ⟨4281995154039960815100791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2854663436026640543400527 4281995154039960815100791)
              ·
                refine ⟨6422992731059941222651187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4281995154039960815100791 6422992731059941222651187)
                ·
                  refine ⟨9634489096589911833976781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6422992731059941222651187 9634489096589911833976781)
                  ·
                    refine ⟨3612933411221216937741293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9634489096589911833976781 3612933411221216937741293)
                    ·
                      refine ⟨1354850029207956351652985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3612933411221216937741293 1354850029207956351652985)
                      ·
                        rfl

theorem cell23_2638561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_2638561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638561 prefixEnd_2638561 := by exact prefixLift 2638561
  have htrace : WordTrace (prefixWord ++ tailWord_2638561) baseStart_2638561 baseEnd_2638561 := by
    simpa [prefixWord, tailWord_2638561, baseEnd_2638561] using wordTrace_append hprefix tailTrace_2638561
  have hstable : (prefixWord ++ tailWord_2638561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638561).length < 2 ^ (prefixWord ++ tailWord_2638561).sum := by decide
  have hdescent : baseEnd_2638561 < baseStart_2638561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638584 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 3, 4, 2]
def baseStart_2638584 : Nat := 118140960795 + 2638584 * 2 ^ 59
def prefixEnd_2638584 : Nat := 4983230072969 + 3 ^ 40 * 2638584 * 2
def baseEnd_2638584 : Nat := 1354861839263009761665379

theorem tailTrace_2638584 : CollatzResearch.WordTrace tailWord_2638584 prefixEnd_2638584 1354861839263009761665379 := by
  unfold tailWord_2638584
  simp only [CollatzResearch.WordTrace]
  refine ⟨48118532336434138557741403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64158043115245518076988537 48118532336434138557741403)
  ·
    refine ⟨72177798504651207836612105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48118532336434138557741403 72177798504651207836612105)
    ·
      refine ⟨54133348878488405877459079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72177798504651207836612105 54133348878488405877459079)
      ·
        refine ⟨81200023317732608816188619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54133348878488405877459079 81200023317732608816188619)
        ·
          refine ⟨121800034976598913224282929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81200023317732608816188619 121800034976598913224282929)
          ·
            refine ⟨91350026232449184918212197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121800034976598913224282929 91350026232449184918212197)
            ·
              refine ⟨17128129918584222172164787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91350026232449184918212197 17128129918584222172164787)
              ·
                refine ⟨25692194877876333258247181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17128129918584222172164787 25692194877876333258247181)
                ·
                  refine ⟨9634573079203624971842693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25692194877876333258247181 9634573079203624971842693)
                  ·
                    refine ⟨1806482452350679682220505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9634573079203624971842693 1806482452350679682220505)
                    ·
                      refine ⟨1354861839263009761665379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1806482452350679682220505 1354861839263009761665379)
                      ·
                        rfl

theorem cell23_2638584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 3, 4, 2].length) (baseStart_2638584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638584 prefixEnd_2638584 := by exact prefixLift 2638584
  have htrace : WordTrace (prefixWord ++ tailWord_2638584) baseStart_2638584 baseEnd_2638584 := by
    simpa [prefixWord, tailWord_2638584, baseEnd_2638584] using wordTrace_append hprefix tailTrace_2638584
  have hstable : (prefixWord ++ tailWord_2638584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638584).length < 2 ^ (prefixWord ++ tailWord_2638584).sum := by decide
  have hdescent : baseEnd_2638584 < baseStart_2638584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638597 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 4, 2, 4]
def baseStart_2638597 : Nat := 118140960795 + 2638597 * 2 ^ 59
def prefixEnd_2638597 : Nat := 4983230072969 + 3 ^ 40 * 2638597 * 2
def baseEnd_2638597 : Nat := 1354868514511518210802819

theorem tailTrace_2638597 : CollatzResearch.WordTrace tailWord_2638597 prefixEnd_2638597 1354868514511518210802819 := by
  unfold tailWord_2638597
  simp only [CollatzResearch.WordTrace]
  refine ⟨96237538821821180335706045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64158359214547453557137363 96237538821821180335706045)
  ·
    refine ⟨36089077058182942625889767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96237538821821180335706045 36089077058182942625889767)
    ·
      refine ⟨54133615587274413938834651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36089077058182942625889767 54133615587274413938834651)
      ·
        refine ⟨81200423380911620908251977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54133615587274413938834651 81200423380911620908251977)
        ·
          refine ⟨60900317535683715681188983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81200423380911620908251977 60900317535683715681188983)
          ·
            refine ⟨91350476303525573521783475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60900317535683715681188983 91350476303525573521783475)
            ·
              refine ⟨137025714455288360282675213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91350476303525573521783475 137025714455288360282675213)
              ·
                refine ⟨51384642920733135106003205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137025714455288360282675213 51384642920733135106003205)
                ·
                  refine ⟨9634620547637462832375601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51384642920733135106003205 9634620547637462832375601)
                  ·
                    refine ⟨7225965410728097124281701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9634620547637462832375601 7225965410728097124281701)
                    ·
                      refine ⟨1354868514511518210802819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7225965410728097124281701 1354868514511518210802819)
                      ·
                        rfl

theorem cell23_2638597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_2638597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638597 prefixEnd_2638597 := by exact prefixLift 2638597
  have htrace : WordTrace (prefixWord ++ tailWord_2638597) baseStart_2638597 baseEnd_2638597 := by
    simpa [prefixWord, tailWord_2638597, baseEnd_2638597] using wordTrace_append hprefix tailTrace_2638597
  have hstable : (prefixWord ++ tailWord_2638597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638597).length < 2 ^ (prefixWord ++ tailWord_2638597).sum := by decide
  have hdescent : baseEnd_2638597 < baseStart_2638597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638601 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 4, 2, 2]
def baseStart_2638601 : Nat := 118140960795 + 2638601 * 2 ^ 59
def prefixEnd_2638601 : Nat := 4983230072969 + 3 ^ 40 * 2638601 * 2
def baseEnd_2638601 : Nat := 1354870568434136195152801

theorem tailTrace_2638601 : CollatzResearch.WordTrace tailWord_2638601 prefixEnd_2638601 1354870568434136195152801 := by
  unfold tailWord_2638601
  simp only [CollatzResearch.WordTrace]
  refine ⟨96237684713806689018851657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64158456475871126012567771 96237684713806689018851657)
  ·
    refine ⟨72178263535355016764138743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96237684713806689018851657 72178263535355016764138743)
    ·
      refine ⟨108267395303032525146208115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72178263535355016764138743 108267395303032525146208115)
      ·
        refine ⟨162401092954548787719312173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108267395303032525146208115 162401092954548787719312173)
        ·
          refine ⟨60900409857955795394742065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162401092954548787719312173 60900409857955795394742065)
          ·
            refine ⟨45675307393466846546056549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60900409857955795394742065 45675307393466846546056549)
            ·
              refine ⟨8564120136275033727385603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45675307393466846546056549 8564120136275033727385603)
              ·
                refine ⟨12846180204412550591078405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8564120136275033727385603 12846180204412550591078405)
                ·
                  refine ⟨2408658788327353235827201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12846180204412550591078405 2408658788327353235827201)
                  ·
                    refine ⟨1806494091245514926870401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2408658788327353235827201 1806494091245514926870401)
                    ·
                      refine ⟨1354870568434136195152801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1806494091245514926870401 1354870568434136195152801)
                      ·
                        rfl

theorem cell23_2638601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 2, 2].length) (baseStart_2638601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638601 prefixEnd_2638601 := by exact prefixLift 2638601
  have htrace : WordTrace (prefixWord ++ tailWord_2638601) baseStart_2638601 baseEnd_2638601 := by
    simpa [prefixWord, tailWord_2638601, baseEnd_2638601] using wordTrace_append hprefix tailTrace_2638601
  have hstable : (prefixWord ++ tailWord_2638601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638601).length < 2 ^ (prefixWord ++ tailWord_2638601).sum := by decide
  have hdescent : baseEnd_2638601 < baseStart_2638601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638618 : List Nat := [3, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2]
def baseStart_2638618 : Nat := 118140960795 + 2638618 * 2 ^ 59
def prefixEnd_2638618 : Nat := 4983230072969 + 3 ^ 40 * 2638618 * 2
def baseEnd_2638618 : Nat := 1354879297605262628640223

theorem tailTrace_2638618 : CollatzResearch.WordTrace tailWord_2638618 prefixEnd_2638618 1354879297605262628640223 := by
  unfold tailWord_2638618
  simp only [CollatzResearch.WordTrace]
  refine ⟨24059576188686275230555127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64158869836496733948147005 24059576188686275230555127)
  ·
    refine ⟨36089364283029412845832691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24059576188686275230555127 36089364283029412845832691)
    ·
      refine ⟨54134046424544119268749037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36089364283029412845832691 54134046424544119268749037)
      ·
        refine ⟨20300267409204044725780889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54134046424544119268749037 20300267409204044725780889)
        ·
          refine ⟨15225200556903033544335667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20300267409204044725780889 15225200556903033544335667)
          ·
            refine ⟨22837800835354550316503501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15225200556903033544335667 22837800835354550316503501)
            ·
              refine ⟨8564175313257956368688813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22837800835354550316503501 8564175313257956368688813)
              ·
                refine ⟨3211565742471733638258305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8564175313257956368688813 3211565742471733638258305)
                ·
                  refine ⟨2408674306853800228693729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3211565742471733638258305 2408674306853800228693729)
                  ·
                    refine ⟨1806505730140350171520297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2408674306853800228693729 1806505730140350171520297)
                    ·
                      refine ⟨1354879297605262628640223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1806505730140350171520297 1354879297605262628640223)
                      ·
                        rfl

theorem cell23_2638618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_2638618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638618 prefixEnd_2638618 := by exact prefixLift 2638618
  have htrace : WordTrace (prefixWord ++ tailWord_2638618) baseStart_2638618 baseEnd_2638618 := by
    simpa [prefixWord, tailWord_2638618, baseEnd_2638618] using wordTrace_append hprefix tailTrace_2638618
  have hstable : (prefixWord ++ tailWord_2638618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638618).length < 2 ^ (prefixWord ++ tailWord_2638618).sum := by decide
  have hdescent : baseEnd_2638618 < baseStart_2638618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638647 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 5]
def baseStart_2638647 : Nat := 118140960795 + 2638647 * 2 ^ 59
def prefixEnd_2638647 : Nat := 4983230072969 + 3 ^ 40 * 2638647 * 2
def baseEnd_2638647 : Nat := 1354894188544243015177589

theorem tailTrace_2638647 : CollatzResearch.WordTrace tailWord_2638647 prefixEnd_2638647 1354894188544243015177589 := by
  unfold tailWord_2638647
  simp only [CollatzResearch.WordTrace]
  refine ⟨96239362471640038875026195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64159574981093359250017463 96239362471640038875026195)
  ·
    refine ⟨144359043707460058312539293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96239362471640038875026195 144359043707460058312539293)
    ·
      refine ⟨54134641390297521867202235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144359043707460058312539293 54134641390297521867202235)
      ·
        refine ⟨81201962085446282800803353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54134641390297521867202235 81201962085446282800803353)
        ·
          refine ⟨60901471564084712100602515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81201962085446282800803353 60901471564084712100602515)
          ·
            refine ⟨91352207346127068150903773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60901471564084712100602515 91352207346127068150903773)
            ·
              refine ⟨34257077754797650556588915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91352207346127068150903773 34257077754797650556588915)
              ·
                refine ⟨51385616632196475834883373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34257077754797650556588915 51385616632196475834883373)
                ·
                  refine ⟨19269606237073678438081265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51385616632196475834883373 19269606237073678438081265)
                  ·
                    refine ⟨14452204677805258828560949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19269606237073678438081265 14452204677805258828560949)
                    ·
                      refine ⟨1354894188544243015177589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14452204677805258828560949 1354894188544243015177589)
                      ·
                        rfl

theorem cell23_2638647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_2638647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638647 prefixEnd_2638647 := by exact prefixLift 2638647
  have htrace : WordTrace (prefixWord ++ tailWord_2638647) baseStart_2638647 baseEnd_2638647 := by
    simpa [prefixWord, tailWord_2638647, baseEnd_2638647] using wordTrace_append hprefix tailTrace_2638647
  have hstable : (prefixWord ++ tailWord_2638647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638647).length < 2 ^ (prefixWord ++ tailWord_2638647).sum := by decide
  have hdescent : baseEnd_2638647 < baseStart_2638647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638674 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_2638674 : Nat := 118140960795 + 2638674 * 2 ^ 59
def prefixEnd_2638674 : Nat := 4983230072969 + 3 ^ 40 * 2638674 * 2
def baseEnd_2638674 : Nat := 1354908052521914409539965

theorem tailTrace_2638674 : CollatzResearch.WordTrace tailWord_2638674 prefixEnd_2638674 1354908052521914409539965 := by
  unfold tailWord_2638674
  simp only [CollatzResearch.WordTrace]
  refine ⟨24060086810635555621564769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64160231495028148324172717 24060086810635555621564769)
  ·
    refine ⟨18045065107976666716173577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24060086810635555621564769 18045065107976666716173577)
    ·
      refine ⟨13533798830982500037130183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18045065107976666716173577 13533798830982500037130183)
      ·
        refine ⟨20300698246473750055695275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13533798830982500037130183 20300698246473750055695275)
        ·
          refine ⟨30451047369710625083542913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20300698246473750055695275 30451047369710625083542913)
          ·
            refine ⟨22838285527282968812657185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30451047369710625083542913 22838285527282968812657185)
            ·
              refine ⟨17128714145462226609492889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22838285527282968812657185 17128714145462226609492889)
              ·
                refine ⟨12846535609096669957119667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17128714145462226609492889 12846535609096669957119667)
                ·
                  refine ⟨19269803413645004935679501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12846535609096669957119667 19269803413645004935679501)
                  ·
                    refine ⟨7226176280116876850879813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19269803413645004935679501 7226176280116876850879813)
                    ·
                      refine ⟨1354908052521914409539965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7226176280116876850879813 1354908052521914409539965)
                      ·
                        rfl

theorem cell23_2638674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_2638674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638674 prefixEnd_2638674 := by exact prefixLift 2638674
  have htrace : WordTrace (prefixWord ++ tailWord_2638674) baseStart_2638674 baseEnd_2638674 := by
    simpa [prefixWord, tailWord_2638674, baseEnd_2638674] using wordTrace_append hprefix tailTrace_2638674
  have hstable : (prefixWord ++ tailWord_2638674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638674).length < 2 ^ (prefixWord ++ tailWord_2638674).sum := by decide
  have hdescent : baseEnd_2638674 < baseStart_2638674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638691 : List Nat := [1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 4]
def baseStart_2638691 : Nat := 118140960795 + 2638691 * 2 ^ 59
def prefixEnd_2638691 : Nat := 4983230072969 + 3 ^ 40 * 2638691 * 2
def baseEnd_2638691 : Nat := 1354916781693040843027387

theorem tailTrace_2638691 : CollatzResearch.WordTrace tailWord_2638691 prefixEnd_2638691 1354916781693040843027387 := by
  unfold tailWord_2638691
  simp only [CollatzResearch.WordTrace]
  refine ⟨96240967283480634389627927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64160644855653756259751951 96240967283480634389627927)
  ·
    refine ⟨144361450925220951584441891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96240967283480634389627927 144361450925220951584441891)
    ·
      refine ⟨216542176387831427376662837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144361450925220951584441891 216542176387831427376662837)
      ·
        refine ⟨20300829036359196316562141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 216542176387831427376662837 20300829036359196316562141)
        ·
          refine ⟨7612810888634698618710803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20300829036359196316562141 7612810888634698618710803)
          ·
            refine ⟨11419216332952047928066205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7612810888634698618710803 11419216332952047928066205)
            ·
              refine ⟨4282206124857017973024827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11419216332952047928066205 4282206124857017973024827)
              ·
                refine ⟨6423309187285526959537241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4282206124857017973024827 6423309187285526959537241)
                ·
                  refine ⟨4817481890464145219652931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6423309187285526959537241 4817481890464145219652931)
                  ·
                    refine ⟨7226222835696217829479397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4817481890464145219652931 7226222835696217829479397)
                    ·
                      refine ⟨1354916781693040843027387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7226222835696217829479397 1354916781693040843027387)
                      ·
                        rfl

theorem cell23_2638691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_2638691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638691 prefixEnd_2638691 := by exact prefixLift 2638691
  have htrace : WordTrace (prefixWord ++ tailWord_2638691) baseStart_2638691 baseEnd_2638691 := by
    simpa [prefixWord, tailWord_2638691, baseEnd_2638691] using wordTrace_append hprefix tailTrace_2638691
  have hstable : (prefixWord ++ tailWord_2638691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638691).length < 2 ^ (prefixWord ++ tailWord_2638691).sum := by decide
  have hdescent : baseEnd_2638691 < baseStart_2638691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638798 : List Nat := [4, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4]
def baseStart_2638798 : Nat := 118140960795 + 2638798 * 2 ^ 59
def prefixEnd_2638798 : Nat := 4983230072969 + 3 ^ 40 * 2638798 * 2
def baseEnd_2638798 : Nat := 1354971724123071924389395

theorem tailTrace_2638798 : CollatzResearch.WordTrace tailWord_2638798 prefixEnd_2638798 1354971724123071924389395 := by
  unfold tailWord_2638798
  simp only [CollatzResearch.WordTrace]
  refine ⟨12030608736761623957971631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64163246596061994442515365 12030608736761623957971631)
  ·
    refine ⟨18045913105142435936957447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12030608736761623957971631 18045913105142435936957447)
    ·
      refine ⟨27068869657713653905436171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18045913105142435936957447 27068869657713653905436171)
      ·
        refine ⟨40603304486570480858154257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27068869657713653905436171 40603304486570480858154257)
        ·
          refine ⟨30452478364927860643615693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40603304486570480858154257 30452478364927860643615693)
          ·
            refine ⟨11419679386847947741355885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30452478364927860643615693 11419679386847947741355885)
            ·
              refine ⟨4282379770067980403008457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11419679386847947741355885 4282379770067980403008457)
              ·
                refine ⟨3211784827550985302256343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4282379770067980403008457 3211784827550985302256343)
                ·
                  refine ⟨4817677241326477953384515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3211784827550985302256343 4817677241326477953384515)
                  ·
                    refine ⟨7226515861989716930076773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4817677241326477953384515 7226515861989716930076773)
                    ·
                      refine ⟨1354971724123071924389395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7226515861989716930076773 1354971724123071924389395)
                      ·
                        rfl

theorem cell23_2638798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_2638798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638798 prefixEnd_2638798 := by exact prefixLift 2638798
  have htrace : WordTrace (prefixWord ++ tailWord_2638798) baseStart_2638798 baseEnd_2638798 := by
    simpa [prefixWord, tailWord_2638798, baseEnd_2638798] using wordTrace_append hprefix tailTrace_2638798
  have hstable : (prefixWord ++ tailWord_2638798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638798).length < 2 ^ (prefixWord ++ tailWord_2638798).sum := by decide
  have hdescent : baseEnd_2638798 < baseStart_2638798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638801 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 3, 2, 3]
def baseStart_2638801 : Nat := 118140960795 + 2638801 * 2 ^ 59
def prefixEnd_2638801 : Nat := 4983230072969 + 3 ^ 40 * 2638801 * 2
def baseEnd_2638801 : Nat := 1354973264565035412651881

theorem tailTrace_2638801 : CollatzResearch.WordTrace tailWord_2638801 prefixEnd_2638801 1354973264565035412651881 := by
  unfold tailWord_2638801
  simp only [CollatzResearch.WordTrace]
  refine ⟨96244979313082123176132257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64163319542054748784088171 96244979313082123176132257)
  ·
    refine ⟨72183734484811592382099193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96244979313082123176132257 72183734484811592382099193)
    ·
      refine ⟨54137800863608694286574395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72183734484811592382099193 54137800863608694286574395)
      ·
        refine ⟨81206701295413041429861593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54137800863608694286574395 81206701295413041429861593)
        ·
          refine ⟨60905025971559781072396195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81206701295413041429861593 60905025971559781072396195)
          ·
            refine ⟨91357538957339671608594293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60905025971559781072396195 91357538957339671608594293)
            ·
              refine ⟨8564769277250594213305715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91357538957339671608594293 8564769277250594213305715)
              ·
                refine ⟨12847153915875891319958573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8564769277250594213305715 12847153915875891319958573)
                ·
                  refine ⟨4817682718453459244984465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12847153915875891319958573 4817682718453459244984465)
                  ·
                    refine ⟨3613262038840094433738349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4817682718453459244984465 3613262038840094433738349)
                    ·
                      refine ⟨1354973264565035412651881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3613262038840094433738349 1354973264565035412651881)
                      ·
                        rfl

theorem cell23_2638801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 2, 3].length) (baseStart_2638801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638801 prefixEnd_2638801 := by exact prefixLift 2638801
  have htrace : WordTrace (prefixWord ++ tailWord_2638801) baseStart_2638801 baseEnd_2638801 := by
    simpa [prefixWord, tailWord_2638801, baseEnd_2638801] using wordTrace_append hprefix tailTrace_2638801
  have hstable : (prefixWord ++ tailWord_2638801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638801).length < 2 ^ (prefixWord ++ tailWord_2638801).sum := by decide
  have hdescent : baseEnd_2638801 < baseStart_2638801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638815 : List Nat := [1, 1, 2, 3, 5, 1, 3, 1, 1, 1, 4]
def baseStart_2638815 : Nat := 118140960795 + 2638815 * 2 ^ 59
def prefixEnd_2638815 : Nat := 4983230072969 + 3 ^ 40 * 2638815 * 2
def baseEnd_2638815 : Nat := 1354980453294198357876817

theorem tailTrace_2638815 : CollatzResearch.WordTrace tailWord_2638815 prefixEnd_2638815 1354980453294198357876817 := by
  unfold tailWord_2638815
  simp only [CollatzResearch.WordTrace]
  refine ⟨96245489935031403567141899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64163659956687602378094599 96245489935031403567141899)
  ·
    refine ⟨144368234902547105350712849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96245489935031403567141899 144368234902547105350712849)
    ·
      refine ⟨108276176176910329013034637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144368234902547105350712849 108276176176910329013034637)
      ·
        refine ⟨40603566066341373379887989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108276176176910329013034637 40603566066341373379887989)
        ·
          refine ⟨3806584318719503754364499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40603566066341373379887989 3806584318719503754364499)
          ·
            refine ⟨5709876478079255631546749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3806584318719503754364499 5709876478079255631546749)
            ·
              refine ⟨2141203679279720861830031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5709876478079255631546749 2141203679279720861830031)
              ·
                refine ⟨3211805518919581292745047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2141203679279720861830031 3211805518919581292745047)
                ·
                  refine ⟨4817708278379371939117571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3211805518919581292745047 4817708278379371939117571)
                  ·
                    refine ⟨7226562417569057908676357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4817708278379371939117571 7226562417569057908676357)
                    ·
                      refine ⟨1354980453294198357876817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7226562417569057908676357 1354980453294198357876817)
                      ·
                        rfl

theorem cell23_2638815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_2638815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638815 prefixEnd_2638815 := by exact prefixLift 2638815
  have htrace : WordTrace (prefixWord ++ tailWord_2638815) baseStart_2638815 baseEnd_2638815 := by
    simpa [prefixWord, tailWord_2638815, baseEnd_2638815] using wordTrace_append hprefix tailTrace_2638815
  have hstable : (prefixWord ++ tailWord_2638815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638815).length < 2 ^ (prefixWord ++ tailWord_2638815).sum := by decide
  have hdescent : baseEnd_2638815 < baseStart_2638815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638821 : List Nat := [1, 3, 1, 6, 1, 11]
def baseStart_2638821 : Nat := 118140960795 + 2638821 * 2 ^ 59
def prefixEnd_2638821 : Nat := 4983230072969 + 3 ^ 40 * 2638821 * 2
def baseEnd_2638821 : Nat := 5576063926658951993423

theorem tailTrace_2638821 : CollatzResearch.WordTrace tailWord_2638821 prefixEnd_2638821 5576063926658951993423 := by
  unfold tailWord_2638821
  simp only [CollatzResearch.WordTrace]
  refine ⟨96245708773009666591860317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64163805848673111061240211 96245708773009666591860317)
  ·
    refine ⟨36092140789878624971947619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96245708773009666591860317 36092140789878624971947619)
    ·
      refine ⟨54138211184817937457921429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36092140789878624971947619 54138211184817937457921429)
      ·
        refine ⟨2537728649288340818340067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54138211184817937457921429 2537728649288340818340067)
        ·
          refine ⟨3806592973932511227510101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2537728649288340818340067 3806592973932511227510101)
          ·
            refine ⟨5576063926658951993423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3806592973932511227510101 5576063926658951993423)
            ·
              rfl

theorem cell23_2638821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 11].length) (baseStart_2638821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638821 prefixEnd_2638821 := by exact prefixLift 2638821
  have htrace : WordTrace (prefixWord ++ tailWord_2638821) baseStart_2638821 baseEnd_2638821 := by
    simpa [prefixWord, tailWord_2638821, baseEnd_2638821] using wordTrace_append hprefix tailTrace_2638821
  have hstable : (prefixWord ++ tailWord_2638821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638821).length < 2 ^ (prefixWord ++ tailWord_2638821).sum := by decide
  have hdescent : baseEnd_2638821 < baseStart_2638821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638838 : List Nat := [5, 1, 1, 1, 3, 3, 1, 8]
def baseStart_2638838 : Nat := 118140960795 + 2638838 * 2 ^ 59
def prefixEnd_2638838 : Nat := 4983230072969 + 3 ^ 40 * 2638838 * 2
def baseEnd_2638838 : Nat := 50184898642564880292193

theorem tailTrace_2638838 : CollatzResearch.WordTrace tailWord_2638838 prefixEnd_2638838 50184898642564880292193 := by
  unfold tailWord_2638838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6015395550871754905951823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64164219209298718996819445 6015395550871754905951823)
  ·
    refine ⟨9023093326307632358927735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6015395550871754905951823 9023093326307632358927735)
    ·
      refine ⟨13534639989461448538391603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9023093326307632358927735 13534639989461448538391603)
      ·
        refine ⟨20301959984192172807587405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13534639989461448538391603 20301959984192172807587405)
        ·
          refine ⟨7613234994072064802845277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20301959984192172807587405 7613234994072064802845277)
          ·
            refine ⟨2854963122777024301066979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7613234994072064802845277 2854963122777024301066979)
            ·
              refine ⟨4282444684165536451600469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2854963122777024301066979 4282444684165536451600469)
              ·
                refine ⟨50184898642564880292193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4282444684165536451600469 50184898642564880292193)
                ·
                  rfl

theorem cell23_2638838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_2638838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638838 prefixEnd_2638838 := by exact prefixLift 2638838
  have htrace : WordTrace (prefixWord ++ tailWord_2638838) baseStart_2638838 baseEnd_2638838 := by
    simpa [prefixWord, tailWord_2638838, baseEnd_2638838] using wordTrace_append hprefix tailTrace_2638838
  have hstable : (prefixWord ++ tailWord_2638838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638838).length < 2 ^ (prefixWord ++ tailWord_2638838).sum := by decide
  have hdescent : baseEnd_2638838 < baseStart_2638838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638864 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 6, 6]
def baseStart_2638864 : Nat := 118140960795 + 2638864 * 2 ^ 59
def prefixEnd_2638864 : Nat := 4983230072969 + 3 ^ 40 * 2638864 * 2
def baseEnd_2638864 : Nat := 451668537948756222054697

theorem tailTrace_2638864 : CollatzResearch.WordTrace tailWord_2638864 prefixEnd_2638864 451668537948756222054697 := by
  unfold tailWord_2638864
  simp only [CollatzResearch.WordTrace]
  refine ⟨48123638555926942467837823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64164851407902589957117097 48123638555926942467837823)
  ·
    refine ⟨72185457833890413701756735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48123638555926942467837823 72185457833890413701756735)
    ·
      refine ⟨108278186750835620552635103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72185457833890413701756735 108278186750835620552635103)
      ·
        refine ⟨162417280126253430828952655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108278186750835620552635103 162417280126253430828952655)
        ·
          refine ⟨243625920189380146243428983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162417280126253430828952655 243625920189380146243428983)
          ·
            refine ⟨365438880284070219365143475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243625920189380146243428983 365438880284070219365143475)
            ·
              refine ⟨548158320426105329047715213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365438880284070219365143475 548158320426105329047715213)
              ·
                refine ⟨205559370159789498392893205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 548158320426105329047715213 205559370159789498392893205)
                ·
                  refine ⟨9635595476240132737166869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 205559370159789498392893205 9635595476240132737166869)
                  ·
                    refine ⟨451668537948756222054697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9635595476240132737166869 451668537948756222054697)
                    ·
                      rfl

theorem cell23_2638864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 6, 6].length) (baseStart_2638864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638864 prefixEnd_2638864 := by exact prefixLift 2638864
  have htrace : WordTrace (prefixWord ++ tailWord_2638864) baseStart_2638864 baseEnd_2638864 := by
    simpa [prefixWord, tailWord_2638864, baseEnd_2638864] using wordTrace_append hprefix tailTrace_2638864
  have hstable : (prefixWord ++ tailWord_2638864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638864).length < 2 ^ (prefixWord ++ tailWord_2638864).sum := by decide
  have hdescent : baseEnd_2638864 < baseStart_2638864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638866 : List Nat := [3, 2, 5, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_2638866 : Nat := 118140960795 + 2638866 * 2 ^ 59
def prefixEnd_2638866 : Nat := 4983230072969 + 3 ^ 40 * 2638866 * 2
def baseEnd_2638866 : Nat := 1355006640807577658339083

theorem tailTrace_2638866 : CollatzResearch.WordTrace tailWord_2638866 prefixEnd_2638866 1355006640807577658339083 := by
  unfold tailWord_2638866
  simp only [CollatzResearch.WordTrace]
  refine ⟨24061837514461659819312113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64164900038564426184832301 24061837514461659819312113)
  ·
    refine ⟨18046378135846244864484085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24061837514461659819312113 18046378135846244864484085)
    ·
      refine ⟨1691847950235585456045383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18046378135846244864484085 1691847950235585456045383)
      ·
        refine ⟨2537771925353378184068075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1691847950235585456045383 2537771925353378184068075)
        ·
          refine ⟨3806657888030067276102113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2537771925353378184068075 3806657888030067276102113)
          ·
            refine ⟨2854993416022550457076585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3806657888030067276102113 2854993416022550457076585)
            ·
              refine ⟨2141245062016912842807439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2854993416022550457076585 2141245062016912842807439)
              ·
                refine ⟨3211867593025369264211159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2141245062016912842807439 3211867593025369264211159)
                ·
                  refine ⟨4817801389538053896316739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3211867593025369264211159 4817801389538053896316739)
                  ·
                    refine ⟨7226702084307080844475109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4817801389538053896316739 7226702084307080844475109)
                    ·
                      refine ⟨1355006640807577658339083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7226702084307080844475109 1355006640807577658339083)
                      ·
                        rfl

theorem cell23_2638866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_2638866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638866 prefixEnd_2638866 := by exact prefixLift 2638866
  have htrace : WordTrace (prefixWord ++ tailWord_2638866) baseStart_2638866 baseEnd_2638866 := by
    simpa [prefixWord, tailWord_2638866, baseEnd_2638866] using wordTrace_append hprefix tailTrace_2638866
  have hstable : (prefixWord ++ tailWord_2638866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638866).length < 2 ^ (prefixWord ++ tailWord_2638866).sum := by decide
  have hdescent : baseEnd_2638866 < baseStart_2638866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638881 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 2, 6]
def baseStart_2638881 : Nat := 118140960795 + 2638881 * 2 ^ 59
def prefixEnd_2638881 : Nat := 4983230072969 + 3 ^ 40 * 2638881 * 2
def baseEnd_2638881 : Nat := 451671447672465033217171

theorem tailTrace_2638881 : CollatzResearch.WordTrace tailWord_2638881 prefixEnd_2638881 451671447672465033217171 := by
  unfold tailWord_2638881
  simp only [CollatzResearch.WordTrace]
  refine ⟨96247897152792296839044497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64165264768528197892696331 96247897152792296839044497)
  ·
    refine ⟨72185922864594222629283373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96247897152792296839044497 72185922864594222629283373)
    ·
      refine ⟨27069721074222833485981265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72185922864594222629283373 27069721074222833485981265)
      ·
        refine ⟨20302290805667125114485949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27069721074222833485981265 20302290805667125114485949)
        ·
          refine ⟨7613359052125171917932231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20302290805667125114485949 7613359052125171917932231)
          ·
            refine ⟨11420038578187757876898347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7613359052125171917932231 11420038578187757876898347)
            ·
              refine ⟨17130057867281636815347521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11420038578187757876898347 17130057867281636815347521)
              ·
                refine ⟨12847543400461227611510641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17130057867281636815347521 12847543400461227611510641)
                ·
                  refine ⟨9635657550345920708632981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12847543400461227611510641 9635657550345920708632981)
                  ·
                    refine ⟨451671447672465033217171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9635657550345920708632981 451671447672465033217171)
                    ·
                      rfl

theorem cell23_2638881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_2638881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638881 prefixEnd_2638881 := by exact prefixLift 2638881
  have htrace : WordTrace (prefixWord ++ tailWord_2638881) baseStart_2638881 baseEnd_2638881 := by
    simpa [prefixWord, tailWord_2638881, baseEnd_2638881] using wordTrace_append hprefix tailTrace_2638881
  have hstable : (prefixWord ++ tailWord_2638881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638881).length < 2 ^ (prefixWord ++ tailWord_2638881).sum := by decide
  have hdescent : baseEnd_2638881 < baseStart_2638881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638882 : List Nat := [3, 3, 1, 1, 1, 5, 1, 2, 2, 1, 3]
def baseStart_2638882 : Nat := 118140960795 + 2638882 * 2 ^ 59
def prefixEnd_2638882 : Nat := 4983230072969 + 3 ^ 40 * 2638882 * 2
def baseEnd_2638882 : Nat := 1355014856498049595739009

theorem tailTrace_2638882 : CollatzResearch.WordTrace tailWord_2638882 prefixEnd_2638882 1355014856498049595739009 := by
  unfold tailWord_2638882
  simp only [CollatzResearch.WordTrace]
  refine ⟨24061983406447168502457725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64165289083859116006553933 24061983406447168502457725)
  ·
    refine ⟨9023243777417688188421647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24061983406447168502457725 9023243777417688188421647)
    ·
      refine ⟨13534865666126532282632471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9023243777417688188421647 13534865666126532282632471)
      ·
        refine ⟨20302298499189798423948707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13534865666126532282632471 20302298499189798423948707)
        ·
          refine ⟨30453447748784697635923061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20302298499189798423948707 30453447748784697635923061)
          ·
            refine ⟨2855010726448565403367787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30453447748784697635923061 2855010726448565403367787)
            ·
              refine ⟨4282516089672848105051681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2855010726448565403367787 4282516089672848105051681)
              ·
                refine ⟨3211887067254636078788761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4282516089672848105051681 3211887067254636078788761)
                ·
                  refine ⟨2408915300440977059091571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3211887067254636078788761 2408915300440977059091571)
                  ·
                    refine ⟨3613372950661465588637357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2408915300440977059091571 3613372950661465588637357)
                    ·
                      refine ⟨1355014856498049595739009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3613372950661465588637357 1355014856498049595739009)
                      ·
                        rfl

theorem cell23_2638882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_2638882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638882 prefixEnd_2638882 := by exact prefixLift 2638882
  have htrace : WordTrace (prefixWord ++ tailWord_2638882) baseStart_2638882 baseEnd_2638882 := by
    simpa [prefixWord, tailWord_2638882, baseEnd_2638882] using wordTrace_append hprefix tailTrace_2638882
  have hstable : (prefixWord ++ tailWord_2638882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638882).length < 2 ^ (prefixWord ++ tailWord_2638882).sum := by decide
  have hdescent : baseEnd_2638882 < baseStart_2638882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638905 : List Nat := [1, 2, 1, 5, 2, 1, 3, 1, 1, 4, 2]
def baseStart_2638905 : Nat := 118140960795 + 2638905 * 2 ^ 59
def prefixEnd_2638905 : Nat := 4983230072969 + 3 ^ 40 * 2638905 * 2
def baseEnd_2638905 : Nat := 1355026666553103005751403

theorem tailTrace_2638905 : CollatzResearch.WordTrace tailWord_2638905 prefixEnd_2638905 1355026666553103005751403 := by
  unfold tailWord_2638905
  simp only [CollatzResearch.WordTrace]
  refine ⟨96248772504705348937918169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64165848336470232625278779 96248772504705348937918169)
  ·
    refine ⟨72186579378529011703438627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96248772504705348937918169 72186579378529011703438627)
    ·
      refine ⟨108279869067793517555157941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72186579378529011703438627 108279869067793517555157941)
      ·
        refine ⟨10151237725105642270796057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108279869067793517555157941 10151237725105642270796057)
        ·
          refine ⟨7613428293829231703097043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10151237725105642270796057 7613428293829231703097043)
          ·
            refine ⟨11420142440743847554645565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7613428293829231703097043 11420142440743847554645565)
            ·
              refine ⟨4282553415278942832992087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11420142440743847554645565 4282553415278942832992087)
              ·
                refine ⟨6423830122918414249488131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4282553415278942832992087 6423830122918414249488131)
                ·
                  refine ⟨9635745184377621374232197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6423830122918414249488131 9635745184377621374232197)
                  ·
                    refine ⟨1806702222070804007668537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9635745184377621374232197 1806702222070804007668537)
                    ·
                      refine ⟨1355026666553103005751403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1806702222070804007668537 1355026666553103005751403)
                      ·
                        rfl

theorem cell23_2638905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_2638905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638905 prefixEnd_2638905 := by exact prefixLift 2638905
  have htrace : WordTrace (prefixWord ++ tailWord_2638905) baseStart_2638905 baseEnd_2638905 := by
    simpa [prefixWord, tailWord_2638905, baseEnd_2638905] using wordTrace_append hprefix tailTrace_2638905
  have hstable : (prefixWord ++ tailWord_2638905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638905).length < 2 ^ (prefixWord ++ tailWord_2638905).sum := by decide
  have hdescent : baseEnd_2638905 < baseStart_2638905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638921 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 4, 3, 3]
def baseStart_2638921 : Nat := 118140960795 + 2638921 * 2 ^ 59
def prefixEnd_2638921 : Nat := 4983230072969 + 3 ^ 40 * 2638921 * 2
def baseEnd_2638921 : Nat := 1355034882243574943151329

theorem tailTrace_2638921 : CollatzResearch.WordTrace tailWord_2638921 prefixEnd_2638921 1355034882243574943151329 := by
  unfold tailWord_2638921
  simp only [CollatzResearch.WordTrace]
  refine ⟨96249356072647383670500617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64166237381764922447000411 96249356072647383670500617)
  ·
    refine ⟨72187017054485537752875463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96249356072647383670500617 72187017054485537752875463)
    ·
      refine ⟨108280525581728306629313195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72187017054485537752875463 108280525581728306629313195)
      ·
        refine ⟨162420788372592459943969793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108280525581728306629313195 162420788372592459943969793)
        ·
          refine ⟨121815591279444344957977345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162420788372592459943969793 121815591279444344957977345)
          ·
            refine ⟨91361693459583258718483009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121815591279444344957977345 91361693459583258718483009)
            ·
              refine ⟨68521270094687444038862257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91361693459583258718483009 68521270094687444038862257)
              ·
                refine ⟨51390952571015583029146693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68521270094687444038862257 51390952571015583029146693)
                ·
                  refine ⟨9635803607065421817965005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51390952571015583029146693 9635803607065421817965005)
                  ·
                    refine ⟨3613426352649533181736877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9635803607065421817965005 3613426352649533181736877)
                    ·
                      refine ⟨1355034882243574943151329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3613426352649533181736877 1355034882243574943151329)
                      ·
                        rfl

theorem cell23_2638921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 3, 3].length) (baseStart_2638921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638921 prefixEnd_2638921 := by exact prefixLift 2638921
  have htrace : WordTrace (prefixWord ++ tailWord_2638921) baseStart_2638921 baseEnd_2638921 := by
    simpa [prefixWord, tailWord_2638921, baseEnd_2638921] using wordTrace_append hprefix tailTrace_2638921
  have hstable : (prefixWord ++ tailWord_2638921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638921).length < 2 ^ (prefixWord ++ tailWord_2638921).sum := by decide
  have hdescent : baseEnd_2638921 < baseStart_2638921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638948 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 2, 5, 2]
def baseStart_2638948 : Nat := 118140960795 + 2638948 * 2 ^ 59
def prefixEnd_2638948 : Nat := 4983230072969 + 3 ^ 40 * 2638948 * 2
def baseEnd_2638948 : Nat := 1355048746221246337513705

theorem tailTrace_2638948 : CollatzResearch.WordTrace tailWord_2638948 prefixEnd_2638948 1355048746221246337513705 := by
  unfold tailWord_2638948
  simp only [CollatzResearch.WordTrace]
  refine ⟨48125170421774783640866749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64166893895699711521155665 48125170421774783640866749)
  ·
    refine ⟨18046938908165543865325031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48125170421774783640866749 18046938908165543865325031)
    ·
      refine ⟨27070408362248315797987547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18046938908165543865325031 27070408362248315797987547)
      ·
        refine ⟨40605612543372473696981321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27070408362248315797987547 40605612543372473696981321)
        ·
          refine ⟨30454209407529355272735991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40605612543372473696981321 30454209407529355272735991)
          ·
            refine ⟨45681314111294032909103987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30454209407529355272735991 45681314111294032909103987)
            ·
              refine ⟨68521971166941049363655981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45681314111294032909103987 68521971166941049363655981)
              ·
                refine ⟨25695739187602893511370993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68521971166941049363655981 25695739187602893511370993)
                ·
                  refine ⟨19271804390702170133528245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25695739187602893511370993 19271804390702170133528245)
                  ·
                    refine ⟨1806731661628328450018273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19271804390702170133528245 1806731661628328450018273)
                    ·
                      refine ⟨1355048746221246337513705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1806731661628328450018273 1355048746221246337513705)
                      ·
                        rfl

theorem cell23_2638948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_2638948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638948 prefixEnd_2638948 := by exact prefixLift 2638948
  have htrace : WordTrace (prefixWord ++ tailWord_2638948) baseStart_2638948 baseEnd_2638948 := by
    simpa [prefixWord, tailWord_2638948, baseEnd_2638948] using wordTrace_append hprefix tailTrace_2638948
  have hstable : (prefixWord ++ tailWord_2638948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638948).length < 2 ^ (prefixWord ++ tailWord_2638948).sum := by decide
  have hdescent : baseEnd_2638948 < baseStart_2638948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638951 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_2638951 : Nat := 118140960795 + 2638951 * 2 ^ 59
def prefixEnd_2638951 : Nat := 4983230072969 + 3 ^ 40 * 2638951 * 2
def baseEnd_2638951 : Nat := 1355050286663209825776191

theorem tailTrace_2638951 : CollatzResearch.WordTrace tailWord_2638951 prefixEnd_2638951 1355050286663209825776191 := by
  unfold tailWord_2638951
  simp only [CollatzResearch.WordTrace]
  refine ⟨96250450262538698794092707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64166966841692465862728471 96250450262538698794092707)
  ·
    refine ⟨144375675393808048191139061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96250450262538698794092707 144375675393808048191139061)
    ·
      refine ⟨13535219568169504517919287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144375675393808048191139061 13535219568169504517919287)
      ·
        refine ⟨20302829352254256776878931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13535219568169504517919287 20302829352254256776878931)
        ·
          refine ⟨30454244028381385165318397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20302829352254256776878931 30454244028381385165318397)
          ·
            refine ⟨11420341510643019436994399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30454244028381385165318397 11420341510643019436994399)
            ·
              refine ⟨17130512265964529155491599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11420341510643019436994399 17130512265964529155491599)
              ·
                refine ⟨25695768398946793733237399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17130512265964529155491599 25695768398946793733237399)
                ·
                  refine ⟨38543652598420190599856099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25695768398946793733237399 38543652598420190599856099)
                  ·
                    refine ⟨57815478897630285899784149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38543652598420190599856099 57815478897630285899784149)
                    ·
                      refine ⟨1355050286663209825776191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 57815478897630285899784149 1355050286663209825776191)
                      ·
                        rfl

theorem cell23_2638951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_2638951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638951 prefixEnd_2638951 := by exact prefixLift 2638951
  have htrace : WordTrace (prefixWord ++ tailWord_2638951) baseStart_2638951 baseEnd_2638951 := by
    simpa [prefixWord, tailWord_2638951, baseEnd_2638951] using wordTrace_append hprefix tailTrace_2638951
  have hstable : (prefixWord ++ tailWord_2638951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638951).length < 2 ^ (prefixWord ++ tailWord_2638951).sum := by decide
  have hdescent : baseEnd_2638951 < baseStart_2638951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2638961 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 1, 3, 4]
def baseStart_2638961 : Nat := 118140960795 + 2638961 * 2 ^ 59
def prefixEnd_2638961 : Nat := 4983230072969 + 3 ^ 40 * 2638961 * 2
def baseEnd_2638961 : Nat := 1355055421469754786651145

theorem tailTrace_2638961 : CollatzResearch.WordTrace tailWord_2638961 prefixEnd_2638961 1355055421469754786651145 := by
  unfold tailWord_2638961
  simp only [CollatzResearch.WordTrace]
  refine ⟨96250814992502470501956737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64167209995001647001304491 96250814992502470501956737)
  ·
    refine ⟨72188111244376852876467553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96250814992502470501956737 72188111244376852876467553)
    ·
      refine ⟨54141083433282639657350665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72188111244376852876467553 54141083433282639657350665)
      ·
        refine ⟨40605812574961979743012999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54141083433282639657350665 40605812574961979743012999)
        ·
          refine ⟨60908718862442969614519499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40605812574961979743012999 60908718862442969614519499)
          ·
            refine ⟨91363078293664454421779249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60908718862442969614519499 91363078293664454421779249)
            ·
              refine ⟨68522308720248340816334437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91363078293664454421779249 68522308720248340816334437)
              ·
                refine ⟨12847932885046563903062707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68522308720248340816334437 12847932885046563903062707)
                ·
                  refine ⟨19271899327569845854594061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12847932885046563903062707 19271899327569845854594061)
                  ·
                    refine ⟨7226962247838692195472773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19271899327569845854594061 7226962247838692195472773)
                    ·
                      refine ⟨1355055421469754786651145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7226962247838692195472773 1355055421469754786651145)
                      ·
                        rfl

theorem cell23_2638961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_2638961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2638961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2638961 prefixEnd_2638961 := by exact prefixLift 2638961
  have htrace : WordTrace (prefixWord ++ tailWord_2638961) baseStart_2638961 baseEnd_2638961 := by
    simpa [prefixWord, tailWord_2638961, baseEnd_2638961] using wordTrace_append hprefix tailTrace_2638961
  have hstable : (prefixWord ++ tailWord_2638961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2638961).length < 2 ^ (prefixWord ++ tailWord_2638961).sum := by decide
  have hdescent : baseEnd_2638961 < baseStart_2638961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2638961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639098 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4]
def baseStart_2639098 : Nat := 118140960795 + 2639098 * 2 ^ 59
def prefixEnd_2639098 : Nat := 4983230072969 + 3 ^ 40 * 2639098 * 2
def baseEnd_2639098 : Nat := 1355125768319420750638015

theorem tailTrace_2639098 : CollatzResearch.WordTrace tailWord_2639098 prefixEnd_2639098 1355125768319420750638015 := by
  unfold tailWord_2639098
  simp only [CollatzResearch.WordTrace]
  refine ⟨24063952948251535724923487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64170541195337428599795965 24063952948251535724923487)
  ·
    refine ⟨36095929422377303587385231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24063952948251535724923487 36095929422377303587385231)
    ·
      refine ⟨54143894133565955381077847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36095929422377303587385231 54143894133565955381077847)
      ·
        refine ⟨81215841200348933071616771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54143894133565955381077847 81215841200348933071616771)
        ·
          refine ⟨121823761800523399607425157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81215841200348933071616771 121823761800523399607425157)
          ·
            refine ⟨22841955337598137426392217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121823761800523399607425157 22841955337598137426392217)
            ·
              refine ⟨17131466503198603069794163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22841955337598137426392217 17131466503198603069794163)
              ·
                refine ⟨25697199754797904604691245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17131466503198603069794163 25697199754797904604691245)
                ·
                  refine ⟨9636449908049214226759217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25697199754797904604691245 9636449908049214226759217)
                  ·
                    refine ⟨7227337431036910670069413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9636449908049214226759217 7227337431036910670069413)
                    ·
                      refine ⟨1355125768319420750638015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7227337431036910670069413 1355125768319420750638015)
                      ·
                        rfl

theorem cell23_2639098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_2639098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639098 prefixEnd_2639098 := by exact prefixLift 2639098
  have htrace : WordTrace (prefixWord ++ tailWord_2639098) baseStart_2639098 baseEnd_2639098 := by
    simpa [prefixWord, tailWord_2639098, baseEnd_2639098] using wordTrace_append hprefix tailTrace_2639098
  have hstable : (prefixWord ++ tailWord_2639098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639098).length < 2 ^ (prefixWord ++ tailWord_2639098).sum := by decide
  have hdescent : baseEnd_2639098 < baseStart_2639098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639102 : List Nat := [4, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_2639102 : Nat := 118140960795 + 2639102 * 2 ^ 59
def prefixEnd_2639102 : Nat := 4983230072969 + 3 ^ 40 * 2639102 * 2
def baseEnd_2639102 : Nat := 1355127822242038734987997

theorem tailTrace_2639102 : CollatzResearch.WordTrace tailWord_2639102 prefixEnd_2639102 1355127822242038734987997 := by
  unfold tailWord_2639102
  simp only [CollatzResearch.WordTrace]
  refine ⟨12031994710623956447854945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64170638456661101055226373 12031994710623956447854945)
  ·
    refine ⟨9023996032967967335891209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12031994710623956447854945 9023996032967967335891209)
    ·
      refine ⟨6767997024725975501918407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9023996032967967335891209 6767997024725975501918407)
      ·
        refine ⟨10151995537088963252877611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6767997024725975501918407 10151995537088963252877611)
        ·
          refine ⟨15227993305633444879316417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10151995537088963252877611 15227993305633444879316417)
          ·
            refine ⟨11420994979225083659487313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15227993305633444879316417 11420994979225083659487313)
            ·
              refine ⟨8565746234418812744615485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11420994979225083659487313 8565746234418812744615485)
              ·
                refine ⟨3212154837907054779230807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8565746234418812744615485 3212154837907054779230807)
                ·
                  refine ⟨4818232256860582168846211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3212154837907054779230807 4818232256860582168846211)
                  ·
                    refine ⟨7227348385290873253269317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4818232256860582168846211 7227348385290873253269317)
                    ·
                      refine ⟨1355127822242038734987997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7227348385290873253269317 1355127822242038734987997)
                      ·
                        rfl

theorem cell23_2639102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_2639102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639102 prefixEnd_2639102 := by exact prefixLift 2639102
  have htrace : WordTrace (prefixWord ++ tailWord_2639102) baseStart_2639102 baseEnd_2639102 := by
    simpa [prefixWord, tailWord_2639102, baseEnd_2639102] using wordTrace_append hprefix tailTrace_2639102
  have hstable : (prefixWord ++ tailWord_2639102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639102).length < 2 ^ (prefixWord ++ tailWord_2639102).sum := by decide
  have hdescent : baseEnd_2639102 < baseStart_2639102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639105 : List Nat := [1, 2, 4, 1, 1, 4, 2, 1, 1, 1, 5]
def baseStart_2639105 : Nat := 118140960795 + 2639105 * 2 ^ 59
def prefixEnd_2639105 : Nat := 4983230072969 + 3 ^ 40 * 2639105 * 2
def baseEnd_2639105 : Nat := 1355129362684002223250483

theorem tailTrace_2639105 : CollatzResearch.WordTrace tailWord_2639105 prefixEnd_2639105 1355129362684002223250483 := by
  unfold tailWord_2639105
  simp only [CollatzResearch.WordTrace]
  refine ⟨96256067103980783095198769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64170711402653855396799179 96256067103980783095198769)
  ·
    refine ⟨72192050327985587321399077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96256067103980783095198769 72192050327985587321399077)
    ·
      refine ⟨13536009436497297622762327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72192050327985587321399077 13536009436497297622762327)
      ·
        refine ⟨20304014154745946434143491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13536009436497297622762327 20304014154745946434143491)
        ·
          refine ⟨30456021232118919651215237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20304014154745946434143491 30456021232118919651215237)
          ·
            refine ⟨5710503981022297434602857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30456021232118919651215237 5710503981022297434602857)
            ·
              refine ⟨4282877985766723075952143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5710503981022297434602857 4282877985766723075952143)
              ·
                refine ⟨6424316978650084613928215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4282877985766723075952143 6424316978650084613928215)
                ·
                  refine ⟨9636475467975126920892323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6424316978650084613928215 9636475467975126920892323)
                  ·
                    refine ⟨14454713201962690381338485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9636475467975126920892323 14454713201962690381338485)
                    ·
                      refine ⟨1355129362684002223250483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14454713201962690381338485 1355129362684002223250483)
                      ·
                        rfl

theorem cell23_2639105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_2639105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639105 prefixEnd_2639105 := by exact prefixLift 2639105
  have htrace : WordTrace (prefixWord ++ tailWord_2639105) baseStart_2639105 baseEnd_2639105 := by
    simpa [prefixWord, tailWord_2639105, baseEnd_2639105] using wordTrace_append hprefix tailTrace_2639105
  have hstable : (prefixWord ++ tailWord_2639105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639105).length < 2 ^ (prefixWord ++ tailWord_2639105).sum := by decide
  have hdescent : baseEnd_2639105 < baseStart_2639105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639108 : List Nat := [2, 3, 2, 2, 2, 1, 11]
def baseStart_2639108 : Nat := 118140960795 + 2639108 * 2 ^ 59
def prefixEnd_2639108 : Nat := 4983230072969 + 3 ^ 40 * 2639108 * 2
def baseEnd_2639108 : Nat := 16730011149703280389049

theorem tailTrace_2639108 : CollatzResearch.WordTrace tailWord_2639108 prefixEnd_2639108 16730011149703280389049 := by
  unfold tailWord_2639108
  simp only [CollatzResearch.WordTrace]
  refine ⟨48128088261484957303778989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64170784348646609738371985 48128088261484957303778989)
  ·
    refine ⟨18048033098056858988917121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48128088261484957303778989 18048033098056858988917121)
    ·
      refine ⟨13536024823542644241687841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18048033098056858988917121 13536024823542644241687841)
      ·
        refine ⟨10152018617656983181265881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13536024823542644241687841 10152018617656983181265881)
        ·
          refine ⟨7614013963242737385949411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10152018617656983181265881 7614013963242737385949411)
          ·
            refine ⟨11421020944864106078924117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7614013963242737385949411 11421020944864106078924117)
            ·
              refine ⟨16730011149703280389049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11421020944864106078924117 16730011149703280389049)
              ·
                rfl

theorem cell23_2639108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 11].length) (baseStart_2639108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639108 prefixEnd_2639108 := by exact prefixLift 2639108
  have htrace : WordTrace (prefixWord ++ tailWord_2639108) baseStart_2639108 baseEnd_2639108 := by
    simpa [prefixWord, tailWord_2639108, baseEnd_2639108] using wordTrace_append hprefix tailTrace_2639108
  have hstable : (prefixWord ++ tailWord_2639108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639108).length < 2 ^ (prefixWord ++ tailWord_2639108).sum := by decide
  have hdescent : baseEnd_2639108 < baseStart_2639108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639168 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 2, 6]
def baseStart_2639168 : Nat := 118140960795 + 2639168 * 2 ^ 59
def prefixEnd_2639168 : Nat := 4983230072969 + 3 ^ 40 * 2639168 * 2
def baseEnd_2639168 : Nat := 451720570655078492254231

theorem tailTrace_2639168 : CollatzResearch.WordTrace tailWord_2639168 prefixEnd_2639168 451720570655078492254231 := by
  unfold tailWord_2639168
  simp only [CollatzResearch.WordTrace]
  refine ⟨48129182451376272427371079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64172243268501696569828105 48129182451376272427371079)
  ·
    refine ⟨72193773677064408641056619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48129182451376272427371079 72193773677064408641056619)
    ·
      refine ⟨108290660515596612961584929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72193773677064408641056619 108290660515596612961584929)
      ·
        refine ⟨81217995386697459721188697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108290660515596612961584929 81217995386697459721188697)
        ·
          refine ⟨60913496540023094790891523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81217995386697459721188697 60913496540023094790891523)
          ·
            refine ⟨91370244810034642186337285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60913496540023094790891523 91370244810034642186337285)
            ·
              refine ⟨17131920901881495409938241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91370244810034642186337285 17131920901881495409938241)
              ·
                refine ⟨12848940676411121557453681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17131920901881495409938241 12848940676411121557453681)
                ·
                  refine ⟨9636705507308341168090261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12848940676411121557453681 9636705507308341168090261)
                  ·
                    refine ⟨451720570655078492254231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9636705507308341168090261 451720570655078492254231)
                    ·
                      rfl

theorem cell23_2639168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 2, 6].length) (baseStart_2639168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639168 prefixEnd_2639168 := by exact prefixLift 2639168
  have htrace : WordTrace (prefixWord ++ tailWord_2639168) baseStart_2639168 baseEnd_2639168 := by
    simpa [prefixWord, tailWord_2639168, baseEnd_2639168] using wordTrace_append hprefix tailTrace_2639168
  have hstable : (prefixWord ++ tailWord_2639168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639168).length < 2 ^ (prefixWord ++ tailWord_2639168).sum := by decide
  have hdescent : baseEnd_2639168 < baseStart_2639168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639169 : List Nat := [1, 2, 5, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_2639169 : Nat := 118140960795 + 2639169 * 2 ^ 59
def prefixEnd_2639169 : Nat := 4983230072969 + 3 ^ 40 * 2639169 * 2
def baseEnd_2639169 : Nat := 1355162225445889972850189

theorem tailTrace_2639169 : CollatzResearch.WordTrace tailWord_2639169 prefixEnd_2639169 1355162225445889972850189 := by
  unfold tailWord_2639169
  simp only [CollatzResearch.WordTrace]
  refine ⟨96258401375748922025528561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64172267583832614683685707 96258401375748922025528561)
  ·
    refine ⟨72193801031811691519146421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96258401375748922025528561 72193801031811691519146421)
    ·
      refine ⟨6768168846732346079919977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72193801031811691519146421 6768168846732346079919977)
      ·
        refine ⟨5076126635049259559939983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6768168846732346079919977 5076126635049259559939983)
        ·
          refine ⟨7614189952573889339909975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5076126635049259559939983 7614189952573889339909975)
          ·
            refine ⟨11421284928860834009864963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7614189952573889339909975 11421284928860834009864963)
            ·
              refine ⟨17131927393291251014797445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11421284928860834009864963 17131927393291251014797445)
              ·
                refine ⟨3212236386242109565274521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17131927393291251014797445 3212236386242109565274521)
                ·
                  refine ⟨2409177289681582173955891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3212236386242109565274521 2409177289681582173955891)
                  ·
                    refine ⟨3613765934522373260933837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2409177289681582173955891 3613765934522373260933837)
                    ·
                      refine ⟨1355162225445889972850189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3613765934522373260933837 1355162225445889972850189)
                      ·
                        rfl

theorem cell23_2639169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_2639169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639169 prefixEnd_2639169 := by exact prefixLift 2639169
  have htrace : WordTrace (prefixWord ++ tailWord_2639169) baseStart_2639169 baseEnd_2639169 := by
    simpa [prefixWord, tailWord_2639169, baseEnd_2639169] using wordTrace_append hprefix tailTrace_2639169
  have hstable : (prefixWord ++ tailWord_2639169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639169).length < 2 ^ (prefixWord ++ tailWord_2639169).sum := by decide
  have hdescent : baseEnd_2639169 < baseStart_2639169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639178 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_2639178 : Nat := 118140960795 + 2639178 * 2 ^ 59
def prefixEnd_2639178 : Nat := 4983230072969 + 3 ^ 40 * 2639178 * 2
def baseEnd_2639178 : Nat := 1355166846771780437637647

theorem tailTrace_2639178 : CollatzResearch.WordTrace tailWord_2639178 prefixEnd_2639178 1355166846771780437637647 := by
  unfold tailWord_2639178
  simp only [CollatzResearch.WordTrace]
  refine ⟨24064682408179079140651547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64172486421810877708404125 24064682408179079140651547)
  ·
    refine ⟨36097023612268618710977321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24064682408179079140651547 36097023612268618710977321)
    ·
      refine ⟨27072767709201464033232991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36097023612268618710977321 27072767709201464033232991)
      ·
        refine ⟨40609151563802196049849487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27072767709201464033232991 40609151563802196049849487)
        ·
          refine ⟨60913727345703294074774231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40609151563802196049849487 60913727345703294074774231)
          ·
            refine ⟨91370591018554941112161347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60913727345703294074774231 91370591018554941112161347)
            ·
              refine ⟨137055886527832411668242021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91370591018554941112161347 137055886527832411668242021)
              ·
                refine ⟨25697978723968577187795379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137055886527832411668242021 25697978723968577187795379)
                ·
                  refine ⟨38546968085952865781693069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25697978723968577187795379 38546968085952865781693069)
                  ·
                    refine ⟨14455113032232324668134901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38546968085952865781693069 14455113032232324668134901)
                    ·
                      refine ⟨1355166846771780437637647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14455113032232324668134901 1355166846771780437637647)
                      ·
                        rfl

theorem cell23_2639178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_2639178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639178 prefixEnd_2639178 := by exact prefixLift 2639178
  have htrace : WordTrace (prefixWord ++ tailWord_2639178) baseStart_2639178 baseEnd_2639178 := by
    simpa [prefixWord, tailWord_2639178, baseEnd_2639178] using wordTrace_append hprefix tailTrace_2639178
  have hstable : (prefixWord ++ tailWord_2639178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639178).length < 2 ^ (prefixWord ++ tailWord_2639178).sum := by decide
  have hdescent : baseEnd_2639178 < baseStart_2639178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639192 : List Nat := [2, 1, 2, 2, 1, 1, 6, 1, 1, 4, 2]
def baseStart_2639192 : Nat := 118140960795 + 2639192 * 2 ^ 59
def prefixEnd_2639192 : Nat := 4983230072969 + 3 ^ 40 * 2639192 * 2
def baseEnd_2639192 : Nat := 1355174035500943382862583

theorem tailTrace_2639192 : CollatzResearch.WordTrace tailWord_2639192 prefixEnd_2639192 1355174035500943382862583 := by
  unfold tailWord_2639192
  simp only [CollatzResearch.WordTrace]
  refine ⟨48129620127332798476807915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64172826836443731302410553 48129620127332798476807915)
  ·
    refine ⟨72194430190999197715211873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48129620127332798476807915 72194430190999197715211873)
    ·
      refine ⟨54145822643249398286408905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72194430190999197715211873 54145822643249398286408905)
      ·
        refine ⟨40609366982437048714806679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54145822643249398286408905 40609366982437048714806679)
        ·
          refine ⟨60914050473655573072210019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40609366982437048714806679 60914050473655573072210019)
          ·
            refine ⟨91371075710483359608315029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60914050473655573072210019 91371075710483359608315029)
            ·
              refine ⟨4283019173928907481639767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91371075710483359608315029 4283019173928907481639767)
              ·
                refine ⟨6424528760893361222459651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4283019173928907481639767 6424528760893361222459651)
                ·
                  refine ⟨9636793141340041833689477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6424528760893361222459651 9636793141340041833689477)
                  ·
                    refine ⟨1806898714001257843816777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9636793141340041833689477 1806898714001257843816777)
                    ·
                      refine ⟨1355174035500943382862583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1806898714001257843816777 1355174035500943382862583)
                      ·
                        rfl

theorem cell23_2639192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_2639192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639192 prefixEnd_2639192 := by exact prefixLift 2639192
  have htrace : WordTrace (prefixWord ++ tailWord_2639192) baseStart_2639192 baseEnd_2639192 := by
    simpa [prefixWord, tailWord_2639192, baseEnd_2639192] using wordTrace_append hprefix tailTrace_2639192
  have hstable : (prefixWord ++ tailWord_2639192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639192).length < 2 ^ (prefixWord ++ tailWord_2639192).sum := by decide
  have hdescent : baseEnd_2639192 < baseStart_2639192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639225 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 2, 3, 3]
def baseStart_2639225 : Nat := 118140960795 + 2639225 * 2 ^ 59
def prefixEnd_2639225 : Nat := 4983230072969 + 3 ^ 40 * 2639225 * 2
def baseEnd_2639225 : Nat := 1355190980362541753749931

theorem tailTrace_2639225 : CollatzResearch.WordTrace tailWord_2639225 prefixEnd_2639225 1355190980362541753749931 := by
  unfold tailWord_2639225
  simp only [CollatzResearch.WordTrace]
  refine ⟨96260443863546043589567129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64173629242364029059711419 96260443863546043589567129)
  ·
    refine ⟨72195332897659532692175347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96260443863546043589567129 72195332897659532692175347)
    ·
      refine ⟨108292999346489299038263021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72195332897659532692175347 108292999346489299038263021)
      ·
        refine ⟨40609874754933487139348633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108292999346489299038263021 40609874754933487139348633)
        ·
          refine ⟨30457406066200115354511475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40609874754933487139348633 30457406066200115354511475)
          ·
            refine ⟨45686109099300173031767213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30457406066200115354511475 45686109099300173031767213)
            ·
              refine ⟨17132290912237564886912705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45686109099300173031767213 17132290912237564886912705)
              ·
                refine ⟨12849218184178173665184529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17132290912237564886912705 12849218184178173665184529)
                ·
                  refine ⟨9636913638133630248888397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12849218184178173665184529 9636913638133630248888397)
                  ·
                    refine ⟨3613842614300111343333149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9636913638133630248888397 3613842614300111343333149)
                    ·
                      refine ⟨1355190980362541753749931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3613842614300111343333149 1355190980362541753749931)
                      ·
                        rfl

theorem cell23_2639225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_2639225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639225 prefixEnd_2639225 := by exact prefixLift 2639225
  have htrace : WordTrace (prefixWord ++ tailWord_2639225) baseStart_2639225 baseEnd_2639225 := by
    simpa [prefixWord, tailWord_2639225, baseEnd_2639225] using wordTrace_append hprefix tailTrace_2639225
  have hstable : (prefixWord ++ tailWord_2639225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639225).length < 2 ^ (prefixWord ++ tailWord_2639225).sum := by decide
  have hdescent : baseEnd_2639225 < baseStart_2639225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639282 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2]
def baseStart_2639282 : Nat := 118140960795 + 2639282 * 2 ^ 59
def prefixEnd_2639282 : Nat := 4983230072969 + 3 ^ 40 * 2639282 * 2
def baseEnd_2639282 : Nat := 1355220248759848030737169

theorem tailTrace_2639282 : CollatzResearch.WordTrace tailWord_2639282 prefixEnd_2639282 1355220248759848030737169 := by
  unfold tailWord_2639282
  simp only [CollatzResearch.WordTrace]
  refine ⟨24065630706084885581098025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64175015216226361549594733 24065630706084885581098025)
  ·
    refine ⟨18049223029563664185823519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24065630706084885581098025 18049223029563664185823519)
    ·
      refine ⟨27073834544345496278735279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18049223029563664185823519 27073834544345496278735279)
      ·
        refine ⟨40610751816518244418102919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27073834544345496278735279 40610751816518244418102919)
        ·
          refine ⟨60916127724777366627154379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40610751816518244418102919 60916127724777366627154379)
          ·
            refine ⟨91374191587166049940731569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60916127724777366627154379 91374191587166049940731569)
            ·
              refine ⟨68530643690374537455548677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91374191587166049940731569 68530643690374537455548677)
              ·
                refine ⟨12849495691945225772915377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68530643690374537455548677 12849495691945225772915377)
                ·
                  refine ⟨9637121768958919329686533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12849495691945225772915377 9637121768958919329686533)
                  ·
                    refine ⟨1806960331679797374316225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9637121768958919329686533 1806960331679797374316225)
                    ·
                      refine ⟨1355220248759848030737169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1806960331679797374316225 1355220248759848030737169)
                      ·
                        rfl

theorem cell23_2639282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_2639282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639282 prefixEnd_2639282 := by exact prefixLift 2639282
  have htrace : WordTrace (prefixWord ++ tailWord_2639282) baseStart_2639282 baseEnd_2639282 := by
    simpa [prefixWord, tailWord_2639282, baseEnd_2639282] using wordTrace_append hprefix tailTrace_2639282
  have hstable : (prefixWord ++ tailWord_2639282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639282).length < 2 ^ (prefixWord ++ tailWord_2639282).sum := by decide
  have hdescent : baseEnd_2639282 < baseStart_2639282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639389 : List Nat := [1, 4, 2, 2, 1, 1, 3, 3, 1, 1, 4]
def baseStart_2639389 : Nat := 118140960795 + 2639389 * 2 ^ 59
def prefixEnd_2639389 : Nat := 4983230072969 + 3 ^ 40 * 2639389 * 2
def baseEnd_2639389 : Nat := 1355275191189879112099177

theorem tailTrace_2639389 : CollatzResearch.WordTrace tailWord_2639389 prefixEnd_2639389 1355275191189879112099177 := by
  unfold tailWord_2639389
  simp only [CollatzResearch.WordTrace]
  refine ⟨96266425434951899598537221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64177616956634599732358147 96266425434951899598537221)
  ·
    refine ⟨18049954769053481174725729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96266425434951899598537221 18049954769053481174725729)
    ·
      refine ⟨13537466076790110881044297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18049954769053481174725729 13537466076790110881044297)
      ·
        refine ⟨10153099557592583160783223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13537466076790110881044297 10153099557592583160783223)
        ·
          refine ⟨15229649336388874741174835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10153099557592583160783223 15229649336388874741174835)
          ·
            refine ⟨22844474004583312111762253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15229649336388874741174835 22844474004583312111762253)
            ·
              refine ⟨8566677751718742041910845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22844474004583312111762253 8566677751718742041910845)
              ·
                refine ⟨3212504156894528265716567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8566677751718742041910845 3212504156894528265716567)
                ·
                  refine ⟨4818756235341792398574851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3212504156894528265716567 4818756235341792398574851)
                  ·
                    refine ⟨7228134353012688597862277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4818756235341792398574851 7228134353012688597862277)
                    ·
                      refine ⟨1355275191189879112099177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7228134353012688597862277 1355275191189879112099177)
                      ·
                        rfl

theorem cell23_2639389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_2639389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639389 prefixEnd_2639389 := by exact prefixLift 2639389
  have htrace : WordTrace (prefixWord ++ tailWord_2639389) baseStart_2639389 baseEnd_2639389 := by
    simpa [prefixWord, tailWord_2639389, baseEnd_2639389] using wordTrace_append hprefix tailTrace_2639389
  have hstable : (prefixWord ++ tailWord_2639389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639389).length < 2 ^ (prefixWord ++ tailWord_2639389).sum := by decide
  have hdescent : baseEnd_2639389 < baseStart_2639389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639390 : List Nat := [4, 3, 3, 1, 1, 2, 1, 2, 6]
def baseStart_2639390 : Nat := 118140960795 + 2639390 * 2 ^ 59
def prefixEnd_2639390 : Nat := 4983230072969 + 3 ^ 40 * 2639390 * 2
def baseEnd_2639390 : Nat := 150586189407837067576297

theorem tailTrace_2639390 : CollatzResearch.WordTrace tailWord_2639390 prefixEnd_2639390 150586189407837067576297 := by
  unfold tailWord_2639390
  simp only [CollatzResearch.WordTrace]
  refine ⟨12033307738493534596165453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64177641271965517846215749 12033307738493534596165453)
  ·
    refine ⟨4512490401935075473562045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12033307738493534596165453 4512490401935075473562045)
    ·
      refine ⟨1692183900725653302585767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4512490401935075473562045 1692183900725653302585767)
      ·
        refine ⟨2538275851088479953878651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1692183900725653302585767 2538275851088479953878651)
        ·
          refine ⟨3807413776632719930817977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2538275851088479953878651 3807413776632719930817977)
          ·
            refine ⟨2855560332474539948113483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3807413776632719930817977 2855560332474539948113483)
            ·
              refine ⟨4283340498711809922170225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2855560332474539948113483 4283340498711809922170225)
              ·
                refine ⟨3212505374033857441627669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4283340498711809922170225 3212505374033857441627669)
                ·
                  refine ⟨150586189407837067576297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3212505374033857441627669 150586189407837067576297)
                  ·
                    rfl

theorem cell23_2639390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_2639390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639390 prefixEnd_2639390 := by exact prefixLift 2639390
  have htrace : WordTrace (prefixWord ++ tailWord_2639390) baseStart_2639390 baseEnd_2639390 := by
    simpa [prefixWord, tailWord_2639390, baseEnd_2639390] using wordTrace_append hprefix tailTrace_2639390
  have hstable : (prefixWord ++ tailWord_2639390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639390).length < 2 ^ (prefixWord ++ tailWord_2639390).sum := by decide
  have hdescent : baseEnd_2639390 < baseStart_2639390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639402 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_2639402 : Nat := 118140960795 + 2639402 * 2 ^ 59
def prefixEnd_2639402 : Nat := 4983230072969 + 3 ^ 40 * 2639402 * 2
def baseEnd_2639402 : Nat := 1355281866438387561236617

theorem tailTrace_2639402 : CollatzResearch.WordTrace tailWord_2639402 prefixEnd_2639402 1355281866438387561236617 := by
  unfold tailWord_2639402
  simp only [CollatzResearch.WordTrace]
  refine ⟨24066724895976200704690115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64177933055936535212506973 24066724895976200704690115)
  ·
    refine ⟨36100087343964301057035173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24066724895976200704690115 36100087343964301057035173)
    ·
      refine ⟨6768766376993306448194095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36100087343964301057035173 6768766376993306448194095)
      ·
        refine ⟨10153149565489959672291143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6768766376993306448194095 10153149565489959672291143)
        ·
          refine ⟨15229724348234939508436715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10153149565489959672291143 15229724348234939508436715)
          ·
            refine ⟨22844586522352409262655073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15229724348234939508436715 22844586522352409262655073)
            ·
              refine ⟨17133439891764306946991305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22844586522352409262655073 17133439891764306946991305)
              ·
                refine ⟨12850079918823230210243479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17133439891764306946991305 12850079918823230210243479)
                ·
                  refine ⟨19275119878234845315365219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12850079918823230210243479 19275119878234845315365219)
                  ·
                    refine ⟨28912679817352267973047829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19275119878234845315365219 28912679817352267973047829)
                    ·
                      refine ⟨1355281866438387561236617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28912679817352267973047829 1355281866438387561236617)
                      ·
                        rfl

theorem cell23_2639402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_2639402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639402 prefixEnd_2639402 := by exact prefixLift 2639402
  have htrace : WordTrace (prefixWord ++ tailWord_2639402) baseStart_2639402 baseEnd_2639402 := by
    simpa [prefixWord, tailWord_2639402, baseEnd_2639402] using wordTrace_append hprefix tailTrace_2639402
  have hstable : (prefixWord ++ tailWord_2639402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639402).length < 2 ^ (prefixWord ++ tailWord_2639402).sum := by decide
  have hdescent : baseEnd_2639402 < baseStart_2639402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639416 : List Nat := [2, 1, 2, 1, 4, 3, 3, 1, 2, 4]
def baseStart_2639416 : Nat := 118140960795 + 2639416 * 2 ^ 59
def prefixEnd_2639416 : Nat := 4983230072969 + 3 ^ 40 * 2639416 * 2
def baseEnd_2639416 : Nat := 451763018389183502153851

theorem tailTrace_2639416 : CollatzResearch.WordTrace tailWord_2639416 prefixEnd_2639416 451763018389183502153851 := by
  unfold tailWord_2639416
  simp only [CollatzResearch.WordTrace]
  refine ⟨48133705102927041604885051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64178273470569388806513401 48133705102927041604885051)
  ·
    refine ⟨72200557654390562407327577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48133705102927041604885051 72200557654390562407327577)
    ·
      refine ⟨54150418240792921805495683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72200557654390562407327577 54150418240792921805495683)
      ·
        refine ⟨81225627361189382708243525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54150418240792921805495683 81225627361189382708243525)
        ·
          refine ⟨15229805130223009257795661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81225627361189382708243525 15229805130223009257795661)
          ·
            refine ⟨5711176923833628471673373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15229805130223009257795661 5711176923833628471673373)
            ·
              refine ⟨2141691346437610676877515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5711176923833628471673373 2141691346437610676877515)
              ·
                refine ⟨3212537019656416015316273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2141691346437610676877515 3212537019656416015316273)
                ·
                  refine ⟨2409402764742312011487205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3212537019656416015316273 2409402764742312011487205)
                  ·
                    refine ⟨451763018389183502153851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2409402764742312011487205 451763018389183502153851)
                    ·
                      rfl

theorem cell23_2639416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 2, 4].length) (baseStart_2639416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639416 prefixEnd_2639416 := by exact prefixLift 2639416
  have htrace : WordTrace (prefixWord ++ tailWord_2639416) baseStart_2639416 baseEnd_2639416 := by
    simpa [prefixWord, tailWord_2639416, baseEnd_2639416] using wordTrace_append hprefix tailTrace_2639416
  have hstable : (prefixWord ++ tailWord_2639416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639416).length < 2 ^ (prefixWord ++ tailWord_2639416).sum := by decide
  have hdescent : baseEnd_2639416 < baseStart_2639416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639479 : List Nat := [1, 1, 3, 1, 1, 3, 1, 5, 1, 4, 2]
def baseStart_2639479 : Nat := 118140960795 + 2639479 * 2 ^ 59
def prefixEnd_2639479 : Nat := 4983230072969 + 3 ^ 40 * 2639479 * 2
def baseEnd_2639479 : Nat := 1355321404448783759973763

theorem tailTrace_2639479 : CollatzResearch.WordTrace tailWord_2639479 prefixEnd_2639479 1355321404448783759973763 := by
  unfold tailWord_2639479
  simp only [CollatzResearch.WordTrace]
  refine ⟨96269708004625844969313491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64179805336417229979542327 96269708004625844969313491)
  ·
    refine ⟨144404562006938767453970237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96269708004625844969313491 144404562006938767453970237)
    ·
      refine ⟨54151710752602037795238839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144404562006938767453970237 54151710752602037795238839)
      ·
        refine ⟨81227566128903056692858259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54151710752602037795238839 81227566128903056692858259)
        ·
          refine ⟨121841349193354585039287389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81227566128903056692858259 121841349193354585039287389)
          ·
            refine ⟨45690505947507969389732771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121841349193354585039287389 45690505947507969389732771)
            ·
              refine ⟨68535758921261954084599157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45690505947507969389732771 68535758921261954084599157)
              ·
                refine ⟨6425227398868308195431171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68535758921261954084599157 6425227398868308195431171)
                ·
                  refine ⟨9637841098302462293146757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6425227398868308195431171 9637841098302462293146757)
                  ·
                    refine ⟨1807095205931711679965017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9637841098302462293146757 1807095205931711679965017)
                    ·
                      refine ⟨1355321404448783759973763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1807095205931711679965017 1355321404448783759973763)
                      ·
                        rfl

theorem cell23_2639479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 4, 2].length) (baseStart_2639479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639479 prefixEnd_2639479 := by exact prefixLift 2639479
  have htrace : WordTrace (prefixWord ++ tailWord_2639479) baseStart_2639479 baseEnd_2639479 := by
    simpa [prefixWord, tailWord_2639479, baseEnd_2639479] using wordTrace_append hprefix tailTrace_2639479
  have hstable : (prefixWord ++ tailWord_2639479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639479).length < 2 ^ (prefixWord ++ tailWord_2639479).sum := by decide
  have hdescent : baseEnd_2639479 < baseStart_2639479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639482 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3]
def baseStart_2639482 : Nat := 118140960795 + 2639482 * 2 ^ 59
def prefixEnd_2639482 : Nat := 4983230072969 + 3 ^ 40 * 2639482 * 2
def baseEnd_2639482 : Nat := 1355322944890747248236249

theorem tailTrace_2639482 : CollatzResearch.WordTrace tailWord_2639482 prefixEnd_2639482 1355322944890747248236249 := by
  unfold tailWord_2639482
  simp only [CollatzResearch.WordTrace]
  refine ⟨24067454355903744120418175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64179878282409984321115133 24067454355903744120418175)
  ·
    refine ⟨36101181533855616180627263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24067454355903744120418175 36101181533855616180627263)
    ·
      refine ⟨54151772300783424270940895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36101181533855616180627263 54151772300783424270940895)
      ·
        refine ⟨81227658451175136406411343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54151772300783424270940895 81227658451175136406411343)
        ·
          refine ⟨121841487676762704609617015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81227658451175136406411343 121841487676762704609617015)
          ·
            refine ⟨182762231515144056914425523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121841487676762704609617015 182762231515144056914425523)
            ·
              refine ⟨274143347272716085371638285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182762231515144056914425523 274143347272716085371638285)
              ·
                refine ⟨102803755227268532014364357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 274143347272716085371638285 102803755227268532014364357)
                ·
                  refine ⟨19275704105112849752693317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102803755227268532014364357 19275704105112849752693317)
                  ·
                    refine ⟨3614194519708659328629997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19275704105112849752693317 3614194519708659328629997)
                    ·
                      refine ⟨1355322944890747248236249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3614194519708659328629997 1355322944890747248236249)
                      ·
                        rfl

theorem cell23_2639482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3].length) (baseStart_2639482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639482 prefixEnd_2639482 := by exact prefixLift 2639482
  have htrace : WordTrace (prefixWord ++ tailWord_2639482) baseStart_2639482 baseEnd_2639482 := by
    simpa [prefixWord, tailWord_2639482, baseEnd_2639482] using wordTrace_append hprefix tailTrace_2639482
  have hstable : (prefixWord ++ tailWord_2639482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639482).length < 2 ^ (prefixWord ++ tailWord_2639482).sum := by decide
  have hdescent : baseEnd_2639482 < baseStart_2639482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639539 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 2, 5, 2]
def baseStart_2639539 : Nat := 118140960795 + 2639539 * 2 ^ 59
def prefixEnd_2639539 : Nat := 4983230072969 + 3 ^ 40 * 2639539 * 2
def baseEnd_2639539 : Nat := 1355352213288053525223487

theorem tailTrace_2639539 : CollatzResearch.WordTrace tailWord_2639539 prefixEnd_2639539 1355352213288053525223487 := by
  unfold tailWord_2639539
  simp only [CollatzResearch.WordTrace]
  refine ⟨96271896384408475216497671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64181264256272316810998447 96271896384408475216497671)
  ·
    refine ⟨144407844576612712824746507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96271896384408475216497671 144407844576612712824746507)
    ·
      refine ⟨216611766864919069237119761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144407844576612712824746507 216611766864919069237119761)
      ·
        refine ⟨162458825148689301927839821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216611766864919069237119761 162458825148689301927839821)
        ·
          refine ⟨60922059430758488222939933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162458825148689301927839821 60922059430758488222939933)
          ·
            refine ⟨22845772286534433083602475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60922059430758488222939933 22845772286534433083602475)
            ·
              refine ⟨34268658429801649625403713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22845772286534433083602475 34268658429801649625403713)
              ·
                refine ⟨25701493822351237219052785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34268658429801649625403713 25701493822351237219052785)
                ·
                  refine ⟨19276120366763427914289589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25701493822351237219052785 19276120366763427914289589)
                  ·
                    refine ⟨1807136284384071366964649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19276120366763427914289589 1807136284384071366964649)
                    ·
                      refine ⟨1355352213288053525223487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1807136284384071366964649 1355352213288053525223487)
                      ·
                        rfl

theorem cell23_2639539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 5, 2].length) (baseStart_2639539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639539 prefixEnd_2639539 := by exact prefixLift 2639539
  have htrace : WordTrace (prefixWord ++ tailWord_2639539) baseStart_2639539 baseEnd_2639539 := by
    simpa [prefixWord, tailWord_2639539, baseEnd_2639539] using wordTrace_append hprefix tailTrace_2639539
  have hstable : (prefixWord ++ tailWord_2639539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639539).length < 2 ^ (prefixWord ++ tailWord_2639539).sum := by decide
  have hdescent : baseEnd_2639539 < baseStart_2639539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639589 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 3, 4, 3]
def baseStart_2639589 : Nat := 118140960795 + 2639589 * 2 ^ 59
def prefixEnd_2639589 : Nat := 4983230072969 + 3 ^ 40 * 2639589 * 2
def baseEnd_2639589 : Nat := 1355377887320778329598257

theorem tailTrace_2639589 : CollatzResearch.WordTrace tailWord_2639589 prefixEnd_2639589 1355377887320778329598257 := by
  unfold tailWord_2639589
  simp only [CollatzResearch.WordTrace]
  refine ⟨96273720034227333755817821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64182480022818222503878547 96273720034227333755817821)
  ·
    refine ⟨36102645012835250158431683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96273720034227333755817821 36102645012835250158431683)
    ·
      refine ⟨54153967519252875237647525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36102645012835250158431683 54153967519252875237647525)
      ·
        refine ⟨10153868909859914107058911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54153967519252875237647525 10153868909859914107058911)
        ·
          refine ⟨15230803364789871160588367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10153868909859914107058911 15230803364789871160588367)
          ·
            refine ⟨22846205047184806740882551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15230803364789871160588367 22846205047184806740882551)
            ·
              refine ⟨34269307570777210111323827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22846205047184806740882551 34269307570777210111323827)
              ·
                refine ⟨51403961356165815166985741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34269307570777210111323827 51403961356165815166985741)
                ·
                  refine ⟨19276485508562180687619653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51403961356165815166985741 19276485508562180687619653)
                  ·
                    refine ⟨3614341032855408878928685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19276485508562180687619653 3614341032855408878928685)
                    ·
                      refine ⟨1355377887320778329598257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3614341032855408878928685 1355377887320778329598257)
                      ·
                        rfl

theorem cell23_2639589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_2639589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639589 prefixEnd_2639589 := by exact prefixLift 2639589
  have htrace : WordTrace (prefixWord ++ tailWord_2639589) baseStart_2639589 baseEnd_2639589 := by
    simpa [prefixWord, tailWord_2639589, baseEnd_2639589] using wordTrace_append hprefix tailTrace_2639589
  have hstable : (prefixWord ++ tailWord_2639589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639589).length < 2 ^ (prefixWord ++ tailWord_2639589).sum := by decide
  have hdescent : baseEnd_2639589 < baseStart_2639589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639606 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3]
def baseStart_2639606 : Nat := 118140960795 + 2639606 * 2 ^ 59
def prefixEnd_2639606 : Nat := 4983230072969 + 3 ^ 40 * 2639606 * 2
def baseEnd_2639606 : Nat := 1355386616491904763085679

theorem tailTrace_2639606 : CollatzResearch.WordTrace tailWord_2639606 prefixEnd_2639606 1355386616491904763085679 := by
  unfold tailWord_2639606
  simp only [CollatzResearch.WordTrace]
  refine ⟨6017146254697859103699167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64182893383443830439457781 6017146254697859103699167)
  ·
    refine ⟨9025719382046788655548751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6017146254697859103699167 9025719382046788655548751)
    ·
      refine ⟨13538579073070182983323127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9025719382046788655548751 13538579073070182983323127)
      ·
        refine ⟨20307868609605274474984691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13538579073070182983323127 20307868609605274474984691)
        ·
          refine ⟨30461802914407911712477037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20307868609605274474984691 30461802914407911712477037)
          ·
            refine ⟨11423176092902966892178889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30461802914407911712477037 11423176092902966892178889)
            ·
              refine ⟨8567382069677225169134167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11423176092902966892178889 8567382069677225169134167)
              ·
                refine ⟨12851073104515837753701251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8567382069677225169134167 12851073104515837753701251)
                ·
                  refine ⟨19276609656773756630551877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12851073104515837753701251 19276609656773756630551877)
                  ·
                    refine ⟨3614364310645079368228477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19276609656773756630551877 3614364310645079368228477)
                    ·
                      refine ⟨1355386616491904763085679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3614364310645079368228477 1355386616491904763085679)
                      ·
                        rfl

theorem cell23_2639606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_2639606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639606 prefixEnd_2639606 := by exact prefixLift 2639606
  have htrace : WordTrace (prefixWord ++ tailWord_2639606) baseStart_2639606 baseEnd_2639606 := by
    simpa [prefixWord, tailWord_2639606, baseEnd_2639606] using wordTrace_append hprefix tailTrace_2639606
  have hstable : (prefixWord ++ tailWord_2639606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639606).length < 2 ^ (prefixWord ++ tailWord_2639606).sum := by decide
  have hdescent : baseEnd_2639606 < baseStart_2639606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639623 : List Nat := [1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 3]
def baseStart_2639623 : Nat := 118140960795 + 2639623 * 2 ^ 59
def prefixEnd_2639623 : Nat := 4983230072969 + 3 ^ 40 * 2639623 * 2
def baseEnd_2639623 : Nat := 1355395345663031196573101

theorem tailTrace_2639623 : CollatzResearch.WordTrace tailWord_2639623 prefixEnd_2639623 1355395345663031196573101 := by
  unfold tailWord_2639623
  simp only [CollatzResearch.WordTrace]
  refine ⟨96274960116104157562555523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64183306744069438375037015 96274960116104157562555523)
  ·
    refine ⟨144412440174156236343833285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96274960116104157562555523 144412440174156236343833285)
    ·
      refine ⟨27077332532654294314468741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144412440174156236343833285 27077332532654294314468741)
      ·
        refine ⟨5076999849872680183962889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27077332532654294314468741 5076999849872680183962889)
        ·
          refine ⟨3807749887404510137972167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5076999849872680183962889 3807749887404510137972167)
          ·
            refine ⟨5711624831106765206958251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3807749887404510137972167 5711624831106765206958251)
            ·
              refine ⟨8567437246660147810437377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5711624831106765206958251 8567437246660147810437377)
              ·
                refine ⟨6425577934995110857828033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8567437246660147810437377 6425577934995110857828033)
                ·
                  refine ⟨4819183451246333143371025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6425577934995110857828033 4819183451246333143371025)
                  ·
                    refine ⟨3614387588434749857528269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4819183451246333143371025 3614387588434749857528269)
                    ·
                      refine ⟨1355395345663031196573101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3614387588434749857528269 1355395345663031196573101)
                      ·
                        rfl

theorem cell23_2639623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_2639623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639623 prefixEnd_2639623 := by exact prefixLift 2639623
  have htrace : WordTrace (prefixWord ++ tailWord_2639623) baseStart_2639623 baseEnd_2639623 := by
    simpa [prefixWord, tailWord_2639623, baseEnd_2639623] using wordTrace_append hprefix tailTrace_2639623
  have hstable : (prefixWord ++ tailWord_2639623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639623).length < 2 ^ (prefixWord ++ tailWord_2639623).sum := by decide
  have hdescent : baseEnd_2639623 < baseStart_2639623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639656 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 3, 5]
def baseStart_2639656 : Nat := 118140960795 + 2639656 * 2 ^ 59
def prefixEnd_2639656 : Nat := 4983230072969 + 3 ^ 40 * 2639656 * 2
def baseEnd_2639656 : Nat := 451804096841543189153483

theorem tailTrace_2639656 : CollatzResearch.WordTrace tailWord_2639656 prefixEnd_2639656 451804096841543189153483 := by
  unfold tailWord_2639656
  simp only [CollatzResearch.WordTrace]
  refine ⟨48138081862492302099253411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64184109149989736132337881 48138081862492302099253411)
  ·
    refine ⟨72207122793738453148880117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48138081862492302099253411 72207122793738453148880117)
    ·
      refine ⟨6769417761912979982707511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72207122793738453148880117 6769417761912979982707511)
      ·
        refine ⟨10154126642869469974061267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6769417761912979982707511 10154126642869469974061267)
        ·
          refine ⟨15231189964304204961091901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10154126642869469974061267 15231189964304204961091901)
          ·
            refine ⟨5711696236614076860409463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15231189964304204961091901 5711696236614076860409463)
            ·
              refine ⟨8567544354921115290614195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5711696236614076860409463 8567544354921115290614195)
              ·
                refine ⟨12851316532381672935921293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8567544354921115290614195 12851316532381672935921293)
                ·
                  refine ⟨4819243699643127350970485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12851316532381672935921293 4819243699643127350970485)
                  ·
                    refine ⟨451804096841543189153483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4819243699643127350970485 451804096841543189153483)
                    ·
                      rfl

theorem cell23_2639656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_2639656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639656 prefixEnd_2639656 := by exact prefixLift 2639656
  have htrace : WordTrace (prefixWord ++ tailWord_2639656) baseStart_2639656 baseEnd_2639656 := by
    simpa [prefixWord, tailWord_2639656, baseEnd_2639656] using wordTrace_append hprefix tailTrace_2639656
  have hstable : (prefixWord ++ tailWord_2639656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639656).length < 2 ^ (prefixWord ++ tailWord_2639656).sum := by decide
  have hdescent : baseEnd_2639656 < baseStart_2639656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639676 : List Nat := [2, 2, 2, 2, 1, 1, 2, 5, 1, 1, 4]
def baseStart_2639676 : Nat := 118140960795 + 2639676 * 2 ^ 59
def prefixEnd_2639676 : Nat := 4983230072969 + 3 ^ 40 * 2639676 * 2
def baseEnd_2639676 : Nat := 1355422560137719489210357

theorem tailTrace_2639676 : CollatzResearch.WordTrace tailWord_2639676 prefixEnd_2639676 1355422560137719489210357 := by
  unfold tailWord_2639676
  simp only [CollatzResearch.WordTrace]
  refine ⟨48138446592456073807117441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64184595456608098409489921 48138446592456073807117441)
  ·
    refine ⟨36103834944342055355338081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48138446592456073807117441 36103834944342055355338081)
    ·
      refine ⟨27077876208256541516503561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36103834944342055355338081 27077876208256541516503561)
      ·
        refine ⟨20308407156192406137377671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27077876208256541516503561 20308407156192406137377671)
        ·
          refine ⟨30462610734288609206066507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20308407156192406137377671 30462610734288609206066507)
          ·
            refine ⟨45693916101432913809099761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30462610734288609206066507 45693916101432913809099761)
            ·
              refine ⟨34270437076074685356824821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45693916101432913809099761 34270437076074685356824821)
              ·
                refine ⟨3212853475882001752202327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34270437076074685356824821 3212853475882001752202327)
                ·
                  refine ⟨4819280213823002628303491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3212853475882001752202327 4819280213823002628303491)
                  ·
                    refine ⟨7228920320734503942455237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4819280213823002628303491 7228920320734503942455237)
                    ·
                      refine ⟨1355422560137719489210357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7228920320734503942455237 1355422560137719489210357)
                      ·
                        rfl

theorem cell23_2639676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_2639676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639676 prefixEnd_2639676 := by exact prefixLift 2639676
  have htrace : WordTrace (prefixWord ++ tailWord_2639676) baseStart_2639676 baseEnd_2639676 := by
    simpa [prefixWord, tailWord_2639676, baseEnd_2639676] using wordTrace_append hprefix tailTrace_2639676
  have hstable : (prefixWord ++ tailWord_2639676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639676).length < 2 ^ (prefixWord ++ tailWord_2639676).sum := by decide
  have hdescent : baseEnd_2639676 < baseStart_2639676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639689 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 3, 2, 4]
def baseStart_2639689 : Nat := 118140960795 + 2639689 * 2 ^ 59
def prefixEnd_2639689 : Nat := 4983230072969 + 3 ^ 40 * 2639689 * 2
def baseEnd_2639689 : Nat := 1355429235386227938347797

theorem tailTrace_2639689 : CollatzResearch.WordTrace tailWord_2639689 prefixEnd_2639689 1355429235386227938347797 := by
  unfold tailWord_2639689
  simp only [CollatzResearch.WordTrace]
  refine ⟨96277367333865050834458121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64184911555910033889638747 96277367333865050834458121)
  ·
    refine ⟨72208025500398788125843591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96277367333865050834458121 72208025500398788125843591)
    ·
      refine ⟨108312038250598182188765387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72208025500398788125843591 108312038250598182188765387)
      ·
        refine ⟨162468057375897273283148081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108312038250598182188765387 162468057375897273283148081)
        ·
          refine ⟨121851043031922954962361061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162468057375897273283148081 121851043031922954962361061)
          ·
            refine ⟨22847070568485554055442699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121851043031922954962361061 22847070568485554055442699)
            ·
              refine ⟨34270605852728331083164049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22847070568485554055442699 34270605852728331083164049)
              ·
                refine ⟨25702954389546248312373037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34270605852728331083164049 25702954389546248312373037)
                ·
                  refine ⟨9638607896079843117139889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25702954389546248312373037 9638607896079843117139889)
                  ·
                    refine ⟨7228955922059882337854917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9638607896079843117139889 7228955922059882337854917)
                    ·
                      refine ⟨1355429235386227938347797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7228955922059882337854917 1355429235386227938347797)
                      ·
                        rfl

theorem cell23_2639689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 2, 4].length) (baseStart_2639689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639689 prefixEnd_2639689 := by exact prefixLift 2639689
  have htrace : WordTrace (prefixWord ++ tailWord_2639689) baseStart_2639689 baseEnd_2639689 := by
    simpa [prefixWord, tailWord_2639689, baseEnd_2639689] using wordTrace_append hprefix tailTrace_2639689
  have hstable : (prefixWord ++ tailWord_2639689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639689).length < 2 ^ (prefixWord ++ tailWord_2639689).sum := by decide
  have hdescent : baseEnd_2639689 < baseStart_2639689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639693 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_2639693 : Nat := 118140960795 + 2639693 * 2 ^ 59
def prefixEnd_2639693 : Nat := 4983230072969 + 3 ^ 40 * 2639693 * 2
def baseEnd_2639693 : Nat := 1355431289308845922697779

theorem tailTrace_2639693 : CollatzResearch.WordTrace tailWord_2639693 prefixEnd_2639693 1355431289308845922697779 := by
  unfold tailWord_2639693
  simp only [CollatzResearch.WordTrace]
  refine ⟨96277513225850559517603733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64185008817233706345069155 96277513225850559517603733)
  ·
    refine ⟨4513008432461744977387675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96277513225850559517603733 4513008432461744977387675)
    ·
      refine ⟨6769512648692617466081513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4513008432461744977387675 6769512648692617466081513)
      ·
        refine ⟨5077134486519463099561135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6769512648692617466081513 5077134486519463099561135)
        ·
          refine ⟨7615701729779194649341703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5077134486519463099561135 7615701729779194649341703)
          ·
            refine ⟨11423552594668791974012555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7615701729779194649341703 11423552594668791974012555)
            ·
              refine ⟨17135328892003187961018833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11423552594668791974012555 17135328892003187961018833)
              ·
                refine ⟨12851496669002390970764125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17135328892003187961018833 12851496669002390970764125)
                ·
                  refine ⟨4819311250875896614036547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12851496669002390970764125 4819311250875896614036547)
                  ·
                    refine ⟨7228966876313844921054821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4819311250875896614036547 7228966876313844921054821)
                    ·
                      refine ⟨1355431289308845922697779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7228966876313844921054821 1355431289308845922697779)
                      ·
                        rfl

theorem cell23_2639693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_2639693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639693 prefixEnd_2639693 := by exact prefixLift 2639693
  have htrace : WordTrace (prefixWord ++ tailWord_2639693) baseStart_2639693 baseEnd_2639693 := by
    simpa [prefixWord, tailWord_2639693, baseEnd_2639693] using wordTrace_append hprefix tailTrace_2639693
  have hstable : (prefixWord ++ tailWord_2639693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639693).length < 2 ^ (prefixWord ++ tailWord_2639693).sum := by decide
  have hdescent : baseEnd_2639693 < baseStart_2639693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639706 : List Nat := [3, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4]
def baseStart_2639706 : Nat := 118140960795 + 2639706 * 2 ^ 59
def prefixEnd_2639706 : Nat := 4983230072969 + 3 ^ 40 * 2639706 * 2
def baseEnd_2639706 : Nat := 1355437964557354371835219

theorem tailTrace_2639706 : CollatzResearch.WordTrace tailWord_2639706 prefixEnd_2639706 1355437964557354371835219 := by
  unfold tailWord_2639706
  simp only [CollatzResearch.WordTrace]
  refine ⟨24069496843700865684456743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64185324916535641825217981 24069496843700865684456743)
  ·
    refine ⟨36104245265551298526685115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24069496843700865684456743 36104245265551298526685115)
    ·
      refine ⟨54156367898326947790027673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36104245265551298526685115 54156367898326947790027673)
      ·
        refine ⟨40617275923745210842520755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54156367898326947790027673 40617275923745210842520755)
        ·
          refine ⟨60925913885617816263781133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40617275923745210842520755 60925913885617816263781133)
          ·
            refine ⟨22847217707106681098917925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60925913885617816263781133 22847217707106681098917925)
            ·
              refine ⟨4283853320082502706047111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22847217707106681098917925 4283853320082502706047111)
              ·
                refine ⟨6425779980123754059070667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4283853320082502706047111 6425779980123754059070667)
                ·
                  refine ⟨9638669970185631088606001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6425779980123754059070667 9638669970185631088606001)
                  ·
                    refine ⟨7229002477639223316454501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9638669970185631088606001 7229002477639223316454501)
                    ·
                      refine ⟨1355437964557354371835219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7229002477639223316454501 1355437964557354371835219)
                      ·
                        rfl

theorem cell23_2639706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_2639706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639706 prefixEnd_2639706 := by exact prefixLift 2639706
  have htrace : WordTrace (prefixWord ++ tailWord_2639706) baseStart_2639706 baseEnd_2639706 := by
    simpa [prefixWord, tailWord_2639706, baseEnd_2639706] using wordTrace_append hprefix tailTrace_2639706
  have hstable : (prefixWord ++ tailWord_2639706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639706).length < 2 ^ (prefixWord ++ tailWord_2639706).sum := by decide
  have hdescent : baseEnd_2639706 < baseStart_2639706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639770 : List Nat := [3, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2]
def baseStart_2639770 : Nat := 118140960795 + 2639770 * 2 ^ 59
def prefixEnd_2639770 : Nat := 4983230072969 + 3 ^ 40 * 2639770 * 2
def baseEnd_2639770 : Nat := 1355470827319242121434925

theorem tailTrace_2639770 : CollatzResearch.WordTrace tailWord_2639770 prefixEnd_2639770 1355470827319242121434925 := by
  unfold tailWord_2639770
  simp only [CollatzResearch.WordTrace]
  refine ⟨24070080411642900417039191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64186881097714401112104509 24070080411642900417039191)
  ·
    refine ⟨36105120617464350625558787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24070080411642900417039191 36105120617464350625558787)
    ·
      refine ⟨54157680926196525938338181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36105120617464350625558787 54157680926196525938338181)
      ·
        refine ⟨10154565173661848613438409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54157680926196525938338181 10154565173661848613438409)
        ·
          refine ⟨7615923880246386460078807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10154565173661848613438409 7615923880246386460078807)
          ·
            refine ⟨11423885820369579690118211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7615923880246386460078807 11423885820369579690118211)
            ·
              refine ⟨17135828730554369535177317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11423885820369579690118211 17135828730554369535177317)
              ·
                refine ⟨3212967886978944287845747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17135828730554369535177317 3212967886978944287845747)
                ·
                  refine ⟨4819451830468416431768621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3212967886978944287845747 4819451830468416431768621)
                  ·
                    refine ⟨1807294436425656161913233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4819451830468416431768621 1807294436425656161913233)
                    ·
                      refine ⟨1355470827319242121434925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1807294436425656161913233 1355470827319242121434925)
                      ·
                        rfl

theorem cell23_2639770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_2639770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639770 prefixEnd_2639770 := by exact prefixLift 2639770
  have htrace : WordTrace (prefixWord ++ tailWord_2639770) baseStart_2639770 baseEnd_2639770 := by
    simpa [prefixWord, tailWord_2639770, baseEnd_2639770] using wordTrace_append hprefix tailTrace_2639770
  have hstable : (prefixWord ++ tailWord_2639770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639770).length < 2 ^ (prefixWord ++ tailWord_2639770).sum := by decide
  have hdescent : baseEnd_2639770 < baseStart_2639770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639799 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 9]
def baseStart_2639799 : Nat := 118140960795 + 2639799 * 2 ^ 59
def prefixEnd_2639799 : Nat := 4983230072969 + 3 ^ 40 * 2639799 * 2
def baseEnd_2639799 : Nat := 1355485718258222507972291

theorem tailTrace_2639799 : CollatzResearch.WordTrace tailWord_2639799 prefixEnd_2639799 1355485718258222507972291 := by
  unfold tailWord_2639799
  simp only [CollatzResearch.WordTrace]
  refine ⟨96281379363466539620962451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64187586242311026413974967 96281379363466539620962451)
  ·
    refine ⟨144422069045199809431443677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96281379363466539620962451 144422069045199809431443677)
    ·
      refine ⟨54158275891949928536791379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144422069045199809431443677 54158275891949928536791379)
      ·
        refine ⟨81237413837924892805187069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54158275891949928536791379 81237413837924892805187069)
        ·
          refine ⟨30464030189221834801945151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81237413837924892805187069 30464030189221834801945151)
          ·
            refine ⟨45696045283832752202917727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30464030189221834801945151 45696045283832752202917727)
            ·
              refine ⟨68544067925749128304376591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45696045283832752202917727 68544067925749128304376591)
              ·
                refine ⟨102816101888623692456564887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68544067925749128304376591 102816101888623692456564887)
                ·
                  refine ⟨154224152832935538684847331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102816101888623692456564887 154224152832935538684847331)
                  ·
                    refine ⟨231336229249403308027270997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 154224152832935538684847331 231336229249403308027270997)
                    ·
                      refine ⟨1355485718258222507972291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 231336229249403308027270997 1355485718258222507972291)
                      ·
                        rfl

theorem cell23_2639799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_2639799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639799 prefixEnd_2639799 := by exact prefixLift 2639799
  have htrace : WordTrace (prefixWord ++ tailWord_2639799) baseStart_2639799 baseEnd_2639799 := by
    simpa [prefixWord, tailWord_2639799, baseEnd_2639799] using wordTrace_append hprefix tailTrace_2639799
  have hstable : (prefixWord ++ tailWord_2639799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639799).length < 2 ^ (prefixWord ++ tailWord_2639799).sum := by decide
  have hdescent : baseEnd_2639799 < baseStart_2639799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639800 : List Nat := [2, 1, 2, 1, 2, 3, 2, 4, 2, 2, 2]
def baseStart_2639800 : Nat := 118140960795 + 2639800 * 2 ^ 59
def prefixEnd_2639800 : Nat := 4983230072969 + 3 ^ 40 * 2639800 * 2
def baseEnd_2639800 : Nat := 1355486231738877004059787

theorem tailTrace_2639800 : CollatzResearch.WordTrace tailWord_2639800 prefixEnd_2639800 1355486231738877004059787 := by
  unfold tailWord_2639800
  simp only [CollatzResearch.WordTrace]
  refine ⟨48140707918231458395874427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64187610557641944527832569 48140707918231458395874427)
  ·
    refine ⟨72211061877347187593811641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48140707918231458395874427 72211061877347187593811641)
    ·
      refine ⟨54158296408010390695358731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72211061877347187593811641 54158296408010390695358731)
      ·
        refine ⟨81237444612015586043038097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54158296408010390695358731 81237444612015586043038097)
        ·
          refine ⟨60928083459011689532278573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81237444612015586043038097 60928083459011689532278573)
          ·
            refine ⟨22848031297129383574604465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60928083459011689532278573 22848031297129383574604465)
            ·
              refine ⟨17136023472847037680953349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22848031297129383574604465 17136023472847037680953349)
              ·
                refine ⟨3213004401158819565178753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17136023472847037680953349 3213004401158819565178753)
                ·
                  refine ⟨2409753300869114673884065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3213004401158819565178753 2409753300869114673884065)
                  ·
                    refine ⟨1807314975651836005413049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2409753300869114673884065 1807314975651836005413049)
                    ·
                      refine ⟨1355486231738877004059787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1807314975651836005413049 1355486231738877004059787)
                      ·
                        rfl

theorem cell23_2639800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 2, 2, 2].length) (baseStart_2639800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639800 prefixEnd_2639800 := by exact prefixLift 2639800
  have htrace : WordTrace (prefixWord ++ tailWord_2639800) baseStart_2639800 baseEnd_2639800 := by
    simpa [prefixWord, tailWord_2639800, baseEnd_2639800] using wordTrace_append hprefix tailTrace_2639800
  have hstable : (prefixWord ++ tailWord_2639800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639800).length < 2 ^ (prefixWord ++ tailWord_2639800).sum := by decide
  have hdescent : baseEnd_2639800 < baseStart_2639800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639857 : List Nat := [1, 2, 2, 2, 5, 2, 2, 2, 5]
def baseStart_2639857 : Nat := 118140960795 + 2639857 * 2 ^ 59
def prefixEnd_2639857 : Nat := 4983230072969 + 3 ^ 40 * 2639857 * 2
def baseEnd_2639857 : Nat := 150612833348464809005225

theorem tailTrace_2639857 : CollatzResearch.WordTrace tailWord_2639857 prefixEnd_2639857 150612833348464809005225 := by
  unfold tailWord_2639857
  simp only [CollatzResearch.WordTrace]
  refine ⟨96283494797256415526573825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64188996531504277017715883 96283494797256415526573825)
  ·
    refine ⟨72212621097942311644930369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96283494797256415526573825 72212621097942311644930369)
    ·
      refine ⟨54159465823456733733697777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72212621097942311644930369 54159465823456733733697777)
      ·
        refine ⟨40619599367592550300273333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54159465823456733733697777 40619599367592550300273333)
        ·
          refine ⟨3808087440711801590650625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40619599367592550300273333 3808087440711801590650625)
          ·
            refine ⟨2856065580533851192987969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3808087440711801590650625 2856065580533851192987969)
            ·
              refine ⟨2142049185400388394740977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2856065580533851192987969 2142049185400388394740977)
              ·
                refine ⟨1606536889050291296055733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2142049185400388394740977 1606536889050291296055733)
                ·
                  refine ⟨150612833348464809005225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1606536889050291296055733 150612833348464809005225)
                  ·
                    rfl

theorem cell23_2639857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 5].length) (baseStart_2639857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639857 prefixEnd_2639857 := by exact prefixLift 2639857
  have htrace : WordTrace (prefixWord ++ tailWord_2639857) baseStart_2639857 baseEnd_2639857 := by
    simpa [prefixWord, tailWord_2639857, baseEnd_2639857] using wordTrace_append hprefix tailTrace_2639857
  have hstable : (prefixWord ++ tailWord_2639857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639857).length < 2 ^ (prefixWord ++ tailWord_2639857).sum := by decide
  have hdescent : baseEnd_2639857 < baseStart_2639857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639883 : List Nat := [1, 1, 1, 1, 6, 1, 3, 2, 3, 4]
def baseStart_2639883 : Nat := 118140960795 + 2639883 * 2 ^ 59
def prefixEnd_2639883 : Nat := 4983230072969 + 3 ^ 40 * 2639883 * 2
def baseEnd_2639883 : Nat := 451842950211066726440635

theorem tailTrace_2639883 : CollatzResearch.WordTrace tailWord_2639883 prefixEnd_2639883 451842950211066726440635 := by
  unfold tailWord_2639883
  simp only [CollatzResearch.WordTrace]
  refine ⟨96284443095162221967020303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64189628730108147978013535 96284443095162221967020303)
  ·
    refine ⟨144426664642743332950530455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96284443095162221967020303 144426664642743332950530455)
    ·
      refine ⟨216639996964114999425795683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144426664642743332950530455 216639996964114999425795683)
      ·
        refine ⟨324959995446172499138693525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216639996964114999425795683 324959995446172499138693525)
        ·
          refine ⟨15232499786539335897126259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 324959995446172499138693525 15232499786539335897126259)
          ·
            refine ⟨22848749679809003845689389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15232499786539335897126259 22848749679809003845689389)
            ·
              refine ⟨8568281129928376442133521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22848749679809003845689389 8568281129928376442133521)
              ·
                refine ⟨6426210847446282331600141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8568281129928376442133521 6426210847446282331600141)
                ·
                  refine ⟨2409829067792355874350053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6426210847446282331600141 2409829067792355874350053)
                  ·
                    refine ⟨451842950211066726440635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2409829067792355874350053 451842950211066726440635)
                    ·
                      rfl

theorem cell23_2639883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 4].length) (baseStart_2639883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639883 prefixEnd_2639883 := by exact prefixLift 2639883
  have htrace : WordTrace (prefixWord ++ tailWord_2639883) baseStart_2639883 baseEnd_2639883 := by
    simpa [prefixWord, tailWord_2639883, baseEnd_2639883] using wordTrace_append hprefix tailTrace_2639883
  have hstable : (prefixWord ++ tailWord_2639883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639883).length < 2 ^ (prefixWord ++ tailWord_2639883).sum := by decide
  have hdescent : baseEnd_2639883 < baseStart_2639883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639896 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 8]
def baseStart_2639896 : Nat := 118140960795 + 2639896 * 2 ^ 59
def prefixEnd_2639896 : Nat := 4983230072969 + 3 ^ 40 * 2639896 * 2
def baseEnd_2639896 : Nat := 150615058431300958717705

theorem tailTrace_2639896 : CollatzResearch.WordTrace tailWord_2639896 prefixEnd_2639896 150615058431300958717705 := by
  unfold tailWord_2639896
  simp only [CollatzResearch.WordTrace]
  refine ⟨48142458622057562593621771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64189944829410083458162361 48142458622057562593621771)
  ·
    refine ⟨72213687933086343890432657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48142458622057562593621771 72213687933086343890432657)
    ·
      refine ⟨54160265949814757917824493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72213687933086343890432657 54160265949814757917824493)
      ·
        refine ⟨20310099731180534219184185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54160265949814757917824493 20310099731180534219184185)
        ·
          refine ⟨15232574798385400664388139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20310099731180534219184185 15232574798385400664388139)
          ·
            refine ⟨22848862197578100996582209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15232574798385400664388139 22848862197578100996582209)
            ·
              refine ⟨17136646648183575747436657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22848862197578100996582209 17136646648183575747436657)
              ·
                refine ⟨12852484986137681810577493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17136646648183575747436657 12852484986137681810577493)
                ·
                  refine ⟨150615058431300958717705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12852484986137681810577493 150615058431300958717705)
                  ·
                    rfl

theorem cell23_2639896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 8].length) (baseStart_2639896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639896 prefixEnd_2639896 := by exact prefixLift 2639896
  have htrace : WordTrace (prefixWord ++ tailWord_2639896) baseStart_2639896 baseEnd_2639896 := by
    simpa [prefixWord, tailWord_2639896, baseEnd_2639896] using wordTrace_append hprefix tailTrace_2639896
  have hstable : (prefixWord ++ tailWord_2639896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639896).length < 2 ^ (prefixWord ++ tailWord_2639896).sum := by decide
  have hdescent : baseEnd_2639896 < baseStart_2639896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639950 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2]
def baseStart_2639950 : Nat := 118140960795 + 2639950 * 2 ^ 59
def prefixEnd_2639950 : Nat := 4983230072969 + 3 ^ 40 * 2639950 * 2
def baseEnd_2639950 : Nat := 1355563253837051417184097

theorem tailTrace_2639950 : CollatzResearch.WordTrace tailWord_2639950 prefixEnd_2639950 1355563253837051417184097 := by
  unfold tailWord_2639950
  simp only [CollatzResearch.WordTrace]
  refine ⟨12035860848239936551213663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64191257857279661606472869 12035860848239936551213663)
  ·
    refine ⟨18053791272359904826820495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12035860848239936551213663 18053791272359904826820495)
    ·
      refine ⟨27080686908539857240230743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18053791272359904826820495 27080686908539857240230743)
      ·
        refine ⟨40621030362809785860346115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27080686908539857240230743 40621030362809785860346115)
        ·
          refine ⟨60931545544214678790519173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40621030362809785860346115 60931545544214678790519173)
          ·
            refine ⟨11424664789540252273222345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60931545544214678790519173 11424664789540252273222345)
            ·
              refine ⟨8568498592155189204916759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11424664789540252273222345 8568498592155189204916759)
              ·
                refine ⟨12852747888232783807375139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8568498592155189204916759 12852747888232783807375139)
                ·
                  refine ⟨19279121832349175711062709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12852747888232783807375139 19279121832349175711062709)
                  ·
                    refine ⟨1807417671782735222912129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19279121832349175711062709 1807417671782735222912129)
                    ·
                      refine ⟨1355563253837051417184097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1807417671782735222912129 1355563253837051417184097)
                      ·
                        rfl

theorem cell23_2639950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_2639950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639950 prefixEnd_2639950 := by exact prefixLift 2639950
  have htrace : WordTrace (prefixWord ++ tailWord_2639950) baseStart_2639950 baseEnd_2639950 := by
    simpa [prefixWord, tailWord_2639950, baseEnd_2639950] using wordTrace_append hprefix tailTrace_2639950
  have hstable : (prefixWord ++ tailWord_2639950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639950).length < 2 ^ (prefixWord ++ tailWord_2639950).sum := by decide
  have hdescent : baseEnd_2639950 < baseStart_2639950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639983 : List Nat := [1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 5]
def baseStart_2639983 : Nat := 118140960795 + 2639983 * 2 ^ 59
def prefixEnd_2639983 : Nat := 4983230072969 + 3 ^ 40 * 2639983 * 2
def baseEnd_2639983 : Nat := 1355580198698649788071445

theorem tailTrace_2639983 : CollatzResearch.WordTrace tailWord_2639983 prefixEnd_2639983 1355580198698649788071445 := by
  unfold tailWord_2639983
  simp only [CollatzResearch.WordTrace]
  refine ⟨96288090394799939045660603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64192060263199959363773735 96288090394799939045660603)
  ·
    refine ⟨144432135592199908568490905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96288090394799939045660603 144432135592199908568490905)
    ·
      refine ⟨108324101694149931426368179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144432135592199908568490905 108324101694149931426368179)
      ·
        refine ⟨162486152541224897139552269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108324101694149931426368179 162486152541224897139552269)
        ·
          refine ⟨60932307202959336427332101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162486152541224897139552269 60932307202959336427332101)
          ·
            refine ⟨11424807600554875580124769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60932307202959336427332101 11424807600554875580124769)
            ·
              refine ⟨8568605700416156685093577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11424807600554875580124769 8568605700416156685093577)
              ·
                refine ⟨6426454275312117513820183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8568605700416156685093577 6426454275312117513820183)
                ·
                  refine ⟨9639681412968176270730275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6426454275312117513820183 9639681412968176270730275)
                  ·
                    refine ⟨14459522119452264406095413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9639681412968176270730275 14459522119452264406095413)
                    ·
                      refine ⟨1355580198698649788071445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14459522119452264406095413 1355580198698649788071445)
                      ·
                        rfl

theorem cell23_2639983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 5].length) (baseStart_2639983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639983 prefixEnd_2639983 := by exact prefixLift 2639983
  have htrace : WordTrace (prefixWord ++ tailWord_2639983) baseStart_2639983 baseEnd_2639983 := by
    simpa [prefixWord, tailWord_2639983, baseEnd_2639983] using wordTrace_append hprefix tailTrace_2639983
  have hstable : (prefixWord ++ tailWord_2639983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639983).length < 2 ^ (prefixWord ++ tailWord_2639983).sum := by decide
  have hdescent : baseEnd_2639983 < baseStart_2639983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639993 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 1, 1, 6]
def baseStart_2639993 : Nat := 118140960795 + 2639993 * 2 ^ 59
def prefixEnd_2639993 : Nat := 4983230072969 + 3 ^ 40 * 2639993 * 2
def baseEnd_2639993 : Nat := 1355585333505194748946399

theorem tailTrace_2639993 : CollatzResearch.WordTrace tailWord_2639993 prefixEnd_2639993 1355585333505194748946399 := by
  unfold tailWord_2639993
  simp only [CollatzResearch.WordTrace]
  refine ⟨96288455124763710753524633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64192303416509140502349755 96288455124763710753524633)
  ·
    refine ⟨72216341343572783065143475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96288455124763710753524633 72216341343572783065143475)
    ·
      refine ⟨108324512015359174597715213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72216341343572783065143475 108324512015359174597715213)
      ·
        refine ⟨40621692005759690474143205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108324512015359174597715213 40621692005759690474143205)
        ·
          refine ⟨7616567251079941963901851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40621692005759690474143205 7616567251079941963901851)
          ·
            refine ⟨11424850876619912945852777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7616567251079941963901851 11424850876619912945852777)
            ·
              refine ⟨8568638157464934709389583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11424850876619912945852777 8568638157464934709389583)
              ·
                refine ⟨12852957236197402064084375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8568638157464934709389583 12852957236197402064084375)
                ·
                  refine ⟨19279435854296103096126563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12852957236197402064084375 19279435854296103096126563)
                  ·
                    refine ⟨28919153781444154644189845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19279435854296103096126563 28919153781444154644189845)
                    ·
                      refine ⟨1355585333505194748946399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28919153781444154644189845 1355585333505194748946399)
                      ·
                        rfl

theorem cell23_2639993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_2639993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639993 prefixEnd_2639993 := by exact prefixLift 2639993
  have htrace : WordTrace (prefixWord ++ tailWord_2639993) baseStart_2639993 baseEnd_2639993 := by
    simpa [prefixWord, tailWord_2639993, baseEnd_2639993] using wordTrace_append hprefix tailTrace_2639993
  have hstable : (prefixWord ++ tailWord_2639993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639993).length < 2 ^ (prefixWord ++ tailWord_2639993).sum := by decide
  have hdescent : baseEnd_2639993 < baseStart_2639993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2639997 : List Nat := [1, 4, 1, 1, 3, 4, 1, 2, 1, 1, 4]
def baseStart_2639997 : Nat := 118140960795 + 2639997 * 2 ^ 59
def prefixEnd_2639997 : Nat := 4983230072969 + 3 ^ 40 * 2639997 * 2
def baseEnd_2639997 : Nat := 1355587387427812733296381

theorem tailTrace_2639997 : CollatzResearch.WordTrace tailWord_2639997 prefixEnd_2639997 1355587387427812733296381 := by
  unfold tailWord_2639997
  simp only [CollatzResearch.WordTrace]
  refine ⟨96288601016749219436670245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64192400677832812957780163 96288601016749219436670245)
  ·
    refine ⟨18054112690640478644375671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96288601016749219436670245 18054112690640478644375671)
    ·
      refine ⟨27081169035960717966563507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18054112690640478644375671 27081169035960717966563507)
      ·
        refine ⟨40621753553941076949845261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27081169035960717966563507 40621753553941076949845261)
        ·
          refine ⟨15233157582727903856191973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40621753553941076949845261 15233157582727903856191973)
          ·
            refine ⟨2856217046761481973035995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15233157582727903856191973 2856217046761481973035995)
            ·
              refine ⟨4284325570142222959553993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2856217046761481973035995 4284325570142222959553993)
              ·
                refine ⟨3213244177606667219665495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4284325570142222959553993 3213244177606667219665495)
                ·
                  refine ⟨4819866266410000829498243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3213244177606667219665495 4819866266410000829498243)
                  ·
                    refine ⟨7229799399615001244247365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4819866266410000829498243 7229799399615001244247365)
                    ·
                      refine ⟨1355587387427812733296381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7229799399615001244247365 1355587387427812733296381)
                      ·
                        rfl

theorem cell23_2639997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_2639997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2639997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2639997 prefixEnd_2639997 := by exact prefixLift 2639997
  have htrace : WordTrace (prefixWord ++ tailWord_2639997) baseStart_2639997 baseEnd_2639997 := by
    simpa [prefixWord, tailWord_2639997, baseEnd_2639997] using wordTrace_append hprefix tailTrace_2639997
  have hstable : (prefixWord ++ tailWord_2639997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2639997).length < 2 ^ (prefixWord ++ tailWord_2639997).sum := by decide
  have hdescent : baseEnd_2639997 < baseStart_2639997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2639997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640010 : List Nat := [3, 1, 2, 3, 1, 3, 1, 2, 1, 2, 4]
def baseStart_2640010 : Nat := 118140960795 + 2640010 * 2 ^ 59
def prefixEnd_2640010 : Nat := 4983230072969 + 3 ^ 40 * 2640010 * 2
def baseEnd_2640010 : Nat := 1355594062676321182433821

theorem tailTrace_2640010 : CollatzResearch.WordTrace tailWord_2640010 prefixEnd_2640010 1355594062676321182433821 := by
  unfold tailWord_2640010
  simp only [CollatzResearch.WordTrace]
  refine ⟨24072268791425530664223371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64192716777134748437928989 24072268791425530664223371)
  ·
    refine ⟨36108403187138295996335057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24072268791425530664223371 36108403187138295996335057)
    ·
      refine ⟨27081302390353721997251293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36108403187138295996335057 27081302390353721997251293)
      ·
        refine ⟨10155488396382645748969235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27081302390353721997251293 10155488396382645748969235)
        ·
          refine ⟨15233232594573968623453853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10155488396382645748969235 15233232594573968623453853)
          ·
            refine ⟨5712462222965238233795195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15233232594573968623453853 5712462222965238233795195)
            ·
              refine ⟨8568693334447857350692793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5712462222965238233795195 8568693334447857350692793)
              ·
                refine ⟨6426520000835893013019595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8568693334447857350692793 6426520000835893013019595)
                ·
                  refine ⟨9639780001253839519529393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6426520000835893013019595 9639780001253839519529393)
                  ·
                    refine ⟨7229835000940379639647045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9639780001253839519529393 7229835000940379639647045)
                    ·
                      refine ⟨1355594062676321182433821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7229835000940379639647045 1355594062676321182433821)
                      ·
                        rfl

theorem cell23_2640010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_2640010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640010 prefixEnd_2640010 := by exact prefixLift 2640010
  have htrace : WordTrace (prefixWord ++ tailWord_2640010) baseStart_2640010 baseEnd_2640010 := by
    simpa [prefixWord, tailWord_2640010, baseEnd_2640010] using wordTrace_append hprefix tailTrace_2640010
  have hstable : (prefixWord ++ tailWord_2640010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640010).length < 2 ^ (prefixWord ++ tailWord_2640010).sum := by decide
  have hdescent : baseEnd_2640010 < baseStart_2640010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640014 : List Nat := [4, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4]
def baseStart_2640014 : Nat := 118140960795 + 2640014 * 2 ^ 59
def prefixEnd_2640014 : Nat := 4983230072969 + 3 ^ 40 * 2640014 * 2
def baseEnd_2640014 : Nat := 1355596116598939166783803

theorem tailTrace_2640014 : CollatzResearch.WordTrace tailWord_2640014 prefixEnd_2640014 1355596116598939166783803 := by
  unfold tailWord_2640014
  simp only [CollatzResearch.WordTrace]
  refine ⟨12036152632210953917504887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64192814038458420893359397 12036152632210953917504887)
  ·
    refine ⟨18054228948316430876257331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12036152632210953917504887 18054228948316430876257331)
    ·
      refine ⟨27081343422474646314385997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18054228948316430876257331 27081343422474646314385997)
      ·
        refine ⟨10155503783427992367894749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27081343422474646314385997 10155503783427992367894749)
        ·
          refine ⟨3808313918785497137960531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10155503783427992367894749 3808313918785497137960531)
          ·
            refine ⟨5712470878178245706940797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3808313918785497137960531 5712470878178245706940797)
            ·
              refine ⟨2142176579316842140102799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5712470878178245706940797 2142176579316842140102799)
              ·
                refine ⟨3213264868975263210154199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2142176579316842140102799 3213264868975263210154199)
                ·
                  refine ⟨4819897303462894815231299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3213264868975263210154199 4819897303462894815231299)
                  ·
                    refine ⟨7229845955194342222846949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4819897303462894815231299 7229845955194342222846949)
                    ·
                      refine ⟨1355596116598939166783803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7229845955194342222846949 1355596116598939166783803)
                      ·
                        rfl

theorem cell23_2640014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_2640014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640014 prefixEnd_2640014 := by exact prefixLift 2640014
  have htrace : WordTrace (prefixWord ++ tailWord_2640014) baseStart_2640014 baseEnd_2640014 := by
    simpa [prefixWord, tailWord_2640014, baseEnd_2640014] using wordTrace_append hprefix tailTrace_2640014
  have hstable : (prefixWord ++ tailWord_2640014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640014).length < 2 ^ (prefixWord ++ tailWord_2640014).sum := by decide
  have hdescent : baseEnd_2640014 < baseStart_2640014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640020 : List Nat := [2, 4, 2, 3, 1, 11]
def baseStart_2640020 : Nat := 118140960795 + 2640020 * 2 ^ 59
def prefixEnd_2640020 : Nat := 4983230072969 + 3 ^ 40 * 2640020 * 2
def baseEnd_2640020 : Nat := 5578597520505621988925

theorem tailTrace_2640020 : CollatzResearch.WordTrace tailWord_2640020 prefixEnd_2640020 5578597520505621988925 := by
  unfold tailWord_2640020
  simp only [CollatzResearch.WordTrace]
  refine ⟨48144719947832947182378757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64192959930443929576505009 48144719947832947182378757)
  ·
    refine ⟨9027134990218677596696017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48144719947832947182378757 9027134990218677596696017)
    ·
      refine ⟨6770351242664008197522013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9027134990218677596696017 6770351242664008197522013)
      ·
        refine ⟨2538881715999003074070755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6770351242664008197522013 2538881715999003074070755)
        ·
          refine ⟨3808322573998504611106133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2538881715999003074070755 3808322573998504611106133)
          ·
            refine ⟨5578597520505621988925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3808322573998504611106133 5578597520505621988925)
            ·
              rfl

theorem cell23_2640020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 11].length) (baseStart_2640020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640020 prefixEnd_2640020 := by exact prefixLift 2640020
  have htrace : WordTrace (prefixWord ++ tailWord_2640020) baseStart_2640020 baseEnd_2640020 := by
    simpa [prefixWord, tailWord_2640020, baseEnd_2640020] using wordTrace_append hprefix tailTrace_2640020
  have hstable : (prefixWord ++ tailWord_2640020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640020).length < 2 ^ (prefixWord ++ tailWord_2640020).sum := by decide
  have hdescent : baseEnd_2640020 < baseStart_2640020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640031 : List Nat := [1, 1, 2, 6, 1, 2, 1, 4, 1, 2, 2]
def baseStart_2640031 : Nat := 118140960795 + 2640031 * 2 ^ 59
def prefixEnd_2640031 : Nat := 4983230072969 + 3 ^ 40 * 2640031 * 2
def baseEnd_2640031 : Nat := 1355604845770065600271225

theorem tailTrace_2640031 : CollatzResearch.WordTrace tailWord_2640031 prefixEnd_2640031 1355604845770065600271225 := by
  unfold tailWord_2640031
  simp only [CollatzResearch.WordTrace]
  refine ⟨96289841098626043243407947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64193227399084028828938631 96289841098626043243407947)
  ·
    refine ⟨144434761647939064865111921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96289841098626043243407947 144434761647939064865111921)
    ·
      refine ⟨108326071235954298648833941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144434761647939064865111921 108326071235954298648833941)
      ·
        refine ⟨5077784589185357749164091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 108326071235954298648833941 5077784589185357749164091)
        ·
          refine ⟨7616676883778036623746137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5077784589185357749164091 7616676883778036623746137)
          ·
            refine ⟨5712507662833527467809603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7616676883778036623746137 5712507662833527467809603)
            ·
              refine ⟨8568761494250291201714405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5712507662833527467809603 8568761494250291201714405)
              ·
                refine ⟨1606642780171929600321451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8568761494250291201714405 1606642780171929600321451)
                ·
                  refine ⟨2409964170257894400482177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1606642780171929600321451 2409964170257894400482177)
                  ·
                    refine ⟨1807473127693420800361633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2409964170257894400482177 1807473127693420800361633)
                    ·
                      refine ⟨1355604845770065600271225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1807473127693420800361633 1355604845770065600271225)
                      ·
                        rfl

theorem cell23_2640031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_2640031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640031 prefixEnd_2640031 := by exact prefixLift 2640031
  have htrace : WordTrace (prefixWord ++ tailWord_2640031) baseStart_2640031 baseEnd_2640031 := by
    simpa [prefixWord, tailWord_2640031, baseEnd_2640031] using wordTrace_append hprefix tailTrace_2640031
  have hstable : (prefixWord ++ tailWord_2640031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640031).length < 2 ^ (prefixWord ++ tailWord_2640031).sum := by decide
  have hdescent : baseEnd_2640031 < baseStart_2640031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640033 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 2, 7]
def baseStart_2640033 : Nat := 118140960795 + 2640033 * 2 ^ 59
def prefixEnd_2640033 : Nat := 4983230072969 + 3 ^ 40 * 2640033 * 2
def baseEnd_2640033 : Nat := 451868624243791530815405

theorem tailTrace_2640033 : CollatzResearch.WordTrace tailWord_2640033 prefixEnd_2640033 451868624243791530815405 := by
  unfold tailWord_2640033
  simp only [CollatzResearch.WordTrace]
  refine ⟨96289914044618797584980753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64193276029745865056653835 96289914044618797584980753)
  ·
    refine ⟨72217435533464098188735565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96289914044618797584980753 72217435533464098188735565)
    ·
      refine ⟨27081538325049036820775837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72217435533464098188735565 27081538325049036820775837)
      ·
        refine ⟨10155576871893388807790939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27081538325049036820775837 10155576871893388807790939)
        ·
          refine ⟨15233365307840083211686409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10155576871893388807790939 15233365307840083211686409)
          ·
            refine ⟨11425023980880062408764807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15233365307840083211686409 11425023980880062408764807)
            ·
              refine ⟨17137535971320093613147211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11425023980880062408764807 17137535971320093613147211)
              ·
                refine ⟨25706303956980140419720817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17137535971320093613147211 25706303956980140419720817)
                ·
                  refine ⟨19279727967735105314790613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25706303956980140419720817 19279727967735105314790613)
                  ·
                    refine ⟨451868624243791530815405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19279727967735105314790613 451868624243791530815405)
                    ·
                      rfl

theorem cell23_2640033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_2640033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640033 prefixEnd_2640033 := by exact prefixLift 2640033
  have htrace : WordTrace (prefixWord ++ tailWord_2640033) baseStart_2640033 baseEnd_2640033 := by
    simpa [prefixWord, tailWord_2640033, baseEnd_2640033] using wordTrace_append hprefix tailTrace_2640033
  have hstable : (prefixWord ++ tailWord_2640033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640033).length < 2 ^ (prefixWord ++ tailWord_2640033).sum := by decide
  have hdescent : baseEnd_2640033 < baseStart_2640033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640057 : List Nat := [1, 2, 1, 4, 1, 2, 2, 4, 1, 3, 2]
def baseStart_2640057 : Nat := 118140960795 + 2640057 * 2 ^ 59
def prefixEnd_2640057 : Nat := 4983230072969 + 3 ^ 40 * 2640057 * 2
def baseEnd_2640057 : Nat := 1355618196267082498546105

theorem tailTrace_2640057 : CollatzResearch.WordTrace tailWord_2640057 prefixEnd_2640057 1355618196267082498546105 := by
  unfold tailWord_2640057
  simp only [CollatzResearch.WordTrace]
  refine ⟨96290789396531849683854425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64193859597687899789236283 96290789396531849683854425)
  ·
    refine ⟨72218092047398887262890819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96290789396531849683854425 72218092047398887262890819)
    ·
      refine ⟨108327138071098330894336229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72218092047398887262890819 108327138071098330894336229)
      ·
        refine ⟨20311338388330937042688043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108327138071098330894336229 20311338388330937042688043)
        ·
          refine ⟨30467007582496405564032065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20311338388330937042688043 30467007582496405564032065)
          ·
            refine ⟨22850255686872304173024049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30467007582496405564032065 22850255686872304173024049)
            ·
              refine ⟨17137691765154228129768037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22850255686872304173024049 17137691765154228129768037)
              ·
                refine ⟨3213317205966417774331507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17137691765154228129768037 3213317205966417774331507)
                ·
                  refine ⟨4819975808949626661497261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3213317205966417774331507 4819975808949626661497261)
                  ·
                    refine ⟨1807490928356109998061473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4819975808949626661497261 1807490928356109998061473)
                    ·
                      refine ⟨1355618196267082498546105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1807490928356109998061473 1355618196267082498546105)
                      ·
                        rfl

theorem cell23_2640057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_2640057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640057 prefixEnd_2640057 := by exact prefixLift 2640057
  have htrace : WordTrace (prefixWord ++ tailWord_2640057) baseStart_2640057 baseEnd_2640057 := by
    simpa [prefixWord, tailWord_2640057, baseEnd_2640057] using wordTrace_append hprefix tailTrace_2640057
  have hstable : (prefixWord ++ tailWord_2640057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640057).length < 2 ^ (prefixWord ++ tailWord_2640057).sum := by decide
  have hdescent : baseEnd_2640057 < baseStart_2640057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640073 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 1, 6, 3]
def baseStart_2640073 : Nat := 118140960795 + 2640073 * 2 ^ 59
def prefixEnd_2640073 : Nat := 4983230072969 + 3 ^ 40 * 2640073 * 2
def baseEnd_2640073 : Nat := 1355626411957554435946031

theorem tailTrace_2640073 : CollatzResearch.WordTrace tailWord_2640073 prefixEnd_2640073 1355626411957554435946031 := by
  unfold tailWord_2640073
  simp only [CollatzResearch.WordTrace]
  refine ⟨96291372964473884416436873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64194248642982589610957915 96291372964473884416436873)
  ·
    refine ⟨72218529723355413312327655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96291372964473884416436873 72218529723355413312327655)
    ·
      refine ⟨108327794585033119968491483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72218529723355413312327655 108327794585033119968491483)
      ·
        refine ⟨162491691877549679952737225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108327794585033119968491483 162491691877549679952737225)
        ·
          refine ⟨121868768908162259964552919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162491691877549679952737225 121868768908162259964552919)
          ·
            refine ⟨182803153362243389946829379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121868768908162259964552919 182803153362243389946829379)
            ·
              refine ⟨274204730043365084920244069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182803153362243389946829379 274204730043365084920244069)
              ·
                refine ⟨51413386883130953422545763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 274204730043365084920244069 51413386883130953422545763)
                ·
                  refine ⟨77120080324696430133818645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51413386883130953422545763 77120080324696430133818645)
                  ·
                    refine ⟨3615003765220145162522749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77120080324696430133818645 3615003765220145162522749)
                    ·
                      refine ⟨1355626411957554435946031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3615003765220145162522749 1355626411957554435946031)
                      ·
                        rfl

theorem cell23_2640073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 6, 3].length) (baseStart_2640073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640073 prefixEnd_2640073 := by exact prefixLift 2640073
  have htrace : WordTrace (prefixWord ++ tailWord_2640073) baseStart_2640073 baseEnd_2640073 := by
    simpa [prefixWord, tailWord_2640073, baseEnd_2640073] using wordTrace_append hprefix tailTrace_2640073
  have hstable : (prefixWord ++ tailWord_2640073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640073).length < 2 ^ (prefixWord ++ tailWord_2640073).sum := by decide
  have hdescent : baseEnd_2640073 < baseStart_2640073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640098 : List Nat := [3, 3, 4, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_2640098 : Nat := 118140960795 + 2640098 * 2 ^ 59
def prefixEnd_2640098 : Nat := 4983230072969 + 3 ^ 40 * 2640098 * 2
def baseEnd_2640098 : Nat := 1355639248973916838133417

theorem tailTrace_2640098 : CollatzResearch.WordTrace tailWord_2640098 prefixEnd_2640098 1355639248973916838133417 := by
  unfold tailWord_2640098
  simp only [CollatzResearch.WordTrace]
  refine ⟨24073071197345828421524237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64194856526255542457397965 24073071197345828421524237)
  ·
    refine ⟨9027401699004685658071589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24073071197345828421524237 9027401699004685658071589)
    ·
      refine ⟨1692637818563378560888423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9027401699004685658071589 1692637818563378560888423)
      ·
        refine ⟨2538956727845067841332635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1692637818563378560888423 2538956727845067841332635)
        ·
          refine ⟨3808435091767601761998953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2538956727845067841332635 3808435091767601761998953)
          ·
            refine ⟨2856326318825701321499215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3808435091767601761998953 2856326318825701321499215)
            ·
              refine ⟨4284489478238551982248823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2856326318825701321499215 4284489478238551982248823)
              ·
                refine ⟨6426734217357827973373235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4284489478238551982248823 6426734217357827973373235)
                ·
                  refine ⟨9640101326036741960059853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6426734217357827973373235 9640101326036741960059853)
                  ·
                    refine ⟨3615037997263778235022445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9640101326036741960059853 3615037997263778235022445)
                    ·
                      refine ⟨1355639248973916838133417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3615037997263778235022445 1355639248973916838133417)
                      ·
                        rfl

theorem cell23_2640098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_2640098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640098 prefixEnd_2640098 := by exact prefixLift 2640098
  have htrace : WordTrace (prefixWord ++ tailWord_2640098) baseStart_2640098 baseEnd_2640098 := by
    simpa [prefixWord, tailWord_2640098, baseEnd_2640098] using wordTrace_append hprefix tailTrace_2640098
  have hstable : (prefixWord ++ tailWord_2640098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640098).length < 2 ^ (prefixWord ++ tailWord_2640098).sum := by decide
  have hdescent : baseEnd_2640098 < baseStart_2640098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640104 : List Nat := [2, 1, 4, 1, 2, 4, 1, 1, 1, 4, 2]
def baseStart_2640104 : Nat := 118140960795 + 2640104 * 2 ^ 59
def prefixEnd_2640104 : Nat := 4983230072969 + 3 ^ 40 * 2640104 * 2
def baseEnd_2640104 : Nat := 1355642329857843814658389

theorem tailTrace_2640104 : CollatzResearch.WordTrace tailWord_2640104 prefixEnd_2640104 1355642329857843814658389 := by
  unfold tailWord_2640104
  simp only [CollatzResearch.WordTrace]
  refine ⟨48146251813680788355407683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64195002418241051140543577 48146251813680788355407683)
  ·
    refine ⟨72219377720521182533111525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48146251813680788355407683 72219377720521182533111525)
    ·
      refine ⟨13541133322597721724958411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72219377720521182533111525 13541133322597721724958411)
      ·
        refine ⟨20311699983896582587437617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13541133322597721724958411 20311699983896582587437617)
        ·
          refine ⟨15233774987922436940578213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20311699983896582587437617 15233774987922436940578213)
          ·
            refine ⟨2856332810235456926358415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15233774987922436940578213 2856332810235456926358415)
            ·
              refine ⟨4284499215353185389537623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2856332810235456926358415 4284499215353185389537623)
              ·
                refine ⟨6426748823029778084306435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4284499215353185389537623 6426748823029778084306435)
                ·
                  refine ⟨9640123234544667126459653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6426748823029778084306435 9640123234544667126459653)
                  ·
                    refine ⟨1807523106477125086211185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9640123234544667126459653 1807523106477125086211185)
                    ·
                      refine ⟨1355642329857843814658389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1807523106477125086211185 1355642329857843814658389)
                      ·
                        rfl

theorem cell23_2640104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_2640104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640104 prefixEnd_2640104 := by exact prefixLift 2640104
  have htrace : WordTrace (prefixWord ++ tailWord_2640104) baseStart_2640104 baseEnd_2640104 := by
    simpa [prefixWord, tailWord_2640104, baseEnd_2640104] using wordTrace_append hprefix tailTrace_2640104
  have hstable : (prefixWord ++ tailWord_2640104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640104).length < 2 ^ (prefixWord ++ tailWord_2640104).sum := by decide
  have hdescent : baseEnd_2640104 < baseStart_2640104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640123 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 8, 5]
def baseStart_2640123 : Nat := 118140960795 + 2640123 * 2 ^ 59
def prefixEnd_2640123 : Nat := 4983230072969 + 3 ^ 40 * 2640123 * 2
def baseEnd_2640123 : Nat := 451884028663426413440267

theorem tailTrace_2640123 : CollatzResearch.WordTrace tailWord_2640123 prefixEnd_2640123 451884028663426413440267 := by
  unfold tailWord_2640123
  simp only [CollatzResearch.WordTrace]
  refine ⟨96293196614292742955757023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64195464409528495303838015 96293196614292742955757023)
  ·
    refine ⟨144439794921439114433635535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96293196614292742955757023 144439794921439114433635535)
    ·
      refine ⟨216659692382158671650453303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144439794921439114433635535 216659692382158671650453303)
      ·
        refine ⟨324989538573238007475679955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216659692382158671650453303 324989538573238007475679955)
        ·
          refine ⟨487484307859857011213519933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324989538573238007475679955 487484307859857011213519933)
          ·
            refine ⟨182806615447446379205069975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 487484307859857011213519933 182806615447446379205069975)
            ·
              refine ⟨274209923171169568807604963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182806615447446379205069975 274209923171169568807604963)
              ·
                refine ⟨411314884756754353211407445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274209923171169568807604963 411314884756754353211407445)
                ·
                  refine ⟨4820096305743215076696181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 411314884756754353211407445 4820096305743215076696181)
                  ·
                    refine ⟨451884028663426413440267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4820096305743215076696181 451884028663426413440267)
                    ·
                      rfl

theorem cell23_2640123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 5].length) (baseStart_2640123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640123 prefixEnd_2640123 := by exact prefixLift 2640123
  have htrace : WordTrace (prefixWord ++ tailWord_2640123) baseStart_2640123 baseEnd_2640123 := by
    simpa [prefixWord, tailWord_2640123, baseEnd_2640123] using wordTrace_append hprefix tailTrace_2640123
  have hstable : (prefixWord ++ tailWord_2640123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640123).length < 2 ^ (prefixWord ++ tailWord_2640123).sum := by decide
  have hdescent : baseEnd_2640123 < baseStart_2640123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640140 : List Nat := [2, 2, 1, 2, 2, 2, 3, 2, 2, 5]
def baseStart_2640140 : Nat := 118140960795 + 2640140 * 2 ^ 59
def prefixEnd_2640140 : Nat := 4983230072969 + 3 ^ 40 * 2640140 * 2
def baseEnd_2640140 : Nat := 451886938387135224602741

theorem tailTrace_2640140 : CollatzResearch.WordTrace tailWord_2640140 prefixEnd_2640140 451886938387135224602741 := by
  unfold tailWord_2640140
  simp only [CollatzResearch.WordTrace]
  refine ⟨48146908327615577429562937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64195877770154103239417249 48146908327615577429562937)
  ·
    refine ⟨36110181245711683072172203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48146908327615577429562937 36110181245711683072172203)
    ·
      refine ⟨54165271868567524608258305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36110181245711683072172203 54165271868567524608258305)
      ·
        refine ⟨40623953901425643456193729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54165271868567524608258305 40623953901425643456193729)
        ·
          refine ⟨30467965426069232592145297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40623953901425643456193729 30467965426069232592145297)
          ·
            refine ⟨22850974069551924444108973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30467965426069232592145297 22850974069551924444108973)
            ·
              refine ⟨8569115276081971666540865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22850974069551924444108973 8569115276081971666540865)
              ·
                refine ⟨6426836457061478749905649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8569115276081971666540865 6426836457061478749905649)
                ·
                  refine ⟨4820127342796109062429237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6426836457061478749905649 4820127342796109062429237)
                  ·
                    refine ⟨451886938387135224602741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4820127342796109062429237 451886938387135224602741)
                    ·
                      rfl

theorem cell23_2640140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_2640140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640140 prefixEnd_2640140 := by exact prefixLift 2640140
  have htrace : WordTrace (prefixWord ++ tailWord_2640140) baseStart_2640140 baseEnd_2640140 := by
    simpa [prefixWord, tailWord_2640140, baseEnd_2640140] using wordTrace_append hprefix tailTrace_2640140
  have hstable : (prefixWord ++ tailWord_2640140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640140).length < 2 ^ (prefixWord ++ tailWord_2640140).sum := by decide
  have hdescent : baseEnd_2640140 < baseStart_2640140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640183 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 10]
def baseStart_2640183 : Nat := 118140960795 + 2640183 * 2 ^ 59
def prefixEnd_2640183 : Nat := 4983230072969 + 3 ^ 40 * 2640183 * 2
def baseEnd_2640183 : Nat := 150631432758838778396725

theorem tailTrace_2640183 : CollatzResearch.WordTrace tailWord_2640183 prefixEnd_2640183 150631432758838778396725 := by
  unfold tailWord_2640183
  simp only [CollatzResearch.WordTrace]
  refine ⟨96295384994075373202941203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64196923329383582135294135 96295384994075373202941203)
  ·
    refine ⟨144443077491113059804411805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96295384994075373202941203 144443077491113059804411805)
    ·
      refine ⟨54166154059167397426654427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144443077491113059804411805 54166154059167397426654427)
      ·
        refine ⟨81249231088751096139981641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54166154059167397426654427 81249231088751096139981641)
        ·
          refine ⟨60936923316563322104986231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81249231088751096139981641 60936923316563322104986231)
          ·
            refine ⟨91405384974844983157479347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60936923316563322104986231 91405384974844983157479347)
            ·
              refine ⟨137108077462267474736219021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91405384974844983157479347 137108077462267474736219021)
              ·
                refine ⟨51415529048350303026082133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137108077462267474736219021 51415529048350303026082133)
                ·
                  refine ⟨150631432758838778396725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 51415529048350303026082133 150631432758838778396725)
                  ·
                    rfl

theorem cell23_2640183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 10].length) (baseStart_2640183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640183 prefixEnd_2640183 := by exact prefixLift 2640183
  have htrace : WordTrace (prefixWord ++ tailWord_2640183) baseStart_2640183 baseEnd_2640183 := by
    simpa [prefixWord, tailWord_2640183, baseEnd_2640183] using wordTrace_append hprefix tailTrace_2640183
  have hstable : (prefixWord ++ tailWord_2640183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640183).length < 2 ^ (prefixWord ++ tailWord_2640183).sum := by decide
  have hdescent : baseEnd_2640183 < baseStart_2640183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640200 : List Nat := [2, 1, 3, 1, 1, 2, 3, 4, 6]
def baseStart_2640200 : Nat := 118140960795 + 2640200 * 2 ^ 59
def prefixEnd_2640200 : Nat := 4983230072969 + 3 ^ 40 * 2640200 * 2
def baseEnd_2640200 : Nat := 150632402666741715450883

theorem tailTrace_2640200 : CollatzResearch.WordTrace tailWord_2640200 prefixEnd_2640200 150632402666741715450883 := by
  unfold tailWord_2640200
  simp only [CollatzResearch.WordTrace]
  refine ⟨48148002517506892553155027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64197336690009190070873369 48148002517506892553155027)
  ·
    refine ⟨72222003776260338829732541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48148002517506892553155027 72222003776260338829732541)
    ·
      refine ⟨27083251416097627061149703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72222003776260338829732541 27083251416097627061149703)
      ·
        refine ⟨40624877124146440591724555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27083251416097627061149703 40624877124146440591724555)
        ·
          refine ⟨60937315686219660887586833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40624877124146440591724555 60937315686219660887586833)
          ·
            refine ⟨45702986764664745665690125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60937315686219660887586833 45702986764664745665690125)
            ·
              refine ⟨17138620036749279624633797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45702986764664745665690125 17138620036749279624633797)
              ·
                refine ⟨3213491256890489929618837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17138620036749279624633797 3213491256890489929618837)
                ·
                  refine ⟨150632402666741715450883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3213491256890489929618837 150632402666741715450883)
                  ·
                    rfl

theorem cell23_2640200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 6].length) (baseStart_2640200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640200 prefixEnd_2640200 := by exact prefixLift 2640200
  have htrace : WordTrace (prefixWord ++ tailWord_2640200) baseStart_2640200 baseEnd_2640200 := by
    simpa [prefixWord, tailWord_2640200, baseEnd_2640200] using wordTrace_append hprefix tailTrace_2640200
  have hstable : (prefixWord ++ tailWord_2640200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640200).length < 2 ^ (prefixWord ++ tailWord_2640200).sum := by decide
  have hdescent : baseEnd_2640200 < baseStart_2640200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640204 : List Nat := [2, 2, 1, 3, 2, 1, 3, 4, 1, 4]
def baseStart_2640204 : Nat := 118140960795 + 2640204 * 2 ^ 59
def prefixEnd_2640204 : Nat := 4983230072969 + 3 ^ 40 * 2640204 * 2
def baseEnd_2640204 : Nat := 451897892641097807802643

theorem tailTrace_2640204 : CollatzResearch.WordTrace tailWord_2640204 prefixEnd_2640204 451897892641097807802643 := by
  unfold tailWord_2640204
  simp only [CollatzResearch.WordTrace]
  refine ⟨48148075463499646894727833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64197433951332862526303777 48148075463499646894727833)
  ·
    refine ⟨36111056597624735171045875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48148075463499646894727833 36111056597624735171045875)
    ·
      refine ⟨54166584896437102756568813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36111056597624735171045875 54166584896437102756568813)
      ·
        refine ⟨20312469336163913533713305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54166584896437102756568813 20312469336163913533713305)
        ·
          refine ⟨15234352002122935150284979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20312469336163913533713305 15234352002122935150284979)
          ·
            refine ⟨22851528003184402725427469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15234352002122935150284979 22851528003184402725427469)
            ·
              refine ⟨8569323001194151022035301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22851528003184402725427469 8569323001194151022035301)
              ·
                refine ⟨1606748062723903316631619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8569323001194151022035301 1606748062723903316631619)
                ·
                  refine ⟨2410122094085854974947429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1606748062723903316631619 2410122094085854974947429)
                  ·
                    refine ⟨451897892641097807802643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2410122094085854974947429 451897892641097807802643)
                    ·
                      rfl

theorem cell23_2640204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 1, 4].length) (baseStart_2640204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640204 prefixEnd_2640204 := by exact prefixLift 2640204
  have htrace : WordTrace (prefixWord ++ tailWord_2640204) baseStart_2640204 baseEnd_2640204 := by
    simpa [prefixWord, tailWord_2640204, baseEnd_2640204] using wordTrace_append hprefix tailTrace_2640204
  have hstable : (prefixWord ++ tailWord_2640204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640204).length < 2 ^ (prefixWord ++ tailWord_2640204).sum := by decide
  have hdescent : baseEnd_2640204 < baseStart_2640204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640318 : List Nat := [4, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2]
def baseStart_2640318 : Nat := 118140960795 + 2640318 * 2 ^ 59
def prefixEnd_2640318 : Nat := 4983230072969 + 3 ^ 40 * 2640318 * 2
def baseEnd_2640318 : Nat := 1355752214717905977382405

theorem tailTrace_2640318 : CollatzResearch.WordTrace tailWord_2640318 prefixEnd_2640318 1355752214717905977382405 := by
  unfold tailWord_2640318
  simp only [CollatzResearch.WordTrace]
  refine ⟨12037538606073286407388201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64200205899057527506070405 12037538606073286407388201)
  ·
    refine ⟨9028153954554964805541151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12037538606073286407388201 9028153954554964805541151)
    ·
      refine ⟨13542230931832447208311727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9028153954554964805541151 13542230931832447208311727)
      ·
        refine ⟨20313346397748670812467591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13542230931832447208311727 20313346397748670812467591)
        ·
          refine ⟨30470019596623006218701387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20313346397748670812467591 30470019596623006218701387)
          ·
            refine ⟨45705029394934509328052081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30470019596623006218701387 45705029394934509328052081)
            ·
              refine ⟨34278772046200881996039061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45705029394934509328052081 34278772046200881996039061)
              ·
                refine ⟨1606817439665666343564331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34278772046200881996039061 1606817439665666343564331)
                ·
                  refine ⟨2410226159498499515346497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1606817439665666343564331 2410226159498499515346497)
                  ·
                    refine ⟨1807669619623874636509873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2410226159498499515346497 1807669619623874636509873)
                    ·
                      refine ⟨1355752214717905977382405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1807669619623874636509873 1355752214717905977382405)
                      ·
                        rfl

theorem cell23_2640318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_2640318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640318 prefixEnd_2640318 := by exact prefixLift 2640318
  have htrace : WordTrace (prefixWord ++ tailWord_2640318) baseStart_2640318 baseEnd_2640318 := by
    simpa [prefixWord, tailWord_2640318, baseEnd_2640318] using wordTrace_append hprefix tailTrace_2640318
  have hstable : (prefixWord ++ tailWord_2640318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640318).length < 2 ^ (prefixWord ++ tailWord_2640318).sum := by decide
  have hdescent : baseEnd_2640318 < baseStart_2640318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640320 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 2, 7]
def baseStart_2640320 : Nat := 118140960795 + 2640320 * 2 ^ 59
def prefixEnd_2640320 : Nat := 4983230072969 + 3 ^ 40 * 2640320 * 2
def baseEnd_2640320 : Nat := 451917747226404989852465

theorem tailTrace_2640320 : CollatzResearch.WordTrace tailWord_2640320 prefixEnd_2640320 451917747226404989852465 := by
  unfold tailWord_2640320
  simp only [CollatzResearch.WordTrace]
  refine ⟨48150190897289522800339207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64200254529719363733785609 48150190897289522800339207)
  ·
    refine ⟨72225286345934284200508811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48150190897289522800339207 72225286345934284200508811)
    ·
      refine ⟨108337929518901426300763217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72225286345934284200508811 108337929518901426300763217)
      ·
        refine ⟨81253447139176069725572413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108337929518901426300763217 81253447139176069725572413)
        ·
          refine ⟨30470042677191026147089655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81253447139176069725572413 30470042677191026147089655)
          ·
            refine ⟨45705064015786539220634483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30470042677191026147089655 45705064015786539220634483)
            ·
              refine ⟨68557596023679808830951725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45705064015786539220634483 68557596023679808830951725)
              ·
                refine ⟨25709098508879928311606897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68557596023679808830951725 25709098508879928311606897)
                ·
                  refine ⟨19281823881659946233705173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25709098508879928311606897 19281823881659946233705173)
                  ·
                    refine ⟨451917747226404989852465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19281823881659946233705173 451917747226404989852465)
                    ·
                      rfl

theorem cell23_2640320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 2, 7].length) (baseStart_2640320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640320 prefixEnd_2640320 := by exact prefixLift 2640320
  have htrace : WordTrace (prefixWord ++ tailWord_2640320) baseStart_2640320 baseEnd_2640320 := by
    simpa [prefixWord, tailWord_2640320, baseEnd_2640320] using wordTrace_append hprefix tailTrace_2640320
  have hstable : (prefixWord ++ tailWord_2640320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640320).length < 2 ^ (prefixWord ++ tailWord_2640320).sum := by decide
  have hdescent : baseEnd_2640320 < baseStart_2640320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640324 : List Nat := [2, 3, 3, 2, 2, 1, 2, 8]
def baseStart_2640324 : Nat := 118140960795 + 2640324 * 2 ^ 59
def prefixEnd_2640324 : Nat := 4983230072969 + 3 ^ 40 * 2640324 * 2
def baseEnd_2640324 : Nat := 50213159096364183478051

theorem tailTrace_2640324 : CollatzResearch.WordTrace tailWord_2640324 prefixEnd_2640324 50213159096364183478051 := by
  unfold tailWord_2640324
  simp only [CollatzResearch.WordTrace]
  refine ⟨48150263843282277141912013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64200351791043036189216017 48150263843282277141912013)
  ·
    refine ⟨18056348941230853928217005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48150263843282277141912013 18056348941230853928217005)
    ·
      refine ⟨6771130852961570223081377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18056348941230853928217005 6771130852961570223081377)
      ·
        refine ⟨5078348139721177667311033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6771130852961570223081377 5078348139721177667311033)
        ·
          refine ⟨3808761104790883250483275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5078348139721177667311033 3808761104790883250483275)
          ·
            refine ⟨5713141657186324875724913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3808761104790883250483275 5713141657186324875724913)
            ·
              refine ⟨4284856242889743656793685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5713141657186324875724913 4284856242889743656793685)
              ·
                refine ⟨50213159096364183478051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4284856242889743656793685 50213159096364183478051)
                ·
                  rfl

theorem cell23_2640324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 8].length) (baseStart_2640324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640324 prefixEnd_2640324 := by exact prefixLift 2640324
  have htrace : WordTrace (prefixWord ++ tailWord_2640324) baseStart_2640324 baseEnd_2640324 := by
    simpa [prefixWord, tailWord_2640324, baseEnd_2640324] using wordTrace_append hprefix tailTrace_2640324
  have hstable : (prefixWord ++ tailWord_2640324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640324).length < 2 ^ (prefixWord ++ tailWord_2640324).sum := by decide
  have hdescent : baseEnd_2640324 < baseStart_2640324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640377 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 2, 4, 3]
def baseStart_2640377 : Nat := 118140960795 + 2640377 * 2 ^ 59
def prefixEnd_2640377 : Nat := 4983230072969 + 3 ^ 40 * 2640377 * 2
def baseEnd_2640377 : Nat := 1355782510076521246544633

theorem tailTrace_2640377 : CollatzResearch.WordTrace tailWord_2640377 prefixEnd_2640377 1355782510076521246544633 := by
  unfold tailWord_2640377
  simp only [CollatzResearch.WordTrace]
  refine ⟨96302460755372544335503385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64201640503581696223668923 96302460755372544335503385)
  ·
    refine ⟨72226845566529408251627539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96302460755372544335503385 72226845566529408251627539)
    ·
      refine ⟨108340268349794112377441309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72226845566529408251627539 108340268349794112377441309)
      ·
        refine ⟨40627600631172792141540491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108340268349794112377441309 40627600631172792141540491)
        ·
          refine ⟨60941400946759188212310737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40627600631172792141540491 60941400946759188212310737)
          ·
            refine ⟨45706050710069391159233053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60941400946759188212310737 45706050710069391159233053)
            ·
              refine ⟨17139769016276021684712395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45706050710069391159233053 17139769016276021684712395)
              ·
                refine ⟨25709653524414032527068593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17139769016276021684712395 25709653524414032527068593)
                ·
                  refine ⟨19282240143310524395301445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25709653524414032527068593 19282240143310524395301445)
                  ·
                    refine ⟨3615420026870723324119021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19282240143310524395301445 3615420026870723324119021)
                    ·
                      refine ⟨1355782510076521246544633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3615420026870723324119021 1355782510076521246544633)
                      ·
                        rfl

theorem cell23_2640377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_2640377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640377 prefixEnd_2640377 := by exact prefixLift 2640377
  have htrace : WordTrace (prefixWord ++ tailWord_2640377) baseStart_2640377 baseEnd_2640377 := by
    simpa [prefixWord, tailWord_2640377, baseEnd_2640377] using wordTrace_append hprefix tailTrace_2640377
  have hstable : (prefixWord ++ tailWord_2640377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640377).length < 2 ^ (prefixWord ++ tailWord_2640377).sum := by decide
  have hdescent : baseEnd_2640377 < baseStart_2640377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640387 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 4]
def baseStart_2640387 : Nat := 118140960795 + 2640387 * 2 ^ 59
def prefixEnd_2640387 : Nat := 4983230072969 + 3 ^ 40 * 2640387 * 2
def baseEnd_2640387 : Nat := 1355787644883066207419587

theorem tailTrace_2640387 : CollatzResearch.WordTrace tailWord_2640387 prefixEnd_2640387 1355787644883066207419587 := by
  unfold tailWord_2640387
  simp only [CollatzResearch.WordTrace]
  refine ⟨96302825485336316043367415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64201883656890877362244943 96302825485336316043367415)
  ·
    refine ⟨144454238228004474065051123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96302825485336316043367415 144454238228004474065051123)
    ·
      refine ⟨216681357342006711097576685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144454238228004474065051123 216681357342006711097576685)
      ·
        refine ⟨81255509003252516661591257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216681357342006711097576685 81255509003252516661591257)
        ·
          refine ⟨60941631752439387496193443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81255509003252516661591257 60941631752439387496193443)
          ·
            refine ⟨91412447628659081244290165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60941631752439387496193443 91412447628659081244290165)
            ·
              refine ⟨8569916965186788866652203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91412447628659081244290165 8569916965186788866652203)
              ·
                refine ⟨12854875447780183299978305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8569916965186788866652203 12854875447780183299978305)
                ·
                  refine ⟨9641156585835137474983729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12854875447780183299978305 9641156585835137474983729)
                  ·
                    refine ⟨7230867439376353106237797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9641156585835137474983729 7230867439376353106237797)
                    ·
                      refine ⟨1355787644883066207419587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7230867439376353106237797 1355787644883066207419587)
                      ·
                        rfl

theorem cell23_2640387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_2640387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640387 prefixEnd_2640387 := by exact prefixLift 2640387
  have htrace : WordTrace (prefixWord ++ tailWord_2640387) baseStart_2640387 baseEnd_2640387 := by
    simpa [prefixWord, tailWord_2640387, baseEnd_2640387] using wordTrace_append hprefix tailTrace_2640387
  have hstable : (prefixWord ++ tailWord_2640387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640387).length < 2 ^ (prefixWord ++ tailWord_2640387).sum := by decide
  have hdescent : baseEnd_2640387 < baseStart_2640387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640427 : List Nat := [1, 1, 1, 1, 2, 1, 3, 6, 2, 5]
def baseStart_2640427 : Nat := 118140960795 + 2640427 * 2 ^ 59
def prefixEnd_2640427 : Nat := 4983230072969 + 3 ^ 40 * 2640427 * 2
def baseEnd_2640427 : Nat := 451936061369748683639801

theorem tailTrace_2640427 : CollatzResearch.WordTrace tailWord_2640427 prefixEnd_2640427 451936061369748683639801 := by
  unfold tailWord_2640427
  simp only [CollatzResearch.WordTrace]
  refine ⟨96304284405191402874823535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64202856270127601916549023 96304284405191402874823535)
  ·
    refine ⟨144456426607787104312235303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96304284405191402874823535 144456426607787104312235303)
    ·
      refine ⟨216684639911680656468352955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144456426607787104312235303 216684639911680656468352955)
      ·
        refine ⟨325026959867520984702529433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216684639911680656468352955 325026959867520984702529433)
        ·
          refine ⟨243770219900640738526897075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325026959867520984702529433 243770219900640738526897075)
          ·
            refine ⟨365655329850961107790345613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243770219900640738526897075 365655329850961107790345613)
            ·
              refine ⟨137120748694110415421379605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 365655329850961107790345613 137120748694110415421379605)
              ·
                refine ⟨6427535095036425722877169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 137120748694110415421379605 6427535095036425722877169)
                ·
                  refine ⟨4820651321277319292157877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6427535095036425722877169 4820651321277319292157877)
                  ·
                    refine ⟨451936061369748683639801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4820651321277319292157877 451936061369748683639801)
                    ·
                      rfl

theorem cell23_2640427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 5].length) (baseStart_2640427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640427 prefixEnd_2640427 := by exact prefixLift 2640427
  have htrace : WordTrace (prefixWord ++ tailWord_2640427) baseStart_2640427 baseEnd_2640427 := by
    simpa [prefixWord, tailWord_2640427, baseEnd_2640427] using wordTrace_append hprefix tailTrace_2640427
  have hstable : (prefixWord ++ tailWord_2640427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640427).length < 2 ^ (prefixWord ++ tailWord_2640427).sum := by decide
  have hdescent : baseEnd_2640427 < baseStart_2640427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640434 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2]
def baseStart_2640434 : Nat := 118140960795 + 2640434 * 2 ^ 59
def prefixEnd_2640434 : Nat := 4983230072969 + 3 ^ 40 * 2640434 * 2
def baseEnd_2640434 : Nat := 1355811778473827523531871

theorem tailTrace_2640434 : CollatzResearch.WordTrace tailWord_2640434 prefixEnd_2640434 1355811778473827523531871 := by
  unfold tailWord_2640434
  simp only [CollatzResearch.WordTrace]
  refine ⟨24076134929041510767582089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64203026477444028713552237 24076134929041510767582089)
  ·
    refine ⟨18057101196781133075686567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24076134929041510767582089 18057101196781133075686567)
    ·
      refine ⟨27085651795171699613529851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18057101196781133075686567 27085651795171699613529851)
      ·
        refine ⟨40628477692757549420294777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27085651795171699613529851 40628477692757549420294777)
        ·
          refine ⟨30471358269568162065221083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40628477692757549420294777 30471358269568162065221083)
          ·
            refine ⟨45707037404352243097831625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30471358269568162065221083 45707037404352243097831625)
            ·
              refine ⟨34280278053264182323373719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45707037404352243097831625 34280278053264182323373719)
              ·
                refine ⟨51420417079896273485060579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34280278053264182323373719 51420417079896273485060579)
                ·
                  refine ⟨77130625619844410227590869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51420417079896273485060579 77130625619844410227590869)
                  ·
                    refine ⟨1807749037965103364709161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 77130625619844410227590869 1807749037965103364709161)
                    ·
                      refine ⟨1355811778473827523531871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1807749037965103364709161 1355811778473827523531871)
                      ·
                        rfl

theorem cell23_2640434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_2640434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640434 prefixEnd_2640434 := by exact prefixLift 2640434
  have htrace : WordTrace (prefixWord ++ tailWord_2640434) baseStart_2640434 baseEnd_2640434 := by
    simpa [prefixWord, tailWord_2640434, baseEnd_2640434] using wordTrace_append hprefix tailTrace_2640434
  have hstable : (prefixWord ++ tailWord_2640434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640434).length < 2 ^ (prefixWord ++ tailWord_2640434).sum := by decide
  have hdescent : baseEnd_2640434 < baseStart_2640434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640437 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_2640437 : Nat := 118140960795 + 2640437 * 2 ^ 59
def prefixEnd_2640437 : Nat := 4983230072969 + 3 ^ 40 * 2640437 * 2
def baseEnd_2640437 : Nat := 1355813318915791011794357

theorem tailTrace_2640437 : CollatzResearch.WordTrace tailWord_2640437 prefixEnd_2640437 1355813318915791011794357 := by
  unfold tailWord_2640437
  simp only [CollatzResearch.WordTrace]
  refine ⟨96304649135155174582687565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64203099423436783055125043 96304649135155174582687565)
  ·
    refine ⟨36114243425683190468507837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96304649135155174582687565 36114243425683190468507837)
    ·
      refine ⟨13542841284631196425690439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36114243425683190468507837 13542841284631196425690439)
      ·
        refine ⟨20314261926946794638535659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13542841284631196425690439 20314261926946794638535659)
        ·
          refine ⟨30471392890420191957803489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20314261926946794638535659 30471392890420191957803489)
          ·
            refine ⟨22853544667815143968352617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30471392890420191957803489 22853544667815143968352617)
            ·
              refine ⟨17140158500861357976264463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22853544667815143968352617 17140158500861357976264463)
              ·
                refine ⟨25710237751292036964396695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17140158500861357976264463 25710237751292036964396695)
                ·
                  refine ⟨38565356626938055446595043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25710237751292036964396695 38565356626938055446595043)
                  ·
                    refine ⟨57848034940407083169892565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38565356626938055446595043 57848034940407083169892565)
                    ·
                      refine ⟨1355813318915791011794357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 57848034940407083169892565 1355813318915791011794357)
                      ·
                        rfl

theorem cell23_2640437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_2640437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640437 prefixEnd_2640437 := by exact prefixLift 2640437
  have htrace : WordTrace (prefixWord ++ tailWord_2640437) baseStart_2640437 baseEnd_2640437 := by
    simpa [prefixWord, tailWord_2640437, baseEnd_2640437] using wordTrace_append hprefix tailTrace_2640437
  have hstable : (prefixWord ++ tailWord_2640437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640437).length < 2 ^ (prefixWord ++ tailWord_2640437).sum := by decide
  have hdescent : baseEnd_2640437 < baseStart_2640437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640447 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 4]
def baseStart_2640447 : Nat := 118140960795 + 2640447 * 2 ^ 59
def prefixEnd_2640447 : Nat := 4983230072969 + 3 ^ 40 * 2640447 * 2
def baseEnd_2640447 : Nat := 1355818453722335972669311

theorem tailTrace_2640447 : CollatzResearch.WordTrace tailWord_2640447 prefixEnd_2640447 1355818453722335972669311 := by
  unfold tailWord_2640447
  simp only [CollatzResearch.WordTrace]
  refine ⟨96305013865118946290551595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64203342576745964193701063 96305013865118946290551595)
  ·
    refine ⟨144457520797678419435827393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96305013865118946290551595 144457520797678419435827393)
    ·
      refine ⟨108343140598258814576870545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144457520797678419435827393 108343140598258814576870545)
      ·
        refine ⟨81257355448694110932652909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108343140598258814576870545 81257355448694110932652909)
        ·
          refine ⟨30471508293260291599744841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81257355448694110932652909 30471508293260291599744841)
          ·
            refine ⟨22853631219945218699808631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30471508293260291599744841 22853631219945218699808631)
            ·
              refine ⟨34280446829917828049712947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22853631219945218699808631 34280446829917828049712947)
              ·
                refine ⟨51420670244876742074569421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34280446829917828049712947 51420670244876742074569421)
                ·
                  refine ⟨19282751341828778277963533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51420670244876742074569421 19282751341828778277963533)
                  ·
                    refine ⟨7231031753185791854236325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19282751341828778277963533 7231031753185791854236325)
                    ·
                      refine ⟨1355818453722335972669311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7231031753185791854236325 1355818453722335972669311)
                      ·
                        rfl

theorem cell23_2640447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_2640447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640447 prefixEnd_2640447 := by exact prefixLift 2640447
  have htrace : WordTrace (prefixWord ++ tailWord_2640447) baseStart_2640447 baseEnd_2640447 := by
    simpa [prefixWord, tailWord_2640447, baseEnd_2640447] using wordTrace_append hprefix tailTrace_2640447
  have hstable : (prefixWord ++ tailWord_2640447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640447).length < 2 ^ (prefixWord ++ tailWord_2640447).sum := by decide
  have hdescent : baseEnd_2640447 < baseStart_2640447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640464 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 4, 4, 2]
def baseStart_2640464 : Nat := 118140960795 + 2640464 * 2 ^ 59
def prefixEnd_2640464 : Nat := 4983230072969 + 3 ^ 40 * 2640464 * 2
def baseEnd_2640464 : Nat := 1355827182893462406156733

theorem tailTrace_2640464 : CollatzResearch.WordTrace tailWord_2640464 prefixEnd_2640464 1355827182893462406156733 := by
  unfold tailWord_2640464
  simp only [CollatzResearch.WordTrace]
  refine ⟨48152816953028679096960223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64203755937371572129280297 48152816953028679096960223)
  ·
    refine ⟨72229225429543018645440335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48152816953028679096960223 72229225429543018645440335)
    ·
      refine ⟨108343838144314527968160503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72229225429543018645440335 108343838144314527968160503)
      ·
        refine ⟨162515757216471791952240755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108343838144314527968160503 162515757216471791952240755)
        ·
          refine ⟨243773635824707687928361133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162515757216471791952240755 243773635824707687928361133)
          ·
            refine ⟨91415113434265382973135425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243773635824707687928361133 91415113434265382973135425)
            ·
              refine ⟨68561335075699037229851569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91415113434265382973135425 68561335075699037229851569)
              ·
                refine ⟨51421001306774277922388677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68561335075699037229851569 51421001306774277922388677)
                ·
                  refine ⟨9641437745020177110447877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51421001306774277922388677 9641437745020177110447877)
                  ·
                    refine ⟨1807769577191283208208977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9641437745020177110447877 1807769577191283208208977)
                    ·
                      refine ⟨1355827182893462406156733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1807769577191283208208977 1355827182893462406156733)
                      ·
                        rfl

theorem cell23_2640464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 4, 4, 2].length) (baseStart_2640464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640464 prefixEnd_2640464 := by exact prefixLift 2640464
  have htrace : WordTrace (prefixWord ++ tailWord_2640464) baseStart_2640464 baseEnd_2640464 := by
    simpa [prefixWord, tailWord_2640464, baseEnd_2640464] using wordTrace_append hprefix tailTrace_2640464
  have hstable : (prefixWord ++ tailWord_2640464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640464).length < 2 ^ (prefixWord ++ tailWord_2640464).sum := by decide
  have hdescent : baseEnd_2640464 < baseStart_2640464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640538 : List Nat := [3, 1, 1, 6, 1, 1, 2, 2, 6]
def baseStart_2640538 : Nat := 118140960795 + 2640538 * 2 ^ 59
def prefixEnd_2640538 : Nat := 4983230072969 + 3 ^ 40 * 2640538 * 2
def baseEnd_2640538 : Nat := 150651686717988346292377

theorem tailTrace_2640538 : CollatzResearch.WordTrace tailWord_2640538 prefixEnd_2640538 150651686717988346292377 := by
  unfold tailWord_2640538
  simp only [CollatzResearch.WordTrace]
  refine ⟨24077083226947317208028567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64205555271859512554742845 24077083226947317208028567)
  ·
    refine ⟨36115624840420975812042851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24077083226947317208028567 36115624840420975812042851)
    ·
      refine ⟨54173437260631463718064277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36115624840420975812042851 54173437260631463718064277)
      ·
        refine ⟨2539379871592099861784263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54173437260631463718064277 2539379871592099861784263)
        ·
          refine ⟨3809069807388149792676395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2539379871592099861784263 3809069807388149792676395)
          ·
            refine ⟨5713604711082224689014593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3809069807388149792676395 5713604711082224689014593)
            ·
              refine ⟨4285203533311668516760945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5713604711082224689014593 4285203533311668516760945)
              ·
                refine ⟨3213902649983751387570709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4285203533311668516760945 3213902649983751387570709)
                ·
                  refine ⟨150651686717988346292377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3213902649983751387570709 150651686717988346292377)
                  ·
                    rfl

theorem cell23_2640538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 6].length) (baseStart_2640538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640538 prefixEnd_2640538 := by exact prefixLift 2640538
  have htrace : WordTrace (prefixWord ++ tailWord_2640538) baseStart_2640538 baseEnd_2640538 := by
    simpa [prefixWord, tailWord_2640538, baseEnd_2640538] using wordTrace_append hprefix tailTrace_2640538
  have hstable : (prefixWord ++ tailWord_2640538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640538).length < 2 ^ (prefixWord ++ tailWord_2640538).sum := by decide
  have hdescent : baseEnd_2640538 < baseStart_2640538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640588 : List Nat := [2, 2, 1, 5, 1, 2, 1, 3, 1, 1, 4]
def baseStart_2640588 : Nat := 118140960795 + 2640588 * 2 ^ 59
def prefixEnd_2640588 : Nat := 4983230072969 + 3 ^ 40 * 2640588 * 2
def baseEnd_2640588 : Nat := 1355890854494619921006163

theorem tailTrace_2640588 : CollatzResearch.WordTrace tailWord_2640588 prefixEnd_2640588 1355890854494619921006163 := by
  unfold tailWord_2640588
  simp only [CollatzResearch.WordTrace]
  refine ⟨48155078278804063685717209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64206771038405418247622945 48155078278804063685717209)
  ·
    refine ⟨36116308709103047764287907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48155078278804063685717209 36116308709103047764287907)
    ·
      refine ⟨54174463063654571646431861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36116308709103047764287907 54174463063654571646431861)
      ·
        refine ⟨5078855912217616091852987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54174463063654571646431861 5078855912217616091852987)
        ·
          refine ⟨7618283868326424137779481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5078855912217616091852987 7618283868326424137779481)
          ·
            refine ⟨5713712901244818103334611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7618283868326424137779481 5713712901244818103334611)
            ·
              refine ⟨8570569351867227155001917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5713712901244818103334611 8570569351867227155001917)
              ·
                refine ⟨3213963506950210183125719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8570569351867227155001917 3213963506950210183125719)
                ·
                  refine ⟨4820945260425315274688579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3213963506950210183125719 4820945260425315274688579)
                  ·
                    refine ⟨7231417890637972912032869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4820945260425315274688579 7231417890637972912032869)
                    ·
                      refine ⟨1355890854494619921006163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7231417890637972912032869 1355890854494619921006163)
                      ·
                        rfl

theorem cell23_2640588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_2640588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640588 prefixEnd_2640588 := by exact prefixLift 2640588
  have htrace : WordTrace (prefixWord ++ tailWord_2640588) baseStart_2640588 baseEnd_2640588 := by
    simpa [prefixWord, tailWord_2640588, baseEnd_2640588] using wordTrace_append hprefix tailTrace_2640588
  have hstable : (prefixWord ++ tailWord_2640588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640588).length < 2 ^ (prefixWord ++ tailWord_2640588).sum := by decide
  have hdescent : baseEnd_2640588 < baseStart_2640588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640634 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5]
def baseStart_2640634 : Nat := 118140960795 + 2640634 * 2 ^ 59
def prefixEnd_2640634 : Nat := 4983230072969 + 3 ^ 40 * 2640634 * 2
def baseEnd_2640634 : Nat := 1355914474604726741030951

theorem tailTrace_2640634 : CollatzResearch.WordTrace tailWord_2640634 prefixEnd_2640634 1355914474604726741030951 := by
  unfold tailWord_2640634
  simp only [CollatzResearch.WordTrace]
  refine ⟨24077958578860369306902239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64207889543627651485072637 24077958578860369306902239)
  ·
    refine ⟨36116937868290553960353359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24077958578860369306902239 36116937868290553960353359)
    ·
      refine ⟨54175406802435830940530039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36116937868290553960353359 54175406802435830940530039)
      ·
        refine ⟨81263110203653746410795059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54175406802435830940530039 81263110203653746410795059)
        ·
          refine ⟨121894665305480619616192589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81263110203653746410795059 121894665305480619616192589)
          ·
            refine ⟨45710499489555232356072221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121894665305480619616192589 45710499489555232356072221)
            ·
              refine ⟨17141437308583212133527083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45710499489555232356072221 17141437308583212133527083)
              ·
                refine ⟨25712155962874818200290625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17141437308583212133527083 25712155962874818200290625)
                ·
                  refine ⟨19284116972156113650217969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25712155962874818200290625 19284116972156113650217969)
                  ·
                    refine ⟨14463087729117085237663477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19284116972156113650217969 14463087729117085237663477)
                    ·
                      refine ⟨1355914474604726741030951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14463087729117085237663477 1355914474604726741030951)
                      ·
                        rfl

theorem cell23_2640634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_2640634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640634 prefixEnd_2640634 := by exact prefixLift 2640634
  have htrace : WordTrace (prefixWord ++ tailWord_2640634) baseStart_2640634 baseEnd_2640634 := by
    simpa [prefixWord, tailWord_2640634, baseEnd_2640634] using wordTrace_append hprefix tailTrace_2640634
  have hstable : (prefixWord ++ tailWord_2640634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640634).length < 2 ^ (prefixWord ++ tailWord_2640634).sum := by decide
  have hdescent : baseEnd_2640634 < baseStart_2640634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640664 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 3, 3, 5]
def baseStart_2640664 : Nat := 118140960795 + 2640664 * 2 ^ 59
def prefixEnd_2640664 : Nat := 4983230072969 + 3 ^ 40 * 2640664 * 2
def baseEnd_2640664 : Nat := 1355929879024361623655813

theorem tailTrace_2640664 : CollatzResearch.WordTrace tailWord_2640664 prefixEnd_2640664 1355929879024361623655813 := by
  unfold tailWord_2640664
  simp only [CollatzResearch.WordTrace]
  refine ⟨48156464252666396175600523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64208619003555194900800697 48156464252666396175600523)
  ·
    refine ⟨72234696378999594263400785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48156464252666396175600523 72234696378999594263400785)
    ·
      refine ⟨54176022284249695697550589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72234696378999594263400785 54176022284249695697550589)
      ·
        refine ⟨20316008356593635886581471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54176022284249695697550589 20316008356593635886581471)
        ·
          refine ⟨30474012534890453829872207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20316008356593635886581471 30474012534890453829872207)
          ·
            refine ⟨45711018802335680744808311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30474012534890453829872207 45711018802335680744808311)
            ·
              refine ⟨68566528203503521117212467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45711018802335680744808311 68566528203503521117212467)
              ·
                refine ⟨102849792305255281675818701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68566528203503521117212467 102849792305255281675818701)
                ·
                  refine ⟨38568672114470730628432013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102849792305255281675818701 38568672114470730628432013)
                  ·
                    refine ⟨14463252042926523985662005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38568672114470730628432013 14463252042926523985662005)
                    ·
                      refine ⟨1355929879024361623655813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14463252042926523985662005 1355929879024361623655813)
                      ·
                        rfl

theorem cell23_2640664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_2640664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640664 prefixEnd_2640664 := by exact prefixLift 2640664
  have htrace : WordTrace (prefixWord ++ tailWord_2640664) baseStart_2640664 baseEnd_2640664 := by
    simpa [prefixWord, tailWord_2640664, baseEnd_2640664] using wordTrace_append hprefix tailTrace_2640664
  have hstable : (prefixWord ++ tailWord_2640664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640664).length < 2 ^ (prefixWord ++ tailWord_2640664).sum := by decide
  have hdescent : baseEnd_2640664 < baseStart_2640664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640672 : List Nat := [2, 1, 1, 5, 1, 4, 2, 1, 2, 1, 3]
def baseStart_2640672 : Nat := 118140960795 + 2640672 * 2 ^ 59
def prefixEnd_2640672 : Nat := 4983230072969 + 3 ^ 40 * 2640672 * 2
def baseEnd_2640672 : Nat := 1355933986869597592355777

theorem tailTrace_2640672 : CollatzResearch.WordTrace tailWord_2640672 prefixEnd_2640672 1355933986869597592355777 := by
  unfold tailWord_2640672
  simp only [CollatzResearch.WordTrace]
  refine ⟨48156610144651904858746135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64208813526202539811661513 48156610144651904858746135)
  ·
    refine ⟨72234915216977857288119203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48156610144651904858746135 72234915216977857288119203)
    ·
      refine ⟨108352372825466785932178805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72234915216977857288119203 108352372825466785932178805)
      ·
        refine ⟨10158034952387511181141763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108352372825466785932178805 10158034952387511181141763)
        ·
          refine ⟨15237052428581266771712645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10158034952387511181141763 15237052428581266771712645)
          ·
            refine ⟨2856947330358987519696121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15237052428581266771712645 2856947330358987519696121)
            ·
              refine ⟨2142710497769240639772091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2856947330358987519696121 2142710497769240639772091)
              ·
                refine ⟨3214065746653860959658137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2142710497769240639772091 3214065746653860959658137)
                ·
                  refine ⟨2410549309990395719743603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3214065746653860959658137 2410549309990395719743603)
                  ·
                    refine ⟨3615823964985593579615405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2410549309990395719743603 3615823964985593579615405)
                    ·
                      refine ⟨1355933986869597592355777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3615823964985593579615405 1355933986869597592355777)
                      ·
                        rfl

theorem cell23_2640672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_2640672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640672 prefixEnd_2640672 := by exact prefixLift 2640672
  have htrace : WordTrace (prefixWord ++ tailWord_2640672) baseStart_2640672 baseEnd_2640672 := by
    simpa [prefixWord, tailWord_2640672, baseEnd_2640672] using wordTrace_append hprefix tailTrace_2640672
  have hstable : (prefixWord ++ tailWord_2640672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640672).length < 2 ^ (prefixWord ++ tailWord_2640672).sum := by decide
  have hdescent : baseEnd_2640672 < baseStart_2640672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640682 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 3, 3, 2]
def baseStart_2640682 : Nat := 118140960795 + 2640682 * 2 ^ 59
def prefixEnd_2640682 : Nat := 4983230072969 + 3 ^ 40 * 2640682 * 2
def baseEnd_2640682 : Nat := 1355939121676142553230731

theorem tailTrace_2640682 : CollatzResearch.WordTrace tailWord_2640682 prefixEnd_2640682 1355939121676142553230731 := by
  unfold tailWord_2640682
  simp only [CollatzResearch.WordTrace]
  refine ⟨24078396254816895356339075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64209056679511720950237533 24078396254816895356339075)
  ·
    refine ⟨36117594382225343034508613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24078396254816895356339075 36117594382225343034508613)
    ·
      refine ⟨6772048946667251818970365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36117594382225343034508613 6772048946667251818970365)
      ·
        refine ⟨2539518355000219432113887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6772048946667251818970365 2539518355000219432113887)
        ·
          refine ⟨3809277532500329148170831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2539518355000219432113887 3809277532500329148170831)
          ·
            refine ⟨5713916298750493722256247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3809277532500329148170831 5713916298750493722256247)
            ·
              refine ⟨8570874448125740583384371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5713916298750493722256247 8570874448125740583384371)
              ·
                refine ⟨12856311672188610875076557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8570874448125740583384371 12856311672188610875076557)
                ·
                  refine ⟨4821116877070729078153709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12856311672188610875076557 4821116877070729078153709)
                  ·
                    refine ⟨1807918828901523404307641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4821116877070729078153709 1807918828901523404307641)
                    ·
                      refine ⟨1355939121676142553230731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1807918828901523404307641 1355939121676142553230731)
                      ·
                        rfl

theorem cell23_2640682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_2640682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640682 prefixEnd_2640682 := by exact prefixLift 2640682
  have htrace : WordTrace (prefixWord ++ tailWord_2640682) baseStart_2640682 baseEnd_2640682 := by
    simpa [prefixWord, tailWord_2640682, baseEnd_2640682] using wordTrace_append hprefix tailTrace_2640682
  have hstable : (prefixWord ++ tailWord_2640682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640682).length < 2 ^ (prefixWord ++ tailWord_2640682).sum := by decide
  have hdescent : baseEnd_2640682 < baseStart_2640682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640684 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 9]
def baseStart_2640684 : Nat := 118140960795 + 2640684 * 2 ^ 59
def prefixEnd_2640684 : Nat := 4983230072969 + 3 ^ 40 * 2640684 * 2
def baseEnd_2640684 : Nat := 150660016515272393933969

theorem tailTrace_2640684 : CollatzResearch.WordTrace tailWord_2640684 prefixEnd_2640684 150660016515272393933969 := by
  unfold tailWord_2640684
  simp only [CollatzResearch.WordTrace]
  refine ⟨48156828982630167883464553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64209105310173557177952737 48156828982630167883464553)
  ·
    refine ⟨36117621736972625912598415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48156828982630167883464553 36117621736972625912598415)
    ·
      refine ⟨54176432605458938868897623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36117621736972625912598415 54176432605458938868897623)
      ·
        refine ⟨81264648908188408303346435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54176432605458938868897623 81264648908188408303346435)
        ·
          refine ⟨121896973362282612455019653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81264648908188408303346435 121896973362282612455019653)
          ·
            refine ⟨22855682505427989835316185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121896973362282612455019653 22855682505427989835316185)
            ·
              refine ⟨17141761879070992376487139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22855682505427989835316185 17141761879070992376487139)
              ·
                refine ⟨25712642818606488564730709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17141761879070992376487139 25712642818606488564730709)
                ·
                  refine ⟨150660016515272393933969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25712642818606488564730709 150660016515272393933969)
                  ·
                    rfl

theorem cell23_2640684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 9].length) (baseStart_2640684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640684 prefixEnd_2640684 := by exact prefixLift 2640684
  have htrace : WordTrace (prefixWord ++ tailWord_2640684) baseStart_2640684 baseEnd_2640684 := by
    simpa [prefixWord, tailWord_2640684, baseEnd_2640684] using wordTrace_append hprefix tailTrace_2640684
  have hstable : (prefixWord ++ tailWord_2640684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640684).length < 2 ^ (prefixWord ++ tailWord_2640684).sum := by decide
  have hdescent : baseEnd_2640684 < baseStart_2640684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640711 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 3]
def baseStart_2640711 : Nat := 118140960795 + 2640711 * 2 ^ 59
def prefixEnd_2640711 : Nat := 4983230072969 + 3 ^ 40 * 2640711 * 2
def baseEnd_2640711 : Nat := 1355954012615122939768097

theorem tailTrace_2640711 : CollatzResearch.WordTrace tailWord_2640711 prefixEnd_2640711 1355954012615122939768097 := by
  unfold tailWord_2640711
  simp only [CollatzResearch.WordTrace]
  refine ⟨96314642736162519378161987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64209761824108346252107991 96314642736162519378161987)
  ·
    refine ⟨144471964104243779067242981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96314642736162519378161987 144471964104243779067242981)
    ·
      refine ⟨27088493269545708575108059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144471964104243779067242981 27088493269545708575108059)
      ·
        refine ⟨40632739904318562862662089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27088493269545708575108059 40632739904318562862662089)
        ·
          refine ⟨30474554928238922146996567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40632739904318562862662089 30474554928238922146996567)
          ·
            refine ⟨45711832392358383220494851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30474554928238922146996567 45711832392358383220494851)
            ·
              refine ⟨68567748588537574830742277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45711832392358383220494851 68567748588537574830742277)
              ·
                refine ⟨12856452860350795280764177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68567748588537574830742277 12856452860350795280764177)
                ·
                  refine ⟨9642339645263096460573133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12856452860350795280764177 9642339645263096460573133)
                  ·
                    refine ⟨3615877366973661172714925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9642339645263096460573133 3615877366973661172714925)
                    ·
                      refine ⟨1355954012615122939768097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3615877366973661172714925 1355954012615122939768097)
                      ·
                        rfl

theorem cell23_2640711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_2640711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640711 prefixEnd_2640711 := by exact prefixLift 2640711
  have htrace : WordTrace (prefixWord ++ tailWord_2640711) baseStart_2640711 baseEnd_2640711 := by
    simpa [prefixWord, tailWord_2640711, baseEnd_2640711] using wordTrace_append hprefix tailTrace_2640711
  have hstable : (prefixWord ++ tailWord_2640711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640711).length < 2 ^ (prefixWord ++ tailWord_2640711).sum := by decide
  have hdescent : baseEnd_2640711 < baseStart_2640711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640788 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_2640788 : Nat := 118140960795 + 2640788 * 2 ^ 59
def prefixEnd_2640788 : Nat := 4983230072969 + 3 ^ 40 * 2640788 * 2
def baseEnd_2640788 : Nat := 1355993550625519138505243

theorem tailTrace_2640788 : CollatzResearch.WordTrace tailWord_2640788 prefixEnd_2640788 1355993550625519138505243 := by
  unfold tailWord_2640788
  simp only [CollatzResearch.WordTrace]
  refine ⟨48158725578441780764357509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64211634104589041019143345 48158725578441780764357509)
  ·
    refine ⟨9029761045957833893317033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48158725578441780764357509 9029761045957833893317033)
    ·
      refine ⟨6772320784468375419987775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9029761045957833893317033 6772320784468375419987775)
      ·
        refine ⟨10158481176702563129981663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6772320784468375419987775 10158481176702563129981663)
        ·
          refine ⟨15237721765053844694972495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10158481176702563129981663 15237721765053844694972495)
          ·
            refine ⟨22856582647580767042458743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15237721765053844694972495 22856582647580767042458743)
            ·
              refine ⟨34284873971371150563688115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22856582647580767042458743 34284873971371150563688115)
              ·
                refine ⟨51427310957056725845532173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34284873971371150563688115 51427310957056725845532173)
                ·
                  refine ⟨19285241608896272192074565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51427310957056725845532173 19285241608896272192074565)
                  ·
                    refine ⟨3615982801668051036013981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19285241608896272192074565 3615982801668051036013981)
                    ·
                      refine ⟨1355993550625519138505243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3615982801668051036013981 1355993550625519138505243)
                      ·
                        rfl

theorem cell23_2640788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_2640788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640788 prefixEnd_2640788 := by exact prefixLift 2640788
  have htrace : WordTrace (prefixWord ++ tailWord_2640788) baseStart_2640788 baseEnd_2640788 := by
    simpa [prefixWord, tailWord_2640788, baseEnd_2640788] using wordTrace_append hprefix tailTrace_2640788
  have hstable : (prefixWord ++ tailWord_2640788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640788).length < 2 ^ (prefixWord ++ tailWord_2640788).sum := by decide
  have hdescent : baseEnd_2640788 < baseStart_2640788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640829 : List Nat := [1, 4, 1, 2, 4, 1, 3, 2, 1, 4]
def baseStart_2640829 : Nat := 118140960795 + 2640829 * 2 ^ 59
def prefixEnd_2640829 : Nat := 4983230072969 + 3 ^ 40 * 2640829 * 2
def baseEnd_2640829 : Nat := 452004867777451159364185

theorem tailTrace_2640829 : CollatzResearch.WordTrace tailWord_2640829 prefixEnd_2640829 452004867777451159364185 := by
  unfold tailWord_2640829
  simp only [CollatzResearch.WordTrace]
  refine ⟨96318946549735025530957541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64212631033156683687305027 96318946549735025530957541)
  ·
    refine ⟨18059802478075317287054539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96318946549735025530957541 18059802478075317287054539)
    ·
      refine ⟨27089703717112975930581809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18059802478075317287054539 27089703717112975930581809)
      ·
        refine ⟨20317277787834731947936357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27089703717112975930581809 20317277787834731947936357)
        ·
          refine ⟨3809489585219012240238067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20317277787834731947936357 3809489585219012240238067)
          ·
            refine ⟨5714234377828518360357101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3809489585219012240238067 5714234377828518360357101)
            ·
              refine ⟨2142837891685694385133913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5714234377828518360357101 2142837891685694385133913)
              ·
                refine ⟨1607128418764270788850435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2142837891685694385133913 1607128418764270788850435)
                ·
                  refine ⟨2410692628146406183275653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1607128418764270788850435 2410692628146406183275653)
                  ·
                    refine ⟨452004867777451159364185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2410692628146406183275653 452004867777451159364185)
                    ·
                      rfl

theorem cell23_2640829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_2640829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640829 prefixEnd_2640829 := by exact prefixLift 2640829
  have htrace : WordTrace (prefixWord ++ tailWord_2640829) baseStart_2640829 baseEnd_2640829 := by
    simpa [prefixWord, tailWord_2640829, baseEnd_2640829] using wordTrace_append hprefix tailTrace_2640829
  have hstable : (prefixWord ++ tailWord_2640829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640829).length < 2 ^ (prefixWord ++ tailWord_2640829).sum := by decide
  have hdescent : baseEnd_2640829 < baseStart_2640829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640868 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 4, 4]
def baseStart_2640868 : Nat := 118140960795 + 2640868 * 2 ^ 59
def prefixEnd_2640868 : Nat := 4983230072969 + 3 ^ 40 * 2640868 * 2
def baseEnd_2640868 : Nat := 452011543025959608501625

theorem tailTrace_2640868 : CollatzResearch.WordTrace tailWord_2640868 prefixEnd_2640868 452011543025959608501625 := by
  unfold tailWord_2640868
  simp only [CollatzResearch.WordTrace]
  refine ⟨48160184498296867595813629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64213579331062490127751505 48160184498296867595813629)
  ·
    refine ⟨18060069186861325348430111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48160184498296867595813629 18060069186861325348430111)
    ·
      refine ⟨27090103780291988022645167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18060069186861325348430111 27090103780291988022645167)
      ·
        refine ⟨40635155670437982033967751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27090103780291988022645167 40635155670437982033967751)
        ·
          refine ⟨60952733505656973050951627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40635155670437982033967751 60952733505656973050951627)
          ·
            refine ⟨91429100258485459576427441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60952733505656973050951627 91429100258485459576427441)
            ·
              refine ⟨68571825193864094682320581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91429100258485459576427441 68571825193864094682320581)
              ·
                refine ⟨12857217223849517752935109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68571825193864094682320581 12857217223849517752935109)
                ·
                  refine ⟨2410728229471784578675333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12857217223849517752935109 2410728229471784578675333)
                  ·
                    refine ⟨452011543025959608501625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2410728229471784578675333 452011543025959608501625)
                    ·
                      rfl

theorem cell23_2640868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_2640868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640868 prefixEnd_2640868 := by exact prefixLift 2640868
  have htrace : WordTrace (prefixWord ++ tailWord_2640868) baseStart_2640868 baseEnd_2640868 := by
    simpa [prefixWord, tailWord_2640868, baseEnd_2640868] using wordTrace_append hprefix tailTrace_2640868
  have hstable : (prefixWord ++ tailWord_2640868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640868).length < 2 ^ (prefixWord ++ tailWord_2640868).sum := by decide
  have hdescent : baseEnd_2640868 < baseStart_2640868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640881 : List Nat := [1, 2, 2, 2, 4, 12]
def baseStart_2640881 : Nat := 118140960795 + 2640881 * 2 ^ 59
def prefixEnd_2640881 : Nat := 4983230072969 + 3 ^ 40 * 2640881 * 2
def baseEnd_2640881 : Nat := 5580416890232046397705

theorem tailTrace_2640881 : CollatzResearch.WordTrace tailWord_2640881 prefixEnd_2640881 5580416890232046397705 := by
  unfold tailWord_2640881
  simp only [CollatzResearch.WordTrace]
  refine ⟨96320843145546638411850497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64213895430364425607900331 96320843145546638411850497)
  ·
    refine ⟨72240632359159978808887873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96320843145546638411850497 72240632359159978808887873)
    ·
      refine ⟨54180474269369984106665905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72240632359159978808887873 54180474269369984106665905)
      ·
        refine ⟨40635355702027488079999429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54180474269369984106665905 40635355702027488079999429)
        ·
          refine ⟨7619129194130154014999893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40635355702027488079999429 7619129194130154014999893)
          ·
            refine ⟨5580416890232046397705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 7619129194130154014999893 5580416890232046397705)
            ·
              rfl

theorem cell23_2640881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 12].length) (baseStart_2640881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640881 prefixEnd_2640881 := by exact prefixLift 2640881
  have htrace : WordTrace (prefixWord ++ tailWord_2640881) baseStart_2640881 baseEnd_2640881 := by
    simpa [prefixWord, tailWord_2640881, baseEnd_2640881] using wordTrace_append hprefix tailTrace_2640881
  have hstable : (prefixWord ++ tailWord_2640881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640881).length < 2 ^ (prefixWord ++ tailWord_2640881).sum := by decide
  have hdescent : baseEnd_2640881 < baseStart_2640881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640886 : List Nat := [5, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3]
def baseStart_2640886 : Nat := 118140960795 + 2640886 * 2 ^ 59
def prefixEnd_2640886 : Nat := 4983230072969 + 3 ^ 40 * 2640886 * 2
def baseEnd_2640886 : Nat := 1356043871729659755079793

theorem tailTrace_2640886 : CollatzResearch.WordTrace tailWord_2640886 prefixEnd_2640886 1356043871729659755079793 := by
  unfold tailWord_2640886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6020064094408032766611407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64214017007019016177188341 6020064094408032766611407)
  ·
    refine ⟨9030096141612049149917111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6020064094408032766611407 9030096141612049149917111)
    ·
      refine ⟨13545144212418073724875667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9030096141612049149917111 13545144212418073724875667)
      ·
        refine ⟨20317716318627110587313501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13545144212418073724875667 20317716318627110587313501)
        ·
          refine ⟨7619143619485166470242563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20317716318627110587313501 7619143619485166470242563)
          ·
            refine ⟨11428715429227749705363845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7619143619485166470242563 11428715429227749705363845)
            ·
              refine ⟨2142884142980203069755721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11428715429227749705363845 2142884142980203069755721)
              ·
                refine ⟨1607163107235152302316791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2142884142980203069755721 1607163107235152302316791)
                ·
                  refine ⟨2410744660852728453475187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1607163107235152302316791 2410744660852728453475187)
                  ·
                    refine ⟨3616116991279092680212781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2410744660852728453475187 3616116991279092680212781)
                    ·
                      refine ⟨1356043871729659755079793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3616116991279092680212781 1356043871729659755079793)
                      ·
                        rfl

theorem cell23_2640886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_2640886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640886 prefixEnd_2640886 := by exact prefixLift 2640886
  have htrace : WordTrace (prefixWord ++ tailWord_2640886) baseStart_2640886 baseEnd_2640886 := by
    simpa [prefixWord, tailWord_2640886, baseEnd_2640886] using wordTrace_append hprefix tailTrace_2640886
  have hstable : (prefixWord ++ tailWord_2640886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640886).length < 2 ^ (prefixWord ++ tailWord_2640886).sum := by decide
  have hdescent : baseEnd_2640886 < baseStart_2640886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640929 : List Nat := [1, 2, 3, 2, 3, 3, 2, 1, 1, 2, 3]
def baseStart_2640929 : Nat := 118140960795 + 2640929 * 2 ^ 59
def prefixEnd_2640929 : Nat := 4983230072969 + 3 ^ 40 * 2640929 * 2
def baseEnd_2640929 : Nat := 1356065951397803086842095

theorem tailTrace_2640929 : CollatzResearch.WordTrace tailWord_2640929 prefixEnd_2640929 1356065951397803086842095 := by
  unfold tailWord_2640929
  simp only [CollatzResearch.WordTrace]
  refine ⟨96322593849372742609597841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64215062566248495073065227 96322593849372742609597841)
  ·
    refine ⟨72241945387029556957198381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96322593849372742609597841 72241945387029556957198381)
    ·
      refine ⟨27090729520136083858949393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72241945387029556957198381 27090729520136083858949393)
      ·
        refine ⟨20318047140102062894212045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27090729520136083858949393 20318047140102062894212045)
        ·
          refine ⟨7619267677538273585329517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20318047140102062894212045 7619267677538273585329517)
          ·
            refine ⟨2857225379076852594498569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7619267677538273585329517 2857225379076852594498569)
            ·
              refine ⟨2142919034307639445873927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2857225379076852594498569 2142919034307639445873927)
              ·
                refine ⟨3214378551461459168810891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2142919034307639445873927 3214378551461459168810891)
                ·
                  refine ⟨4821567827192188753216337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3214378551461459168810891 4821567827192188753216337)
                  ·
                    refine ⟨3616175870394141564912253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4821567827192188753216337 3616175870394141564912253)
                    ·
                      refine ⟨1356065951397803086842095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3616175870394141564912253 1356065951397803086842095)
                      ·
                        rfl

theorem cell23_2640929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_2640929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640929 prefixEnd_2640929 := by exact prefixLift 2640929
  have htrace : WordTrace (prefixWord ++ tailWord_2640929) baseStart_2640929 baseEnd_2640929 := by
    simpa [prefixWord, tailWord_2640929, baseEnd_2640929] using wordTrace_append hprefix tailTrace_2640929
  have hstable : (prefixWord ++ tailWord_2640929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640929).length < 2 ^ (prefixWord ++ tailWord_2640929).sum := by decide
  have hdescent : baseEnd_2640929 < baseStart_2640929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640942 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_2640942 : Nat := 118140960795 + 2640942 * 2 ^ 59
def prefixEnd_2640942 : Nat := 4983230072969 + 3 ^ 40 * 2640942 * 2
def baseEnd_2640942 : Nat := 1356072626646311535979535

theorem tailTrace_2640942 : CollatzResearch.WordTrace tailWord_2640942 prefixEnd_2640942 1356072626646311535979535 := by
  unfold tailWord_2640942
  simp only [CollatzResearch.WordTrace]
  refine ⟨12040383499790705728727635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64215378665550430553214053 12040383499790705728727635)
  ·
    refine ⟨18060575249686058593091453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12040383499790705728727635 18060575249686058593091453)
    ·
      refine ⟨6772715718632271972409295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18060575249686058593091453 6772715718632271972409295)
      ·
        refine ⟨10159073577948407958613943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6772715718632271972409295 10159073577948407958613943)
        ·
          refine ⟨15238610366922611937920915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10159073577948407958613943 15238610366922611937920915)
          ·
            refine ⟨22857915550383917906881373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15238610366922611937920915 22857915550383917906881373)
            ·
              refine ⟨8571718331393969215080515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22857915550383917906881373 8571718331393969215080515)
              ·
                refine ⟨12857577497090953822620773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8571718331393969215080515 12857577497090953822620773)
                ·
                  refine ⟨2410795780704553841741395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12857577497090953822620773 2410795780704553841741395)
                  ·
                    refine ⟨3616193671056830762612093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2410795780704553841741395 3616193671056830762612093)
                    ·
                      refine ⟨1356072626646311535979535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3616193671056830762612093 1356072626646311535979535)
                      ·
                        rfl

theorem cell23_2640942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_2640942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640942 prefixEnd_2640942 := by exact prefixLift 2640942
  have htrace : WordTrace (prefixWord ++ tailWord_2640942) baseStart_2640942 baseEnd_2640942 := by
    simpa [prefixWord, tailWord_2640942, baseEnd_2640942] using wordTrace_append hprefix tailTrace_2640942
  have hstable : (prefixWord ++ tailWord_2640942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640942).length < 2 ^ (prefixWord ++ tailWord_2640942).sum := by decide
  have hdescent : baseEnd_2640942 < baseStart_2640942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2640968 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 2, 1, 5]
def baseStart_2640968 : Nat := 118140960795 + 2640968 * 2 ^ 59
def prefixEnd_2640968 : Nat := 4983230072969 + 3 ^ 40 * 2640968 * 2
def baseEnd_2640968 : Nat := 1356085977143328434254415

theorem tailTrace_2640968 : CollatzResearch.WordTrace tailWord_2640968 prefixEnd_2640968 1356085977143328434254415 := by
  unfold tailWord_2640968
  simp only [CollatzResearch.WordTrace]
  refine ⟨48162008148115726135133779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64216010864154301513511705 48162008148115726135133779)
  ·
    refine ⟨72243012222173589202700669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48162008148115726135133779 72243012222173589202700669)
    ·
      refine ⟨27091129583315095951012751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72243012222173589202700669 27091129583315095951012751)
      ·
        refine ⟨40636694374972643926519127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27091129583315095951012751 40636694374972643926519127)
        ·
          refine ⟨60955041562458965889778691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40636694374972643926519127 60955041562458965889778691)
          ·
            refine ⟨91432562343688448834668037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60955041562458965889778691 91432562343688448834668037)
            ·
              refine ⟨17143605439441584156500257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91432562343688448834668037 17143605439441584156500257)
              ·
                refine ⟨12857704079581188117375193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17143605439441584156500257 12857704079581188117375193)
                ·
                  refine ⟨9643278059685891088031395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12857704079581188117375193 9643278059685891088031395)
                  ·
                    refine ⟨14464917089528836632047093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9643278059685891088031395 14464917089528836632047093)
                    ·
                      refine ⟨1356085977143328434254415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14464917089528836632047093 1356085977143328434254415)
                      ·
                        rfl

theorem cell23_2640968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_2640968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2640968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2640968 prefixEnd_2640968 := by exact prefixLift 2640968
  have htrace : WordTrace (prefixWord ++ tailWord_2640968) baseStart_2640968 baseEnd_2640968 := by
    simpa [prefixWord, tailWord_2640968, baseEnd_2640968] using wordTrace_append hprefix tailTrace_2640968
  have hstable : (prefixWord ++ tailWord_2640968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2640968).length < 2 ^ (prefixWord ++ tailWord_2640968).sum := by decide
  have hdescent : baseEnd_2640968 < baseStart_2640968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2640968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641005 : List Nat := [1, 5, 1, 1, 2, 2, 3, 1, 7]
def baseStart_2641005 : Nat := 118140960795 + 2641005 * 2 ^ 59
def prefixEnd_2641005 : Nat := 4983230072969 + 3 ^ 40 * 2641005 * 2
def baseEnd_2641005 : Nat := 150678330658616087721305

theorem tailTrace_2641005 : CollatzResearch.WordTrace tailWord_2641005 prefixEnd_2641005 150678330658616087721305 := by
  unfold tailWord_2641005
  simp only [CollatzResearch.WordTrace]
  refine ⟨96325365797097407589364469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64216910531398271726242979 96325365797097407589364469)
  ·
    refine ⟨9030503043477881961502919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96325365797097407589364469 9030503043477881961502919)
    ·
      refine ⟨13545754565216822942254379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9030503043477881961502919 13545754565216822942254379)
      ·
        refine ⟨20318631847825234413381569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13545754565216822942254379 20318631847825234413381569)
        ·
          refine ⟨15238973885868925810036177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20318631847825234413381569 15238973885868925810036177)
          ·
            refine ⟨11429230414401694357527133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15238973885868925810036177 11429230414401694357527133)
            ·
              refine ⟨4285961405400635384072675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11429230414401694357527133 4285961405400635384072675)
              ·
                refine ⟨6428942108100953076109013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4285961405400635384072675 6428942108100953076109013)
                ·
                  refine ⟨150678330658616087721305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6428942108100953076109013 150678330658616087721305)
                  ·
                    rfl

theorem cell23_2641005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_2641005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641005 prefixEnd_2641005 := by exact prefixLift 2641005
  have htrace : WordTrace (prefixWord ++ tailWord_2641005) baseStart_2641005 baseEnd_2641005 := by
    simpa [prefixWord, tailWord_2641005, baseEnd_2641005] using wordTrace_append hprefix tailTrace_2641005
  have hstable : (prefixWord ++ tailWord_2641005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641005).length < 2 ^ (prefixWord ++ tailWord_2641005).sum := by decide
  have hdescent : baseEnd_2641005 < baseStart_2641005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641068 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 6]
def baseStart_2641068 : Nat := 118140960795 + 2641068 * 2 ^ 59
def prefixEnd_2641068 : Nat := 4983230072969 + 3 ^ 40 * 2641068 * 2
def baseEnd_2641068 : Nat := 1356137325208778043003955

theorem tailTrace_2641068 : CollatzResearch.WordTrace tailWord_2641068 prefixEnd_2641068 1356137325208778043003955 := by
  unfold tailWord_2641068
  simp only [CollatzResearch.WordTrace]
  refine ⟨48163831797934584674453929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64218442397246112899271905 48163831797934584674453929)
  ·
    refine ⟨36122873848450938505840447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48163831797934584674453929 36122873848450938505840447)
    ·
      refine ⟨54184310772676407758760671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36122873848450938505840447 54184310772676407758760671)
      ·
        refine ⟨81276466159014611638141007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54184310772676407758760671 81276466159014611638141007)
        ·
          refine ⟨121914699238521917457211511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81276466159014611638141007 121914699238521917457211511)
          ·
            refine ⟨182872048857782876185817267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121914699238521917457211511 182872048857782876185817267)
            ·
              refine ⟨274308073286674314278725901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182872048857782876185817267 274308073286674314278725901)
              ·
                refine ⟨102865527482502867854522213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 274308073286674314278725901 102865527482502867854522213)
                ·
                  refine ⟨19287286402969287722722915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102865527482502867854522213 19287286402969287722722915)
                  ·
                    refine ⟨28930929604453931584084373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19287286402969287722722915 28930929604453931584084373)
                    ·
                      refine ⟨1356137325208778043003955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28930929604453931584084373 1356137325208778043003955)
                      ·
                        rfl

theorem cell23_2641068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_2641068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641068 prefixEnd_2641068 := by exact prefixLift 2641068
  have htrace : WordTrace (prefixWord ++ tailWord_2641068) baseStart_2641068 baseEnd_2641068 := by
    simpa [prefixWord, tailWord_2641068, baseEnd_2641068] using wordTrace_append hprefix tailTrace_2641068
  have hstable : (prefixWord ++ tailWord_2641068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641068).length < 2 ^ (prefixWord ++ tailWord_2641068).sum := by decide
  have hdescent : baseEnd_2641068 < baseStart_2641068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641075 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 3]
def baseStart_2641075 : Nat := 118140960795 + 2641075 * 2 ^ 59
def prefixEnd_2641075 : Nat := 4983230072969 + 3 ^ 40 * 2641075 * 2
def baseEnd_2641075 : Nat := 1356140919573359515616423

theorem tailTrace_2641075 : CollatzResearch.WordTrace tailWord_2641075 prefixEnd_2641075 1356140919573359515616423 := by
  unfold tailWord_2641075
  simp only [CollatzResearch.WordTrace]
  refine ⟨96327918906843809544412679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64218612604562539696275119 96327918906843809544412679)
  ·
    refine ⟨144491878360265714316619019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96327918906843809544412679 144491878360265714316619019)
    ·
      refine ⟨216737817540398571474928529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144491878360265714316619019 216737817540398571474928529)
      ·
        refine ⟨162553363155298928606196397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216737817540398571474928529 162553363155298928606196397)
        ·
          refine ⟨60957511183237098227323649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162553363155298928606196397 60957511183237098227323649)
          ·
            refine ⟨45718133387427823670492737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60957511183237098227323649 45718133387427823670492737)
            ·
              refine ⟨34288600040570867752869553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45718133387427823670492737 34288600040570867752869553)
              ·
                refine ⟨25716450030428150814652165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34288600040570867752869553 25716450030428150814652165)
                ·
                  refine ⟨4821834380705278277747281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25716450030428150814652165 4821834380705278277747281)
                  ·
                    refine ⟨3616375785528958708310461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4821834380705278277747281 3616375785528958708310461)
                    ·
                      refine ⟨1356140919573359515616423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3616375785528958708310461 1356140919573359515616423)
                      ·
                        rfl

theorem cell23_2641075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 3].length) (baseStart_2641075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641075 prefixEnd_2641075 := by exact prefixLift 2641075
  have htrace : WordTrace (prefixWord ++ tailWord_2641075) baseStart_2641075 baseEnd_2641075 := by
    simpa [prefixWord, tailWord_2641075, baseEnd_2641075] using wordTrace_append hprefix tailTrace_2641075
  have hstable : (prefixWord ++ tailWord_2641075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641075).length < 2 ^ (prefixWord ++ tailWord_2641075).sum := by decide
  have hdescent : baseEnd_2641075 < baseStart_2641075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641089 : List Nat := [1, 2, 6, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_2641089 : Nat := 118140960795 + 2641089 * 2 ^ 59
def prefixEnd_2641089 : Nat := 4983230072969 + 3 ^ 40 * 2641089 * 2
def baseEnd_2641089 : Nat := 1356148108302522460841359

theorem tailTrace_2641089 : CollatzResearch.WordTrace tailWord_2641089 prefixEnd_2641089 1356148108302522460841359 := by
  unfold tailWord_2641089
  simp only [CollatzResearch.WordTrace]
  refine ⟨96328429528793089935422321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64218953019195393290281547 96328429528793089935422321)
  ·
    refine ⟨72246322146594817451566741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96328429528793089935422321 72246322146594817451566741)
    ·
      refine ⟨3386546350621632068042191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72246322146594817451566741 3386546350621632068042191)
      ·
        refine ⟨5079819525932448102063287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3386546350621632068042191 5079819525932448102063287)
        ·
          refine ⟨7619729288898672153094931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5079819525932448102063287 7619729288898672153094931)
          ·
            refine ⟨11429593933348008229642397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7619729288898672153094931 11429593933348008229642397)
            ·
              refine ⟨4286097725005503086115899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11429593933348008229642397 4286097725005503086115899)
              ·
                refine ⟨6429146587508254629173849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4286097725005503086115899 6429146587508254629173849)
                ·
                  refine ⟨4821859940631190971880387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6429146587508254629173849 4821859940631190971880387)
                  ·
                    refine ⟨7232789910946786457820581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4821859940631190971880387 7232789910946786457820581)
                    ·
                      refine ⟨1356148108302522460841359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7232789910946786457820581 1356148108302522460841359)
                      ·
                        rfl

theorem cell23_2641089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_2641089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641089 prefixEnd_2641089 := by exact prefixLift 2641089
  have htrace : WordTrace (prefixWord ++ tailWord_2641089) baseStart_2641089 baseEnd_2641089 := by
    simpa [prefixWord, tailWord_2641089, baseEnd_2641089] using wordTrace_append hprefix tailTrace_2641089
  have hstable : (prefixWord ++ tailWord_2641089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641089).length < 2 ^ (prefixWord ++ tailWord_2641089).sum := by decide
  have hdescent : baseEnd_2641089 < baseStart_2641089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641132 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 1, 5, 2]
def baseStart_2641132 : Nat := 118140960795 + 2641132 * 2 ^ 59
def prefixEnd_2641132 : Nat := 4983230072969 + 3 ^ 40 * 2641132 * 2
def baseEnd_2641132 : Nat := 1356170187970665792603661

theorem tailTrace_2641132 : CollatzResearch.WordTrace tailWord_2641132 prefixEnd_2641132 1356170187970665792603661 := by
  unfold tailWord_2641132
  simp only [CollatzResearch.WordTrace]
  refine ⟨48164998933818654139618825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64219998578424872186158433 48164998933818654139618825)
  ·
    refine ⟨36123749200363990604714119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48164998933818654139618825 36123749200363990604714119)
    ·
      refine ⟨54185623800545985907071179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36123749200363990604714119 54185623800545985907071179)
      ·
        refine ⟨81278435700818978860606769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54185623800545985907071179 81278435700818978860606769)
        ·
          refine ⟨60958826775614234145455077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81278435700818978860606769 60958826775614234145455077)
          ·
            refine ⟨11429780020427668902272827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60958826775614234145455077 11429780020427668902272827)
            ·
              refine ⟨17144670030641503353409241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11429780020427668902272827 17144670030641503353409241)
              ·
                refine ⟨12858502522981127515056931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17144670030641503353409241 12858502522981127515056931)
                ·
                  refine ⟨19287753784471691272585397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12858502522981127515056931 19287753784471691272585397)
                  ·
                    refine ⟨1808226917294221056804881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19287753784471691272585397 1808226917294221056804881)
                    ·
                      refine ⟨1356170187970665792603661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1808226917294221056804881 1356170187970665792603661)
                      ·
                        rfl

theorem cell23_2641132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 5, 2].length) (baseStart_2641132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641132 prefixEnd_2641132 := by exact prefixLift 2641132
  have htrace : WordTrace (prefixWord ++ tailWord_2641132) baseStart_2641132 baseEnd_2641132 := by
    simpa [prefixWord, tailWord_2641132, baseEnd_2641132] using wordTrace_append hprefix tailTrace_2641132
  have hstable : (prefixWord ++ tailWord_2641132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641132).length < 2 ^ (prefixWord ++ tailWord_2641132).sum := by decide
  have hdescent : baseEnd_2641132 < baseStart_2641132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641175 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 6]
def baseStart_2641175 : Nat := 118140960795 + 2641175 * 2 ^ 59
def prefixEnd_2641175 : Nat := 4983230072969 + 3 ^ 40 * 2641175 * 2
def baseEnd_2641175 : Nat := 1356192267638809124365963

theorem tailTrace_2641175 : CollatzResearch.WordTrace tailWord_2641175 prefixEnd_2641175 1356192267638809124365963 := by
  unfold tailWord_2641175
  simp only [CollatzResearch.WordTrace]
  refine ⟨96331566206481526623052979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64221044137654351082035319 96331566206481526623052979)
  ·
    refine ⟨144497349309722289934579469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96331566206481526623052979 144497349309722289934579469)
    ·
      refine ⟨54186505991145858725467301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144497349309722289934579469 54186505991145858725467301)
      ·
        refine ⟨10159969873339848511025119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54186505991145858725467301 10159969873339848511025119)
        ·
          refine ⟨15239954810009772766537679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10159969873339848511025119 15239954810009772766537679)
          ·
            refine ⟨22859932215014659149806519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15239954810009772766537679 22859932215014659149806519)
            ·
              refine ⟨34289898322521988724709779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22859932215014659149806519 34289898322521988724709779)
              ·
                refine ⟨51434847483782983087064669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34289898322521988724709779 51434847483782983087064669)
                ·
                  refine ⟨19288067806418618657649251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51434847483782983087064669 19288067806418618657649251)
                  ·
                    refine ⟨28932101709627927986473877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19288067806418618657649251 28932101709627927986473877)
                    ·
                      refine ⟨1356192267638809124365963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28932101709627927986473877 1356192267638809124365963)
                      ·
                        rfl

theorem cell23_2641175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_2641175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641175 prefixEnd_2641175 := by exact prefixLift 2641175
  have htrace : WordTrace (prefixWord ++ tailWord_2641175) baseStart_2641175 baseEnd_2641175 := by
    simpa [prefixWord, tailWord_2641175, baseEnd_2641175] using wordTrace_append hprefix tailTrace_2641175
  have hstable : (prefixWord ++ tailWord_2641175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641175).length < 2 ^ (prefixWord ++ tailWord_2641175).sum := by decide
  have hdescent : baseEnd_2641175 < baseStart_2641175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641189 : List Nat := [1, 3, 1, 2, 4, 2, 1, 3, 2, 4]
def baseStart_2641189 : Nat := 118140960795 + 2641189 * 2 ^ 59
def prefixEnd_2641189 : Nat := 4983230072969 + 3 ^ 40 * 2641189 * 2
def baseEnd_2641189 : Nat := 452066485455990689863633

theorem tailTrace_2641189 : CollatzResearch.WordTrace tailWord_2641189 prefixEnd_2641189 452066485455990689863633 := by
  unfold tailWord_2641189
  simp only [CollatzResearch.WordTrace]
  refine ⟨96332076828430807014062621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64221384552287204676041747 96332076828430807014062621)
  ·
    refine ⟨36124528810661552630273483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96332076828430807014062621 36124528810661552630273483)
    ·
      refine ⟨54186793215992328945410225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36124528810661552630273483 54186793215992328945410225)
      ·
        refine ⟨40640094911994246709057669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54186793215992328945410225 40640094911994246709057669)
        ·
          refine ⟨7620017795998921257948313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40640094911994246709057669 7620017795998921257948313)
          ·
            refine ⟨5715013346999190943461235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7620017795998921257948313 5715013346999190943461235)
            ·
              refine ⟨8572520020498786415191853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5715013346999190943461235 8572520020498786415191853)
              ·
                refine ⟨3214695007687044905696945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8572520020498786415191853 3214695007687044905696945)
                ·
                  refine ⟨2411021255765283679272709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3214695007687044905696945 2411021255765283679272709)
                  ·
                    refine ⟨452066485455990689863633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2411021255765283679272709 452066485455990689863633)
                    ·
                      rfl

theorem cell23_2641189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 4].length) (baseStart_2641189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641189 prefixEnd_2641189 := by exact prefixLift 2641189
  have htrace : WordTrace (prefixWord ++ tailWord_2641189) baseStart_2641189 baseEnd_2641189 := by
    simpa [prefixWord, tailWord_2641189, baseEnd_2641189] using wordTrace_append hprefix tailTrace_2641189
  have hstable : (prefixWord ++ tailWord_2641189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641189).length < 2 ^ (prefixWord ++ tailWord_2641189).sum := by decide
  have hdescent : baseEnd_2641189 < baseStart_2641189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641192 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_2641192 : Nat := 118140960795 + 2641192 * 2 ^ 59
def prefixEnd_2641192 : Nat := 4983230072969 + 3 ^ 40 * 2641192 * 2
def baseEnd_2641192 : Nat := 1356200996809935557853385

theorem tailTrace_2641192 : CollatzResearch.WordTrace tailWord_2641192 prefixEnd_2641192 1356200996809935557853385 := by
  unfold tailWord_2641192
  simp only [CollatzResearch.WordTrace]
  refine ⟨48166093123709969263210915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64221457498279959017614553 48166093123709969263210915)
  ·
    refine ⟨72249139685564953894816373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48166093123709969263210915 72249139685564953894816373)
    ·
      refine ⟨6773356845521714427639035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72249139685564953894816373 6773356845521714427639035)
      ·
        refine ⟨10160035268282571641458553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6773356845521714427639035 10160035268282571641458553)
        ·
          refine ⟨7620026451211928731093915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10160035268282571641458553 7620026451211928731093915)
          ·
            refine ⟨11430039676817893096640873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7620026451211928731093915 11430039676817893096640873)
            ·
              refine ⟨8572529757613419822480655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11430039676817893096640873 8572529757613419822480655)
              ·
                refine ⟨12858794636420129733720983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8572529757613419822480655 12858794636420129733720983)
                ·
                  refine ⟨19288191954630194600581475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12858794636420129733720983 19288191954630194600581475)
                  ·
                    refine ⟨28932287931945291900872213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19288191954630194600581475 28932287931945291900872213)
                    ·
                      refine ⟨1356200996809935557853385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28932287931945291900872213 1356200996809935557853385)
                      ·
                        rfl

theorem cell23_2641192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_2641192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641192 prefixEnd_2641192 := by exact prefixLift 2641192
  have htrace : WordTrace (prefixWord ++ tailWord_2641192) baseStart_2641192 baseEnd_2641192 := by
    simpa [prefixWord, tailWord_2641192, baseEnd_2641192] using wordTrace_append hprefix tailTrace_2641192
  have hstable : (prefixWord ++ tailWord_2641192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641192).length < 2 ^ (prefixWord ++ tailWord_2641192).sum := by decide
  have hdescent : baseEnd_2641192 < baseStart_2641192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641206 : List Nat := [5, 1, 2, 3, 1, 1, 1, 2, 1, 6]
def baseStart_2641206 : Nat := 118140960795 + 2641206 * 2 ^ 59
def prefixEnd_2641206 : Nat := 4983230072969 + 3 ^ 40 * 2641206 * 2
def baseEnd_2641206 : Nat := 452069395179699501026107

theorem tailTrace_2641206 : CollatzResearch.WordTrace tailWord_2641206 prefixEnd_2641206 452069395179699501026107 := by
  unfold tailWord_2641206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6020793554335576182339467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64221797912912812611620981 6020793554335576182339467)
  ·
    refine ⟨9031190331503364273509201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6020793554335576182339467 9031190331503364273509201)
    ·
      refine ⟨6773392748627523205131901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9031190331503364273509201 6773392748627523205131901)
      ·
        refine ⟨2540022280735321201924463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6773392748627523205131901 2540022280735321201924463)
        ·
          refine ⟨3810033421102981802886695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2540022280735321201924463 3810033421102981802886695)
          ·
            refine ⟨5715050131654472704330043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3810033421102981802886695 5715050131654472704330043)
            ·
              refine ⟨8572575197481709056495065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5715050131654472704330043 8572575197481709056495065)
              ·
                refine ⟨6429431398111281792371299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8572575197481709056495065 6429431398111281792371299)
                ·
                  refine ⟨9644147097166922688556949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6429431398111281792371299 9644147097166922688556949)
                  ·
                    refine ⟨452069395179699501026107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9644147097166922688556949 452069395179699501026107)
                    ·
                      rfl

theorem cell23_2641206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_2641206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641206 prefixEnd_2641206 := by exact prefixLift 2641206
  have htrace : WordTrace (prefixWord ++ tailWord_2641206) baseStart_2641206 baseEnd_2641206 := by
    simpa [prefixWord, tailWord_2641206, baseEnd_2641206] using wordTrace_append hprefix tailTrace_2641206
  have hstable : (prefixWord ++ tailWord_2641206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641206).length < 2 ^ (prefixWord ++ tailWord_2641206).sum := by decide
  have hdescent : baseEnd_2641206 < baseStart_2641206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641209 : List Nat := [1, 2, 1, 6, 2, 1, 1, 2, 1, 2, 4]
def baseStart_2641209 : Nat := 118140960795 + 2641209 * 2 ^ 59
def prefixEnd_2641209 : Nat := 4983230072969 + 3 ^ 40 * 2641209 * 2
def baseEnd_2641209 : Nat := 1356209725981061991340807

theorem tailTrace_2641209 : CollatzResearch.WordTrace tailWord_2641209 prefixEnd_2641209 1356209725981061991340807 := by
  unfold tailWord_2641209
  simp only [CollatzResearch.WordTrace]
  refine ⟨96332806288358350429790681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64221870858905566953193787 96332806288358350429790681)
  ·
    refine ⟨72249604716268762822343011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96332806288358350429790681 72249604716268762822343011)
    ·
      refine ⟨108374407074403144233514517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72249604716268762822343011 108374407074403144233514517)
      ·
        refine ⟨5080050331612647385945993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 108374407074403144233514517 5080050331612647385945993)
        ·
          refine ⟨3810037748709485539459495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5080050331612647385945993 3810037748709485539459495)
          ·
            refine ⟨5715056623064228309189243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3810037748709485539459495 5715056623064228309189243)
            ·
              refine ⟨8572584934596342463783865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5715056623064228309189243 8572584934596342463783865)
              ·
                refine ⟨6429438700947256847837899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8572584934596342463783865 6429438700947256847837899)
                ·
                  refine ⟨9644158051420885271756849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6429438700947256847837899 9644158051420885271756849)
                  ·
                    refine ⟨7233118538565663953817637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9644158051420885271756849 7233118538565663953817637)
                    ·
                      refine ⟨1356209725981061991340807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7233118538565663953817637 1356209725981061991340807)
                      ·
                        rfl

theorem cell23_2641209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_2641209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641209 prefixEnd_2641209 := by exact prefixLift 2641209
  have htrace : WordTrace (prefixWord ++ tailWord_2641209) baseStart_2641209 baseEnd_2641209 := by
    simpa [prefixWord, tailWord_2641209, baseEnd_2641209] using wordTrace_append hprefix tailTrace_2641209
  have hstable : (prefixWord ++ tailWord_2641209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641209).length < 2 ^ (prefixWord ++ tailWord_2641209).sum := by decide
  have hdescent : baseEnd_2641209 < baseStart_2641209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641212 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 3, 3, 3]
def baseStart_2641212 : Nat := 118140960795 + 2641212 * 2 ^ 59
def prefixEnd_2641212 : Nat := 4983230072969 + 3 ^ 40 * 2641212 * 2
def baseEnd_2641212 : Nat := 1356211266423025479603293

theorem tailTrace_2641212 : CollatzResearch.WordTrace tailWord_2641212 prefixEnd_2641212 1356211266423025479603293 := by
  unfold tailWord_2641212
  simp only [CollatzResearch.WordTrace]
  refine ⟨48166457853673740971074945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64221943804898321294766593 48166457853673740971074945)
  ·
    refine ⟨36124843390255305728306209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48166457853673740971074945 36124843390255305728306209)
    ·
      refine ⟨27093632542691479296229657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36124843390255305728306209 27093632542691479296229657)
      ·
        refine ⟨20320224407018609472172243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27093632542691479296229657 20320224407018609472172243)
        ·
          refine ⟨30480336610527914208258365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20320224407018609472172243 30480336610527914208258365)
          ·
            refine ⟨11430126228947967828096887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30480336610527914208258365 11430126228947967828096887)
            ·
              refine ⟨17145189343421951742145331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11430126228947967828096887 17145189343421951742145331)
              ·
                refine ⟨25717784015132927613217997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17145189343421951742145331 25717784015132927613217997)
                ·
                  refine ⟨9644169005674847854956749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25717784015132927613217997 9644169005674847854956749)
                  ·
                    refine ⟨3616563377128067945608781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9644169005674847854956749 3616563377128067945608781)
                    ·
                      refine ⟨1356211266423025479603293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3616563377128067945608781 1356211266423025479603293)
                      ·
                        rfl

theorem cell23_2641212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_2641212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641212 prefixEnd_2641212 := by exact prefixLift 2641212
  have htrace : WordTrace (prefixWord ++ tailWord_2641212) baseStart_2641212 baseEnd_2641212 := by
    simpa [prefixWord, tailWord_2641212, baseEnd_2641212] using wordTrace_append hprefix tailTrace_2641212
  have hstable : (prefixWord ++ tailWord_2641212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641212).length < 2 ^ (prefixWord ++ tailWord_2641212).sum := by decide
  have hdescent : baseEnd_2641212 < baseStart_2641212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641213 : List Nat := [1, 4, 1, 5, 1, 1, 3, 1, 1, 1, 4]
def baseStart_2641213 : Nat := 118140960795 + 2641213 * 2 ^ 59
def prefixEnd_2641213 : Nat := 4983230072969 + 3 ^ 40 * 2641213 * 2
def baseEnd_2641213 : Nat := 1356211779903679975690789

theorem tailTrace_2641213 : CollatzResearch.WordTrace tailWord_2641213 prefixEnd_2641213 1356211779903679975690789 := by
  unfold tailWord_2641213
  simp only [CollatzResearch.WordTrace]
  refine ⟨96332952180343859112936293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64221968120229239408624195 96332952180343859112936293)
  ·
    refine ⟨18062428533814473583675555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96332952180343859112936293 18062428533814473583675555)
    ·
      refine ⟨27093642800721710375513333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18062428533814473583675555 27093642800721710375513333)
      ·
        refine ⟨2540029012567660347704375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27093642800721710375513333 2540029012567660347704375)
        ·
          refine ⟨3810043518851490521556563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2540029012567660347704375 3810043518851490521556563)
          ·
            refine ⟨5715065278277235782334845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3810043518851490521556563 5715065278277235782334845)
            ·
              refine ⟨2143149479353963418375567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5715065278277235782334845 2143149479353963418375567)
              ·
                refine ⟨3214724219030945127563351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2143149479353963418375567 3214724219030945127563351)
                ·
                  refine ⟨4822086328546417691345027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3214724219030945127563351 4822086328546417691345027)
                  ·
                    refine ⟨7233129492819626537017541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4822086328546417691345027 7233129492819626537017541)
                    ·
                      refine ⟨1356211779903679975690789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7233129492819626537017541 1356211779903679975690789)
                      ·
                        rfl

theorem cell23_2641213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_2641213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641213 prefixEnd_2641213 := by exact prefixLift 2641213
  have htrace : WordTrace (prefixWord ++ tailWord_2641213) baseStart_2641213 baseEnd_2641213 := by
    simpa [prefixWord, tailWord_2641213, baseEnd_2641213] using wordTrace_append hprefix tailTrace_2641213
  have hstable : (prefixWord ++ tailWord_2641213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641213).length < 2 ^ (prefixWord ++ tailWord_2641213).sum := by decide
  have hdescent : baseEnd_2641213 < baseStart_2641213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641225 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 2, 2, 5]
def baseStart_2641225 : Nat := 118140960795 + 2641225 * 2 ^ 59
def prefixEnd_2641225 : Nat := 4983230072969 + 3 ^ 40 * 2641225 * 2
def baseEnd_2641225 : Nat := 1356217941671533928740733

theorem tailTrace_2641225 : CollatzResearch.WordTrace tailWord_2641225 prefixEnd_2641225 1356217941671533928740733 := by
  unfold tailWord_2641225
  simp only [CollatzResearch.WordTrace]
  refine ⟨96333389856300385162373129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64222259904200256774915419 96333389856300385162373129)
  ·
    refine ⟨72250042392225288871779847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96333389856300385162373129 72250042392225288871779847)
    ·
      refine ⟨108375063588337933307669771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72250042392225288871779847 108375063588337933307669771)
      ·
        refine ⟨162562595382506899961504657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108375063588337933307669771 162562595382506899961504657)
        ·
          refine ⟨121921946536880174971128493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162562595382506899961504657 121921946536880174971128493)
          ·
            refine ⟨45720729951330065614173185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121921946536880174971128493 45720729951330065614173185)
            ·
              refine ⟨34290547463497549210629889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45720729951330065614173185 34290547463497549210629889)
              ·
                refine ⟨25717910597623161907972417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34290547463497549210629889 25717910597623161907972417)
                ·
                  refine ⟨19288432948217371430979313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25717910597623161907972417 19288432948217371430979313)
                  ·
                    refine ⟨14466324711163028573234485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19288432948217371430979313 14466324711163028573234485)
                    ·
                      refine ⟨1356217941671533928740733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14466324711163028573234485 1356217941671533928740733)
                      ·
                        rfl

theorem cell23_2641225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_2641225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641225 prefixEnd_2641225 := by exact prefixLift 2641225
  have htrace : WordTrace (prefixWord ++ tailWord_2641225) baseStart_2641225 baseEnd_2641225 := by
    simpa [prefixWord, tailWord_2641225, baseEnd_2641225] using wordTrace_append hprefix tailTrace_2641225
  have hstable : (prefixWord ++ tailWord_2641225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641225).length < 2 ^ (prefixWord ++ tailWord_2641225).sum := by decide
  have hdescent : baseEnd_2641225 < baseStart_2641225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641235 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 4]
def baseStart_2641235 : Nat := 118140960795 + 2641235 * 2 ^ 59
def prefixEnd_2641235 : Nat := 4983230072969 + 3 ^ 40 * 2641235 * 2
def baseEnd_2641235 : Nat := 1356223076478078889615687

theorem tailTrace_2641235 : CollatzResearch.WordTrace tailWord_2641235 prefixEnd_2641235 1356223076478078889615687 := by
  unfold tailWord_2641235
  simp only [CollatzResearch.WordTrace]
  refine ⟨96333754586264156870237159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64222503057509437913491439 96333754586264156870237159)
  ·
    refine ⟨144500631879396235305355739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96333754586264156870237159 144500631879396235305355739)
    ·
      refine ⟨216750947819094352958033609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144500631879396235305355739 216750947819094352958033609)
      ·
        refine ⟨162563210864320764718525207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216750947819094352958033609 162563210864320764718525207)
        ·
          refine ⟨243844816296481147077787811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162563210864320764718525207 243844816296481147077787811)
          ·
            refine ⟨365767224444721720616681717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243844816296481147077787811 365767224444721720616681717)
            ·
              refine ⟨34290677291692661307813911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 365767224444721720616681717 34290677291692661307813911)
              ·
                refine ⟨51436015937538991961720867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34290677291692661307813911 51436015937538991961720867)
                ·
                  refine ⟨77154023906308487942581301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51436015937538991961720867 77154023906308487942581301)
                  ·
                    refine ⟨7233189741216420744616997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77154023906308487942581301 7233189741216420744616997)
                    ·
                      refine ⟨1356223076478078889615687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7233189741216420744616997 1356223076478078889615687)
                      ·
                        rfl

theorem cell23_2641235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 4].length) (baseStart_2641235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641235 prefixEnd_2641235 := by exact prefixLift 2641235
  have htrace : WordTrace (prefixWord ++ tailWord_2641235) baseStart_2641235 baseEnd_2641235 := by
    simpa [prefixWord, tailWord_2641235, baseEnd_2641235] using wordTrace_append hprefix tailTrace_2641235
  have hstable : (prefixWord ++ tailWord_2641235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641235).length < 2 ^ (prefixWord ++ tailWord_2641235).sum := by decide
  have hdescent : baseEnd_2641235 < baseStart_2641235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641239 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 3, 3, 2]
def baseStart_2641239 : Nat := 118140960795 + 2641239 * 2 ^ 59
def prefixEnd_2641239 : Nat := 4983230072969 + 3 ^ 40 * 2641239 * 2
def baseEnd_2641239 : Nat := 1356225130400696873965669

theorem tailTrace_2641239 : CollatzResearch.WordTrace tailWord_2641239 prefixEnd_2641239 1356225130400696873965669 := by
  unfold tailWord_2641239
  simp only [CollatzResearch.WordTrace]
  refine ⟨96333900478249665553382771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64222600318833110368921847 96333900478249665553382771)
  ·
    refine ⟨144500850717374498330074157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96333900478249665553382771 144500850717374498330074157)
    ·
      refine ⟨54187819019015436873777809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144500850717374498330074157 54187819019015436873777809)
      ·
        refine ⟨40640864264261577655333357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54187819019015436873777809 40640864264261577655333357)
        ·
          refine ⟨15240324099098091620750009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40640864264261577655333357 15240324099098091620750009)
          ·
            refine ⟨11430243074323568715562507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15240324099098091620750009 11430243074323568715562507)
            ·
              refine ⟨17145364611485353073343761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11430243074323568715562507 17145364611485353073343761)
              ·
                refine ⟨12859023458614014805007821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17145364611485353073343761 12859023458614014805007821)
                ·
                  refine ⟨4822133796980255551877933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12859023458614014805007821 4822133796980255551877933)
                  ·
                    refine ⟨1808300173867595831954225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4822133796980255551877933 1808300173867595831954225)
                    ·
                      refine ⟨1356225130400696873965669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1808300173867595831954225 1356225130400696873965669)
                      ·
                        rfl

theorem cell23_2641239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_2641239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641239 prefixEnd_2641239 := by exact prefixLift 2641239
  have htrace : WordTrace (prefixWord ++ tailWord_2641239) baseStart_2641239 baseEnd_2641239 := by
    simpa [prefixWord, tailWord_2641239, baseEnd_2641239] using wordTrace_append hprefix tailTrace_2641239
  have hstable : (prefixWord ++ tailWord_2641239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641239).length < 2 ^ (prefixWord ++ tailWord_2641239).sum := by decide
  have hdescent : baseEnd_2641239 < baseStart_2641239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641275 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 9]
def baseStart_2641275 : Nat := 118140960795 + 2641275 * 2 ^ 59
def prefixEnd_2641275 : Nat := 4983230072969 + 3 ^ 40 * 2641275 * 2
def baseEnd_2641275 : Nat := 150693735078250970346167

theorem tailTrace_2641275 : CollatzResearch.WordTrace tailWord_2641275 prefixEnd_2641275 150693735078250970346167 := by
  unfold tailWord_2641275
  simp only [CollatzResearch.WordTrace]
  refine ⟨96335213506119243701693279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64223475670746162467795519 96335213506119243701693279)
  ·
    refine ⟨144502820259178865552539919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96335213506119243701693279 144502820259178865552539919)
    ·
      refine ⟨216754230388768298328809879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144502820259178865552539919 216754230388768298328809879)
      ·
        refine ⟨325131345583152447493214819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216754230388768298328809879 325131345583152447493214819)
        ·
          refine ⟨487697018374728671239822229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325131345583152447493214819 487697018374728671239822229)
          ·
            refine ⟨22860797736315406464366667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 487697018374728671239822229 22860797736315406464366667)
            ·
              refine ⟨34291196604473109696550001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22860797736315406464366667 34291196604473109696550001)
              ·
                refine ⟨25718397453354832272412501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34291196604473109696550001 25718397453354832272412501)
                ·
                  refine ⟨150693735078250970346167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25718397453354832272412501 150693735078250970346167)
                  ·
                    rfl

theorem cell23_2641275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 9].length) (baseStart_2641275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641275 prefixEnd_2641275 := by exact prefixLift 2641275
  have htrace : WordTrace (prefixWord ++ tailWord_2641275) baseStart_2641275 baseEnd_2641275 := by
    simpa [prefixWord, tailWord_2641275, baseEnd_2641275] using wordTrace_append hprefix tailTrace_2641275
  have hstable : (prefixWord ++ tailWord_2641275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641275).length < 2 ^ (prefixWord ++ tailWord_2641275).sum := by decide
  have hdescent : baseEnd_2641275 < baseStart_2641275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641292 : List Nat := [2, 2, 1, 2, 1, 3, 4, 1, 7]
def baseStart_2641292 : Nat := 118140960795 + 2641292 * 2 ^ 59
def prefixEnd_2641292 : Nat := 4983230072969 + 3 ^ 40 * 2641292 * 2
def baseEnd_2641292 : Nat := 150694704986153907400325

theorem tailTrace_2641292 : CollatzResearch.WordTrace tailWord_2641292 prefixEnd_2641292 150694704986153907400325 := by
  unfold tailWord_2641292
  simp only [CollatzResearch.WordTrace]
  refine ⟨48167916773528827802531065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64223889031371770403374753 48167916773528827802531065)
  ·
    refine ⟨36125937580146620851898299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48167916773528827802531065 36125937580146620851898299)
    ·
      refine ⟨54188906370219931277847449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36125937580146620851898299 54188906370219931277847449)
      ·
        refine ⟨40641679777664948458385587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54188906370219931277847449 40641679777664948458385587)
        ·
          refine ⟨60962519666497422687578381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40641679777664948458385587 60962519666497422687578381)
          ·
            refine ⟨22860944874936533507841893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60962519666497422687578381 22860944874936533507841893)
            ·
              refine ⟨4286427164050600032720355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22860944874936533507841893 4286427164050600032720355)
              ·
                refine ⟨6429640746075900049080533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4286427164050600032720355 6429640746075900049080533)
                ·
                  refine ⟨150694704986153907400325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6429640746075900049080533 150694704986153907400325)
                  ·
                    rfl

theorem cell23_2641292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 7].length) (baseStart_2641292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641292 prefixEnd_2641292 := by exact prefixLift 2641292
  have htrace : WordTrace (prefixWord ++ tailWord_2641292) baseStart_2641292 baseEnd_2641292 := by
    simpa [prefixWord, tailWord_2641292, baseEnd_2641292] using wordTrace_append hprefix tailTrace_2641292
  have hstable : (prefixWord ++ tailWord_2641292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641292).length < 2 ^ (prefixWord ++ tailWord_2641292).sum := by decide
  have hdescent : baseEnd_2641292 < baseStart_2641292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641359 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 2, 4, 2]
def baseStart_2641359 : Nat := 118140960795 + 2641359 * 2 ^ 59
def prefixEnd_2641359 : Nat := 4983230072969 + 3 ^ 40 * 2641359 * 2
def baseEnd_2641359 : Nat := 1356286748079236404465117

theorem tailTrace_2641359 : CollatzResearch.WordTrace tailWord_2641359 prefixEnd_2641359 1356286748079236404465117 := by
  unfold tailWord_2641359
  simp only [CollatzResearch.WordTrace]
  refine ⟨96338277237814926047751131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64225518158543284031834087 96338277237814926047751131)
  ·
    refine ⟨144507415856722389071626697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96338277237814926047751131 144507415856722389071626697)
    ·
      refine ⟨108380561892541791803720023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144507415856722389071626697 108380561892541791803720023)
      ·
        refine ⟨162570842838812687705580035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108380561892541791803720023 162570842838812687705580035)
        ·
          refine ⟨243856264258219031558370053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162570842838812687705580035 243856264258219031558370053)
          ·
            refine ⟨45723049548416068417194385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 243856264258219031558370053 45723049548416068417194385)
            ·
              refine ⟨34292287161312051312895789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45723049548416068417194385 34292287161312051312895789)
              ·
                refine ⟨12859607685492019242335921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34292287161312051312895789 12859607685492019242335921)
                ·
                  refine ⟨9644705764119014431751941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12859607685492019242335921 9644705764119014431751941)
                  ·
                    refine ⟨1808382330772315205953489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9644705764119014431751941 1808382330772315205953489)
                    ·
                      refine ⟨1356286748079236404465117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1808382330772315205953489 1356286748079236404465117)
                      ·
                        rfl

theorem cell23_2641359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 4, 2].length) (baseStart_2641359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641359 prefixEnd_2641359 := by exact prefixLift 2641359
  have htrace : WordTrace (prefixWord ++ tailWord_2641359) baseStart_2641359 baseEnd_2641359 := by
    simpa [prefixWord, tailWord_2641359, baseEnd_2641359] using wordTrace_append hprefix tailTrace_2641359
  have hstable : (prefixWord ++ tailWord_2641359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641359).length < 2 ^ (prefixWord ++ tailWord_2641359).sum := by decide
  have hdescent : baseEnd_2641359 < baseStart_2641359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641402 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6]
def baseStart_2641402 : Nat := 118140960795 + 2641402 * 2 ^ 59
def prefixEnd_2641402 : Nat := 4983230072969 + 3 ^ 40 * 2641402 * 2
def baseEnd_2641402 : Nat := 1356308827747379736227419

theorem tailTrace_2641402 : CollatzResearch.WordTrace tailWord_2641402 prefixEnd_2641402 1356308827747379736227419 := by
  unfold tailWord_2641402
  simp only [CollatzResearch.WordTrace]
  refine ⟨24084961394164786097891615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64226563717772762927710973 24084961394164786097891615)
  ·
    refine ⟨36127442091247179146837423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24084961394164786097891615 36127442091247179146837423)
    ·
      refine ⟨54191163136870768720256135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36127442091247179146837423 54191163136870768720256135)
      ·
        refine ⟨81286744705306153080384203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54191163136870768720256135 81286744705306153080384203)
        ·
          refine ⟨121930117057959229620576305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81286744705306153080384203 121930117057959229620576305)
          ·
            refine ⟨91447587793469422215432229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121930117057959229620576305 91447587793469422215432229)
            ·
              refine ⟨17146422711275516665393543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91447587793469422215432229 17146422711275516665393543)
              ·
                refine ⟨25719634066913274998090315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17146422711275516665393543 25719634066913274998090315)
                ·
                  refine ⟨38579451100369912497135473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25719634066913274998090315 38579451100369912497135473)
                  ·
                    refine ⟨28934588325277434372851605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38579451100369912497135473 28934588325277434372851605)
                    ·
                      refine ⟨1356308827747379736227419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28934588325277434372851605 1356308827747379736227419)
                      ·
                        rfl

theorem cell23_2641402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_2641402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641402 prefixEnd_2641402 := by exact prefixLift 2641402
  have htrace : WordTrace (prefixWord ++ tailWord_2641402) baseStart_2641402 baseEnd_2641402 := by
    simpa [prefixWord, tailWord_2641402, baseEnd_2641402] using wordTrace_append hprefix tailTrace_2641402
  have hstable : (prefixWord ++ tailWord_2641402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641402).length < 2 ^ (prefixWord ++ tailWord_2641402).sum := by decide
  have hdescent : baseEnd_2641402 < baseStart_2641402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641429 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 3, 5]
def baseStart_2641429 : Nat := 118140960795 + 2641429 * 2 ^ 59
def prefixEnd_2641429 : Nat := 4983230072969 + 3 ^ 40 * 2641429 * 2
def baseEnd_2641429 : Nat := 452107563908350376863265

theorem tailTrace_2641429 : CollatzResearch.WordTrace tailWord_2641429 prefixEnd_2641429 452107563908350376863265 := by
  unfold tailWord_2641429
  simp only [CollatzResearch.WordTrace]
  refine ⟨96340830347561328002799341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64227220231707552001866227 96340830347561328002799341)
  ·
    refine ⟨36127811380335498001049753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96340830347561328002799341 36127811380335498001049753)
    ·
      refine ⟨27095858535251623500787315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36127811380335498001049753 27095858535251623500787315)
      ·
        refine ⟨40643787802877435251180973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27095858535251623500787315 40643787802877435251180973)
        ·
          refine ⟨15241420426079038219192865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40643787802877435251180973 15241420426079038219192865)
          ·
            refine ⟨11431065319559278664394649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15241420426079038219192865 11431065319559278664394649)
            ·
              refine ⟨8573298989669458998295987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11431065319559278664394649 8573298989669458998295987)
              ·
                refine ⟨12859948484504188497443981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8573298989669458998295987 12859948484504188497443981)
                ·
                  refine ⟨4822480681689070686541493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12859948484504188497443981 4822480681689070686541493)
                  ·
                    refine ⟨452107563908350376863265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4822480681689070686541493 452107563908350376863265)
                    ·
                      rfl

theorem cell23_2641429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_2641429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641429 prefixEnd_2641429 := by exact prefixLift 2641429
  have htrace : WordTrace (prefixWord ++ tailWord_2641429) baseStart_2641429 baseEnd_2641429 := by
    simpa [prefixWord, tailWord_2641429, baseEnd_2641429] using wordTrace_append hprefix tailTrace_2641429
  have hstable : (prefixWord ++ tailWord_2641429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641429).length < 2 ^ (prefixWord ++ tailWord_2641429).sum := by decide
  have hdescent : baseEnd_2641429 < baseStart_2641429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641436 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 1, 5, 2]
def baseStart_2641436 : Nat := 118140960795 + 2641436 * 2 ^ 59
def prefixEnd_2641436 : Nat := 4983230072969 + 3 ^ 40 * 2641436 * 2
def baseEnd_2641436 : Nat := 1356326286089632603202263

theorem tailTrace_2641436 : CollatzResearch.WordTrace tailWord_2641436 prefixEnd_2641436 1356326286089632603202263 := by
  unfold tailWord_2641436
  simp only [CollatzResearch.WordTrace]
  refine ⟨48170542829267984099152081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64227390439023978798869441 48170542829267984099152081)
  ·
    refine ⟨36127907121950988074364061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48170542829267984099152081 36127907121950988074364061)
    ·
      refine ⟨13547965170731620527886523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36127907121950988074364061 13547965170731620527886523)
      ·
        refine ⟨20321947756097430791829785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13547965170731620527886523 20321947756097430791829785)
        ·
          refine ⟨15241460817073073093872339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20321947756097430791829785 15241460817073073093872339)
          ·
            refine ⟨22862191225609609640808509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15241460817073073093872339 22862191225609609640808509)
            ·
              refine ⟨8573321709603603615303191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22862191225609609640808509 8573321709603603615303191)
              ·
                refine ⟨12859982564405405422954787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8573321709603603615303191 12859982564405405422954787)
                ·
                  refine ⟨19289973846608108134432181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12859982564405405422954787 19289973846608108134432181)
                  ·
                    refine ⟨1808435048119510137603017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19289973846608108134432181 1808435048119510137603017)
                    ·
                      refine ⟨1356326286089632603202263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1808435048119510137603017 1356326286089632603202263)
                      ·
                        rfl

theorem cell23_2641436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_2641436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641436 prefixEnd_2641436 := by exact prefixLift 2641436
  have htrace : WordTrace (prefixWord ++ tailWord_2641436) baseStart_2641436 baseEnd_2641436 := by
    simpa [prefixWord, tailWord_2641436, baseEnd_2641436] using wordTrace_append hprefix tailTrace_2641436
  have hstable : (prefixWord ++ tailWord_2641436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641436).length < 2 ^ (prefixWord ++ tailWord_2641436).sum := by decide
  have hdescent : baseEnd_2641436 < baseStart_2641436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641472 : List Nat := [2, 1, 1, 2, 2, 2, 1, 12]
def baseStart_2641472 : Nat := 118140960795 + 2641472 * 2 ^ 59
def prefixEnd_2641472 : Nat := 4983230072969 + 3 ^ 40 * 2641472 * 2
def baseEnd_2641472 : Nat := 50234991533081276383411

theorem tailTrace_2641472 : CollatzResearch.WordTrace tailWord_2641472 prefixEnd_2641472 50234991533081276383411 := by
  unfold tailWord_2641472
  simp only [CollatzResearch.WordTrace]
  refine ⟨48171199343202773173307335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64228265790937030897743113 48171199343202773173307335)
  ·
    refine ⟨72256799014804159759961003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48171199343202773173307335 72256799014804159759961003)
    ·
      refine ⟨108385198522206239639941505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72256799014804159759961003 108385198522206239639941505)
      ·
        refine ⟨81288898891654679729956129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108385198522206239639941505 81288898891654679729956129)
        ·
          refine ⟨60966674168741009797467097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81288898891654679729956129 60966674168741009797467097)
          ·
            refine ⟨45725005626555757348100323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60966674168741009797467097 45725005626555757348100323)
            ·
              refine ⟨68587508439833636022150485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45725005626555757348100323 68587508439833636022150485)
              ·
                refine ⟨50234991533081276383411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 68587508439833636022150485 50234991533081276383411)
                ·
                  rfl

theorem cell23_2641472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 12].length) (baseStart_2641472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641472 prefixEnd_2641472 := by exact prefixLift 2641472
  have htrace : WordTrace (prefixWord ++ tailWord_2641472) baseStart_2641472 baseEnd_2641472 := by
    simpa [prefixWord, tailWord_2641472, baseEnd_2641472] using wordTrace_append hprefix tailTrace_2641472
  have hstable : (prefixWord ++ tailWord_2641472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641472).length < 2 ^ (prefixWord ++ tailWord_2641472).sum := by decide
  have hdescent : baseEnd_2641472 < baseStart_2641472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641517 : List Nat := [1, 5, 1, 1, 4, 2, 1, 1, 3, 2, 2]
def baseStart_2641517 : Nat := 118140960795 + 2641517 * 2 ^ 59
def prefixEnd_2641517 : Nat := 4983230072969 + 3 ^ 40 * 2641517 * 2
def baseEnd_2641517 : Nat := 1356367878022646786289391

theorem tailTrace_2641517 : CollatzResearch.WordTrace tailWord_2641517 prefixEnd_2641517 1356367878022646786289391 := by
  unfold tailWord_2641517
  simp only [CollatzResearch.WordTrace]
  refine ⟨96344039971242519032002805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64229359980828346021335203 96344039971242519032002805)
  ·
    refine ⟨9032253747303986159250263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96344039971242519032002805 9032253747303986159250263)
    ·
      refine ⟨13548380620955979238875395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9032253747303986159250263 13548380620955979238875395)
      ·
        refine ⟨20322570931433968858313093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13548380620955979238875395 20322570931433968858313093)
        ·
          refine ⟨3810482049643869160933705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20322570931433968858313093 3810482049643869160933705)
          ·
            refine ⟨2857861537232901870700279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3810482049643869160933705 2857861537232901870700279)
            ·
              refine ⟨4286792305849352806050419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2857861537232901870700279 4286792305849352806050419)
              ·
                refine ⟨6430188458774029209075629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4286792305849352806050419 6430188458774029209075629)
                ·
                  refine ⟨2411320672040260953403361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6430188458774029209075629 2411320672040260953403361)
                  ·
                    refine ⟨1808490504030195715052521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2411320672040260953403361 1808490504030195715052521)
                    ·
                      refine ⟨1356367878022646786289391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1808490504030195715052521 1356367878022646786289391)
                      ·
                        rfl

theorem cell23_2641517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_2641517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641517 prefixEnd_2641517 := by exact prefixLift 2641517
  have htrace : WordTrace (prefixWord ++ tailWord_2641517) baseStart_2641517 baseEnd_2641517 := by
    simpa [prefixWord, tailWord_2641517, baseEnd_2641517] using wordTrace_append hprefix tailTrace_2641517
  have hstable : (prefixWord ++ tailWord_2641517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641517).length < 2 ^ (prefixWord ++ tailWord_2641517).sum := by decide
  have hdescent : baseEnd_2641517 < baseStart_2641517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641543 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 3, 3, 2]
def baseStart_2641543 : Nat := 118140960795 + 2641543 * 2 ^ 59
def prefixEnd_2641543 : Nat := 4983230072969 + 3 ^ 40 * 2641543 * 2
def baseEnd_2641543 : Nat := 1356381228519663684564271

theorem tailTrace_2641543 : CollatzResearch.WordTrace tailWord_2641543 prefixEnd_2641543 1356381228519663684564271 := by
  unfold tailWord_2641543
  simp only [CollatzResearch.WordTrace]
  refine ⟨96344988269148325472449283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64229992179432216981632855 96344988269148325472449283)
  ·
    refine ⟨144517482403722488208673925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96344988269148325472449283 144517482403722488208673925)
    ·
      refine ⟨27097027950697966539126361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144517482403722488208673925 27097027950697966539126361)
      ·
        refine ⟨20322770963023474904344771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27097027950697966539126361 20322770963023474904344771)
        ·
          refine ⟨30484156444535212356517157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20322770963023474904344771 30484156444535212356517157)
          ·
            refine ⟨5715779333350352316846967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30484156444535212356517157 5715779333350352316846967)
            ·
              refine ⟨8573669000025528475270451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5715779333350352316846967 8573669000025528475270451)
              ·
                refine ⟨12860503500038292712905677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8573669000025528475270451 12860503500038292712905677)
                ·
                  refine ⟨4822688812514359767339629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12860503500038292712905677 4822688812514359767339629)
                  ·
                    refine ⟨1808508304692884912752361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4822688812514359767339629 1808508304692884912752361)
                    ·
                      refine ⟨1356381228519663684564271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1808508304692884912752361 1356381228519663684564271)
                      ·
                        rfl

theorem cell23_2641543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_2641543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641543 prefixEnd_2641543 := by exact prefixLift 2641543
  have htrace : WordTrace (prefixWord ++ tailWord_2641543) baseStart_2641543 baseEnd_2641543 := by
    simpa [prefixWord, tailWord_2641543, baseEnd_2641543] using wordTrace_append hprefix tailTrace_2641543
  have hstable : (prefixWord ++ tailWord_2641543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641543).length < 2 ^ (prefixWord ++ tailWord_2641543).sum := by decide
  have hdescent : baseEnd_2641543 < baseStart_2641543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641567 : List Nat := [1, 1, 2, 7, 1, 1, 2, 2, 2, 1, 3]
def baseStart_2641567 : Nat := 118140960795 + 2641567 * 2 ^ 59
def prefixEnd_2641567 : Nat := 4983230072969 + 3 ^ 40 * 2641567 * 2
def baseEnd_2641567 : Nat := 1356393552055371590664161

theorem tailTrace_2641567 : CollatzResearch.WordTrace tailWord_2641567 prefixEnd_2641567 1356393552055371590664161 := by
  unfold tailWord_2641567
  simp only [CollatzResearch.WordTrace]
  refine ⟨96345863621061377571322955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64230575747374251714215303 96345863621061377571322955)
  ·
    refine ⟨144518795431592066356984433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96345863621061377571322955 144518795431592066356984433)
    ·
      refine ⟨108389096573694049767738325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144518795431592066356984433 108389096573694049767738325)
      ·
        refine ⟨2540369450945954291431367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 108389096573694049767738325 2540369450945954291431367)
        ·
          refine ⟨3810554176418931437147051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2540369450945954291431367 3810554176418931437147051)
          ·
            refine ⟨5715831264628397155720577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3810554176418931437147051 5715831264628397155720577)
            ·
              refine ⟨4286873448471297866790433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5715831264628397155720577 4286873448471297866790433)
              ·
                refine ⟨3215155086353473400092825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4286873448471297866790433 3215155086353473400092825)
                ·
                  refine ⟨2411366314765105050069619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3215155086353473400092825 2411366314765105050069619)
                  ·
                    refine ⟨3617049472147657575104429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2411366314765105050069619 3617049472147657575104429)
                    ·
                      refine ⟨1356393552055371590664161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3617049472147657575104429 1356393552055371590664161)
                      ·
                        rfl

theorem cell23_2641567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_2641567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641567 prefixEnd_2641567 := by exact prefixLift 2641567
  have htrace : WordTrace (prefixWord ++ tailWord_2641567) baseStart_2641567 baseEnd_2641567 := by
    simpa [prefixWord, tailWord_2641567, baseEnd_2641567] using wordTrace_append hprefix tailTrace_2641567
  have hstable : (prefixWord ++ tailWord_2641567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641567).length < 2 ^ (prefixWord ++ tailWord_2641567).sum := by decide
  have hdescent : baseEnd_2641567 < baseStart_2641567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641573 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 4, 2, 2]
def baseStart_2641573 : Nat := 118140960795 + 2641573 * 2 ^ 59
def prefixEnd_2641573 : Nat := 4983230072969 + 3 ^ 40 * 2641573 * 2
def baseEnd_2641573 : Nat := 1356396632939298567189133

theorem tailTrace_2641573 : CollatzResearch.WordTrace tailWord_2641573 prefixEnd_2641573 1356396632939298567189133 := by
  unfold tailWord_2641573
  simp only [CollatzResearch.WordTrace]
  refine ⟨96346082459039640596041373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64230721639359760397360915 96346082459039640596041373)
  ·
    refine ⟨36129780922139865223515515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96346082459039640596041373 36129780922139865223515515)
    ·
      refine ⟨54194671383209797835273273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36129780922139865223515515 54194671383209797835273273)
      ·
        refine ⟨40646003537407348376454955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54194671383209797835273273 40646003537407348376454955)
        ·
          refine ⟨60969005306111022564682433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40646003537407348376454955 60969005306111022564682433)
          ·
            refine ⟨45726753979583266923511825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60969005306111022564682433 45726753979583266923511825)
            ·
              refine ⟨34295065484687450192633869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45726753979583266923511825 34295065484687450192633869)
              ·
                refine ⟨12860649556757793822237701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34295065484687450192633869 12860649556757793822237701)
                ·
                  refine ⟨2411371791892086341669569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12860649556757793822237701 2411371791892086341669569)
                  ·
                    refine ⟨1808528843919064756252177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2411371791892086341669569 1808528843919064756252177)
                    ·
                      refine ⟨1356396632939298567189133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1808528843919064756252177 1356396632939298567189133)
                      ·
                        rfl

theorem cell23_2641573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_2641573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641573 prefixEnd_2641573 := by exact prefixLift 2641573
  have htrace : WordTrace (prefixWord ++ tailWord_2641573) baseStart_2641573 baseEnd_2641573 := by
    simpa [prefixWord, tailWord_2641573, baseEnd_2641573] using wordTrace_append hprefix tailTrace_2641573
  have hstable : (prefixWord ++ tailWord_2641573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641573).length < 2 ^ (prefixWord ++ tailWord_2641573).sum := by decide
  have hdescent : baseEnd_2641573 < baseStart_2641573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641596 : List Nat := [2, 2, 2, 3, 1, 3, 1, 2, 7]
def baseStart_2641596 : Nat := 118140960795 + 2641596 * 2 ^ 59
def prefixEnd_2641596 : Nat := 4983230072969 + 3 ^ 40 * 2641596 * 2
def baseEnd_2641596 : Nat := 150712049221594664133503

theorem tailTrace_2641596 : CollatzResearch.WordTrace tailWord_2641596 prefixEnd_2641596 150712049221594664133503 := by
  unfold tailWord_2641596
  simp only [CollatzResearch.WordTrace]
  refine ⟨48173460668978157762064321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64231280891970877016085761 48173460668978157762064321)
  ·
    refine ⟨36130095501733618321548241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48173460668978157762064321 36130095501733618321548241)
    ·
      refine ⟨27097571626300213741161181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36130095501733618321548241 27097571626300213741161181)
      ·
        refine ⟨10161589359862580152935443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27097571626300213741161181 10161589359862580152935443)
        ·
          refine ⟨15242384039793870229403165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10161589359862580152935443 15242384039793870229403165)
          ·
            refine ⟨5715894014922701336026187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15242384039793870229403165 5715894014922701336026187)
            ·
              refine ⟨8573841022384052004039281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5715894014922701336026187 8573841022384052004039281)
              ·
                refine ⟨6430380766788039003029461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8573841022384052004039281 6430380766788039003029461)
                ·
                  refine ⟨150712049221594664133503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6430380766788039003029461 150712049221594664133503)
                  ·
                    rfl

theorem cell23_2641596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 7].length) (baseStart_2641596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641596 prefixEnd_2641596 := by exact prefixLift 2641596
  have htrace : WordTrace (prefixWord ++ tailWord_2641596) baseStart_2641596 baseEnd_2641596 := by
    simpa [prefixWord, tailWord_2641596, baseEnd_2641596] using wordTrace_append hprefix tailTrace_2641596
  have hstable : (prefixWord ++ tailWord_2641596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641596).length < 2 ^ (prefixWord ++ tailWord_2641596).sum := by decide
  have hdescent : baseEnd_2641596 < baseStart_2641596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641616 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 1, 7, 2]
def baseStart_2641616 : Nat := 118140960795 + 2641616 * 2 ^ 59
def prefixEnd_2641616 : Nat := 4983230072969 + 3 ^ 40 * 2641616 * 2
def baseEnd_2641616 : Nat := 1356418712607441898951435

theorem tailTrace_2641616 : CollatzResearch.WordTrace tailWord_2641616 prefixEnd_2641616 1356418712607441898951435 := by
  unfold tailWord_2641616
  simp only [CollatzResearch.WordTrace]
  refine ⟨48173825398941929469928351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64231767198589239293237801 48173825398941929469928351)
  ·
    refine ⟨72260738098412894204892527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48173825398941929469928351 72260738098412894204892527)
    ·
      refine ⟨108391107147619341307338791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72260738098412894204892527 108391107147619341307338791)
      ·
        refine ⟨162586660721429011961008187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108391107147619341307338791 162586660721429011961008187)
        ·
          refine ⟨243879991082143517941512281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162586660721429011961008187 243879991082143517941512281)
          ·
            refine ⟨182909993311607638456134211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243879991082143517941512281 182909993311607638456134211)
            ·
              refine ⟨274364989967411457684201317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182909993311607638456134211 274364989967411457684201317)
              ·
                refine ⟨51443435618889648315787747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 274364989967411457684201317 51443435618889648315787747)
                ·
                  refine ⟨77165153428334472473681621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51443435618889648315787747 77165153428334472473681621)
                  ·
                    refine ⟨1808558283476589198601913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 77165153428334472473681621 1808558283476589198601913)
                    ·
                      refine ⟨1356418712607441898951435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1808558283476589198601913 1356418712607441898951435)
                      ·
                        rfl

theorem cell23_2641616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 7, 2].length) (baseStart_2641616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641616 prefixEnd_2641616 := by exact prefixLift 2641616
  have htrace : WordTrace (prefixWord ++ tailWord_2641616) baseStart_2641616 baseEnd_2641616 := by
    simpa [prefixWord, tailWord_2641616, baseEnd_2641616] using wordTrace_append hprefix tailTrace_2641616
  have hstable : (prefixWord ++ tailWord_2641616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641616).length < 2 ^ (prefixWord ++ tailWord_2641616).sum := by decide
  have hdescent : baseEnd_2641616 < baseStart_2641616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641646 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_2641646 : Nat := 118140960795 + 2641646 * 2 ^ 59
def prefixEnd_2641646 : Nat := 4983230072969 + 3 ^ 40 * 2641646 * 2
def baseEnd_2641646 : Nat := 1356434117027076781576297

theorem tailTrace_2641646 : CollatzResearch.WordTrace tailWord_2641646 prefixEnd_2641646 1356434117027076781576297 := by
  unfold tailWord_2641646
  simp only [CollatzResearch.WordTrace]
  refine ⟨12043593123471896757931099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64232496658516782708965861 12043593123471896757931099)
  ·
    refine ⟨18065389685207845136896649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12043593123471896757931099 18065389685207845136896649)
    ·
      refine ⟨13549042263905883852672487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18065389685207845136896649 13549042263905883852672487)
      ·
        refine ⟨20323563395858825779008731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13549042263905883852672487 20323563395858825779008731)
        ·
          refine ⟨30485345093788238668513097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20323563395858825779008731 30485345093788238668513097)
          ·
            refine ⟨22864008820341179001384823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30485345093788238668513097 22864008820341179001384823)
            ·
              refine ⟨34296013230511768502077235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22864008820341179001384823 34296013230511768502077235)
              ·
                refine ⟨51444019845767652753115853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34296013230511768502077235 51444019845767652753115853)
                ·
                  refine ⟨19291507442162869782418445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51444019845767652753115853 19291507442162869782418445)
                  ·
                    refine ⟨7234315290811076168406917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19291507442162869782418445 7234315290811076168406917)
                    ·
                      refine ⟨1356434117027076781576297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7234315290811076168406917 1356434117027076781576297)
                      ·
                        rfl

theorem cell23_2641646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_2641646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641646 prefixEnd_2641646 := by exact prefixLift 2641646
  have htrace : WordTrace (prefixWord ++ tailWord_2641646) baseStart_2641646 baseEnd_2641646 := by
    simpa [prefixWord, tailWord_2641646, baseEnd_2641646] using wordTrace_append hprefix tailTrace_2641646
  have hstable : (prefixWord ++ tailWord_2641646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641646).length < 2 ^ (prefixWord ++ tailWord_2641646).sum := by decide
  have hdescent : baseEnd_2641646 < baseStart_2641646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641656 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 5, 4]
def baseStart_2641656 : Nat := 118140960795 + 2641656 * 2 ^ 59
def prefixEnd_2641656 : Nat := 4983230072969 + 3 ^ 40 * 2641656 * 2
def baseEnd_2641656 : Nat := 452146417277873914150417

theorem tailTrace_2641656 : CollatzResearch.WordTrace tailWord_2641656 prefixEnd_2641656 452146417277873914150417 := by
  unfold tailWord_2641656
  simp only [CollatzResearch.WordTrace]
  refine ⟨48174554858869472885656411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64232739811825963847541881 48174554858869472885656411)
  ·
    refine ⟨72261832288304209328484617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48174554858869472885656411 72261832288304209328484617)
    ·
      refine ⟨54196374216228156996363463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72261832288304209328484617 54196374216228156996363463)
      ·
        refine ⟨81294561324342235494545195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54196374216228156996363463 81294561324342235494545195)
        ·
          refine ⟨121941841986513353241817793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81294561324342235494545195 121941841986513353241817793)
          ·
            refine ⟨91456381489885014931363345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121941841986513353241817793 91456381489885014931363345)
            ·
              refine ⟨68592286117413761198522509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91456381489885014931363345 68592286117413761198522509)
              ·
                refine ⟨25722107294030160449445941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68592286117413761198522509 25722107294030160449445941)
                ·
                  refine ⟨2411447558815327542135557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25722107294030160449445941 2411447558815327542135557)
                  ·
                    refine ⟨452146417277873914150417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2411447558815327542135557 452146417277873914150417)
                    ·
                      rfl

theorem cell23_2641656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 5, 4].length) (baseStart_2641656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641656 prefixEnd_2641656 := by exact prefixLift 2641656
  have htrace : WordTrace (prefixWord ++ tailWord_2641656) baseStart_2641656 baseEnd_2641656 := by
    simpa [prefixWord, tailWord_2641656, baseEnd_2641656] using wordTrace_append hprefix tailTrace_2641656
  have hstable : (prefixWord ++ tailWord_2641656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641656).length < 2 ^ (prefixWord ++ tailWord_2641656).sum := by decide
  have hdescent : baseEnd_2641656 < baseStart_2641656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641659 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 6]
def baseStart_2641659 : Nat := 118140960795 + 2641659 * 2 ^ 59
def prefixEnd_2641659 : Nat := 4983230072969 + 3 ^ 40 * 2641659 * 2
def baseEnd_2641659 : Nat := 1356440792275585230713737

theorem tailTrace_2641659 : CollatzResearch.WordTrace tailWord_2641659 prefixEnd_2641659 1356440792275585230713737 := by
  unfold tailWord_2641659
  simp only [CollatzResearch.WordTrace]
  refine ⟨96349219136728077283672031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64232812757818718189114687 96349219136728077283672031)
  ·
    refine ⟨144523828705092115925508047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96349219136728077283672031 144523828705092115925508047)
    ·
      refine ⟨216785743057638173888262071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144523828705092115925508047 216785743057638173888262071)
      ·
        refine ⟨325178614586457260832393107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216785743057638173888262071 325178614586457260832393107)
        ·
          refine ⟨487767921879685891248589661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325178614586457260832393107 487767921879685891248589661)
          ·
            refine ⟨182912970704882209218221123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 487767921879685891248589661 182912970704882209218221123)
            ·
              refine ⟨274369456057323313827331685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182912970704882209218221123 274369456057323313827331685)
              ·
                refine ⟨51444273010748121342624691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 274369456057323313827331685 51444273010748121342624691)
                ·
                  refine ⟨77166409516122182013937037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51444273010748121342624691 77166409516122182013937037)
                  ·
                    refine ⟨28937403568545818255226389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77166409516122182013937037 28937403568545818255226389)
                    ·
                      refine ⟨1356440792275585230713737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28937403568545818255226389 1356440792275585230713737)
                      ·
                        rfl

theorem cell23_2641659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 6].length) (baseStart_2641659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641659 prefixEnd_2641659 := by exact prefixLift 2641659
  have htrace : WordTrace (prefixWord ++ tailWord_2641659) baseStart_2641659 baseEnd_2641659 := by
    simpa [prefixWord, tailWord_2641659, baseEnd_2641659] using wordTrace_append hprefix tailTrace_2641659
  have hstable : (prefixWord ++ tailWord_2641659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641659).length < 2 ^ (prefixWord ++ tailWord_2641659).sum := by decide
  have hdescent : baseEnd_2641659 < baseStart_2641659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641690 : List Nat := [3, 1, 1, 3, 2, 4, 1, 1, 3, 4]
def baseStart_2641690 : Nat := 118140960795 + 2641690 * 2 ^ 59
def prefixEnd_2641690 : Nat := 4983230072969 + 3 ^ 40 * 2641690 * 2
def baseEnd_2641690 : Nat := 452152236725291536475365

theorem tailTrace_2641690 : CollatzResearch.WordTrace tailWord_2641690 prefixEnd_2641690 452152236725291536475365 := by
  unfold tailWord_2641690
  simp only [CollatzResearch.WordTrace]
  refine ⟨24087587449903942394512631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64233566533077179718700349 24087587449903942394512631)
  ·
    refine ⟨36131381174855913591768947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24087587449903942394512631 36131381174855913591768947)
    ·
      refine ⟨54197071762283870387653421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36131381174855913591768947 54197071762283870387653421)
      ·
        refine ⟨20323901910856451395370033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54197071762283870387653421 20323901910856451395370033)
        ·
          refine ⟨15242926433142338546527525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20323901910856451395370033 15242926433142338546527525)
          ·
            refine ⟨2858048706214188477473911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15242926433142338546527525 2858048706214188477473911)
            ·
              refine ⟨4287073059321282716210867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2858048706214188477473911 4287073059321282716210867)
              ·
                refine ⟨6430609588981924074316301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4287073059321282716210867 6430609588981924074316301)
                ·
                  refine ⟨2411478595868221527868613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6430609588981924074316301 2411478595868221527868613)
                  ·
                    refine ⟨452152236725291536475365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2411478595868221527868613 452152236725291536475365)
                    ·
                      rfl

theorem cell23_2641690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 3, 4].length) (baseStart_2641690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641690 prefixEnd_2641690 := by exact prefixLift 2641690
  have htrace : WordTrace (prefixWord ++ tailWord_2641690) baseStart_2641690 baseEnd_2641690 := by
    simpa [prefixWord, tailWord_2641690, baseEnd_2641690] using wordTrace_append hprefix tailTrace_2641690
  have hstable : (prefixWord ++ tailWord_2641690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641690).length < 2 ^ (prefixWord ++ tailWord_2641690).sum := by decide
  have hdescent : baseEnd_2641690 < baseStart_2641690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641741 : List Nat := [1, 6, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_2641741 : Nat := 118140960795 + 2641741 * 2 ^ 59
def prefixEnd_2641741 : Nat := 4983230072969 + 3 ^ 40 * 2641741 * 2
def baseEnd_2641741 : Nat := 452160965896417969962787

theorem tailTrace_2641741 : CollatzResearch.WordTrace tailWord_2641741 prefixEnd_2641741 452160965896417969962787 := by
  unfold tailWord_2641741
  simp only [CollatzResearch.WordTrace]
  refine ⟨96352209922431005288157077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64234806614954003525438051 96352209922431005288157077)
  ·
    refine ⟨4516509840113953372882363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96352209922431005288157077 4516509840113953372882363)
    ·
      refine ⟨6774764760170930059323545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4516509840113953372882363 6774764760170930059323545)
      ·
        refine ⟨5081073570128197544492659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6774764760170930059323545 5081073570128197544492659)
        ·
          refine ⟨7621610355192296316738989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5081073570128197544492659 7621610355192296316738989)
          ·
            refine ⟨2858103883197111118777121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7621610355192296316738989 2858103883197111118777121)
            ·
              refine ⟨2143577912397833339082841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2858103883197111118777121 2143577912397833339082841)
              ·
                refine ⟨1607683434298375004312131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2143577912397833339082841 1607683434298375004312131)
                ·
                  refine ⟨2411525151447562506468197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1607683434298375004312131 2411525151447562506468197)
                  ·
                    refine ⟨452160965896417969962787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2411525151447562506468197 452160965896417969962787)
                    ·
                      rfl

theorem cell23_2641741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_2641741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641741 prefixEnd_2641741 := by exact prefixLift 2641741
  have htrace : WordTrace (prefixWord ++ tailWord_2641741) baseStart_2641741 baseEnd_2641741 := by
    simpa [prefixWord, tailWord_2641741, baseEnd_2641741] using wordTrace_append hprefix tailTrace_2641741
  have hstable : (prefixWord ++ tailWord_2641741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641741).length < 2 ^ (prefixWord ++ tailWord_2641741).sum := by decide
  have hdescent : baseEnd_2641741 < baseStart_2641741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641774 : List Nat := [4, 1, 2, 3, 1, 3, 1, 1, 2, 3, 2]
def baseStart_2641774 : Nat := 118140960795 + 2641774 * 2 ^ 59
def prefixEnd_2641774 : Nat := 4983230072969 + 3 ^ 40 * 2641774 * 2
def baseEnd_2641774 : Nat := 1356499842550852280775709

theorem tailTrace_2641774 : CollatzResearch.WordTrace tailWord_2641774 prefixEnd_2641774 1356499842550852280775709 := by
  unfold tailWord_2641774
  simp only [CollatzResearch.WordTrace]
  refine ⟨12044176691413931490513547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64235609020874301282738917 12044176691413931490513547)
  ·
    refine ⟨18066265037120897235770321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12044176691413931490513547 18066265037120897235770321)
    ·
      refine ⟨13549698777840672926827741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18066265037120897235770321 13549698777840672926827741)
      ·
        refine ⟨5081137041690252347560403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13549698777840672926827741 5081137041690252347560403)
        ·
          refine ⟨7621705562535378521340605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5081137041690252347560403 7621705562535378521340605)
          ·
            refine ⟨2858139585950766945502727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7621705562535378521340605 2858139585950766945502727)
            ·
              refine ⟨4287209378926150418254091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2858139585950766945502727 4287209378926150418254091)
              ·
                refine ⟨6430814068389225627381137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4287209378926150418254091 6430814068389225627381137)
                ·
                  refine ⟨4823110551291919220535853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6430814068389225627381137 4823110551291919220535853)
                  ·
                    refine ⟨1808666456734469707700945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4823110551291919220535853 1808666456734469707700945)
                    ·
                      refine ⟨1356499842550852280775709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1808666456734469707700945 1356499842550852280775709)
                      ·
                        rfl

theorem cell23_2641774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_2641774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641774 prefixEnd_2641774 := by exact prefixLift 2641774
  have htrace : WordTrace (prefixWord ++ tailWord_2641774) baseStart_2641774 baseEnd_2641774 := by
    simpa [prefixWord, tailWord_2641774, baseEnd_2641774] using wordTrace_append hprefix tailTrace_2641774
  have hstable : (prefixWord ++ tailWord_2641774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641774).length < 2 ^ (prefixWord ++ tailWord_2641774).sum := by decide
  have hdescent : baseEnd_2641774 < baseStart_2641774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641863 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 3]
def baseStart_2641863 : Nat := 118140960795 + 2641863 * 2 ^ 59
def prefixEnd_2641863 : Nat := 4983230072969 + 3 ^ 40 * 2641863 * 2
def baseEnd_2641863 : Nat := 1356545542329102432562799

theorem tailTrace_2641863 : CollatzResearch.WordTrace tailWord_2641863 prefixEnd_2641863 1356545542329102432562799 := by
  unfold tailWord_2641863
  simp only [CollatzResearch.WordTrace]
  refine ⟨96356659627989020124098243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64237773085326013416065495 96356659627989020124098243)
  ·
    refine ⟨144534989441983530186147365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96356659627989020124098243 144534989441983530186147365)
    ·
      refine ⟨27100310520371911909902631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144534989441983530186147365 27100310520371911909902631)
      ·
        refine ⟨40650465780557867864853947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27100310520371911909902631 40650465780557867864853947)
        ·
          refine ⟨60975698670836801797280921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40650465780557867864853947 60975698670836801797280921)
          ·
            refine ⟨45731774003127601347960691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60975698670836801797280921 45731774003127601347960691)
            ·
              refine ⟨68597661004691402021941037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45731774003127601347960691 68597661004691402021941037)
              ·
                refine ⟨25724122876759275758227889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68597661004691402021941037 25724122876759275758227889)
                ·
                  refine ⟨19293092157569456818670917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25724122876759275758227889 19293092157569456818670917)
                  ·
                    refine ⟨3617454779544273153500797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19293092157569456818670917 3617454779544273153500797)
                    ·
                      refine ⟨1356545542329102432562799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3617454779544273153500797 1356545542329102432562799)
                      ·
                        rfl

theorem cell23_2641863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_2641863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641863 prefixEnd_2641863 := by exact prefixLift 2641863
  have htrace : WordTrace (prefixWord ++ tailWord_2641863) baseStart_2641863 baseEnd_2641863 := by
    simpa [prefixWord, tailWord_2641863, baseEnd_2641863] using wordTrace_append hprefix tailTrace_2641863
  have hstable : (prefixWord ++ tailWord_2641863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641863).length < 2 ^ (prefixWord ++ tailWord_2641863).sum := by decide
  have hdescent : baseEnd_2641863 < baseStart_2641863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641881 : List Nat := [1, 2, 1, 2, 7, 1, 1, 2, 1, 3, 2]
def baseStart_2641881 : Nat := 118140960795 + 2641881 * 2 ^ 59
def prefixEnd_2641881 : Nat := 4983230072969 + 3 ^ 40 * 2641881 * 2
def baseEnd_2641881 : Nat := 1356554784980883362137717

theorem tailTrace_2641881 : CollatzResearch.WordTrace tailWord_2641881 prefixEnd_2641881 1356554784980883362137717 := by
  unfold tailWord_2641881
  simp only [CollatzResearch.WordTrace]
  refine ⟨96357316141923809198253497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64238210761282539465502331 96357316141923809198253497)
  ·
    refine ⟨72267987106442856898690123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96357316141923809198253497 72267987106442856898690123)
    ·
      refine ⟨108401980659664285348035185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72267987106442856898690123 108401980659664285348035185)
      ·
        refine ⟨81301485494748214011026389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108401980659664285348035185 81301485494748214011026389)
        ·
          refine ⟨1905503566283161265883431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 81301485494748214011026389 1905503566283161265883431)
          ·
            refine ⟨2858255349424741898825147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1905503566283161265883431 2858255349424741898825147)
            ·
              refine ⟨4287383024137112848237721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2858255349424741898825147 4287383024137112848237721)
              ·
                refine ⟨3215537268102834636178291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4287383024137112848237721 3215537268102834636178291)
                ·
                  refine ⟨4823305902154251954267437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3215537268102834636178291 4823305902154251954267437)
                  ·
                    refine ⟨1808739713307844482850289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4823305902154251954267437 1808739713307844482850289)
                    ·
                      refine ⟨1356554784980883362137717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1808739713307844482850289 1356554784980883362137717)
                      ·
                        rfl

theorem cell23_2641881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 1, 3, 2].length) (baseStart_2641881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641881 prefixEnd_2641881 := by exact prefixLift 2641881
  have htrace : WordTrace (prefixWord ++ tailWord_2641881) baseStart_2641881 baseEnd_2641881 := by
    simpa [prefixWord, tailWord_2641881, baseEnd_2641881] using wordTrace_append hprefix tailTrace_2641881
  have hstable : (prefixWord ++ tailWord_2641881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641881).length < 2 ^ (prefixWord ++ tailWord_2641881).sum := by decide
  have hdescent : baseEnd_2641881 < baseStart_2641881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641917 : List Nat := [1, 4, 1, 1, 1, 2, 6, 2, 5]
def baseStart_2641917 : Nat := 118140960795 + 2641917 * 2 ^ 59
def prefixEnd_2641917 : Nat := 4983230072969 + 3 ^ 40 * 2641917 * 2
def baseEnd_2641917 : Nat := 150730363364938357920839

theorem tailTrace_2641917 : CollatzResearch.WordTrace tailWord_2641917 prefixEnd_2641917 150730363364938357920839 := by
  unfold tailWord_2641917
  simp only [CollatzResearch.WordTrace]
  refine ⟨96358629169793387346564005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64239086113195591564376003 96358629169793387346564005)
  ·
    refine ⟨18067242969336260127480751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96358629169793387346564005 18067242969336260127480751)
    ·
      refine ⟨27100864454004390191221127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18067242969336260127480751 27100864454004390191221127)
      ·
        refine ⟨40651296681006585286831691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27100864454004390191221127 40651296681006585286831691)
        ·
          refine ⟨60976945021509877930247537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40651296681006585286831691 60976945021509877930247537)
          ·
            refine ⟨45732708766132408447685653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60976945021509877930247537 45732708766132408447685653)
            ·
              refine ⟨2143720723412456645985265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45732708766132408447685653 2143720723412456645985265)
              ·
                refine ⟨1607790542559342484488949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2143720723412456645985265 1607790542559342484488949)
                ·
                  refine ⟨150730363364938357920839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1607790542559342484488949 150730363364938357920839)
                  ·
                    rfl

theorem cell23_2641917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_2641917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641917 prefixEnd_2641917 := by exact prefixLift 2641917
  have htrace : WordTrace (prefixWord ++ tailWord_2641917) baseStart_2641917 baseEnd_2641917 := by
    simpa [prefixWord, tailWord_2641917, baseEnd_2641917] using wordTrace_append hprefix tailTrace_2641917
  have hstable : (prefixWord ++ tailWord_2641917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641917).length < 2 ^ (prefixWord ++ tailWord_2641917).sum := by decide
  have hdescent : baseEnd_2641917 < baseStart_2641917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2641993 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 1, 2, 6]
def baseStart_2641993 : Nat := 118140960795 + 2641993 * 2 ^ 59
def prefixEnd_2641993 : Nat := 4983230072969 + 3 ^ 40 * 2641993 * 2
def baseEnd_2641993 : Nat := 1356612294814186923937201

theorem tailTrace_2641993 : CollatzResearch.WordTrace tailWord_2641993 prefixEnd_2641993 1356612294814186923937201 := by
  unfold tailWord_2641993
  simp only [CollatzResearch.WordTrace]
  refine ⟨96361401117518052326330633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64240934078345368217553755 96361401117518052326330633)
  ·
    refine ⟨72271050838138539244747975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96361401117518052326330633 72271050838138539244747975)
    ·
      refine ⟨108406576257207808867121963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72271050838138539244747975 108406576257207808867121963)
      ·
        refine ⟨162609864385811713300682945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108406576257207808867121963 162609864385811713300682945)
        ·
          refine ⟨121957398289358784975512209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162609864385811713300682945 121957398289358784975512209)
          ·
            refine ⟨91468048717019088731634157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121957398289358784975512209 91468048717019088731634157)
            ·
              refine ⟨34300518268882158274362809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91468048717019088731634157 34300518268882158274362809)
              ·
                refine ⟨25725388701661618705772107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34300518268882158274362809 25725388701661618705772107)
                ·
                  refine ⟨38588083052492428058658161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25725388701661618705772107 38588083052492428058658161)
                  ·
                    refine ⟨28941062289369321043993621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38588083052492428058658161 28941062289369321043993621)
                    ·
                      refine ⟨1356612294814186923937201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28941062289369321043993621 1356612294814186923937201)
                      ·
                        rfl

theorem cell23_2641993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_2641993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2641993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2641993 prefixEnd_2641993 := by exact prefixLift 2641993
  have htrace : WordTrace (prefixWord ++ tailWord_2641993) baseStart_2641993 baseEnd_2641993 := by
    simpa [prefixWord, tailWord_2641993, baseEnd_2641993] using wordTrace_append hprefix tailTrace_2641993
  have hstable : (prefixWord ++ tailWord_2641993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2641993).length < 2 ^ (prefixWord ++ tailWord_2641993).sum := by decide
  have hdescent : baseEnd_2641993 < baseStart_2641993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2641993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642034 : List Nat := [3, 2, 1, 2, 2, 2, 3, 1, 3, 1, 3]
def baseStart_2642034 : Nat := 118140960795 + 2642034 * 2 ^ 59
def prefixEnd_2642034 : Nat := 4983230072969 + 3 ^ 40 * 2642034 * 2
def baseEnd_2642034 : Nat := 1356633347521021263524513

theorem tailTrace_2642034 : CollatzResearch.WordTrace tailWord_2642034 prefixEnd_2642034 1356633347521021263524513 := by
  unfold tailWord_2642034
  simp only [CollatzResearch.WordTrace]
  refine ⟨24090724127592379082143289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64241931006913010885715437 24090724127592379082143289)
  ·
    refine ⟨18068043095694284311607467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24090724127592379082143289 18068043095694284311607467)
    ·
      refine ⟨27102064643541426467411201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18068043095694284311607467 27102064643541426467411201)
      ·
        refine ⟨20326548482656069850558401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27102064643541426467411201 20326548482656069850558401)
        ·
          refine ⟨15244911361992052387918801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20326548482656069850558401 15244911361992052387918801)
          ·
            refine ⟨11433683521494039290939101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15244911361992052387918801 11433683521494039290939101)
            ·
              refine ⟨4287631320560264734102163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11433683521494039290939101 4287631320560264734102163)
              ·
                refine ⟨6431446980840397101153245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4287631320560264734102163 6431446980840397101153245)
                ·
                  refine ⟨2411792617815148912932467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6431446980840397101153245 2411792617815148912932467)
                  ·
                    refine ⟨3617688926722723369398701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2411792617815148912932467 3617688926722723369398701)
                    ·
                      refine ⟨1356633347521021263524513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3617688926722723369398701 1356633347521021263524513)
                      ·
                        rfl

theorem cell23_2642034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_2642034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642034 prefixEnd_2642034 := by exact prefixLift 2642034
  have htrace : WordTrace (prefixWord ++ tailWord_2642034) baseStart_2642034 baseEnd_2642034 := by
    simpa [prefixWord, tailWord_2642034, baseEnd_2642034] using wordTrace_append hprefix tailTrace_2642034
  have hstable : (prefixWord ++ tailWord_2642034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642034).length < 2 ^ (prefixWord ++ tailWord_2642034).sum := by decide
  have hdescent : baseEnd_2642034 < baseStart_2642034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642040 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 3, 1, 4]
def baseStart_2642040 : Nat := 118140960795 + 2642040 * 2 ^ 59
def prefixEnd_2642040 : Nat := 4983230072969 + 3 ^ 40 * 2642040 * 2
def baseEnd_2642040 : Nat := 1356636428404948240049485

theorem tailTrace_2642040 : CollatzResearch.WordTrace tailWord_2642040 prefixEnd_2642040 1356636428404948240049485 := by
  unfold tailWord_2642040
  simp only [CollatzResearch.WordTrace]
  refine ⟨48181557674173889676645787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64242076898898519568861049 48181557674173889676645787)
  ·
    refine ⟨72272336511260834514968681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48181557674173889676645787 72272336511260834514968681)
    ·
      refine ⟨54204252383445625886226511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72272336511260834514968681 54204252383445625886226511)
      ·
        refine ⟨81306378575168438829339767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54204252383445625886226511 81306378575168438829339767)
        ·
          refine ⟨121959567862752658244009651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81306378575168438829339767 121959567862752658244009651)
          ·
            refine ⟨182939351794128987366014477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121959567862752658244009651 182939351794128987366014477)
            ·
              refine ⟨68602256922798370262255429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182939351794128987366014477 68602256922798370262255429)
              ·
                refine ⟨12862923173024694424172893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68602256922798370262255429 12862923173024694424172893)
                ·
                  refine ⟨4823596189884260409064835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12862923173024694424172893 4823596189884260409064835)
                  ·
                    refine ⟨7235394284826390613597253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4823596189884260409064835 7235394284826390613597253)
                    ·
                      refine ⟨1356636428404948240049485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7235394284826390613597253 1356636428404948240049485)
                      ·
                        rfl

theorem cell23_2642040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_2642040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642040 prefixEnd_2642040 := by exact prefixLift 2642040
  have htrace : WordTrace (prefixWord ++ tailWord_2642040) baseStart_2642040 baseEnd_2642040 := by
    simpa [prefixWord, tailWord_2642040, baseEnd_2642040] using wordTrace_append hprefix tailTrace_2642040
  have hstable : (prefixWord ++ tailWord_2642040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642040).length < 2 ^ (prefixWord ++ tailWord_2642040).sum := by decide
  have hdescent : baseEnd_2642040 < baseStart_2642040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642077 : List Nat := [1, 4, 2, 1, 1, 3, 3, 1, 1, 1, 5]
def baseStart_2642077 : Nat := 118140960795 + 2642077 * 2 ^ 59
def prefixEnd_2642077 : Nat := 4983230072969 + 3 ^ 40 * 2642077 * 2
def baseEnd_2642077 : Nat := 1356655427189164595286815

theorem tailTrace_2642077 : CollatzResearch.WordTrace tailWord_2642077 prefixEnd_2642077 1356655427189164595286815 := by
  unfold tailWord_2642077
  simp only [CollatzResearch.WordTrace]
  refine ⟨96364464849213734672388485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64242976566142489781592323 96364464849213734672388485)
  ·
    refine ⟨18068337159227575251072841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96364464849213734672388485 18068337159227575251072841)
    ·
      refine ⟨13551252869420681438304631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18068337159227575251072841 13551252869420681438304631)
      ·
        refine ⟨20326879304131022157456947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13551252869420681438304631 20326879304131022157456947)
        ·
          refine ⟨30490318956196533236185421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20326879304131022157456947 30490318956196533236185421)
          ·
            refine ⟨11433869608573699963569533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30490318956196533236185421 11433869608573699963569533)
            ·
              refine ⟨4287701103215137486338575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11433869608573699963569533 4287701103215137486338575)
              ·
                refine ⟨6431551654822706229507863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4287701103215137486338575 6431551654822706229507863)
                ·
                  refine ⟨9647327482234059344261795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6431551654822706229507863 9647327482234059344261795)
                  ·
                    refine ⟨14470991223351089016392693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9647327482234059344261795 14470991223351089016392693)
                    ·
                      refine ⟨1356655427189164595286815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14470991223351089016392693 1356655427189164595286815)
                      ·
                        rfl

theorem cell23_2642077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_2642077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642077 prefixEnd_2642077 := by exact prefixLift 2642077
  have htrace : WordTrace (prefixWord ++ tailWord_2642077) baseStart_2642077 baseEnd_2642077 := by
    simpa [prefixWord, tailWord_2642077, baseEnd_2642077] using wordTrace_append hprefix tailTrace_2642077
  have hstable : (prefixWord ++ tailWord_2642077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642077).length < 2 ^ (prefixWord ++ tailWord_2642077).sum := by decide
  have hdescent : baseEnd_2642077 < baseStart_2642077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642107 : List Nat := [1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 3]
def baseStart_2642107 : Nat := 118140960795 + 2642107 * 2 ^ 59
def prefixEnd_2642107 : Nat := 4983230072969 + 3 ^ 40 * 2642107 * 2
def baseEnd_2642107 : Nat := 1356670831608799477911677

theorem tailTrace_2642107 : CollatzResearch.WordTrace tailWord_2642107 prefixEnd_2642107 1356670831608799477911677 := by
  unfold tailWord_2642107
  simp only [CollatzResearch.WordTrace]
  refine ⟨96365559039105049795980575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64243706026070033197320383 96365559039105049795980575)
  ·
    refine ⟨144548338558657574693970863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96365559039105049795980575 144548338558657574693970863)
    ·
      refine ⟨216822507837986362040956295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144548338558657574693970863 216822507837986362040956295)
      ·
        refine ⟨325233761756979543061434443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216822507837986362040956295 325233761756979543061434443)
        ·
          refine ⟨487850642635469314592151665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325233761756979543061434443 487850642635469314592151665)
          ·
            refine ⟨365887981976601985944113749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 487850642635469314592151665 365887981976601985944113749)
            ·
              refine ⟨4287749788788304522782583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 365887981976601985944113749 4287749788788304522782583)
              ·
                refine ⟨6431624683182456784173875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4287749788788304522782583 6431624683182456784173875)
                ·
                  refine ⟨9647437024773685176260813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6431624683182456784173875 9647437024773685176260813)
                  ·
                    refine ⟨3617788884290131941097805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9647437024773685176260813 3617788884290131941097805)
                    ·
                      refine ⟨1356670831608799477911677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3617788884290131941097805 1356670831608799477911677)
                      ·
                        rfl

theorem cell23_2642107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 3].length) (baseStart_2642107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642107 prefixEnd_2642107 := by exact prefixLift 2642107
  have htrace : WordTrace (prefixWord ++ tailWord_2642107) baseStart_2642107 baseEnd_2642107 := by
    simpa [prefixWord, tailWord_2642107, baseEnd_2642107] using wordTrace_append hprefix tailTrace_2642107
  have hstable : (prefixWord ++ tailWord_2642107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642107).length < 2 ^ (prefixWord ++ tailWord_2642107).sum := by decide
  have hdescent : baseEnd_2642107 < baseStart_2642107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642120 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_2642120 : Nat := 118140960795 + 2642120 * 2 ^ 59
def prefixEnd_2642120 : Nat := 4983230072969 + 3 ^ 40 * 2642120 * 2
def baseEnd_2642120 : Nat := 1356677506857307927049117

theorem tailTrace_2642120 : CollatzResearch.WordTrace tailWord_2642120 prefixEnd_2642120 1356677506857307927049117 := by
  unfold tailWord_2642120
  simp only [CollatzResearch.WordTrace]
  refine ⟨48183016594028976508101907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64244022125371968677469209 48183016594028976508101907)
  ·
    refine ⟨72274524891043464762152861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48183016594028976508101907 72274524891043464762152861)
    ·
      refine ⟨27102946834141299285807323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72274524891043464762152861 27102946834141299285807323)
      ·
        refine ⟨40654420251211948928710985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27102946834141299285807323 40654420251211948928710985)
        ·
          refine ⟨30490815188408961696533239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40654420251211948928710985 30490815188408961696533239)
          ·
            refine ⟨45736222782613442544799859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30490815188408961696533239 45736222782613442544799859)
            ·
              refine ⟨68604334173920163817199789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45736222782613442544799859 68604334173920163817199789)
              ·
                refine ⟨25726625315220061431449921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68604334173920163817199789 25726625315220061431449921)
                ·
                  refine ⟨19294968986415046073587441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25726625315220061431449921 19294968986415046073587441)
                  ·
                    refine ⟨14471226739811284555190581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19294968986415046073587441 14471226739811284555190581)
                    ·
                      refine ⟨1356677506857307927049117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14471226739811284555190581 1356677506857307927049117)
                      ·
                        rfl

theorem cell23_2642120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_2642120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642120 prefixEnd_2642120 := by exact prefixLift 2642120
  have htrace : WordTrace (prefixWord ++ tailWord_2642120) baseStart_2642120 baseEnd_2642120 := by
    simpa [prefixWord, tailWord_2642120, baseEnd_2642120] using wordTrace_append hprefix tailTrace_2642120
  have hstable : (prefixWord ++ tailWord_2642120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642120).length < 2 ^ (prefixWord ++ tailWord_2642120).sum := by decide
  have hdescent : baseEnd_2642120 < baseStart_2642120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642141 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_2642141 : Nat := 118140960795 + 2642141 * 2 ^ 59
def prefixEnd_2642141 : Nat := 4983230072969 + 3 ^ 40 * 2642141 * 2
def baseEnd_2642141 : Nat := 1356688289951052344886521

theorem tailTrace_2642141 : CollatzResearch.WordTrace tailWord_2642141 prefixEnd_2642141 1356688289951052344886521 := by
  unfold tailWord_2642141
  simp only [CollatzResearch.WordTrace]
  refine ⟨96366799120981873602718277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64244532747321249068478851 96366799120981873602718277)
  ·
    refine ⟨18068774835184101300509677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96366799120981873602718277 18068774835184101300509677)
    ·
      refine ⟨6775790563194037987691129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18068774835184101300509677 6775790563194037987691129)
      ·
        refine ⟨5081842922395528490768347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6775790563194037987691129 5081842922395528490768347)
        ·
          refine ⟨7622764383593292736152521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5081842922395528490768347 7622764383593292736152521)
          ·
            refine ⟨5717073287694969552114391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7622764383593292736152521 5717073287694969552114391)
            ·
              refine ⟨8575609931542454328171587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5717073287694969552114391 8575609931542454328171587)
              ·
                refine ⟨12863414897313681492257381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8575609931542454328171587 12863414897313681492257381)
                ·
                  refine ⟨2411890293246315279798259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12863414897313681492257381 2411890293246315279798259)
                  ·
                    refine ⟨3617835439869472919697389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2411890293246315279798259 3617835439869472919697389)
                    ·
                      refine ⟨1356688289951052344886521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3617835439869472919697389 1356688289951052344886521)
                      ·
                        rfl

theorem cell23_2642141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_2642141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642141 prefixEnd_2642141 := by exact prefixLift 2642141
  have htrace : WordTrace (prefixWord ++ tailWord_2642141) baseStart_2642141 baseEnd_2642141 := by
    simpa [prefixWord, tailWord_2642141, baseEnd_2642141] using wordTrace_append hprefix tailTrace_2642141
  have hstable : (prefixWord ++ tailWord_2642141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642141).length < 2 ^ (prefixWord ++ tailWord_2642141).sum := by decide
  have hdescent : baseEnd_2642141 < baseStart_2642141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642197 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 4, 3, 3]
def baseStart_2642197 : Nat := 118140960795 + 2642197 * 2 ^ 59
def prefixEnd_2642197 : Nat := 4983230072969 + 3 ^ 40 * 2642197 * 2
def baseEnd_2642197 : Nat := 1356717044867704125786263

theorem tailTrace_2642197 : CollatzResearch.WordTrace tailWord_2642197 prefixEnd_2642197 1356717044867704125786263 := by
  unfold tailWord_2642197
  simp only [CollatzResearch.WordTrace]
  refine ⟨96368841608778995166756845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64245894405852663444504563 96368841608778995166756845)
  ·
    refine ⟨36138315603292123187533817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96368841608778995166756845 36138315603292123187533817)
    ·
      refine ⟨27103736702469092390650363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36138315603292123187533817 27103736702469092390650363)
      ·
        refine ⟨40655605053703638585975545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27103736702469092390650363 40655605053703638585975545)
        ·
          refine ⟨30491703790277728939481659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40655605053703638585975545 30491703790277728939481659)
          ·
            refine ⟨45737555685416593409222489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30491703790277728939481659 45737555685416593409222489)
            ·
              refine ⟨34303166764062445056916867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45737555685416593409222489 34303166764062445056916867)
              ·
                refine ⟨51454750146093667585375301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34303166764062445056916867 51454750146093667585375301)
                ·
                  refine ⟨9647765652392562672257869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51454750146093667585375301 9647765652392562672257869)
                  ·
                    refine ⟨3617912119647211002096701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9647765652392562672257869 3617912119647211002096701)
                    ·
                      refine ⟨1356717044867704125786263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3617912119647211002096701 1356717044867704125786263)
                      ·
                        rfl

theorem cell23_2642197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_2642197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642197 prefixEnd_2642197 := by exact prefixLift 2642197
  have htrace : WordTrace (prefixWord ++ tailWord_2642197) baseStart_2642197 baseEnd_2642197 := by
    simpa [prefixWord, tailWord_2642197, baseEnd_2642197] using wordTrace_append hprefix tailTrace_2642197
  have hstable : (prefixWord ++ tailWord_2642197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642197).length < 2 ^ (prefixWord ++ tailWord_2642197).sum := by decide
  have hdescent : baseEnd_2642197 < baseStart_2642197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642234 : List Nat := [3, 1, 1, 1, 4, 3, 2, 1, 2, 5]
def baseStart_2642234 : Nat := 118140960795 + 2642234 * 2 ^ 59
def prefixEnd_2642234 : Nat := 4983230072969 + 3 ^ 40 * 2642234 * 2
def baseEnd_2642234 : Nat := 452245347883973493674531

theorem tailTrace_2642234 : CollatzResearch.WordTrace tailWord_2642234 prefixEnd_2642234 452245347883973493674531 := by
  unfold tailWord_2642234
  simp only [CollatzResearch.WordTrace]
  refine ⟨24092547777411237621463439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64246794073096633657235837 24092547777411237621463439)
  ·
    refine ⟨36138821666116856432195159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24092547777411237621463439 36138821666116856432195159)
    ·
      refine ⟨54208232499175284648292739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36138821666116856432195159 54208232499175284648292739)
      ·
        refine ⟨81312348748762926972439109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54208232499175284648292739 81312348748762926972439109)
        ·
          refine ⟨15246065390393048807332333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81312348748762926972439109 15246065390393048807332333)
          ·
            refine ⟨5717274521397393302749625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15246065390393048807332333 5717274521397393302749625)
            ·
              refine ⟨4287955891048044977062219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5717274521397393302749625 4287955891048044977062219)
              ·
                refine ⟨6431933836572067465593329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4287955891048044977062219 6431933836572067465593329)
                ·
                  refine ⟨4823950377429050599194997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6431933836572067465593329 4823950377429050599194997)
                  ·
                    refine ⟨452245347883973493674531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4823950377429050599194997 452245347883973493674531)
                    ·
                      rfl

theorem cell23_2642234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 2, 5].length) (baseStart_2642234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642234 prefixEnd_2642234 := by exact prefixLift 2642234
  have htrace : WordTrace (prefixWord ++ tailWord_2642234) baseStart_2642234 baseEnd_2642234 := by
    simpa [prefixWord, tailWord_2642234, baseEnd_2642234] using wordTrace_append hprefix tailTrace_2642234
  have hstable : (prefixWord ++ tailWord_2642234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642234).length < 2 ^ (prefixWord ++ tailWord_2642234).sum := by decide
  have hdescent : baseEnd_2642234 < baseStart_2642234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642287 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 3]
def baseStart_2642287 : Nat := 118140960795 + 2642287 * 2 ^ 59
def prefixEnd_2642287 : Nat := 4983230072969 + 3 ^ 40 * 2642287 * 2
def baseEnd_2642287 : Nat := 1356763258126608773660849

theorem tailTrace_2642287 : CollatzResearch.WordTrace tailWord_2642287 prefixEnd_2642287 1356763258126608773660849 := by
  unfold tailWord_2642287
  simp only [CollatzResearch.WordTrace]
  refine ⟨96372124178452940537533115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64248082785635293691688743 96372124178452940537533115)
  ·
    refine ⟨144558186267679410806299673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96372124178452940537533115 144558186267679410806299673)
    ·
      refine ⟨108418639700759558104724755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144558186267679410806299673 108418639700759558104724755)
      ·
        refine ⟨162627959551139337157087133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108418639700759558104724755 162627959551139337157087133)
        ·
          refine ⟨60985484831677251433907675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162627959551139337157087133 60985484831677251433907675)
          ·
            refine ⟨91478227247515877150861513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60985484831677251433907675 91478227247515877150861513)
            ·
              refine ⟨68608670435636907863146135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91478227247515877150861513 68608670435636907863146135)
              ·
                refine ⟨102913005653455361794719203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68608670435636907863146135 102913005653455361794719203)
                ·
                  refine ⟨154369508480183042692078805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102913005653455361794719203 154369508480183042692078805)
                  ·
                    refine ⟨3618035355004290063095597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 154369508480183042692078805 3618035355004290063095597)
                    ·
                      refine ⟨1356763258126608773660849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3618035355004290063095597 1356763258126608773660849)
                      ·
                        rfl

theorem cell23_2642287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 3].length) (baseStart_2642287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642287 prefixEnd_2642287 := by exact prefixLift 2642287
  have htrace : WordTrace (prefixWord ++ tailWord_2642287) baseStart_2642287 baseEnd_2642287 := by
    simpa [prefixWord, tailWord_2642287, baseEnd_2642287] using wordTrace_append hprefix tailTrace_2642287
  have hstable : (prefixWord ++ tailWord_2642287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642287).length < 2 ^ (prefixWord ++ tailWord_2642287).sum := by decide
  have hdescent : baseEnd_2642287 < baseStart_2642287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642354 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 6, 4]
def baseStart_2642354 : Nat := 118140960795 + 2642354 * 2 ^ 59
def prefixEnd_2642354 : Nat := 4983230072969 + 3 ^ 40 * 2642354 * 2
def baseEnd_2642354 : Nat := 452265887110153337174347

theorem tailTrace_2642354 : CollatzResearch.WordTrace tailWord_2642354 prefixEnd_2642354 452265887110153337174347 := by
  unfold tailWord_2642354
  simp only [CollatzResearch.WordTrace]
  refine ⟨24093641967302552745055529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64249711912806807320148077 24093641967302552745055529)
  ·
    refine ⟨18070231475476914558791647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24093641967302552745055529 18070231475476914558791647)
    ·
      refine ⟨27105347213215371838187471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18070231475476914558791647 27105347213215371838187471)
      ·
        refine ⟨40658020819823057757281207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27105347213215371838187471 40658020819823057757281207)
        ·
          refine ⟨60987031229734586635921811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40658020819823057757281207 60987031229734586635921811)
          ·
            refine ⟨91480546844601879953882717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60987031229734586635921811 91480546844601879953882717)
            ·
              refine ⟨34305205066725704982706019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91480546844601879953882717 34305205066725704982706019)
              ·
                refine ⟨51457807600088557474059029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34305205066725704982706019 51457807600088557474059029)
                ·
                  refine ⟨2412084731254151131596517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51457807600088557474059029 2412084731254151131596517)
                  ·
                    refine ⟨452265887110153337174347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2412084731254151131596517 452265887110153337174347)
                    ·
                      rfl

theorem cell23_2642354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_2642354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642354 prefixEnd_2642354 := by exact prefixLift 2642354
  have htrace : WordTrace (prefixWord ++ tailWord_2642354) baseStart_2642354 baseEnd_2642354 := by
    simpa [prefixWord, tailWord_2642354, baseEnd_2642354] using wordTrace_append hprefix tailTrace_2642354
  have hstable : (prefixWord ++ tailWord_2642354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642354).length < 2 ^ (prefixWord ++ tailWord_2642354).sum := by decide
  have hdescent : baseEnd_2642354 < baseStart_2642354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642361 : List Nat := [1, 2, 1, 4, 3, 1, 2, 3, 1, 1, 4]
def baseStart_2642361 : Nat := 118140960795 + 2642361 * 2 ^ 59
def prefixEnd_2642361 : Nat := 4983230072969 + 3 ^ 40 * 2642361 * 2
def baseEnd_2642361 : Nat := 1356801255695041484135509

theorem tailTrace_2642361 : CollatzResearch.WordTrace tailWord_2642361 prefixEnd_2642361 1356801255695041484135509 := by
  unfold tailWord_2642361
  simp only [CollatzResearch.WordTrace]
  refine ⟨96374823180184851175726937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64249882120123234117151291 96374823180184851175726937)
  ·
    refine ⟨72281117385138638381795203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96374823180184851175726937 72281117385138638381795203)
    ·
      refine ⟨108421676077707957572692805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72281117385138638381795203 108421676077707957572692805)
      ·
        refine ⟨20329064264570242044879901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108421676077707957572692805 20329064264570242044879901)
        ·
          refine ⟨7623399099213840766829963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20329064264570242044879901 7623399099213840766829963)
          ·
            refine ⟨11435098648820761150244945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7623399099213840766829963 11435098648820761150244945)
            ·
              refine ⟨8576323986615570862683709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11435098648820761150244945 8576323986615570862683709)
              ·
                refine ⟨3216121494980839073506391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8576323986615570862683709 3216121494980839073506391)
                ·
                  refine ⟨4824182242471258610259587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3216121494980839073506391 4824182242471258610259587)
                  ·
                    refine ⟨7236273363706887915389381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4824182242471258610259587 7236273363706887915389381)
                    ·
                      refine ⟨1356801255695041484135509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7236273363706887915389381 1356801255695041484135509)
                      ·
                        rfl

theorem cell23_2642361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_2642361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642361 prefixEnd_2642361 := by exact prefixLift 2642361
  have htrace : WordTrace (prefixWord ++ tailWord_2642361) baseStart_2642361 baseEnd_2642361 := by
    simpa [prefixWord, tailWord_2642361, baseEnd_2642361] using wordTrace_append hprefix tailTrace_2642361
  have hstable : (prefixWord ++ tailWord_2642361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642361).length < 2 ^ (prefixWord ++ tailWord_2642361).sum := by decide
  have hdescent : baseEnd_2642361 < baseStart_2642361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642372 : List Nat := [2, 3, 3, 2, 3, 1, 1, 1, 3, 1, 3]
def baseStart_2642372 : Nat := 118140960795 + 2642372 * 2 ^ 59
def prefixEnd_2642372 : Nat := 4983230072969 + 3 ^ 40 * 2642372 * 2
def baseEnd_2642372 : Nat := 1356806903982240941097959

theorem tailTrace_2642372 : CollatzResearch.WordTrace tailWord_2642372 prefixEnd_2642372 1356806903982240941097959 := by
  unfold tailWord_2642372
  simp only [CollatzResearch.WordTrace]
  refine ⟨48187612191572500027188685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64250149588763333369584913 48187612191572500027188685)
  ·
    refine ⟨18070354571839687510195757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48187612191572500027188685 18070354571839687510195757)
    ·
      refine ⟨6776382964439882816323409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18070354571839687510195757 6776382964439882816323409)
      ·
        refine ⟨5082287223329912112242557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6776382964439882816323409 5082287223329912112242557)
        ·
          refine ⟨1905857708748717042090959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5082287223329912112242557 1905857708748717042090959)
          ·
            refine ⟨2858786563123075563136439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1905857708748717042090959 2858786563123075563136439)
            ·
              refine ⟨4288179844684613344704659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2858786563123075563136439 4288179844684613344704659)
              ·
                refine ⟨6432269767026920017056989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4288179844684613344704659 6432269767026920017056989)
                ·
                  refine ⟨2412101162635095006396371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6432269767026920017056989 2412101162635095006396371)
                  ·
                    refine ⟨3618151743952642509594557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2412101162635095006396371 3618151743952642509594557)
                    ·
                      refine ⟨1356806903982240941097959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3618151743952642509594557 1356806903982240941097959)
                      ·
                        rfl

theorem cell23_2642372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_2642372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642372 prefixEnd_2642372 := by exact prefixLift 2642372
  have htrace : WordTrace (prefixWord ++ tailWord_2642372) baseStart_2642372 baseEnd_2642372 := by
    simpa [prefixWord, tailWord_2642372, baseEnd_2642372] using wordTrace_append hprefix tailTrace_2642372
  have hstable : (prefixWord ++ tailWord_2642372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642372).length < 2 ^ (prefixWord ++ tailWord_2642372).sum := by decide
  have hdescent : baseEnd_2642372 < baseStart_2642372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642388 : List Nat := [2, 4, 1, 2, 2, 2, 1, 3, 2, 4]
def baseStart_2642388 : Nat := 118140960795 + 2642388 * 2 ^ 59
def prefixEnd_2642388 : Nat := 4983230072969 + 3 ^ 40 * 2642388 * 2
def baseEnd_2642388 : Nat := 452271706557570959499295

theorem tailTrace_2642388 : CollatzResearch.WordTrace tailWord_2642388 prefixEnd_2642388 452271706557570959499295 := by
  unfold tailWord_2642388
  simp only [CollatzResearch.WordTrace]
  refine ⟨48187903975543517393479909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64250538634058023191306545 48187903975543517393479909)
  ·
    refine ⟨9035231995414409511277483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48187903975543517393479909 9035231995414409511277483)
    ·
      refine ⟨13552847993121614266916225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9035231995414409511277483 13552847993121614266916225)
      ·
        refine ⟨10164635994841210700187169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13552847993121614266916225 10164635994841210700187169)
        ·
          refine ⟨7623476996130908025140377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10164635994841210700187169 7623476996130908025140377)
          ·
            refine ⟨5717607747098181018855283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7623476996130908025140377 5717607747098181018855283)
            ·
              refine ⟨8576411620647271528282925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5717607747098181018855283 8576411620647271528282925)
              ·
                refine ⟨3216154357742726823106097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8576411620647271528282925 3216154357742726823106097)
                ·
                  refine ⟨2412115768307045117329573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3216154357742726823106097 2412115768307045117329573)
                  ·
                    refine ⟨452271706557570959499295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2412115768307045117329573 452271706557570959499295)
                    ·
                      rfl

theorem cell23_2642388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_2642388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642388 prefixEnd_2642388 := by exact prefixLift 2642388
  have htrace : WordTrace (prefixWord ++ tailWord_2642388) baseStart_2642388 baseEnd_2642388 := by
    simpa [prefixWord, tailWord_2642388, baseEnd_2642388] using wordTrace_append hprefix tailTrace_2642388
  have hstable : (prefixWord ++ tailWord_2642388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642388).length < 2 ^ (prefixWord ++ tailWord_2642388).sum := by decide
  have hdescent : baseEnd_2642388 < baseStart_2642388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642444 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 1, 8]
def baseStart_2642444 : Nat := 118140960795 + 2642444 * 2 ^ 59
def prefixEnd_2642444 : Nat := 4983230072969 + 3 ^ 40 * 2642444 * 2
def baseEnd_2642444 : Nat := 452281291529788219799209

theorem tailTrace_2642444 : CollatzResearch.WordTrace tailWord_2642444 prefixEnd_2642444 452281291529788219799209 := by
  unfold tailWord_2642444
  simp only [CollatzResearch.WordTrace]
  refine ⟨48188925219442078175499193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64251900292589437567332257 48188925219442078175499193)
  ·
    refine ⟨36141693914581558631624395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48188925219442078175499193 36141693914581558631624395)
    ·
      refine ⟨54212540871872337947436593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36141693914581558631624395 54212540871872337947436593)
      ·
        refine ⟨40659405653904253460577445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54212540871872337947436593 40659405653904253460577445)
        ·
          refine ⟨7623638560107047523858271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40659405653904253460577445 7623638560107047523858271)
          ·
            refine ⟨11435457840160571285787407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7623638560107047523858271 11435457840160571285787407)
            ·
              refine ⟨17153186760240856928681111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11435457840160571285787407 17153186760240856928681111)
              ·
                refine ⟨25729780140361285393021667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17153186760240856928681111 25729780140361285393021667)
                ·
                  refine ⟨38594670210541928089532501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25729780140361285393021667 38594670210541928089532501)
                  ·
                    refine ⟨452281291529788219799209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38594670210541928089532501 452281291529788219799209)
                    ·
                      rfl

theorem cell23_2642444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_2642444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642444 prefixEnd_2642444 := by exact prefixLift 2642444
  have htrace : WordTrace (prefixWord ++ tailWord_2642444) baseStart_2642444 baseEnd_2642444 := by
    simpa [prefixWord, tailWord_2642444, baseEnd_2642444] using wordTrace_append hprefix tailTrace_2642444
  have hstable : (prefixWord ++ tailWord_2642444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642444).length < 2 ^ (prefixWord ++ tailWord_2642444).sum := by decide
  have hdescent : baseEnd_2642444 < baseStart_2642444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642445 : List Nat := [1, 7, 1, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_2642445 : Nat := 118140960795 + 2642445 * 2 ^ 59
def prefixEnd_2642445 : Nat := 4983230072969 + 3 ^ 40 * 2642445 * 2
def baseEnd_2642445 : Nat := 1356844388070019155485123

theorem tailTrace_2642445 : CollatzResearch.WordTrace tailWord_2642445 prefixEnd_2642445 1356844388070019155485123 := by
  unfold tailWord_2642445
  simp only [CollatzResearch.WordTrace]
  refine ⟨96377886911880533521784789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64251924607920355681189859 96377886911880533521784789)
  ·
    refine ⟨2258856724497200004416831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 96377886911880533521784789 2258856724497200004416831)
    ·
      refine ⟨3388285086745800006625247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2258856724497200004416831 3388285086745800006625247)
      ·
        refine ⟨5082427630118700009937871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3388285086745800006625247 5082427630118700009937871)
        ·
          refine ⟨7623641445178050014906807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5082427630118700009937871 7623641445178050014906807)
          ·
            refine ⟨11435462167767075022360211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7623641445178050014906807 11435462167767075022360211)
            ·
              refine ⟨17153193251650612533540317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11435462167767075022360211 17153193251650612533540317)
              ·
                refine ⟨6432447469368979700077619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17153193251650612533540317 6432447469368979700077619)
                ·
                  refine ⟨9648671204053469550116429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6432447469368979700077619 9648671204053469550116429)
                  ·
                    refine ⟨3618251701520051081293661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9648671204053469550116429 3618251701520051081293661)
                    ·
                      refine ⟨1356844388070019155485123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3618251701520051081293661 1356844388070019155485123)
                      ·
                        rfl

theorem cell23_2642445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_2642445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642445 prefixEnd_2642445 := by exact prefixLift 2642445
  have htrace : WordTrace (prefixWord ++ tailWord_2642445) baseStart_2642445 baseEnd_2642445 := by
    simpa [prefixWord, tailWord_2642445, baseEnd_2642445] using wordTrace_append hprefix tailTrace_2642445
  have hstable : (prefixWord ++ tailWord_2642445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642445).length < 2 ^ (prefixWord ++ tailWord_2642445).sum := by decide
  have hdescent : baseEnd_2642445 < baseStart_2642445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642472 : List Nat := [2, 1, 5, 2, 1, 1, 4, 1, 1, 3, 2]
def baseStart_2642472 : Nat := 118140960795 + 2642472 * 2 ^ 59
def prefixEnd_2642472 : Nat := 4983230072969 + 3 ^ 40 * 2642472 * 2
def baseEnd_2642472 : Nat := 1356858252047690549847499

theorem tailTrace_2642472 : CollatzResearch.WordTrace tailWord_2642472 prefixEnd_2642472 1356858252047690549847499 := by
  unfold tailWord_2642472
  simp only [CollatzResearch.WordTrace]
  refine ⟨48189435841391358566508835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64252581121855144755345113 48189435841391358566508835)
  ·
    refine ⟨72284153762087037849763253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48189435841391358566508835 72284153762087037849763253)
    ·
      refine ⟨6776639415195659798415305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72284153762087037849763253 6776639415195659798415305)
      ·
        refine ⟨5082479561396744848811479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6776639415195659798415305 5082479561396744848811479)
        ·
          refine ⟨7623719342095117273217219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5082479561396744848811479 7623719342095117273217219)
          ·
            refine ⟨11435579013142675909825829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7623719342095117273217219 11435579013142675909825829)
            ·
              refine ⟨2144171064964251733092343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11435579013142675909825829 2144171064964251733092343)
              ·
                refine ⟨3216256597446377599638515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2144171064964251733092343 3216256597446377599638515)
                ·
                  refine ⟨4824384896169566399457773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3216256597446377599638515 4824384896169566399457773)
                  ·
                    refine ⟨1809144336063587399796665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4824384896169566399457773 1809144336063587399796665)
                    ·
                      refine ⟨1356858252047690549847499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1809144336063587399796665 1356858252047690549847499)
                      ·
                        rfl

theorem cell23_2642472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_2642472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642472 prefixEnd_2642472 := by exact prefixLift 2642472
  have htrace : WordTrace (prefixWord ++ tailWord_2642472) baseStart_2642472 baseEnd_2642472 := by
    simpa [prefixWord, tailWord_2642472, baseEnd_2642472] using wordTrace_append hprefix tailTrace_2642472
  have hstable : (prefixWord ++ tailWord_2642472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642472).length < 2 ^ (prefixWord ++ tailWord_2642472).sum := by decide
  have hdescent : baseEnd_2642472 < baseStart_2642472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642501 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 2, 3, 3]
def baseStart_2642501 : Nat := 118140960795 + 2642501 * 2 ^ 59
def prefixEnd_2642501 : Nat := 4983230072969 + 3 ^ 40 * 2642501 * 2
def baseEnd_2642501 : Nat := 1356873142986670936384865

theorem tailTrace_2642501 : CollatzResearch.WordTrace tailWord_2642501 prefixEnd_2642501 1356873142986670936384865 := by
  unfold tailWord_2642501
  simp only [CollatzResearch.WordTrace]
  refine ⟨96379929399677655085823357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64253286266451770057215571 96379929399677655085823357)
  ·
    refine ⟨36142473524879120657183759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96379929399677655085823357 36142473524879120657183759)
    ·
      refine ⟨54213710287318680985775639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36142473524879120657183759 54213710287318680985775639)
      ·
        refine ⟨81320565430978021478663459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54213710287318680985775639 81320565430978021478663459)
        ·
          refine ⟨121980848146467032217995189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81320565430978021478663459 121980848146467032217995189)
          ·
            refine ⟨11435704513731284270437049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121980848146467032217995189 11435704513731284270437049)
            ·
              refine ⟨8576778385298463202827787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11435704513731284270437049 8576778385298463202827787)
              ·
                refine ⟨12865167577947694804241681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8576778385298463202827787 12865167577947694804241681)
                ·
                  refine ⟨9648875683460771103181261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12865167577947694804241681 9648875683460771103181261)
                  ·
                    refine ⟨3618328381297789163692973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9648875683460771103181261 3618328381297789163692973)
                    ·
                      refine ⟨1356873142986670936384865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3618328381297789163692973 1356873142986670936384865)
                      ·
                        rfl

theorem cell23_2642501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 3, 3].length) (baseStart_2642501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642501 prefixEnd_2642501 := by exact prefixLift 2642501
  have htrace : WordTrace (prefixWord ++ tailWord_2642501) baseStart_2642501 baseEnd_2642501 := by
    simpa [prefixWord, tailWord_2642501, baseEnd_2642501] using wordTrace_append hprefix tailTrace_2642501
  have hstable : (prefixWord ++ tailWord_2642501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642501).length < 2 ^ (prefixWord ++ tailWord_2642501).sum := by decide
  have hdescent : baseEnd_2642501 < baseStart_2642501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642502 : List Nat := [6, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2]
def baseStart_2642502 : Nat := 118140960795 + 2642502 * 2 ^ 59
def prefixEnd_2642502 : Nat := 4983230072969 + 3 ^ 40 * 2642502 * 2
def baseEnd_2642502 : Nat := 1356873656467325432472361

theorem tailTrace_2642502 : CollatzResearch.WordTrace tailWord_2642502 prefixEnd_2642502 1356873656467325432472361 := by
  unfold tailWord_2642502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3011873933521063508019055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64253310581782688171073173 3011873933521063508019055)
  ·
    refine ⟨4517810900281595262028583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3011873933521063508019055 4517810900281595262028583)
    ·
      refine ⟨6776716350422392893042875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4517810900281595262028583 6776716350422392893042875)
      ·
        refine ⟨10165074525633589339564313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6776716350422392893042875 10165074525633589339564313)
        ·
          refine ⟨7623805894225192004673235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10165074525633589339564313 7623805894225192004673235)
          ·
            refine ⟨11435708841337788007009853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7623805894225192004673235 11435708841337788007009853)
            ·
              refine ⟨4288390815501670502628695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11435708841337788007009853 4288390815501670502628695)
              ·
                refine ⟨6432586223252505753943043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4288390815501670502628695 6432586223252505753943043)
                ·
                  refine ⟨9648879334878758630914565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6432586223252505753943043 9648879334878758630914565)
                  ·
                    refine ⟨1809164875289767243296481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9648879334878758630914565 1809164875289767243296481)
                    ·
                      refine ⟨1356873656467325432472361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1809164875289767243296481 1356873656467325432472361)
                      ·
                        rfl

theorem cell23_2642502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_2642502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642502 prefixEnd_2642502 := by exact prefixLift 2642502
  have htrace : WordTrace (prefixWord ++ tailWord_2642502) baseStart_2642502 baseEnd_2642502 := by
    simpa [prefixWord, tailWord_2642502, baseEnd_2642502] using wordTrace_append hprefix tailTrace_2642502
  have hstable : (prefixWord ++ tailWord_2642502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642502).length < 2 ^ (prefixWord ++ tailWord_2642502).sum := by decide
  have hdescent : baseEnd_2642502 < baseStart_2642502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642511 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 2, 5, 2]
def baseStart_2642511 : Nat := 118140960795 + 2642511 * 2 ^ 59
def prefixEnd_2642511 : Nat := 4983230072969 + 3 ^ 40 * 2642511 * 2
def baseEnd_2642511 : Nat := 1356878277793215897259819

theorem tailTrace_2642511 : CollatzResearch.WordTrace tailWord_2642511 prefixEnd_2642511 1356878277793215897259819 := by
  unfold tailWord_2642511
  simp only [CollatzResearch.WordTrace]
  refine ⟨96380294129641426793687387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64253529419760951195791591 96380294129641426793687387)
  ·
    refine ⟨144570441194462140190531081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96380294129641426793687387 144570441194462140190531081)
    ·
      refine ⟨108427830895846605142898311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144570441194462140190531081 108427830895846605142898311)
      ·
        refine ⟨162641746343769907714347467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108427830895846605142898311 162641746343769907714347467)
        ·
          refine ⟨243962619515654861571521201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162641746343769907714347467 243962619515654861571521201)
          ·
            refine ⟨182971964636741146178640901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243962619515654861571521201 182971964636741146178640901)
            ·
              refine ⟨34307243369388964908495169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 182971964636741146178640901 34307243369388964908495169)
              ·
                refine ⟨25730432527041723681371377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34307243369388964908495169 25730432527041723681371377)
                ·
                  refine ⟨19297824395281292761028533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25730432527041723681371377 19297824395281292761028533)
                  ·
                    refine ⟨1809171037057621196346425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19297824395281292761028533 1809171037057621196346425)
                    ·
                      refine ⟨1356878277793215897259819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1809171037057621196346425 1356878277793215897259819)
                      ·
                        rfl

theorem cell23_2642511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 5, 2].length) (baseStart_2642511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642511 prefixEnd_2642511 := by exact prefixLift 2642511
  have htrace : WordTrace (prefixWord ++ tailWord_2642511) baseStart_2642511 baseEnd_2642511 := by
    simpa [prefixWord, tailWord_2642511, baseEnd_2642511] using wordTrace_append hprefix tailTrace_2642511
  have hstable : (prefixWord ++ tailWord_2642511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642511).length < 2 ^ (prefixWord ++ tailWord_2642511).sum := by decide
  have hdescent : baseEnd_2642511 < baseStart_2642511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642554 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6]
def baseStart_2642554 : Nat := 118140960795 + 2642554 * 2 ^ 59
def prefixEnd_2642554 : Nat := 4983230072969 + 3 ^ 40 * 2642554 * 2
def baseEnd_2642554 : Nat := 1356900357461359229022121

theorem tailTrace_2642554 : CollatzResearch.WordTrace tailWord_2642554 prefixEnd_2642554 1356900357461359229022121 := by
  unfold tailWord_2642554
  simp only [CollatzResearch.WordTrace]
  refine ⟨24095465617121411284375679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64254574978990430091668477 24095465617121411284375679)
  ·
    refine ⟨36143198425682116926563519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24095465617121411284375679 36143198425682116926563519)
    ·
      refine ⟨54214797638523175389845279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36143198425682116926563519 54214797638523175389845279)
      ·
        refine ⟨81322196457784763084767919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54214797638523175389845279 81322196457784763084767919)
        ·
          refine ⟨121983294686677144627151879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81322196457784763084767919 121983294686677144627151879)
          ·
            refine ⟨182974942030015716940727819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121983294686677144627151879 182974942030015716940727819)
            ·
              refine ⟨274462413045023575411091729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182974942030015716940727819 274462413045023575411091729)
              ·
                refine ⟨205846809783767681558318797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274462413045023575411091729 205846809783767681558318797)
                ·
                  refine ⟨77192553668912880584369549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 205846809783767681558318797 77192553668912880584369549)
                  ·
                    refine ⟨28947207625842330219138581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77192553668912880584369549 28947207625842330219138581)
                    ·
                      refine ⟨1356900357461359229022121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28947207625842330219138581 1356900357461359229022121)
                      ·
                        rfl

theorem cell23_2642554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_2642554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642554 prefixEnd_2642554 := by exact prefixLift 2642554
  have htrace : WordTrace (prefixWord ++ tailWord_2642554) baseStart_2642554 baseEnd_2642554 := by
    simpa [prefixWord, tailWord_2642554, baseEnd_2642554] using wordTrace_append hprefix tailTrace_2642554
  have hstable : (prefixWord ++ tailWord_2642554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642554).length < 2 ^ (prefixWord ++ tailWord_2642554).sum := by decide
  have hdescent : baseEnd_2642554 < baseStart_2642554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642608 : List Nat := [2, 1, 1, 1, 2, 1, 3, 5, 3, 1, 3]
def baseStart_2642608 : Nat := 118140960795 + 2642608 * 2 ^ 59
def prefixEnd_2642608 : Nat := 4983230072969 + 3 ^ 40 * 2642608 * 2
def baseEnd_2642608 : Nat := 1356928085416702017746873

theorem tailTrace_2642608 : CollatzResearch.WordTrace tailWord_2642608 prefixEnd_2642608 1356928085416702017746873 := by
  unfold tailWord_2642608
  simp only [CollatzResearch.WordTrace]
  refine ⟨48191916005145006179984239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64255888006860008239978985 48191916005145006179984239)
  ·
    refine ⟨72287874007717509269976359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48191916005145006179984239 72287874007717509269976359)
    ·
      refine ⟨108431811011576263904964539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72287874007717509269976359 108431811011576263904964539)
      ·
        refine ⟨162647716517364395857446809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108431811011576263904964539 162647716517364395857446809)
        ·
          refine ⟨121985787388023296893085107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162647716517364395857446809 121985787388023296893085107)
          ·
            refine ⟨182978681082034945339627661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121985787388023296893085107 182978681082034945339627661)
            ·
              refine ⟨68617005405763104502360373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182978681082034945339627661 68617005405763104502360373)
              ·
                refine ⟨6432844256790291047096285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68617005405763104502360373 6432844256790291047096285)
                ·
                  refine ⟨2412316596296359142661107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6432844256790291047096285 2412316596296359142661107)
                  ·
                    refine ⟨3618474894444538713991661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2412316596296359142661107 3618474894444538713991661)
                    ·
                      refine ⟨1356928085416702017746873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3618474894444538713991661 1356928085416702017746873)
                      ·
                        rfl

theorem cell23_2642608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 3, 1, 3].length) (baseStart_2642608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642608 prefixEnd_2642608 := by exact prefixLift 2642608
  have htrace : WordTrace (prefixWord ++ tailWord_2642608) baseStart_2642608 baseEnd_2642608 := by
    simpa [prefixWord, tailWord_2642608, baseEnd_2642608] using wordTrace_append hprefix tailTrace_2642608
  have hstable : (prefixWord ++ tailWord_2642608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642608).length < 2 ^ (prefixWord ++ tailWord_2642608).sum := by decide
  have hdescent : baseEnd_2642608 < baseStart_2642608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642611 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 3, 5]
def baseStart_2642611 : Nat := 118140960795 + 2642611 * 2 ^ 59
def prefixEnd_2642611 : Nat := 4983230072969 + 3 ^ 40 * 2642611 * 2
def baseEnd_2642611 : Nat := 452309875286221835336453

theorem tailTrace_2642611 : CollatzResearch.WordTrace tailWord_2642611 prefixEnd_2642611 452309875286221835336453 := by
  unfold tailWord_2642611
  simp only [CollatzResearch.WordTrace]
  refine ⟨96383941429279143872327687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64255960952852762581551791 96383941429279143872327687)
  ·
    refine ⟨144575912143918715808491531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96383941429279143872327687 144575912143918715808491531)
    ·
      refine ⟨216863868215878073712737297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144575912143918715808491531 216863868215878073712737297)
      ·
        refine ⟨162647901161908555284552973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216863868215878073712737297 162647901161908555284552973)
        ·
          refine ⟨60992962935715708231707365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162647901161908555284552973 60992962935715708231707365)
          ·
            refine ⟨11436180550446695293445131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60992962935715708231707365 11436180550446695293445131)
            ·
              refine ⟨17154270825670042940167697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11436180550446695293445131 17154270825670042940167697)
              ·
                refine ⟨12865703119252532205125773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17154270825670042940167697 12865703119252532205125773)
                ·
                  refine ⟨4824638669719699576922165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12865703119252532205125773 4824638669719699576922165)
                  ·
                    refine ⟨452309875286221835336453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4824638669719699576922165 452309875286221835336453)
                    ·
                      rfl

theorem cell23_2642611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 5].length) (baseStart_2642611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642611 prefixEnd_2642611 := by exact prefixLift 2642611
  have htrace : WordTrace (prefixWord ++ tailWord_2642611) baseStart_2642611 baseEnd_2642611 := by
    simpa [prefixWord, tailWord_2642611, baseEnd_2642611] using wordTrace_append hprefix tailTrace_2642611
  have hstable : (prefixWord ++ tailWord_2642611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642611).length < 2 ^ (prefixWord ++ tailWord_2642611).sum := by decide
  have hdescent : baseEnd_2642611 < baseStart_2642611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642618 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2]
def baseStart_2642618 : Nat := 118140960795 + 2642618 * 2 ^ 59
def prefixEnd_2642618 : Nat := 4983230072969 + 3 ^ 40 * 2642618 * 2
def baseEnd_2642618 : Nat := 1356933220223246978621827

theorem tailTrace_2642618 : CollatzResearch.WordTrace tailWord_2642618 prefixEnd_2642618 1356933220223246978621827 := by
  unfold tailWord_2642618
  simp only [CollatzResearch.WordTrace]
  refine ⟨24096049185063446016958127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64256131160169189378555005 24096049185063446016958127)
  ·
    refine ⟨36144073777595169025437191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24096049185063446016958127 36144073777595169025437191)
    ·
      refine ⟨54216110666392753538155787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36144073777595169025437191 54216110666392753538155787)
      ·
        refine ⟨81324165999589130307233681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54216110666392753538155787 81324165999589130307233681)
        ·
          refine ⟨60993124499691847730425261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81324165999589130307233681 60993124499691847730425261)
          ·
            refine ⟨22872421687384442898909473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60993124499691847730425261 22872421687384442898909473)
            ·
              refine ⟨17154316265538332174182105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22872421687384442898909473 17154316265538332174182105)
              ·
                refine ⟨12865737199153749130636579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17154316265538332174182105 12865737199153749130636579)
                ·
                  refine ⟨19298605798730623695954869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12865737199153749130636579 19298605798730623695954869)
                  ·
                    refine ⟨1809244293630995971495769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19298605798730623695954869 1809244293630995971495769)
                    ·
                      refine ⟨1356933220223246978621827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1809244293630995971495769 1356933220223246978621827)
                      ·
                        rfl

theorem cell23_2642618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2].length) (baseStart_2642618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642618 prefixEnd_2642618 := by exact prefixLift 2642618
  have htrace : WordTrace (prefixWord ++ tailWord_2642618) baseStart_2642618 baseEnd_2642618 := by
    simpa [prefixWord, tailWord_2642618, baseEnd_2642618] using wordTrace_append hprefix tailTrace_2642618
  have hstable : (prefixWord ++ tailWord_2642618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642618).length < 2 ^ (prefixWord ++ tailWord_2642618).sum := by decide
  have hdescent : baseEnd_2642618 < baseStart_2642618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642628 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 3, 5]
def baseStart_2642628 : Nat := 118140960795 + 2642628 * 2 ^ 59
def prefixEnd_2642628 : Nat := 4983230072969 + 3 ^ 40 * 2642628 * 2
def baseEnd_2642628 : Nat := 452312785009930646498927

theorem tailTrace_2642628 : CollatzResearch.WordTrace tailWord_2642628 prefixEnd_2642628 452312785009930646498927 := by
  unfold tailWord_2642628
  simp only [CollatzResearch.WordTrace]
  refine ⟨48192280735108777887848269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64256374313478370517131025 48192280735108777887848269)
  ·
    refine ⟨18072105275665791707943101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48192280735108777887848269 18072105275665791707943101)
    ·
      refine ⟨6777039478374671890478663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18072105275665791707943101 6777039478374671890478663)
      ·
        refine ⟨10165559217562007835717995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6777039478374671890478663 10165559217562007835717995)
        ·
          refine ⟨15248338826343011753576993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10165559217562007835717995 15248338826343011753576993)
          ·
            refine ⟨11436254119757258815182745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15248338826343011753576993 11436254119757258815182745)
            ·
              refine ⟨8577190589817944111387059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11436254119757258815182745 8577190589817944111387059)
              ·
                refine ⟨12865785884726916167080589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8577190589817944111387059 12865785884726916167080589)
                ·
                  refine ⟨4824669706772593562655221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12865785884726916167080589 4824669706772593562655221)
                  ·
                    refine ⟨452312785009930646498927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4824669706772593562655221 452312785009930646498927)
                    ·
                      rfl

theorem cell23_2642628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_2642628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642628 prefixEnd_2642628 := by exact prefixLift 2642628
  have htrace : WordTrace (prefixWord ++ tailWord_2642628) baseStart_2642628 baseEnd_2642628 := by
    simpa [prefixWord, tailWord_2642628, baseEnd_2642628] using wordTrace_append hprefix tailTrace_2642628
  have hstable : (prefixWord ++ tailWord_2642628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642628).length < 2 ^ (prefixWord ++ tailWord_2642628).sum := by decide
  have hdescent : baseEnd_2642628 < baseStart_2642628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642641 : List Nat := [1, 2, 2, 1, 2, 3, 1, 4, 1, 6]
def baseStart_2642641 : Nat := 118140960795 + 2642641 * 2 ^ 59
def prefixEnd_2642641 : Nat := 4983230072969 + 3 ^ 40 * 2642641 * 2
def baseEnd_2642641 : Nat := 452315010092766796211407

theorem tailTrace_2642641 : CollatzResearch.WordTrace tailWord_2642641 prefixEnd_2642641 452315010092766796211407 := by
  unfold tailWord_2642641
  simp only [CollatzResearch.WordTrace]
  refine ⟨96385035619170458995919777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64256690412780305997279851 96385035619170458995919777)
  ·
    refine ⟨72288776714377844246939833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96385035619170458995919777 72288776714377844246939833)
    ·
      refine ⟨54216582535783383185204875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72288776714377844246939833 54216582535783383185204875)
      ·
        refine ⟨81324873803675074777807313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54216582535783383185204875 81324873803675074777807313)
        ·
          refine ⟨60993655352756306083355485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81324873803675074777807313 60993655352756306083355485)
          ·
            refine ⟨22872620757283614781258307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60993655352756306083355485 22872620757283614781258307)
            ·
              refine ⟨34308931135925422171887461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22872620757283614781258307 34308931135925422171887461)
              ·
                refine ⟨6432924587986016657228899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34308931135925422171887461 6432924587986016657228899)
                ·
                  refine ⟨9649386881979024985843349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6432924587986016657228899 9649386881979024985843349)
                  ·
                    refine ⟨452315010092766796211407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9649386881979024985843349 452315010092766796211407)
                    ·
                      rfl

theorem cell23_2642641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_2642641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642641 prefixEnd_2642641 := by exact prefixLift 2642641
  have htrace : WordTrace (prefixWord ++ tailWord_2642641) baseStart_2642641 baseEnd_2642641 := by
    simpa [prefixWord, tailWord_2642641, baseEnd_2642641] using wordTrace_append hprefix tailTrace_2642641
  have hstable : (prefixWord ++ tailWord_2642641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642641).length < 2 ^ (prefixWord ++ tailWord_2642641).sum := by decide
  have hdescent : baseEnd_2642641 < baseStart_2642641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642665 : List Nat := [1, 2, 1, 1, 1, 2, 5, 3, 3, 2, 2]
def baseStart_2642665 : Nat := 118140960795 + 2642665 * 2 ^ 59
def prefixEnd_2642665 : Nat := 4983230072969 + 3 ^ 40 * 2642665 * 2
def baseEnd_2642665 : Nat := 1356957353814008294734111

theorem tailTrace_2642665 : CollatzResearch.WordTrace tailWord_2642665 prefixEnd_2642665 1356957353814008294734111 := by
  unfold tailWord_2642665
  simp only [CollatzResearch.WordTrace]
  refine ⟨96385910971083511094793449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64257273980722340729862299 96385910971083511094793449)
  ·
    refine ⟨72289433228312633321095087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96385910971083511094793449 72289433228312633321095087)
    ·
      refine ⟨108434149842468949981642631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72289433228312633321095087 108434149842468949981642631)
      ·
        refine ⟨162651224763703424972463947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108434149842468949981642631 162651224763703424972463947)
        ·
          refine ⟨243976837145555137458695921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162651224763703424972463947 243976837145555137458695921)
          ·
            refine ⟨182982627859166353094021941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243976837145555137458695921 182982627859166353094021941)
            ·
              refine ⟨17154621361796845602564557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 182982627859166353094021941 17154621361796845602564557)
              ·
                refine ⟨6432983010673817100961709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17154621361796845602564557 6432983010673817100961709)
                ·
                  refine ⟨2412368629002681412860641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6432983010673817100961709 2412368629002681412860641)
                  ·
                    refine ⟨1809276471752011059645481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2412368629002681412860641 1809276471752011059645481)
                    ·
                      refine ⟨1356957353814008294734111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1809276471752011059645481 1356957353814008294734111)
                      ·
                        rfl

theorem cell23_2642665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 2, 2].length) (baseStart_2642665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642665 prefixEnd_2642665 := by exact prefixLift 2642665
  have htrace : WordTrace (prefixWord ++ tailWord_2642665) baseStart_2642665 baseEnd_2642665 := by
    simpa [prefixWord, tailWord_2642665, baseEnd_2642665] using wordTrace_append hprefix tailTrace_2642665
  have hstable : (prefixWord ++ tailWord_2642665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642665).length < 2 ^ (prefixWord ++ tailWord_2642665).sum := by decide
  have hdescent : baseEnd_2642665 < baseStart_2642665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642678 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_2642678 : Nat := 118140960795 + 2642678 * 2 ^ 59
def prefixEnd_2642678 : Nat := 4983230072969 + 3 ^ 40 * 2642678 * 2
def baseEnd_2642678 : Nat := 1356964029062516743871551

theorem tailTrace_2642678 : CollatzResearch.WordTrace tailWord_2642678 prefixEnd_2642678 1356964029062516743871551 := by
  unfold tailWord_2642678
  simp only [CollatzResearch.WordTrace]
  refine ⟨6024149070002275894688543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64257590080024276210011125 6024149070002275894688543)
  ·
    refine ⟨9036223605003413842032815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6024149070002275894688543 9036223605003413842032815)
    ·
      refine ⟨13554335407505120763049223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9036223605003413842032815 13554335407505120763049223)
      ·
        refine ⟨20331503111257681144573835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13554335407505120763049223 20331503111257681144573835)
        ·
          refine ⟨30497254666886521716860753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20331503111257681144573835 30497254666886521716860753)
          ·
            refine ⟨22872941000164891287645565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30497254666886521716860753 22872941000164891287645565)
            ·
              refine ⟨8577352875061834232867087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22872941000164891287645565 8577352875061834232867087)
              ·
                refine ⟨12866029312592751349300631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8577352875061834232867087 12866029312592751349300631)
                ·
                  refine ⟨19299043968889127023950947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12866029312592751349300631 19299043968889127023950947)
                  ·
                    refine ⟨28948565953333690535926421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19299043968889127023950947 28948565953333690535926421)
                    ·
                      refine ⟨1356964029062516743871551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28948565953333690535926421 1356964029062516743871551)
                      ·
                        rfl

theorem cell23_2642678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_2642678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642678 prefixEnd_2642678 := by exact prefixLift 2642678
  have htrace : WordTrace (prefixWord ++ tailWord_2642678) baseStart_2642678 baseEnd_2642678 := by
    simpa [prefixWord, tailWord_2642678, baseEnd_2642678] using wordTrace_append hprefix tailTrace_2642678
  have hstable : (prefixWord ++ tailWord_2642678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642678).length < 2 ^ (prefixWord ++ tailWord_2642678).sum := by decide
  have hdescent : baseEnd_2642678 < baseStart_2642678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642685 : List Nat := [1, 4, 1, 1, 1, 1, 6, 2, 1, 2, 3]
def baseStart_2642685 : Nat := 118140960795 + 2642685 * 2 ^ 59
def prefixEnd_2642685 : Nat := 4983230072969 + 3 ^ 40 * 2642685 * 2
def baseEnd_2642685 : Nat := 1356967623427098216484019

theorem tailTrace_2642685 : CollatzResearch.WordTrace tailWord_2642685 prefixEnd_2642685 1356967623427098216484019 := by
  unfold tailWord_2642685
  simp only [CollatzResearch.WordTrace]
  refine ⟨96386640431011054510521509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64257760287340703007014339 96386640431011054510521509)
  ·
    refine ⟨18072495080814572720722783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96386640431011054510521509 18072495080814572720722783)
    ·
      refine ⟨27108742621221859081084175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18072495080814572720722783 27108742621221859081084175)
      ·
        refine ⟨40663113931832788621626263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27108742621221859081084175 40663113931832788621626263)
        ·
          refine ⟨60994670897749182932439395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40663113931832788621626263 60994670897749182932439395)
          ·
            refine ⟨91492006346623774398659093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60994670897749182932439395 91492006346623774398659093)
            ·
              refine ⟨4288687797497989424937145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91492006346623774398659093 4288687797497989424937145)
              ·
                refine ⟨3216515848123492068702859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4288687797497989424937145 3216515848123492068702859)
                ·
                  refine ⟨4824773772185238103054289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3216515848123492068702859 4824773772185238103054289)
                  ·
                    refine ⟨3618580329138928577290717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4824773772185238103054289 3618580329138928577290717)
                    ·
                      refine ⟨1356967623427098216484019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3618580329138928577290717 1356967623427098216484019)
                      ·
                        rfl

theorem cell23_2642685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_2642685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642685 prefixEnd_2642685 := by exact prefixLift 2642685
  have htrace : WordTrace (prefixWord ++ tailWord_2642685) baseStart_2642685 baseEnd_2642685 := by
    simpa [prefixWord, tailWord_2642685, baseEnd_2642685] using wordTrace_append hprefix tailTrace_2642685
  have hstable : (prefixWord ++ tailWord_2642685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642685).length < 2 ^ (prefixWord ++ tailWord_2642685).sum := by decide
  have hdescent : baseEnd_2642685 < baseStart_2642685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642698 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 3, 3, 3]
def baseStart_2642698 : Nat := 118140960795 + 2642698 * 2 ^ 59
def prefixEnd_2642698 : Nat := 4983230072969 + 3 ^ 40 * 2642698 * 2
def baseEnd_2642698 : Nat := 1356974298675606665621459

theorem tailTrace_2642698 : CollatzResearch.WordTrace tailWord_2642698 prefixEnd_2642698 1356974298675606665621459 := by
  unfold tailWord_2642698
  simp only [CollatzResearch.WordTrace]
  refine ⟨24096778644990989432686187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64258076386642638487163165 24096778644990989432686187)
  ·
    refine ⟨36145167967486484149029281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24096778644990989432686187 36145167967486484149029281)
    ·
      refine ⟨27108875975614863111771961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36145167967486484149029281 27108875975614863111771961)
      ·
        refine ⟨20331656981711147333828971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27108875975614863111771961 20331656981711147333828971)
        ·
          refine ⟨30497485472566721000743457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20331656981711147333828971 30497485472566721000743457)
          ·
            refine ⟨22873114104425040750557593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30497485472566721000743457 22873114104425040750557593)
            ·
              refine ⟨17154835578318780562918195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22873114104425040750557593 17154835578318780562918195)
              ·
                refine ⟨25732253367478170844377293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17154835578318780562918195 25732253367478170844377293)
                ·
                  refine ⟨9649595012804314066641485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25732253367478170844377293 9649595012804314066641485)
                  ·
                    refine ⟨3618598129801617774990557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9649595012804314066641485 3618598129801617774990557)
                    ·
                      refine ⟨1356974298675606665621459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3618598129801617774990557 1356974298675606665621459)
                      ·
                        rfl

theorem cell23_2642698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_2642698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642698 prefixEnd_2642698 := by exact prefixLift 2642698
  have htrace : WordTrace (prefixWord ++ tailWord_2642698) baseStart_2642698 baseEnd_2642698 := by
    simpa [prefixWord, tailWord_2642698, baseEnd_2642698] using wordTrace_append hprefix tailTrace_2642698
  have hstable : (prefixWord ++ tailWord_2642698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642698).length < 2 ^ (prefixWord ++ tailWord_2642698).sum := by decide
  have hdescent : baseEnd_2642698 < baseStart_2642698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642716 : List Nat := [2, 2, 3, 1, 1, 4, 3, 2, 1, 2, 2]
def baseStart_2642716 : Nat := 118140960795 + 2642716 * 2 ^ 59
def prefixEnd_2642716 : Nat := 4983230072969 + 3 ^ 40 * 2642716 * 2
def baseEnd_2642716 : Nat := 1356983541327387595196377

theorem tailTrace_2642716 : CollatzResearch.WordTrace tailWord_2642716 prefixEnd_2642716 1356983541327387595196377 := by
  unfold tailWord_2642716
  simp only [CollatzResearch.WordTrace]
  refine ⟨48193885546949373402450001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64258514062599164536600001 48193885546949373402450001)
  ·
    refine ⟨36145414160212030051837501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48193885546949373402450001 36145414160212030051837501)
    ·
      refine ⟨13554530310079511269439063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36145414160212030051837501 13554530310079511269439063)
      ·
        refine ⟨20331795465119266904158595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13554530310079511269439063 20331795465119266904158595)
        ·
          refine ⟨30497693197678900356237893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20331795465119266904158595 30497693197678900356237893)
          ·
            refine ⟨5718317474564793816794605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30497693197678900356237893 5718317474564793816794605)
            ·
              refine ⟨2144369052961797681297977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5718317474564793816794605 2144369052961797681297977)
              ·
                refine ⟨1608276789721348260973483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2144369052961797681297977 1608276789721348260973483)
                ·
                  refine ⟨2412415184582022391460225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1608276789721348260973483 2412415184582022391460225)
                  ·
                    refine ⟨1809311388436516793595169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2412415184582022391460225 1809311388436516793595169)
                    ·
                      refine ⟨1356983541327387595196377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1809311388436516793595169 1356983541327387595196377)
                      ·
                        rfl

theorem cell23_2642716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_2642716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642716 prefixEnd_2642716 := by exact prefixLift 2642716
  have htrace : WordTrace (prefixWord ++ tailWord_2642716) baseStart_2642716 baseEnd_2642716 := by
    simpa [prefixWord, tailWord_2642716, baseEnd_2642716] using wordTrace_append hprefix tailTrace_2642716
  have hstable : (prefixWord ++ tailWord_2642716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642716).length < 2 ^ (prefixWord ++ tailWord_2642716).sum := by decide
  have hdescent : baseEnd_2642716 < baseStart_2642716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642725 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 3, 3, 2]
def baseStart_2642725 : Nat := 118140960795 + 2642725 * 2 ^ 59
def prefixEnd_2642725 : Nat := 4983230072969 + 3 ^ 40 * 2642725 * 2
def baseEnd_2642725 : Nat := 1356988162653278059983835

theorem tailTrace_2642725 : CollatzResearch.WordTrace tailWord_2642725 prefixEnd_2642725 1356988162653278059983835 := by
  unfold tailWord_2642725
  simp only [CollatzResearch.WordTrace]
  refine ⟨96388099350866141341977629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64258732900577427561318419 96388099350866141341977629)
  ·
    refine ⟨36145537256574803003241611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96388099350866141341977629 36145537256574803003241611)
    ·
      refine ⟨54218305884862204504862417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36145537256574803003241611 54218305884862204504862417)
      ·
        refine ⟨40663729413646653378646813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54218305884862204504862417 40663729413646653378646813)
        ·
          refine ⟨15248898530117495016992555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40663729413646653378646813 15248898530117495016992555)
          ·
            refine ⟨22873347795176242525488833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15248898530117495016992555 22873347795176242525488833)
            ·
              refine ⟨17155010846382181894116625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22873347795176242525488833 17155010846382181894116625)
              ·
                refine ⟨12866258134786636420587469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17155010846382181894116625 12866258134786636420587469)
                ·
                  refine ⟨4824846800544988657720301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12866258134786636420587469 4824846800544988657720301)
                  ·
                    refine ⟨1809317550204370746645113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4824846800544988657720301 1809317550204370746645113)
                    ·
                      refine ⟨1356988162653278059983835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1809317550204370746645113 1356988162653278059983835)
                      ·
                        rfl

theorem cell23_2642725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_2642725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642725 prefixEnd_2642725 := by exact prefixLift 2642725
  have htrace : WordTrace (prefixWord ++ tailWord_2642725) baseStart_2642725 baseEnd_2642725 := by
    simpa [prefixWord, tailWord_2642725, baseEnd_2642725] using wordTrace_append hprefix tailTrace_2642725
  have hstable : (prefixWord ++ tailWord_2642725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642725).length < 2 ^ (prefixWord ++ tailWord_2642725).sum := by decide
  have hdescent : baseEnd_2642725 < baseStart_2642725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642755 : List Nat := [1, 1, 1, 3, 1, 4, 3, 2, 1, 4, 2]
def baseStart_2642755 : Nat := 118140960795 + 2642755 * 2 ^ 59
def prefixEnd_2642755 : Nat := 4983230072969 + 3 ^ 40 * 2642755 * 2
def baseEnd_2642755 : Nat := 1357003567072912942608697

theorem tailTrace_2642755 : CollatzResearch.WordTrace tailWord_2642755 prefixEnd_2642755 1357003567072912942608697 := by
  unfold tailWord_2642755
  simp only [CollatzResearch.WordTrace]
  refine ⟨96389193540757456465569719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64259462360504970977046479 96389193540757456465569719)
  ·
    refine ⟨144583790311136184698354579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96389193540757456465569719 144583790311136184698354579)
    ·
      refine ⟨216875685466704277047531869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144583790311136184698354579 216875685466704277047531869)
      ·
        refine ⟨81328382050014103892824451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216875685466704277047531869 81328382050014103892824451)
        ·
          refine ⟨121992573075021155839236677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81328382050014103892824451 121992573075021155839236677)
          ·
            refine ⟨22873607451566466719856877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121992573075021155839236677 22873607451566466719856877)
            ·
              refine ⟨8577602794337425019946329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22873607451566466719856877 8577602794337425019946329)
              ·
                refine ⟨6433202095753068764959747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8577602794337425019946329 6433202095753068764959747)
                ·
                  refine ⟨9649803143629603147439621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6433202095753068764959747 9649803143629603147439621)
                  ·
                    refine ⟨1809338089430550590144929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9649803143629603147439621 1809338089430550590144929)
                    ·
                      refine ⟨1357003567072912942608697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1809338089430550590144929 1357003567072912942608697)
                      ·
                        rfl

theorem cell23_2642755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 4, 2].length) (baseStart_2642755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642755 prefixEnd_2642755 := by exact prefixLift 2642755
  have htrace : WordTrace (prefixWord ++ tailWord_2642755) baseStart_2642755 baseEnd_2642755 := by
    simpa [prefixWord, tailWord_2642755, baseEnd_2642755] using wordTrace_append hprefix tailTrace_2642755
  have hstable : (prefixWord ++ tailWord_2642755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642755).length < 2 ^ (prefixWord ++ tailWord_2642755).sum := by decide
  have hdescent : baseEnd_2642755 < baseStart_2642755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642771 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 7]
def baseStart_2642771 : Nat := 118140960795 + 2642771 * 2 ^ 59
def prefixEnd_2642771 : Nat := 4983230072969 + 3 ^ 40 * 2642771 * 2
def baseEnd_2642771 : Nat := 1357011782763384880008623

theorem tailTrace_2642771 : CollatzResearch.WordTrace tailWord_2642771 prefixEnd_2642771 1357011782763384880008623 := by
  unfold tailWord_2642771
  simp only [CollatzResearch.WordTrace]
  refine ⟨96389777108699491198152167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64259851405799660798768111 96389777108699491198152167)
  ·
    refine ⟨144584665663049236797228251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96389777108699491198152167 144584665663049236797228251)
    ·
      refine ⟨216876998494573855195842377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144584665663049236797228251 216876998494573855195842377)
      ·
        refine ⟨162657748870930391396881783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216876998494573855195842377 162657748870930391396881783)
        ·
          refine ⟨243986623306395587095322675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162657748870930391396881783 243986623306395587095322675)
          ·
            refine ⟨365979934959593380642984013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243986623306395587095322675 365979934959593380642984013)
            ·
              refine ⟨137242475609847517741119005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 365979934959593380642984013 137242475609847517741119005)
              ·
                refine ⟨51465928353692819152919627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137242475609847517741119005 51465928353692819152919627)
                ·
                  refine ⟨77198892530539228729379441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51465928353692819152919627 77198892530539228729379441)
                  ·
                    refine ⟨57899169397904421547034581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77198892530539228729379441 57899169397904421547034581)
                    ·
                      refine ⟨1357011782763384880008623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 57899169397904421547034581 1357011782763384880008623)
                      ·
                        rfl

theorem cell23_2642771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_2642771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642771 prefixEnd_2642771 := by exact prefixLift 2642771
  have htrace : WordTrace (prefixWord ++ tailWord_2642771) baseStart_2642771 baseEnd_2642771 := by
    simpa [prefixWord, tailWord_2642771, baseEnd_2642771] using wordTrace_append hprefix tailTrace_2642771
  have hstable : (prefixWord ++ tailWord_2642771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642771).length < 2 ^ (prefixWord ++ tailWord_2642771).sum := by decide
  have hdescent : baseEnd_2642771 < baseStart_2642771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642808 : List Nat := [2, 1, 2, 1, 1, 1, 1, 7, 2, 5]
def baseStart_2642808 : Nat := 118140960795 + 2642808 * 2 ^ 59
def prefixEnd_2642808 : Nat := 4983230072969 + 3 ^ 40 * 2642808 * 2
def baseEnd_2642808 : Nat := 452343593849200411748651

theorem tailTrace_2642808 : CollatzResearch.WordTrace tailWord_2642808 prefixEnd_2642808 452343593849200411748651 := by
  unfold tailWord_2642808
  simp only [CollatzResearch.WordTrace]
  refine ⟨48195563304782723258624539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64260751073043631011499385 48195563304782723258624539)
  ·
    refine ⟨72293344957174084887936809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48195563304782723258624539 72293344957174084887936809)
    ·
      refine ⟨54220008717880563665952607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72293344957174084887936809 54220008717880563665952607)
      ·
        refine ⟨81330013076820845498928911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54220008717880563665952607 81330013076820845498928911)
        ·
          refine ⟨121995019615231268248393367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81330013076820845498928911 121995019615231268248393367)
          ·
            refine ⟨182992529422846902372590051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121995019615231268248393367 182992529422846902372590051)
            ·
              refine ⟨274488794134270353558885077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182992529422846902372590051 274488794134270353558885077)
              ·
                refine ⟨6433331112521961411536369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 274488794134270353558885077 6433331112521961411536369)
                ·
                  refine ⟨4824998334391471058652277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6433331112521961411536369 4824998334391471058652277)
                  ·
                    refine ⟨452343593849200411748651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4824998334391471058652277 452343593849200411748651)
                    ·
                      rfl

theorem cell23_2642808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_2642808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642808 prefixEnd_2642808 := by exact prefixLift 2642808
  have htrace : WordTrace (prefixWord ++ tailWord_2642808) baseStart_2642808 baseEnd_2642808 := by
    simpa [prefixWord, tailWord_2642808, baseEnd_2642808] using wordTrace_append hprefix tailTrace_2642808
  have hstable : (prefixWord ++ tailWord_2642808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642808).length < 2 ^ (prefixWord ++ tailWord_2642808).sum := by decide
  have hdescent : baseEnd_2642808 < baseStart_2642808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642915 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 3, 5]
def baseStart_2642915 : Nat := 118140960795 + 2642915 * 2 ^ 59
def prefixEnd_2642915 : Nat := 4983230072969 + 3 ^ 40 * 2642915 * 2
def baseEnd_2642915 : Nat := 452361907992544105535987

theorem tailTrace_2642915 : CollatzResearch.WordTrace tailWord_2642915 prefixEnd_2642915 452361907992544105535987 := by
  unfold tailWord_2642915
  simp only [CollatzResearch.WordTrace]
  refine ⟨96395029220177803791394199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64263352813451869194262799 96395029220177803791394199)
  ·
    refine ⟨144592543830266705687091299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96395029220177803791394199 144592543830266705687091299)
    ·
      refine ⟨216888815745400058530636949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144592543830266705687091299 216888815745400058530636949)
      ·
        refine ⟨10166663238065627743623607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 216888815745400058530636949 10166663238065627743623607)
        ·
          refine ⟨15249994857098441615435411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10166663238065627743623607 15249994857098441615435411)
          ·
            refine ⟨22874992285647662423153117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15249994857098441615435411 22874992285647662423153117)
            ·
              refine ⟨8578122107117873408682419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22874992285647662423153117 8578122107117873408682419)
              ·
                refine ⟨12867183160676810113023629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8578122107117873408682419 12867183160676810113023629)
                ·
                  refine ⟨4825193685253803792383861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12867183160676810113023629 4825193685253803792383861)
                  ·
                    refine ⟨452361907992544105535987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4825193685253803792383861 452361907992544105535987)
                    ·
                      rfl

theorem cell23_2642915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 5].length) (baseStart_2642915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642915 prefixEnd_2642915 := by exact prefixLift 2642915
  have htrace : WordTrace (prefixWord ++ tailWord_2642915) baseStart_2642915 baseEnd_2642915 := by
    simpa [prefixWord, tailWord_2642915, baseEnd_2642915] using wordTrace_append hprefix tailTrace_2642915
  have hstable : (prefixWord ++ tailWord_2642915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642915).length < 2 ^ (prefixWord ++ tailWord_2642915).sum := by decide
  have hdescent : baseEnd_2642915 < baseStart_2642915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642973 : List Nat := [1, 4, 2, 2, 4, 1, 1, 1, 2, 3, 2]
def baseStart_2642973 : Nat := 118140960795 + 2642973 * 2 ^ 59
def prefixEnd_2642973 : Nat := 4983230072969 + 3 ^ 40 * 2642973 * 2
def baseEnd_2642973 : Nat := 1357115505855593089682695

theorem tailTrace_2642973 : CollatzResearch.WordTrace tailWord_2642973 prefixEnd_2642973 1357115505855593089682695 := by
  unfold tailWord_2642973
  simp only [CollatzResearch.WordTrace]
  refine ⟨96397144653967679697005573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64264763102645119798003715 96397144653967679697005573)
  ·
    refine ⟨18074464622618939943188545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96397144653967679697005573 18074464622618939943188545)
    ·
      refine ⟨13555848466964204957391409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18074464622618939943188545 13555848466964204957391409)
      ·
        refine ⟨10166886350223153718043557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13555848466964204957391409 10166886350223153718043557)
        ·
          refine ⟨1906291190666841322133167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10166886350223153718043557 1906291190666841322133167)
          ·
            refine ⟨2859436786000261983199751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1906291190666841322133167 2859436786000261983199751)
            ·
              refine ⟨4289155179000392974799627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2859436786000261983199751 4289155179000392974799627)
              ·
                refine ⟨6433732768500589462199441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4289155179000392974799627 6433732768500589462199441)
                ·
                  refine ⟨4825299576375442096649581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6433732768500589462199441 4825299576375442096649581)
                  ·
                    refine ⟨1809487341140790786243593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4825299576375442096649581 1809487341140790786243593)
                    ·
                      refine ⟨1357115505855593089682695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1809487341140790786243593 1357115505855593089682695)
                      ·
                        rfl

theorem cell23_2642973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_2642973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642973 prefixEnd_2642973 := by exact prefixLift 2642973
  have htrace : WordTrace (prefixWord ++ tailWord_2642973) baseStart_2642973 baseEnd_2642973 := by
    simpa [prefixWord, tailWord_2642973, baseEnd_2642973] using wordTrace_append hprefix tailTrace_2642973
  have hstable : (prefixWord ++ tailWord_2642973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642973).length < 2 ^ (prefixWord ++ tailWord_2642973).sum := by decide
  have hdescent : baseEnd_2642973 < baseStart_2642973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2642996 : List Nat := [2, 5, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_2642996 : Nat := 118140960795 + 2642996 * 2 ^ 59
def prefixEnd_2642996 : Nat := 4983230072969 + 3 ^ 40 * 2642996 * 2
def baseEnd_2642996 : Nat := 452375771970215499898363

theorem tailTrace_2642996 : CollatzResearch.WordTrace tailWord_2642996 prefixEnd_2642996 452375771970215499898363 := by
  unfold tailWord_2642996
  simp only [CollatzResearch.WordTrace]
  refine ⟨48198991766442177312546421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64265322355256236416728561 48198991766442177312546421)
  ·
    refine ⟨4518655478103954123051227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48198991766442177312546421 4518655478103954123051227)
    ·
      refine ⟨6777983217155931184576841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4518655478103954123051227 6777983217155931184576841)
      ·
        refine ⟨5083487412866948388432631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6777983217155931184576841 5083487412866948388432631)
        ·
          refine ⟨7625231119300422582648947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5083487412866948388432631 7625231119300422582648947)
          ·
            refine ⟨11437846678950633873973421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7625231119300422582648947 11437846678950633873973421)
            ·
              refine ⟨4289192504606487702740033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11437846678950633873973421 4289192504606487702740033)
              ·
                refine ⟨3216894378454865777055025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4289192504606487702740033 3216894378454865777055025)
                ·
                  refine ⟨2412670783841149332791269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3216894378454865777055025 2412670783841149332791269)
                  ·
                    refine ⟨452375771970215499898363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2412670783841149332791269 452375771970215499898363)
                    ·
                      rfl

theorem cell23_2642996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_2642996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2642996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2642996 prefixEnd_2642996 := by exact prefixLift 2642996
  have htrace : WordTrace (prefixWord ++ tailWord_2642996) baseStart_2642996 baseEnd_2642996 := by
    simpa [prefixWord, tailWord_2642996, baseEnd_2642996] using wordTrace_append hprefix tailTrace_2642996
  have hstable : (prefixWord ++ tailWord_2642996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2642996).length < 2 ^ (prefixWord ++ tailWord_2642996).sum := by decide
  have hdescent : baseEnd_2642996 < baseStart_2642996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2642996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643025 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 2, 3, 4]
def baseStart_2643025 : Nat := 118140960795 + 2643025 * 2 ^ 59
def prefixEnd_2643025 : Nat := 4983230072969 + 3 ^ 40 * 2643025 * 2
def baseEnd_2643025 : Nat := 1357142206849626886232455

theorem tailTrace_2643025 : CollatzResearch.WordTrace tailWord_2643025 prefixEnd_2643025 1357142206849626886232455 := by
  unfold tailWord_2643025
  simp only [CollatzResearch.WordTrace]
  refine ⟨96399041249779292577898529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64266027499852861718599019 96399041249779292577898529)
  ·
    refine ⟨72299280937334469433423897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96399041249779292577898529 72299280937334469433423897)
    ·
      refine ⟨54224460703000852075067923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72299280937334469433423897 54224460703000852075067923)
      ·
        refine ⟨81336691054501278112601885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54224460703000852075067923 81336691054501278112601885)
        ·
          refine ⟨30501259145437979292225707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81336691054501278112601885 30501259145437979292225707)
          ·
            refine ⟨45751888718156968938338561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30501259145437979292225707 45751888718156968938338561)
            ·
              refine ⟨34313916538617726703753921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45751888718156968938338561 34313916538617726703753921)
              ·
                refine ⟨25735437403963295027815441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34313916538617726703753921 25735437403963295027815441)
                ·
                  refine ⟨19301578052972471270861581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25735437403963295027815441 19301578052972471270861581)
                  ·
                    refine ⟨7238091769864676726573093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19301578052972471270861581 7238091769864676726573093)
                    ·
                      refine ⟨1357142206849626886232455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7238091769864676726573093 1357142206849626886232455)
                      ·
                        rfl

theorem cell23_2643025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_2643025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643025 prefixEnd_2643025 := by exact prefixLift 2643025
  have htrace : WordTrace (prefixWord ++ tailWord_2643025) baseStart_2643025 baseEnd_2643025 := by
    simpa [prefixWord, tailWord_2643025, baseEnd_2643025] using wordTrace_append hprefix tailTrace_2643025
  have hstable : (prefixWord ++ tailWord_2643025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643025).length < 2 ^ (prefixWord ++ tailWord_2643025).sum := by decide
  have hdescent : baseEnd_2643025 < baseStart_2643025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643037 : List Nat := [1, 4, 4, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_2643037 : Nat := 118140960795 + 2643037 * 2 ^ 59
def prefixEnd_2643037 : Nat := 4983230072969 + 3 ^ 40 * 2643037 * 2
def baseEnd_2643037 : Nat := 1357148368617480839282401

theorem tailTrace_2643037 : CollatzResearch.WordTrace tailWord_2643037 prefixEnd_2643037 1357148368617480839282401 := by
  unfold tailWord_2643037
  simp only [CollatzResearch.WordTrace]
  refine ⟨96399478925735818627335365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64266319283823879084890243 96399478925735818627335365)
  ·
    refine ⟨18074902298575465992625381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96399478925735818627335365 18074902298575465992625381)
    ·
      refine ⟨3389044180982899873617259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18074902298575465992625381 3389044180982899873617259)
      ·
        refine ⟨5083566271474349810425889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3389044180982899873617259 5083566271474349810425889)
        ·
          refine ⟨3812674703605762357819417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5083566271474349810425889 3812674703605762357819417)
          ·
            refine ⟨2859506027704321768364563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3812674703605762357819417 2859506027704321768364563)
            ·
              refine ⟨4289259041556482652546845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2859506027704321768364563 4289259041556482652546845)
              ·
                refine ⟨1608472140583680994705067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4289259041556482652546845 1608472140583680994705067)
                ·
                  refine ⟨2412708210875521492057601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1608472140583680994705067 2412708210875521492057601)
                  ·
                    refine ⟨1809531158156641119043201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2412708210875521492057601 1809531158156641119043201)
                    ·
                      refine ⟨1357148368617480839282401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1809531158156641119043201 1357148368617480839282401)
                      ·
                        rfl

theorem cell23_2643037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_2643037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643037 prefixEnd_2643037 := by exact prefixLift 2643037
  have htrace : WordTrace (prefixWord ++ tailWord_2643037) baseStart_2643037 baseEnd_2643037 := by
    simpa [prefixWord, tailWord_2643037, baseEnd_2643037] using wordTrace_append hprefix tailTrace_2643037
  have hstable : (prefixWord ++ tailWord_2643037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643037).length < 2 ^ (prefixWord ++ tailWord_2643037).sum := by decide
  have hdescent : baseEnd_2643037 < baseStart_2643037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643062 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_2643062 : Nat := 118140960795 + 2643062 * 2 ^ 59
def prefixEnd_2643062 : Nat := 4983230072969 + 3 ^ 40 * 2643062 * 2
def baseEnd_2643062 : Nat := 1357161205633843241469785

theorem tailTrace_2643062 : CollatzResearch.WordTrace tailWord_2643062 prefixEnd_2643062 1357161205633843241469785 := by
  unfold tailWord_2643062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6025024421915327993562215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64266927167096831931330293 6025024421915327993562215)
  ·
    refine ⟨9037536632872991990343323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6025024421915327993562215 9037536632872991990343323)
    ·
      refine ⟨13556304949309487985514985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9037536632872991990343323 13556304949309487985514985)
      ·
        refine ⟨10167228711982115989136239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13556304949309487985514985 10167228711982115989136239)
        ·
          refine ⟨15250843067973173983704359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10167228711982115989136239 15250843067973173983704359)
          ·
            refine ⟨22876264601959760975556539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15250843067973173983704359 22876264601959760975556539)
            ·
              refine ⟨34314396902939641463334809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22876264601959760975556539 34314396902939641463334809)
              ·
                refine ⟨25735797677204731097501107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34314396902939641463334809 25735797677204731097501107)
                ·
                  refine ⟨38603696515807096646251661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25735797677204731097501107 38603696515807096646251661)
                  ·
                    refine ⟨14476386193427661242344373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38603696515807096646251661 14476386193427661242344373)
                    ·
                      refine ⟨1357161205633843241469785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14476386193427661242344373 1357161205633843241469785)
                      ·
                        rfl

theorem cell23_2643062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_2643062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643062 prefixEnd_2643062 := by exact prefixLift 2643062
  have htrace : WordTrace (prefixWord ++ tailWord_2643062) baseStart_2643062 baseEnd_2643062 := by
    simpa [prefixWord, tailWord_2643062, baseEnd_2643062] using wordTrace_append hprefix tailTrace_2643062
  have hstable : (prefixWord ++ tailWord_2643062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643062).length < 2 ^ (prefixWord ++ tailWord_2643062).sum := by decide
  have hdescent : baseEnd_2643062 < baseStart_2643062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643080 : List Nat := [2, 1, 3, 4, 3, 1, 1, 2, 1, 3, 2]
def baseStart_2643080 : Nat := 118140960795 + 2643080 * 2 ^ 59
def prefixEnd_2643080 : Nat := 4983230072969 + 3 ^ 40 * 2643080 * 2
def baseEnd_2643080 : Nat := 1357170448285624171044703

theorem tailTrace_2643080 : CollatzResearch.WordTrace tailWord_2643080 prefixEnd_2643080 1357170448285624171044703 := by
  unfold tailWord_2643080
  simp only [CollatzResearch.WordTrace]
  refine ⟨48200523632290018485575347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64267364843053357980767129 48200523632290018485575347)
  ·
    refine ⟨72300785448435027728363021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48200523632290018485575347 72300785448435027728363021)
    ·
      refine ⟨27112794543163135398136133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72300785448435027728363021 27112794543163135398136133)
      ·
        refine ⟨5083648976843087887150525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27112794543163135398136133 5083648976843087887150525)
        ·
          refine ⟨1906368366316157957681447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5083648976843087887150525 1906368366316157957681447)
          ·
            refine ⟨2859552549474236936522171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1906368366316157957681447 2859552549474236936522171)
            ·
              refine ⟨4289328824211355404783257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2859552549474236936522171 4289328824211355404783257)
              ·
                refine ⟨3216996618158516553587443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4289328824211355404783257 3216996618158516553587443)
                ·
                  refine ⟨4825494927237774830381165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3216996618158516553587443 4825494927237774830381165)
                  ·
                    refine ⟨1809560597714165561392937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4825494927237774830381165 1809560597714165561392937)
                    ·
                      refine ⟨1357170448285624171044703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1809560597714165561392937 1357170448285624171044703)
                      ·
                        rfl

theorem cell23_2643080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_2643080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643080 prefixEnd_2643080 := by exact prefixLift 2643080
  have htrace : WordTrace (prefixWord ++ tailWord_2643080) baseStart_2643080 baseEnd_2643080 := by
    simpa [prefixWord, tailWord_2643080, baseEnd_2643080] using wordTrace_append hprefix tailTrace_2643080
  have hstable : (prefixWord ++ tailWord_2643080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643080).length < 2 ^ (prefixWord ++ tailWord_2643080).sum := by decide
  have hdescent : baseEnd_2643080 < baseStart_2643080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643122 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5]
def baseStart_2643122 : Nat := 118140960795 + 2643122 * 2 ^ 59
def prefixEnd_2643122 : Nat := 4983230072969 + 3 ^ 40 * 2643122 * 2
def baseEnd_2643122 : Nat := 1357192014473113006719509

theorem tailTrace_2643122 : CollatzResearch.WordTrace tailWord_2643122 prefixEnd_2643122 1357192014473113006719509 := by
  unfold tailWord_2643122
  simp only [CollatzResearch.WordTrace]
  refine ⟨24100644782606969536044905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64268386086951918762786413 24100644782606969536044905)
  ·
    refine ⟨18075483586955227152033679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24100644782606969536044905 18075483586955227152033679)
    ·
      refine ⟨27113225380432840728050519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18075483586955227152033679 27113225380432840728050519)
      ·
        refine ⟨40669838070649261092075779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27113225380432840728050519 40669838070649261092075779)
        ·
          refine ⟨61004757105973891638113669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40669838070649261092075779 61004757105973891638113669)
          ·
            refine ⟨11438391957370104682146313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61004757105973891638113669 11438391957370104682146313)
            ·
              refine ⟨8578793968027578511609735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11438391957370104682146313 8578793968027578511609735)
              ·
                refine ⟨12868190952041367767414603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8578793968027578511609735 12868190952041367767414603)
                ·
                  refine ⟨19302286428062051651121905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12868190952041367767414603 19302286428062051651121905)
                  ·
                    refine ⟨14476714821046538738341429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19302286428062051651121905 14476714821046538738341429)
                    ·
                      refine ⟨1357192014473113006719509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14476714821046538738341429 1357192014473113006719509)
                      ·
                        rfl

theorem cell23_2643122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_2643122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643122 prefixEnd_2643122 := by exact prefixLift 2643122
  have htrace : WordTrace (prefixWord ++ tailWord_2643122) baseStart_2643122 baseEnd_2643122 := by
    simpa [prefixWord, tailWord_2643122, baseEnd_2643122] using wordTrace_append hprefix tailTrace_2643122
  have hstable : (prefixWord ++ tailWord_2643122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643122).length < 2 ^ (prefixWord ++ tailWord_2643122).sum := by decide
  have hdescent : baseEnd_2643122 < baseStart_2643122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643155 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 10]
def baseStart_2643155 : Nat := 118140960795 + 2643155 * 2 ^ 59
def prefixEnd_2643155 : Nat := 4983230072969 + 3 ^ 40 * 2643155 * 2
def baseEnd_2643155 : Nat := 150800995481634597511873

theorem tailTrace_2643155 : CollatzResearch.WordTrace tailWord_2643155 prefixEnd_2643155 150800995481634597511873 := by
  unfold tailWord_2643155
  simp only [CollatzResearch.WordTrace]
  refine ⟨96403782739308324780130919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64269188492872216520087279 96403782739308324780130919)
  ·
    refine ⟨144605674108962487170196379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96403782739308324780130919 144605674108962487170196379)
    ·
      refine ⟨216908511163443730755294569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144605674108962487170196379 216908511163443730755294569)
      ·
        refine ⟨162681383372582798066470927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216908511163443730755294569 162681383372582798066470927)
        ·
          refine ⟨244022075058874197099706391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162681383372582798066470927 244022075058874197099706391)
          ·
            refine ⟨366033112588311295649559587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244022075058874197099706391 366033112588311295649559587)
            ·
              refine ⟨549049668882466943474339381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366033112588311295649559587 549049668882466943474339381)
              ·
                refine ⟨51473406457731275950719317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 549049668882466943474339381 51473406457731275950719317)
                ·
                  refine ⟨150800995481634597511873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 51473406457731275950719317 150800995481634597511873)
                  ·
                    rfl

theorem cell23_2643155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 10].length) (baseStart_2643155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643155 prefixEnd_2643155 := by exact prefixLift 2643155
  have htrace : WordTrace (prefixWord ++ tailWord_2643155) baseStart_2643155 baseEnd_2643155 := by
    simpa [prefixWord, tailWord_2643155, baseEnd_2643155] using wordTrace_append hprefix tailTrace_2643155
  have hstable : (prefixWord ++ tailWord_2643155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643155).length < 2 ^ (prefixWord ++ tailWord_2643155).sum := by decide
  have hdescent : baseEnd_2643155 < baseStart_2643155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643176 : List Nat := [2, 1, 4, 1, 2, 1, 1, 6, 1, 4]
def baseStart_2643176 : Nat := 118140960795 + 2643176 * 2 ^ 59
def prefixEnd_2643176 : Nat := 4983230072969 + 3 ^ 40 * 2643176 * 2
def baseEnd_2643176 : Nat := 452406580809485265148087

theorem tailTrace_2643176 : CollatzResearch.WordTrace tailWord_2643176 prefixEnd_2643176 452406580809485265148087 := by
  unfold tailWord_2643176
  simp only [CollatzResearch.WordTrace]
  refine ⟨48202274336116122683322691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64269699114821496911096921 48202274336116122683322691)
  ·
    refine ⟨72303411504174184024984037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48202274336116122683322691 72303411504174184024984037)
    ·
      refine ⟨13556889657032659504684507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72303411504174184024984037 13556889657032659504684507)
      ·
        refine ⟨20335334485548989257026761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13556889657032659504684507 20335334485548989257026761)
        ·
          refine ⟨15251500864161741942770071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20335334485548989257026761 15251500864161741942770071)
          ·
            refine ⟨22877251296242612914155107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15251500864161741942770071 22877251296242612914155107)
            ·
              refine ⟨34315876944363919371232661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22877251296242612914155107 34315876944363919371232661)
              ·
                refine ⟨1608556731767058720526531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34315876944363919371232661 1608556731767058720526531)
                ·
                  refine ⟨2412835097650588080789797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1608556731767058720526531 2412835097650588080789797)
                  ·
                    refine ⟨452406580809485265148087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2412835097650588080789797 452406580809485265148087)
                    ·
                      rfl

theorem cell23_2643176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_2643176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643176 prefixEnd_2643176 := by exact prefixLift 2643176
  have htrace : WordTrace (prefixWord ++ tailWord_2643176) baseStart_2643176 baseEnd_2643176 := by
    simpa [prefixWord, tailWord_2643176, baseEnd_2643176] using wordTrace_append hprefix tailTrace_2643176
  have hstable : (prefixWord ++ tailWord_2643176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643176).length < 2 ^ (prefixWord ++ tailWord_2643176).sum := by decide
  have hdescent : baseEnd_2643176 < baseStart_2643176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643209 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 1, 5, 2]
def baseStart_2643209 : Nat := 118140960795 + 2643209 * 2 ^ 59
def prefixEnd_2643209 : Nat := 4983230072969 + 3 ^ 40 * 2643209 * 2
def baseEnd_2643209 : Nat := 1357236687290054166331609

theorem tailTrace_2643209 : CollatzResearch.WordTrace tailWord_2643209 prefixEnd_2643209 1357236687290054166331609 := by
  unfold tailWord_2643209
  simp only [CollatzResearch.WordTrace]
  refine ⟨96405752281112692002596681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64270501520741794668397787 96405752281112692002596681)
  ·
    refine ⟨72304314210834519001947511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96405752281112692002596681 72304314210834519001947511)
    ·
      refine ⟨108456471316251778502921267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72304314210834519001947511 108456471316251778502921267)
      ·
        refine ⟨162684706974377667754381901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108456471316251778502921267 162684706974377667754381901)
        ·
          refine ⟨61006765115391625407893213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162684706974377667754381901 61006765115391625407893213)
          ·
            refine ⟨22877536918271859527959955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61006765115391625407893213 22877536918271859527959955)
            ·
              refine ⟨34316305377407789291939933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22877536918271859527959955 34316305377407789291939933)
              ·
                refine ⟨12868614516527920984477475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34316305377407789291939933 12868614516527920984477475)
                ·
                  refine ⟨19302921774791881476716213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12868614516527920984477475 19302921774791881476716213)
                  ·
                    refine ⟨1809648916386738888442145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19302921774791881476716213 1809648916386738888442145)
                    ·
                      refine ⟨1357236687290054166331609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1809648916386738888442145 1357236687290054166331609)
                      ·
                        rfl

theorem cell23_2643209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 5, 2].length) (baseStart_2643209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643209 prefixEnd_2643209 := by exact prefixLift 2643209
  have htrace : WordTrace (prefixWord ++ tailWord_2643209) baseStart_2643209 baseEnd_2643209 := by
    simpa [prefixWord, tailWord_2643209, baseEnd_2643209] using wordTrace_append hprefix tailTrace_2643209
  have hstable : (prefixWord ++ tailWord_2643209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643209).length < 2 ^ (prefixWord ++ tailWord_2643209).sum := by decide
  have hdescent : baseEnd_2643209 < baseStart_2643209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643226 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2]
def baseStart_2643226 : Nat := 118140960795 + 2643226 * 2 ^ 59
def prefixEnd_2643226 : Nat := 4983230072969 + 3 ^ 40 * 2643226 * 2
def baseEnd_2643226 : Nat := 1357245416461180599819031

theorem tailTrace_2643226 : CollatzResearch.WordTrace tailWord_2643226 prefixEnd_2643226 1357245416461180599819031 := by
  unfold tailWord_2643226
  simp only [CollatzResearch.WordTrace]
  refine ⟨24101593080512775976491383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64270914881367402603977021 24101593080512775976491383)
  ·
    refine ⟨36152389620769163964737075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24101593080512775976491383 36152389620769163964737075)
    ·
      refine ⟨54228584431153745947105613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36152389620769163964737075 54228584431153745947105613)
      ·
        refine ⟨20335719161682654730164605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54228584431153745947105613 20335719161682654730164605)
        ·
          refine ⟨7625894685630995523811727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20335719161682654730164605 7625894685630995523811727)
          ·
            refine ⟨11438842028446493285717591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7625894685630995523811727 11438842028446493285717591)
            ·
              refine ⟨17158263042669739928576387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11438842028446493285717591 17158263042669739928576387)
              ·
                refine ⟨25737394564004609892864581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17158263042669739928576387 25737394564004609892864581)
                ·
                  refine ⟨4825761480750864354912109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25737394564004609892864581 4825761480750864354912109)
                  ·
                    refine ⟨1809660555281574133092041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4825761480750864354912109 1809660555281574133092041)
                    ·
                      refine ⟨1357245416461180599819031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1809660555281574133092041 1357245416461180599819031)
                      ·
                        rfl

theorem cell23_2643226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_2643226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643226 prefixEnd_2643226 := by exact prefixLift 2643226
  have htrace : WordTrace (prefixWord ++ tailWord_2643226) baseStart_2643226 baseEnd_2643226 := by
    simpa [prefixWord, tailWord_2643226, baseEnd_2643226] using wordTrace_append hprefix tailTrace_2643226
  have hstable : (prefixWord ++ tailWord_2643226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643226).length < 2 ^ (prefixWord ++ tailWord_2643226).sum := by decide
  have hdescent : baseEnd_2643226 < baseStart_2643226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643256 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 5, 2, 2]
def baseStart_2643256 : Nat := 118140960795 + 2643256 * 2 ^ 59
def prefixEnd_2643256 : Nat := 4983230072969 + 3 ^ 40 * 2643256 * 2
def baseEnd_2643256 : Nat := 1357260820880815482443893

theorem tailTrace_2643256 : CollatzResearch.WordTrace tailWord_2643256 prefixEnd_2643256 1357260820880815482443893 := by
  unfold tailWord_2643256
  simp only [CollatzResearch.WordTrace]
  refine ⟨48203733255971209514778811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64271644341294946019705081 48203733255971209514778811)
  ·
    refine ⟨72305599883956814272168217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48203733255971209514778811 72305599883956814272168217)
    ·
      refine ⟨54229199912967610704126163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72305599883956814272168217 54229199912967610704126163)
      ·
        refine ⟨81343799869451416056189245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54229199912967610704126163 81343799869451416056189245)
        ·
          refine ⟨30503924951044281021070967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81343799869451416056189245 30503924951044281021070967)
          ·
            refine ⟨45755887426566421531606451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30503924951044281021070967 45755887426566421531606451)
            ·
              refine ⟨68633831139849632297409677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45755887426566421531606451 68633831139849632297409677)
              ·
                refine ⟨25737686677443612111528629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68633831139849632297409677 25737686677443612111528629)
                ·
                  refine ⟨2412908126010338635455809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25737686677443612111528629 2412908126010338635455809)
                  ·
                    refine ⟨1809681094507753976591857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2412908126010338635455809 1809681094507753976591857)
                    ·
                      refine ⟨1357260820880815482443893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1809681094507753976591857 1357260820880815482443893)
                      ·
                        rfl

theorem cell23_2643256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 5, 2, 2].length) (baseStart_2643256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643256 prefixEnd_2643256 := by exact prefixLift 2643256
  have htrace : WordTrace (prefixWord ++ tailWord_2643256) baseStart_2643256 baseEnd_2643256 := by
    simpa [prefixWord, tailWord_2643256, baseEnd_2643256] using wordTrace_append hprefix tailTrace_2643256
  have hstable : (prefixWord ++ tailWord_2643256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643256).length < 2 ^ (prefixWord ++ tailWord_2643256).sum := by decide
  have hdescent : baseEnd_2643256 < baseStart_2643256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643276 : List Nat := [2, 2, 1, 3, 2, 4, 1, 1, 1, 1, 5]
def baseStart_2643276 : Nat := 118140960795 + 2643276 * 2 ^ 59
def prefixEnd_2643276 : Nat := 4983230072969 + 3 ^ 40 * 2643276 * 2
def baseEnd_2643276 : Nat := 1357271090493905404193801

theorem tailTrace_2643276 : CollatzResearch.WordTrace tailWord_2643276 prefixEnd_2643276 1357271090493905404193801 := by
  unfold tailWord_2643276
  simp only [CollatzResearch.WordTrace]
  refine ⟨48204097985934981222642841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64272130647913308296857121 48204097985934981222642841)
  ·
    refine ⟨36153073489451235916982131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48204097985934981222642841 36153073489451235916982131)
    ·
      refine ⟨54229610234176853875473197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36153073489451235916982131 54229610234176853875473197)
      ·
        refine ⟨20336103837816320203302449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54229610234176853875473197 20336103837816320203302449)
        ·
          refine ⟨15252077878362240152476837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20336103837816320203302449 15252077878362240152476837)
          ·
            refine ⟨2859764602192920028589407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15252077878362240152476837 2859764602192920028589407)
            ·
              refine ⟨4289646903289380042884111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2859764602192920028589407 4289646903289380042884111)
              ·
                refine ⟨6434470354934070064326167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4289646903289380042884111 6434470354934070064326167)
                ·
                  refine ⟨9651705532401105096489251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6434470354934070064326167 9651705532401105096489251)
                  ·
                    refine ⟨14477558298601657644733877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9651705532401105096489251 14477558298601657644733877)
                    ·
                      refine ⟨1357271090493905404193801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14477558298601657644733877 1357271090493905404193801)
                      ·
                        rfl

theorem cell23_2643276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_2643276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643276 prefixEnd_2643276 := by exact prefixLift 2643276
  have htrace : WordTrace (prefixWord ++ tailWord_2643276) baseStart_2643276 baseEnd_2643276 := by
    simpa [prefixWord, tailWord_2643276, baseEnd_2643276] using wordTrace_append hprefix tailTrace_2643276
  have hstable : (prefixWord ++ tailWord_2643276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643276).length < 2 ^ (prefixWord ++ tailWord_2643276).sum := by decide
  have hdescent : baseEnd_2643276 < baseStart_2643276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643349 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 1, 6, 3]
def baseStart_2643349 : Nat := 118140960795 + 2643349 * 2 ^ 59
def prefixEnd_2643349 : Nat := 4983230072969 + 3 ^ 40 * 2643349 * 2
def baseEnd_2643349 : Nat := 1357308574581683618580965

theorem tailTrace_2643349 : CollatzResearch.WordTrace tailWord_2643349 prefixEnd_2643349 1357308574581683618580965 := by
  unfold tailWord_2643349
  simp only [CollatzResearch.WordTrace]
  refine ⟨96410858500605495912693101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64273905667070330608462067 96410858500605495912693101)
  ·
    refine ⟨36154071937727060967259913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96410858500605495912693101 36154071937727060967259913)
    ·
      refine ⟨27115553953295295725444935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36154071937727060967259913 27115553953295295725444935)
      ·
        refine ⟨40673330929942943588167403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27115553953295295725444935 40673330929942943588167403)
        ·
          refine ⟨61009996394914415382251105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40673330929942943588167403 61009996394914415382251105)
          ·
            refine ⟨45757497296185811536688329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61009996394914415382251105 45757497296185811536688329)
            ·
              refine ⟨34318122972139358652516247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45757497296185811536688329 34318122972139358652516247)
              ·
                refine ⟨51477184458209037978774371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34318122972139358652516247 51477184458209037978774371)
                ·
                  refine ⟨77215776687313556968161557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51477184458209037978774371 77215776687313556968161557)
                  ·
                    refine ⟨3619489532217822982882573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77215776687313556968161557 3619489532217822982882573)
                    ·
                      refine ⟨1357308574581683618580965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3619489532217822982882573 1357308574581683618580965)
                      ·
                        rfl

theorem cell23_2643349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_2643349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643349 prefixEnd_2643349 := by exact prefixLift 2643349
  have htrace : WordTrace (prefixWord ++ tailWord_2643349) baseStart_2643349 baseEnd_2643349 := by
    simpa [prefixWord, tailWord_2643349, baseEnd_2643349] using wordTrace_append hprefix tailTrace_2643349
  have hstable : (prefixWord ++ tailWord_2643349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643349).length < 2 ^ (prefixWord ++ tailWord_2643349).sum := by decide
  have hdescent : baseEnd_2643349 < baseStart_2643349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643379 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 3]
def baseStart_2643379 : Nat := 118140960795 + 2643379 * 2 ^ 59
def prefixEnd_2643379 : Nat := 4983230072969 + 3 ^ 40 * 2643379 * 2
def baseEnd_2643379 : Nat := 1357323979001318501205827

theorem tailTrace_2643379 : CollatzResearch.WordTrace tailWord_2643379 prefixEnd_2643379 1357323979001318501205827 := by
  unfold tailWord_2643379
  simp only [CollatzResearch.WordTrace]
  refine ⟨96411952690496811036285191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64274635126997874024190127 96411952690496811036285191)
  ·
    refine ⟨144617929035745216554427787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96411952690496811036285191 144617929035745216554427787)
    ·
      refine ⟨216926893553617824831641681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144617929035745216554427787 216926893553617824831641681)
      ·
        refine ⟨162695170165213368623731261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216926893553617824831641681 162695170165213368623731261)
        ·
          refine ⟨61010688811955013233899223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162695170165213368623731261 61010688811955013233899223)
          ·
            refine ⟨91516033217932519850848835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61010688811955013233899223 91516033217932519850848835)
            ·
              refine ⟨137274049826898779776273253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91516033217932519850848835 137274049826898779776273253)
              ·
                refine ⟨25738884342543521208051235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137274049826898779776273253 25738884342543521208051235)
                ·
                  refine ⟨38608326513815281812076853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25738884342543521208051235 38608326513815281812076853)
                  ·
                    refine ⟨3619530610670182669882205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38608326513815281812076853 3619530610670182669882205)
                    ·
                      refine ⟨1357323979001318501205827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3619530610670182669882205 1357323979001318501205827)
                      ·
                        rfl

theorem cell23_2643379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 3].length) (baseStart_2643379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643379 prefixEnd_2643379 := by exact prefixLift 2643379
  have htrace : WordTrace (prefixWord ++ tailWord_2643379) baseStart_2643379 baseEnd_2643379 := by
    simpa [prefixWord, tailWord_2643379, baseEnd_2643379] using wordTrace_append hprefix tailTrace_2643379
  have hstable : (prefixWord ++ tailWord_2643379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643379).length < 2 ^ (prefixWord ++ tailWord_2643379).sum := by decide
  have hdescent : baseEnd_2643379 < baseStart_2643379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
