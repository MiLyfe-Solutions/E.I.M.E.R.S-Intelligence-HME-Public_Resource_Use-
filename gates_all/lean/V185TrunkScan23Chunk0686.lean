import V185TrunkScan23Chunk0685

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4056476 : List Nat := [2, 2, 3, 4, 1, 2, 1, 1, 3, 1, 3]
def baseStart_4056476 : Nat := 118140960795 + 4056476 * 2 ^ 59
def prefixEnd_4056476 : Nat := 4983230072969 + 3 ^ 40 * 4056476 * 2
def baseEnd_4056476 : Nat := 2082921951427776252694613

theorem tailTrace_4056476 : CollatzResearch.WordTrace tailWord_4056476 prefixEnd_4056476 2082921951427776252694613 := by
  unfold tailWord_4056476
  simp only [CollatzResearch.WordTrace]
  refine ⟨73975917226043858895002641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98634556301391811860003521 73975917226043858895002641)
  ·
    refine ⟨55481937919532894171251981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73975917226043858895002641 55481937919532894171251981)
    ·
      refine ⟨20805726719824835314219493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55481937919532894171251981 20805726719824835314219493)
      ·
        refine ⟨3901073759967156621416155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20805726719824835314219493 3901073759967156621416155)
        ·
          refine ⟨5851610639950734932124233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3901073759967156621416155 5851610639950734932124233)
          ·
            refine ⟨4388707979963051199093175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5851610639950734932124233 4388707979963051199093175)
            ·
              refine ⟨6583061969944576798639763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4388707979963051199093175 6583061969944576798639763)
              ·
                refine ⟨9874592954916865197959645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6583061969944576798639763 9874592954916865197959645)
                ·
                  refine ⟨3702972358093824449234867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9874592954916865197959645 3702972358093824449234867)
                  ·
                    refine ⟨5554458537140736673852301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3702972358093824449234867 5554458537140736673852301)
                    ·
                      refine ⟨2082921951427776252694613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5554458537140736673852301 2082921951427776252694613)
                      ·
                        rfl

theorem cell23_4056476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_4056476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056476 prefixEnd_4056476 := by exact prefixLift 4056476
  have htrace : WordTrace (prefixWord ++ tailWord_4056476) baseStart_4056476 baseEnd_4056476 := by
    simpa [prefixWord, tailWord_4056476, baseEnd_4056476] using wordTrace_append hprefix tailTrace_4056476
  have hstable : (prefixWord ++ tailWord_4056476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056476).length < 2 ^ (prefixWord ++ tailWord_4056476).sum := by decide
  have hdescent : baseEnd_4056476 < baseStart_4056476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056492 : List Nat := [2, 2, 1, 1, 1, 1, 8, 1, 2, 4]
def baseStart_4056492 : Nat := 118140960795 + 4056492 * 2 ^ 59
def prefixEnd_4056492 : Nat := 4983230072969 + 3 ^ 40 * 4056492 * 2
def baseEnd_4056492 : Nat := 694310055706082730031513

theorem tailTrace_4056492 : CollatzResearch.WordTrace tailWord_4056492 prefixEnd_4056492 694310055706082730031513 := by
  unfold tailWord_4056492
  simp only [CollatzResearch.WordTrace]
  refine ⟨73976209010014876261293865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98634945346686501681725153 73976209010014876261293865)
  ·
    refine ⟨55482156757511157195970399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73976209010014876261293865 55482156757511157195970399)
    ·
      refine ⟨83223235136266735793955599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55482156757511157195970399 83223235136266735793955599)
      ·
        refine ⟨124834852704400103690933399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83223235136266735793955599 124834852704400103690933399)
        ·
          refine ⟨187252279056600155536400099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124834852704400103690933399 187252279056600155536400099)
          ·
            refine ⟨280878418584900233304600149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187252279056600155536400099 280878418584900233304600149)
            ·
              refine ⟨3291543967791799609038283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 280878418584900233304600149 3291543967791799609038283)
              ·
                refine ⟨4937315951687699413557425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3291543967791799609038283 4937315951687699413557425)
                ·
                  refine ⟨3702986963765774560168069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4937315951687699413557425 3702986963765774560168069)
                  ·
                    refine ⟨694310055706082730031513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3702986963765774560168069 694310055706082730031513)
                    ·
                      rfl

theorem cell23_4056492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 4].length) (baseStart_4056492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056492 prefixEnd_4056492 := by exact prefixLift 4056492
  have htrace : WordTrace (prefixWord ++ tailWord_4056492) baseStart_4056492 baseEnd_4056492 := by
    simpa [prefixWord, tailWord_4056492, baseEnd_4056492] using wordTrace_append hprefix tailTrace_4056492
  have hstable : (prefixWord ++ tailWord_4056492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056492).length < 2 ^ (prefixWord ++ tailWord_4056492).sum := by decide
  have hdescent : baseEnd_4056492 < baseStart_4056492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056515 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 6, 1, 3]
def baseStart_4056515 : Nat := 118140960795 + 4056515 * 2 ^ 59
def prefixEnd_4056515 : Nat := 4983230072969 + 3 ^ 40 * 4056515 * 2
def baseEnd_4056515 : Nat := 2082941977173301600106933

theorem tailTrace_4056515 : CollatzResearch.WordTrace tailWord_4056515 prefixEnd_4056515 2082941977173301600106933 := by
  unfold tailWord_4056515
  simp only [CollatzResearch.WordTrace]
  refine ⟨147953256898946427450674999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98635504599297618300449999 147953256898946427450674999)
  ·
    refine ⟨221929885348419641176012499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147953256898946427450674999 221929885348419641176012499)
    ·
      refine ⟨332894828022629461764018749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221929885348419641176012499 332894828022629461764018749)
      ·
        refine ⟨124835560508486048161507031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332894828022629461764018749 124835560508486048161507031)
        ·
          refine ⟨187253340762729072242260547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124835560508486048161507031 187253340762729072242260547)
          ·
            refine ⟨280880011144093608363390821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187253340762729072242260547 280880011144093608363390821)
            ·
              refine ⟨52665002089517551568135779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280880011144093608363390821 52665002089517551568135779)
              ·
                refine ⟨78997503134276327352203669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52665002089517551568135779 78997503134276327352203669)
                ·
                  refine ⟨3703007959419202844634547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78997503134276327352203669 3703007959419202844634547)
                  ·
                    refine ⟨5554511939128804266951821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3703007959419202844634547 5554511939128804266951821)
                    ·
                      refine ⟨2082941977173301600106933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5554511939128804266951821 2082941977173301600106933)
                      ·
                        rfl

theorem cell23_4056515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 1, 3].length) (baseStart_4056515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056515 prefixEnd_4056515 := by exact prefixLift 4056515
  have htrace : WordTrace (prefixWord ++ tailWord_4056515) baseStart_4056515 baseEnd_4056515 := by
    simpa [prefixWord, tailWord_4056515, baseEnd_4056515] using wordTrace_append hprefix tailTrace_4056515
  have hstable : (prefixWord ++ tailWord_4056515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056515).length < 2 ^ (prefixWord ++ tailWord_4056515).sum := by decide
  have hdescent : baseEnd_4056515 < baseStart_4056515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056549 : List Nat := [1, 3, 1, 5, 1, 1, 2, 3, 2, 1, 3]
def baseStart_4056549 : Nat := 118140960795 + 4056549 * 2 ^ 59
def prefixEnd_4056549 : Nat := 4983230072969 + 3 ^ 40 * 4056549 * 2
def baseEnd_4056549 : Nat := 2082959435515554467081777

theorem tailTrace_4056549 : CollatzResearch.WordTrace tailWord_4056549 prefixEnd_4056549 2082959435515554467081777 := by
  unfold tailWord_4056549
  simp only [CollatzResearch.WordTrace]
  refine ⟨147954496980823251257412701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98636331320548834171608467 147954496980823251257412701)
  ·
    refine ⟨55482936367808719221529763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147954496980823251257412701 55482936367808719221529763)
    ·
      refine ⟨83224404551713078832294645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55482936367808719221529763 83224404551713078832294645)
      ·
        refine ⟨7802287926723101140527623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83224404551713078832294645 7802287926723101140527623)
        ·
          refine ⟨11703431890084651710791435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7802287926723101140527623 11703431890084651710791435)
          ·
            refine ⟨17555147835126977566187153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11703431890084651710791435 17555147835126977566187153)
            ·
              refine ⟨13166360876345233174640365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17555147835126977566187153 13166360876345233174640365)
              ·
                refine ⟨4937385328629462440490137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13166360876345233174640365 4937385328629462440490137)
                ·
                  refine ⟨3703038996472096830367603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4937385328629462440490137 3703038996472096830367603)
                  ·
                    refine ⟨5554558494708145245551405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3703038996472096830367603 5554558494708145245551405)
                    ·
                      refine ⟨2082959435515554467081777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5554558494708145245551405 2082959435515554467081777)
                      ·
                        rfl

theorem cell23_4056549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_4056549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056549 prefixEnd_4056549 := by exact prefixLift 4056549
  have htrace : WordTrace (prefixWord ++ tailWord_4056549) baseStart_4056549 baseEnd_4056549 := by
    simpa [prefixWord, tailWord_4056549, baseEnd_4056549] using wordTrace_append hprefix tailTrace_4056549
  have hstable : (prefixWord ++ tailWord_4056549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056549).length < 2 ^ (prefixWord ++ tailWord_4056549).sum := by decide
  have hdescent : baseEnd_4056549 < baseStart_4056549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056572 : List Nat := [2, 2, 2, 1, 2, 1, 4, 2, 1, 4, 2]
def baseStart_4056572 : Nat := 118140960795 + 4056572 * 2 ^ 59
def prefixEnd_4056572 : Nat := 4983230072969 + 3 ^ 40 * 4056572 * 2
def baseEnd_4056572 : Nat := 2082971245570607877094171

theorem tailTrace_4056572 : CollatzResearch.WordTrace tailWord_4056572 prefixEnd_4056572 2082971245570607877094171 := by
  unfold tailWord_4056572
  simp only [CollatzResearch.WordTrace]
  refine ⟨73977667929869963092749985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98636890573159950790333313 73977667929869963092749985)
  ·
    refine ⟨55483250947402472319562489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73977667929869963092749985 55483250947402472319562489)
    ·
      refine ⟨41612438210551854239671867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55483250947402472319562489 41612438210551854239671867)
      ·
        refine ⟨62418657315827781359507801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41612438210551854239671867 62418657315827781359507801)
        ·
          refine ⟨46813992986870836019630851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62418657315827781359507801 46813992986870836019630851)
          ·
            refine ⟨70220989480306254029446277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46813992986870836019630851 70220989480306254029446277)
            ·
              refine ⟨13166435527557422630521177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70220989480306254029446277 13166435527557422630521177)
              ·
                refine ⟨9874826645668066972890883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13166435527557422630521177 9874826645668066972890883)
                ·
                  refine ⟨14812239968502100459336325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9874826645668066972890883 14812239968502100459336325)
                  ·
                    refine ⟨2777294994094143836125561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14812239968502100459336325 2777294994094143836125561)
                    ·
                      refine ⟨2082971245570607877094171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2777294994094143836125561 2082971245570607877094171)
                      ·
                        rfl

theorem cell23_4056572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_4056572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056572 prefixEnd_4056572 := by exact prefixLift 4056572
  have htrace : WordTrace (prefixWord ++ tailWord_4056572) baseStart_4056572 baseEnd_4056572 := by
    simpa [prefixWord, tailWord_4056572, baseEnd_4056572] using wordTrace_append hprefix tailTrace_4056572
  have hstable : (prefixWord ++ tailWord_4056572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056572).length < 2 ^ (prefixWord ++ tailWord_4056572).sum := by decide
  have hdescent : baseEnd_4056572 < baseStart_4056572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056595 : List Nat := [1, 1, 1, 2, 1, 7, 2, 1, 7]
def baseStart_4056595 : Nat := 118140960795 + 4056595 * 2 ^ 59
def prefixEnd_4056595 : Nat := 4983230072969 + 3 ^ 40 * 4056595 * 2
def baseEnd_4056595 : Nat := 231442561736184587456285

theorem tailTrace_4056595 : CollatzResearch.WordTrace tailWord_4056595 prefixEnd_4056595 231442561736184587456285 := by
  unfold tailWord_4056595
  simp only [CollatzResearch.WordTrace]
  refine ⟨147956174738656601113587239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98637449825771067409058159 147956174738656601113587239)
  ·
    refine ⟨221934262107984901670380859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147956174738656601113587239 221934262107984901670380859)
    ·
      refine ⟨332901393161977352505571289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221934262107984901670380859 332901393161977352505571289)
      ·
        refine ⟨249676044871483014379178467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332901393161977352505571289 249676044871483014379178467)
        ·
          refine ⟨374514067307224521568767701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249676044871483014379178467 374514067307224521568767701)
          ·
            refine ⟨8777673452513074724267993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 374514067307224521568767701 8777673452513074724267993)
            ·
              refine ⟨6583255089384806043200995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8777673452513074724267993 6583255089384806043200995)
              ·
                refine ⟨9874882634077209064801493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6583255089384806043200995 9874882634077209064801493)
                ·
                  refine ⟨231442561736184587456285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9874882634077209064801493 231442561736184587456285)
                  ·
                    rfl

theorem cell23_4056595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 7].length) (baseStart_4056595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056595 prefixEnd_4056595 := by exact prefixLift 4056595
  have htrace : WordTrace (prefixWord ++ tailWord_4056595) baseStart_4056595 baseEnd_4056595 := by
    simpa [prefixWord, tailWord_4056595, baseEnd_4056595] using wordTrace_append hprefix tailTrace_4056595
  have hstable : (prefixWord ++ tailWord_4056595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056595).length < 2 ^ (prefixWord ++ tailWord_4056595).sum := by decide
  have hdescent : baseEnd_4056595 < baseStart_4056595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056625 : List Nat := [1, 2, 2, 3, 1, 1, 1, 5, 2, 5]
def baseStart_4056625 : Nat := 118140960795 + 4056625 * 2 ^ 59
def prefixEnd_4056625 : Nat := 4983230072969 + 3 ^ 40 * 4056625 * 2
def baseEnd_4056625 : Nat := 694332820015098723243809

theorem tailTrace_4056625 : CollatzResearch.WordTrace tailWord_4056625 prefixEnd_4056625 694332820015098723243809 := by
  unfold tailWord_4056625
  simp only [CollatzResearch.WordTrace]
  refine ⟨147957268928547916237179329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98638179285698610824786219 147957268928547916237179329)
  ·
    refine ⟨110967951696410937177884497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147957268928547916237179329 110967951696410937177884497)
    ·
      refine ⟨83225963772308202883413373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110967951696410937177884497 83225963772308202883413373)
      ·
        refine ⟨31209736414615576081280015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83225963772308202883413373 31209736414615576081280015)
        ·
          refine ⟨46814604621923364121920023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31209736414615576081280015 46814604621923364121920023)
          ·
            refine ⟨70221906932885046182880035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46814604621923364121920023 70221906932885046182880035)
            ·
              refine ⟨105332860399327569274320053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70221906932885046182880035 105332860399327569274320053)
              ·
                refine ⟨9874955662436959619467505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105332860399327569274320053 9874955662436959619467505)
                ·
                  refine ⟨7406216746827719714600629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9874955662436959619467505 7406216746827719714600629)
                  ·
                    refine ⟨694332820015098723243809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7406216746827719714600629 694332820015098723243809)
                    ·
                      rfl

theorem cell23_4056625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_4056625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056625 prefixEnd_4056625 := by exact prefixLift 4056625
  have htrace : WordTrace (prefixWord ++ tailWord_4056625) baseStart_4056625 baseEnd_4056625 := by
    simpa [prefixWord, tailWord_4056625, baseEnd_4056625] using wordTrace_append hprefix tailTrace_4056625
  have hstable : (prefixWord ++ tailWord_4056625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056625).length < 2 ^ (prefixWord ++ tailWord_4056625).sum := by decide
  have hdescent : baseEnd_4056625 < baseStart_4056625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056629 : List Nat := [1, 3, 3, 1, 1, 5, 1, 3, 5]
def baseStart_4056629 : Nat := 118140960795 + 4056629 * 2 ^ 59
def prefixEnd_4056629 : Nat := 4983230072969 + 3 ^ 40 * 4056629 * 2
def baseEnd_4056629 : Nat := 231444501551990461564601

theorem tailTrace_4056629 : CollatzResearch.WordTrace tailWord_4056629 prefixEnd_4056629 231444501551990461564601 := by
  unfold tailWord_4056629
  simp only [CollatzResearch.WordTrace]
  refine ⟨147957414820533424920324941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98638276547022283280216627 147957414820533424920324941)
  ·
    refine ⟨55484030557700034345121853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147957414820533424920324941 55484030557700034345121853)
    ·
      refine ⟨20806511459137512879420695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55484030557700034345121853 20806511459137512879420695)
      ·
        refine ⟨31209767188706269319131043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20806511459137512879420695 31209767188706269319131043)
        ·
          refine ⟨46814650783059403978696565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31209767188706269319131043 46814650783059403978696565)
          ·
            refine ⟨4388873510911819123002803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46814650783059403978696565 4388873510911819123002803)
            ·
              refine ⟨6583310266367728684504205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4388873510911819123002803 6583310266367728684504205)
              ·
                refine ⟨2468741349887898256689077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6583310266367728684504205 2468741349887898256689077)
                ·
                  refine ⟨231444501551990461564601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2468741349887898256689077 231444501551990461564601)
                  ·
                    rfl

theorem cell23_4056629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 5].length) (baseStart_4056629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056629 prefixEnd_4056629 := by exact prefixLift 4056629
  have htrace : WordTrace (prefixWord ++ tailWord_4056629) baseStart_4056629 baseEnd_4056629 := by
    simpa [prefixWord, tailWord_4056629, baseEnd_4056629] using wordTrace_append hprefix tailTrace_4056629
  have hstable : (prefixWord ++ tailWord_4056629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056629).length < 2 ^ (prefixWord ++ tailWord_4056629).sum := by decide
  have hdescent : baseEnd_4056629 < baseStart_4056629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056646 : List Nat := [6, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_4056646 : Nat := 118140960795 + 4056646 * 2 ^ 59
def prefixEnd_4056646 : Nat := 4983230072969 + 3 ^ 40 * 4056646 * 2
def baseEnd_4056646 : Nat := 231445471459893398618759

theorem tailTrace_4056646 : CollatzResearch.WordTrace tailWord_4056646 prefixEnd_4056646 231445471459893398618759 := by
  unfold tailWord_4056646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4623688589420994900740431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98638689907647891215795861 4623688589420994900740431)
  ·
    refine ⟨6935532884131492351110647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4623688589420994900740431 6935532884131492351110647)
    ·
      refine ⟨10403299326197238526665971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6935532884131492351110647 10403299326197238526665971)
      ·
        refine ⟨15604948989295857789998957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10403299326197238526665971 15604948989295857789998957)
        ·
          refine ⟨5851855870985946671249609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15604948989295857789998957 5851855870985946671249609)
          ·
            refine ⟨4388891903239460003437207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5851855870985946671249609 4388891903239460003437207)
            ·
              refine ⟨6583337854859190005155811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4388891903239460003437207 6583337854859190005155811)
              ·
                refine ⟨9875006782288785007733717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6583337854859190005155811 9875006782288785007733717)
                ·
                  refine ⟨231445471459893398618759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9875006782288785007733717 231445471459893398618759)
                  ·
                    rfl

theorem cell23_4056646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_4056646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056646 prefixEnd_4056646 := by exact prefixLift 4056646
  have htrace : WordTrace (prefixWord ++ tailWord_4056646) baseStart_4056646 baseEnd_4056646 := by
    simpa [prefixWord, tailWord_4056646, baseEnd_4056646] using wordTrace_append hprefix tailTrace_4056646
  have hstable : (prefixWord ++ tailWord_4056646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056646).length < 2 ^ (prefixWord ++ tailWord_4056646).sum := by decide
  have hdescent : baseEnd_4056646 < baseStart_4056646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056665 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 3, 4, 3]
def baseStart_4056665 : Nat := 118140960795 + 4056665 * 2 ^ 59
def prefixEnd_4056665 : Nat := 4983230072969 + 3 ^ 40 * 4056665 * 2
def baseEnd_4056665 : Nat := 2083018999271476013231243

theorem tailTrace_4056665 : CollatzResearch.WordTrace tailWord_4056665 prefixEnd_4056665 2083018999271476013231243 := by
  unfold tailWord_4056665
  simp only [CollatzResearch.WordTrace]
  refine ⟨147958727848403003068635449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98639151898935335379090299 147958727848403003068635449)
  ·
    refine ⟨110969045886302252301476587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147958727848403003068635449 110969045886302252301476587)
    ·
      refine ⟨166453568829453378452214881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110969045886302252301476587 166453568829453378452214881)
      ·
        refine ⟨124840176622090033839161161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166453568829453378452214881 124840176622090033839161161)
        ·
          refine ⟨93630132466567525379370871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124840176622090033839161161 93630132466567525379370871)
          ·
            refine ⟨140445198699851288069056307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93630132466567525379370871 140445198699851288069056307)
            ·
              refine ⟨210667798049776932103584461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140445198699851288069056307 210667798049776932103584461)
              ·
                refine ⟨79000424268666349538844173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210667798049776932103584461 79000424268666349538844173)
                ·
                  refine ⟨29625159100749881077066565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79000424268666349538844173 29625159100749881077066565)
                  ·
                    refine ⟨5554717331390602701949981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29625159100749881077066565 5554717331390602701949981)
                    ·
                      refine ⟨2083018999271476013231243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5554717331390602701949981 2083018999271476013231243)
                      ·
                        rfl

theorem cell23_4056665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_4056665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056665 prefixEnd_4056665 := by exact prefixLift 4056665
  have htrace : WordTrace (prefixWord ++ tailWord_4056665) baseStart_4056665 baseEnd_4056665 := by
    simpa [prefixWord, tailWord_4056665, baseEnd_4056665] using wordTrace_append hprefix tailTrace_4056665
  have hstable : (prefixWord ++ tailWord_4056665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056665).length < 2 ^ (prefixWord ++ tailWord_4056665).sum := by decide
  have hdescent : baseEnd_4056665 < baseStart_4056665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056715 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 5, 5]
def baseStart_4056715 : Nat := 118140960795 + 4056715 * 2 ^ 59
def prefixEnd_4056715 : Nat := 4983230072969 + 3 ^ 40 * 4056715 * 2
def baseEnd_4056715 : Nat := 694348224434733605868671

theorem tailTrace_4056715 : CollatzResearch.WordTrace tailWord_4056715 prefixEnd_4056715 694348224434733605868671 := by
  unfold tailWord_4056715
  simp only [CollatzResearch.WordTrace]
  refine ⟨147960551498221861607955599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98640367665481241071970399 147960551498221861607955599)
  ·
    refine ⟨221940827247332792411933399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147960551498221861607955599 221940827247332792411933399)
    ·
      refine ⟨332911240870999188617900099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221940827247332792411933399 332911240870999188617900099)
      ·
        refine ⟨499366861306498782926850149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332911240870999188617900099 499366861306498782926850149)
        ·
          refine ⟨93631286494968521798784403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 499366861306498782926850149 93631286494968521798784403)
          ·
            refine ⟨140446929742452782698176605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93631286494968521798784403 140446929742452782698176605)
            ·
              refine ⟨52667598653419793511816227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140446929742452782698176605 52667598653419793511816227)
              ·
                refine ⟨79001397980129690267724341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52667598653419793511816227 79001397980129690267724341)
                ·
                  refine ⟨7406381060637158462599157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79001397980129690267724341 7406381060637158462599157)
                  ·
                    refine ⟨694348224434733605868671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7406381060637158462599157 694348224434733605868671)
                    ·
                      rfl

theorem cell23_4056715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 5].length) (baseStart_4056715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056715 prefixEnd_4056715 := by exact prefixLift 4056715
  have htrace : WordTrace (prefixWord ++ tailWord_4056715) baseStart_4056715 baseEnd_4056715 := by
    simpa [prefixWord, tailWord_4056715, baseEnd_4056715] using wordTrace_append hprefix tailTrace_4056715
  have hstable : (prefixWord ++ tailWord_4056715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056715).length < 2 ^ (prefixWord ++ tailWord_4056715).sum := by decide
  have hdescent : baseEnd_4056715 < baseStart_4056715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056749 : List Nat := [1, 5, 2, 1, 1, 1, 3, 3, 1, 5]
def baseStart_4056749 : Nat := 118140960795 + 4056749 * 2 ^ 59
def prefixEnd_4056749 : Nat := 4983230072969 + 3 ^ 40 * 4056749 * 2
def baseEnd_4056749 : Nat := 694354043882151228193619

theorem tailTrace_4056749 : CollatzResearch.WordTrace tailWord_4056749 prefixEnd_4056749 694354043882151228193619 := by
  unfold tailWord_4056749
  simp only [CollatzResearch.WordTrace]
  refine ⟨147961791580098685414693301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98641194386732456943128867 147961791580098685414693301)
  ·
    refine ⟨13871417960634251757627497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147961791580098685414693301 13871417960634251757627497)
    ·
      refine ⟨10403563470475688818220623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13871417960634251757627497 10403563470475688818220623)
      ·
        refine ⟨15605345205713533227330935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10403563470475688818220623 15605345205713533227330935)
        ·
          refine ⟨23408017808570299840996403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15605345205713533227330935 23408017808570299840996403)
          ·
            refine ⟨35112026712855449761494605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23408017808570299840996403 35112026712855449761494605)
            ·
              refine ⟨13167010017320793660560477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35112026712855449761494605 13167010017320793660560477)
              ·
                refine ⟨4937628756495297622710179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13167010017320793660560477 4937628756495297622710179)
                ·
                  refine ⟨7406443134742946434065269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4937628756495297622710179 7406443134742946434065269)
                  ·
                    refine ⟨694354043882151228193619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7406443134742946434065269 694354043882151228193619)
                    ·
                      rfl

theorem cell23_4056749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_4056749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056749 prefixEnd_4056749 := by exact prefixLift 4056749
  have htrace : WordTrace (prefixWord ++ tailWord_4056749) baseStart_4056749 baseEnd_4056749 := by
    simpa [prefixWord, tailWord_4056749, baseEnd_4056749] using wordTrace_append hprefix tailTrace_4056749
  have hstable : (prefixWord ++ tailWord_4056749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056749).length < 2 ^ (prefixWord ++ tailWord_4056749).sum := by decide
  have hdescent : baseEnd_4056749 < baseStart_4056749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056770 : List Nat := [3, 5, 1, 2, 1, 1, 3, 1, 6]
def baseStart_4056770 : Nat := 118140960795 + 4056770 * 2 ^ 59
def prefixEnd_4056770 : Nat := 4983230072969 + 3 ^ 40 * 4056770 * 2
def baseEnd_4056770 : Nat := 231452546082244233602029

theorem tailTrace_4056770 : CollatzResearch.WordTrace tailWord_4056770 prefixEnd_4056770 231452546082244233602029 := by
  unfold tailWord_4056770
  simp only [CollatzResearch.WordTrace]
  refine ⟨36990639378255651500301941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98641705008681737334138509 36990639378255651500301941)
  ·
    refine ⟨3467872441711467328153307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36990639378255651500301941 3467872441711467328153307)
    ·
      refine ⟨5201808662567200992229961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3467872441711467328153307 5201808662567200992229961)
      ·
        refine ⟨3901356496925400744172471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5201808662567200992229961 3901356496925400744172471)
        ·
          refine ⟨5852034745388101116258707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3901356496925400744172471 5852034745388101116258707)
          ·
            refine ⟨8778052118082151674388061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5852034745388101116258707 8778052118082151674388061)
            ·
              refine ⟨3291769544280806877895523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8778052118082151674388061 3291769544280806877895523)
              ·
                refine ⟨4937654316421210316843285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3291769544280806877895523 4937654316421210316843285)
                ·
                  refine ⟨231452546082244233602029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4937654316421210316843285 231452546082244233602029)
                  ·
                    rfl

theorem cell23_4056770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_4056770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056770 prefixEnd_4056770 := by exact prefixLift 4056770
  have htrace : WordTrace (prefixWord ++ tailWord_4056770) baseStart_4056770 baseEnd_4056770 := by
    simpa [prefixWord, tailWord_4056770, baseEnd_4056770] using wordTrace_append hprefix tailTrace_4056770
  have hstable : (prefixWord ++ tailWord_4056770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056770).length < 2 ^ (prefixWord ++ tailWord_4056770).sum := by decide
  have hdescent : baseEnd_4056770 < baseStart_4056770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056775 : List Nat := [1, 1, 4, 1, 1, 1, 4, 10]
def baseStart_4056775 : Nat := 118140960795 + 4056775 * 2 ^ 59
def prefixEnd_4056775 : Nat := 4983230072969 + 3 ^ 40 * 4056775 * 2
def baseEnd_4056775 : Nat := 77150943783091503068731

theorem tailTrace_4056775 : CollatzResearch.WordTrace tailWord_4056775 prefixEnd_4056775 77150943783091503068731 := by
  unfold tailWord_4056775
  simp only [CollatzResearch.WordTrace]
  refine ⟨147962739878004491855139779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98641826585336327903426519 147962739878004491855139779)
  ·
    refine ⟨221944109817006737782709669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147962739878004491855139779 221944109817006737782709669)
    ·
      refine ⟨41614520590688763334258063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221944109817006737782709669 41614520590688763334258063)
      ·
        refine ⟨62421780886033145001387095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41614520590688763334258063 62421780886033145001387095)
        ·
          refine ⟨93632671329049717502080643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62421780886033145001387095 93632671329049717502080643)
          ·
            refine ⟨140449006993574576253120965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93632671329049717502080643 140449006993574576253120965)
            ·
              refine ⟨26334188811295233047460181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140449006993574576253120965 26334188811295233047460181)
              ·
                refine ⟨77150943783091503068731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26334188811295233047460181 77150943783091503068731)
                ·
                  rfl

theorem cell23_4056775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 10].length) (baseStart_4056775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056775 prefixEnd_4056775 := by exact prefixLift 4056775
  have htrace : WordTrace (prefixWord ++ tailWord_4056775) baseStart_4056775 baseEnd_4056775 := by
    simpa [prefixWord, tailWord_4056775, baseEnd_4056775] using wordTrace_append hprefix tailTrace_4056775
  have hstable : (prefixWord ++ tailWord_4056775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056775).length < 2 ^ (prefixWord ++ tailWord_4056775).sum := by decide
  have hdescent : baseEnd_4056775 < baseStart_4056775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056782 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6]
def baseStart_4056782 : Nat := 118140960795 + 4056782 * 2 ^ 59
def prefixEnd_4056782 : Nat := 4983230072969 + 3 ^ 40 * 4056782 * 2
def baseEnd_4056782 : Nat := 2083079076508052055468205

theorem tailTrace_4056782 : CollatzResearch.WordTrace tailWord_4056782 prefixEnd_4056782 2083079076508052055468205 := by
  unfold tailWord_4056782
  simp only [CollatzResearch.WordTrace]
  refine ⟨18495374398622391506330575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98641996792652754700429733 18495374398622391506330575)
  ·
    refine ⟨27743061597933587259495863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18495374398622391506330575 27743061597933587259495863)
    ·
      refine ⟨41614592396900380889243795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27743061597933587259495863 41614592396900380889243795)
      ·
        refine ⟨62421888595350571333865693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41614592396900380889243795 62421888595350571333865693)
        ·
          refine ⟨23408208223256464250199635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62421888595350571333865693 23408208223256464250199635)
          ·
            refine ⟨35112312334884696375299453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23408208223256464250199635 35112312334884696375299453)
            ·
              refine ⟨13167117125581761140737295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35112312334884696375299453 13167117125581761140737295)
              ·
                refine ⟨19750675688372641711105943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13167117125581761140737295 19750675688372641711105943)
                ·
                  refine ⟨29626013532558962566658915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19750675688372641711105943 29626013532558962566658915)
                  ·
                    refine ⟨44439020298838443849988373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29626013532558962566658915 44439020298838443849988373)
                    ·
                      refine ⟨2083079076508052055468205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44439020298838443849988373 2083079076508052055468205)
                      ·
                        rfl

theorem cell23_4056782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_4056782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056782 prefixEnd_4056782 := by exact prefixLift 4056782
  have htrace : WordTrace (prefixWord ++ tailWord_4056782) baseStart_4056782 baseEnd_4056782 := by
    simpa [prefixWord, tailWord_4056782, baseEnd_4056782] using wordTrace_append hprefix tailTrace_4056782
  have hstable : (prefixWord ++ tailWord_4056782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056782).length < 2 ^ (prefixWord ++ tailWord_4056782).sum := by decide
  have hdescent : baseEnd_4056782 < baseStart_4056782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056786 : List Nat := [3, 2, 2, 2, 2, 2, 2, 2, 1, 1, 4]
def baseStart_4056786 : Nat := 118140960795 + 4056786 * 2 ^ 59
def prefixEnd_4056786 : Nat := 4983230072969 + 3 ^ 40 * 4056786 * 2
def baseEnd_4056786 : Nat := 2083081130430670039818187

theorem tailTrace_4056786 : CollatzResearch.WordTrace tailWord_4056786 prefixEnd_4056786 2083081130430670039818187 := by
  unfold tailWord_4056786
  simp only [CollatzResearch.WordTrace]
  refine ⟨36990785270241160183447553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98642094053976427155860141 36990785270241160183447553)
  ·
    refine ⟨27743088952680870137585665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36990785270241160183447553 27743088952680870137585665)
    ·
      refine ⟨20807316714510652603189249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27743088952680870137585665 20807316714510652603189249)
      ·
        refine ⟨15605487535882989452391937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20807316714510652603189249 15605487535882989452391937)
        ·
          refine ⟨11704115651912242089293953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15605487535882989452391937 11704115651912242089293953)
          ·
            refine ⟨8778086738934181566970465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11704115651912242089293953 8778086738934181566970465)
            ·
              refine ⟨6583565054200636175227849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8778086738934181566970465 6583565054200636175227849)
              ·
                refine ⟨4937673790650477131420887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6583565054200636175227849 4937673790650477131420887)
                ·
                  refine ⟨7406510685975715697131331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4937673790650477131420887 7406510685975715697131331)
                  ·
                    refine ⟨11109766028963573545696997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7406510685975715697131331 11109766028963573545696997)
                    ·
                      refine ⟨2083081130430670039818187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11109766028963573545696997 2083081130430670039818187)
                      ·
                        rfl

theorem cell23_4056786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_4056786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056786 prefixEnd_4056786 := by exact prefixLift 4056786
  have htrace : WordTrace (prefixWord ++ tailWord_4056786) baseStart_4056786 baseEnd_4056786 := by
    simpa [prefixWord, tailWord_4056786, baseEnd_4056786] using wordTrace_append hprefix tailTrace_4056786
  have hstable : (prefixWord ++ tailWord_4056786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056786).length < 2 ^ (prefixWord ++ tailWord_4056786).sum := by decide
  have hdescent : baseEnd_4056786 < baseStart_4056786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056797 : List Nat := [1, 4, 3, 3, 1, 2, 1, 3, 1, 1, 3]
def baseStart_4056797 : Nat := 118140960795 + 4056797 * 2 ^ 59
def prefixEnd_4056797 : Nat := 4983230072969 + 3 ^ 40 * 4056797 * 2
def baseEnd_4056797 : Nat := 2083086778717869496780637

theorem tailTrace_4056797 : CollatzResearch.WordTrace tailWord_4056797 prefixEnd_4056797 2083086778717869496780637 := by
  unfold tailWord_4056797
  simp only [CollatzResearch.WordTrace]
  refine ⟨147963542283924789612440645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98642361522616526408293763 147963542283924789612440645)
  ·
    refine ⟨27743164178235898052332621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147963542283924789612440645 27743164178235898052332621)
    ·
      refine ⟨10403686566838461769624733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27743164178235898052332621 10403686566838461769624733)
      ·
        refine ⟨3901382462564423163609275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10403686566838461769624733 3901382462564423163609275)
        ·
          refine ⟨5852073693846634745413913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3901382462564423163609275 5852073693846634745413913)
          ·
            refine ⟨4389055270384976059060435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5852073693846634745413913 4389055270384976059060435)
            ·
              refine ⟨6583582905577464088590653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4389055270384976059060435 6583582905577464088590653)
              ·
                refine ⟨2468843589591549033221495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6583582905577464088590653 2468843589591549033221495)
                ·
                  refine ⟨3703265384387323549832243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2468843589591549033221495 3703265384387323549832243)
                  ·
                    refine ⟨5554898076580985324748365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3703265384387323549832243 5554898076580985324748365)
                    ·
                      refine ⟨2083086778717869496780637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5554898076580985324748365 2083086778717869496780637)
                      ·
                        rfl

theorem cell23_4056797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_4056797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056797 prefixEnd_4056797 := by exact prefixLift 4056797
  have htrace : WordTrace (prefixWord ++ tailWord_4056797) baseStart_4056797 baseEnd_4056797 := by
    simpa [prefixWord, tailWord_4056797, baseEnd_4056797] using wordTrace_append hprefix tailTrace_4056797
  have hstable : (prefixWord ++ tailWord_4056797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056797).length < 2 ^ (prefixWord ++ tailWord_4056797).sum := by decide
  have hdescent : baseEnd_4056797 < baseStart_4056797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056819 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 4, 1, 3]
def baseStart_4056819 : Nat := 118140960795 + 4056819 * 2 ^ 59
def prefixEnd_4056819 : Nat := 4983230072969 + 3 ^ 40 * 4056819 * 2
def baseEnd_4056819 : Nat := 2083098075292268410705535

theorem tailTrace_4056819 : CollatzResearch.WordTrace tailWord_4056819 prefixEnd_4056819 2083098075292268410705535 := by
  unfold tailWord_4056819
  simp only [CollatzResearch.WordTrace]
  refine ⟨147964344689845087369741511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98642896459896724913161007 147964344689845087369741511)
  ·
    refine ⟨221946517034767631054612267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147964344689845087369741511 221946517034767631054612267)
    ·
      refine ⟨332919775552151446581918401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221946517034767631054612267 332919775552151446581918401)
      ·
        refine ⟨249689831664113584936438801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332919775552151446581918401 249689831664113584936438801)
        ·
          refine ⟨187267373748085188702329101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249689831664113584936438801 187267373748085188702329101)
          ·
            refine ⟨70225265155531945763373413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187267373748085188702329101 70225265155531945763373413)
            ·
              refine ⟨13167237216662239830632515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70225265155531945763373413 13167237216662239830632515)
              ·
                refine ⟨19750855824993359745948773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13167237216662239830632515 19750855824993359745948773)
                ·
                  refine ⟨3703285467186254952365395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19750855824993359745948773 3703285467186254952365395)
                  ·
                    refine ⟨5554928200779382428548093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3703285467186254952365395 5554928200779382428548093)
                    ·
                      refine ⟨2083098075292268410705535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5554928200779382428548093 2083098075292268410705535)
                      ·
                        rfl

theorem cell23_4056819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 1, 3].length) (baseStart_4056819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056819 prefixEnd_4056819 := by exact prefixLift 4056819
  have htrace : WordTrace (prefixWord ++ tailWord_4056819) baseStart_4056819 baseEnd_4056819 := by
    simpa [prefixWord, tailWord_4056819, baseEnd_4056819] using wordTrace_append hprefix tailTrace_4056819
  have hstable : (prefixWord ++ tailWord_4056819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056819).length < 2 ^ (prefixWord ++ tailWord_4056819).sum := by decide
  have hdescent : baseEnd_4056819 < baseStart_4056819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056830 : List Nat := [4, 2, 2, 1, 3, 2, 2, 1, 2, 4]
def baseStart_4056830 : Nat := 118140960795 + 4056830 * 2 ^ 59
def prefixEnd_4056830 : Nat := 4983230072969 + 3 ^ 40 * 4056830 * 2
def baseEnd_4056830 : Nat := 694367907859822622555995

theorem tailTrace_4056830 : CollatzResearch.WordTrace tailWord_4056830 prefixEnd_4056830 694367907859822622555995 := by
  unfold tailWord_4056830
  simp only [CollatzResearch.WordTrace]
  refine ⟨18495593236600654531048993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98643163928536824165594629 18495593236600654531048993)
  ·
    refine ⟨13871694927450490898286745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18495593236600654531048993 13871694927450490898286745)
    ·
      refine ⟨10403771195587868173715059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13871694927450490898286745 10403771195587868173715059)
      ·
        refine ⟨15605656793381802260572589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10403771195587868173715059 15605656793381802260572589)
        ·
          refine ⟨5852121297518175847714721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15605656793381802260572589 5852121297518175847714721)
          ·
            refine ⟨4389090973138631885786041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5852121297518175847714721 4389090973138631885786041)
            ·
              refine ⟨3291818229853973914339531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4389090973138631885786041 3291818229853973914339531)
              ·
                refine ⟨4937727344780960871509297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3291818229853973914339531 4937727344780960871509297)
                ·
                  refine ⟨3703295508585720653631973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4937727344780960871509297 3703295508585720653631973)
                  ·
                    refine ⟨694367907859822622555995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3703295508585720653631973 694367907859822622555995)
                    ·
                      rfl

theorem cell23_4056830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_4056830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056830 prefixEnd_4056830 := by exact prefixLift 4056830
  have htrace : WordTrace (prefixWord ++ tailWord_4056830) baseStart_4056830 baseEnd_4056830 := by
    simpa [prefixWord, tailWord_4056830, baseEnd_4056830] using wordTrace_append hprefix tailTrace_4056830
  have hstable : (prefixWord ++ tailWord_4056830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056830).length < 2 ^ (prefixWord ++ tailWord_4056830).sum := by decide
  have hdescent : baseEnd_4056830 < baseStart_4056830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056859 : List Nat := [1, 1, 1, 1, 1, 1, 4, 6, 1, 4, 2]
def baseStart_4056859 : Nat := 118140960795 + 4056859 * 2 ^ 59
def prefixEnd_4056859 : Nat := 4983230072969 + 3 ^ 40 * 4056859 * 2
def baseEnd_4056859 : Nat := 2083118614518448254205351

theorem tailTrace_4056859 : CollatzResearch.WordTrace tailWord_4056859 prefixEnd_4056859 2083118614518448254205351 := by
  unfold tailWord_4056859
  simp only [CollatzResearch.WordTrace]
  refine ⟨147965803609700174201197631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98643869073133449467465087 147965803609700174201197631)
  ·
    refine ⟨221948705414550261301796447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147965803609700174201197631 221948705414550261301796447)
    ·
      refine ⟨332923058121825391952694671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221948705414550261301796447 332923058121825391952694671)
      ·
        refine ⟨499384587182738087929042007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332923058121825391952694671 499384587182738087929042007)
        ·
          refine ⟨749076880774107131893563011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499384587182738087929042007 749076880774107131893563011)
          ·
            refine ⟨1123615321161160697840344517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749076880774107131893563011 1123615321161160697840344517)
            ·
              refine ⟨210677872717717630845064597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1123615321161160697840344517 210677872717717630845064597)
              ·
                refine ⟨9875525283643013945862403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 210677872717717630845064597 9875525283643013945862403)
                ·
                  refine ⟨14813287925464520918793605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9875525283643013945862403 14813287925464520918793605)
                  ·
                    refine ⟨2777491486024597672273801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14813287925464520918793605 2777491486024597672273801)
                    ·
                      refine ⟨2083118614518448254205351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2777491486024597672273801 2083118614518448254205351)
                      ·
                        rfl

theorem cell23_4056859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 4, 2].length) (baseStart_4056859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056859 prefixEnd_4056859 := by exact prefixLift 4056859
  have htrace : WordTrace (prefixWord ++ tailWord_4056859) baseStart_4056859 baseEnd_4056859 := by
    simpa [prefixWord, tailWord_4056859, baseEnd_4056859] using wordTrace_append hprefix tailTrace_4056859
  have hstable : (prefixWord ++ tailWord_4056859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056859).length < 2 ^ (prefixWord ++ tailWord_4056859).sum := by decide
  have hdescent : baseEnd_4056859 < baseStart_4056859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056863 : List Nat := [1, 1, 2, 4, 2, 1, 5, 1, 1, 3, 2]
def baseStart_4056863 : Nat := 118140960795 + 4056863 * 2 ^ 59
def prefixEnd_4056863 : Nat := 4983230072969 + 3 ^ 40 * 4056863 * 2
def baseEnd_4056863 : Nat := 2083120668441066238555333

theorem tailTrace_4056863 : CollatzResearch.WordTrace tailWord_4056863 prefixEnd_4056863 2083120668441066238555333 := by
  unfold tailWord_4056863
  simp only [CollatzResearch.WordTrace]
  refine ⟨147965949501685682884343243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98643966334457121922895495 147965949501685682884343243)
  ·
    refine ⟨221948924252528524326514865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147965949501685682884343243 221948924252528524326514865)
    ·
      refine ⟨166461693189396393244886149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221948924252528524326514865 166461693189396393244886149)
      ·
        refine ⟨31211567473011823733416153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166461693189396393244886149 31211567473011823733416153)
        ·
          refine ⟨23408675604758867800062115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31211567473011823733416153 23408675604758867800062115)
          ·
            refine ⟨35113013407138301700093173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23408675604758867800062115 35113013407138301700093173)
            ·
              refine ⟨3291845006919215784383735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35113013407138301700093173 3291845006919215784383735)
              ·
                refine ⟨4937767510378823676575603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3291845006919215784383735 4937767510378823676575603)
                ·
                  refine ⟨7406651265568235514863405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4937767510378823676575603 7406651265568235514863405)
                  ·
                    refine ⟨2777494224588088318073777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7406651265568235514863405 2777494224588088318073777)
                    ·
                      refine ⟨2083120668441066238555333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2777494224588088318073777 2083120668441066238555333)
                      ·
                        rfl

theorem cell23_4056863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_4056863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056863 prefixEnd_4056863 := by exact prefixLift 4056863
  have htrace : WordTrace (prefixWord ++ tailWord_4056863) baseStart_4056863 baseEnd_4056863 := by
    simpa [prefixWord, tailWord_4056863, baseEnd_4056863] using wordTrace_append hprefix tailTrace_4056863
  have hstable : (prefixWord ++ tailWord_4056863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056863).length < 2 ^ (prefixWord ++ tailWord_4056863).sum := by decide
  have hdescent : baseEnd_4056863 < baseStart_4056863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056886 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_4056886 : Nat := 118140960795 + 4056886 * 2 ^ 59
def prefixEnd_4056886 : Nat := 4983230072969 + 3 ^ 40 * 4056886 * 2
def baseEnd_4056886 : Nat := 694377492832039882855909

theorem tailTrace_4056886 : CollatzResearch.WordTrace tailWord_4056886 prefixEnd_4056886 694377492832039882855909 := by
  unfold tailWord_4056886
  simp only [CollatzResearch.WordTrace]
  refine ⟨9247924273787647363276907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98644525587068238541620341 9247924273787647363276907)
  ·
    refine ⟨13871886410681471044915361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9247924273787647363276907 13871886410681471044915361)
    ·
      refine ⟨10403914808011103283686521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13871886410681471044915361 10403914808011103283686521)
      ·
        refine ⟨7802936106008327462764891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10403914808011103283686521 7802936106008327462764891)
        ·
          refine ⟨11704404159012491194147337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7802936106008327462764891 11704404159012491194147337)
          ·
            refine ⟨8778303119259368395610503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11704404159012491194147337 8778303119259368395610503)
            ·
              refine ⟨13167454678889052593415755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8778303119259368395610503 13167454678889052593415755)
              ·
                refine ⟨19751182018333578890123633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13167454678889052593415755 19751182018333578890123633)
                ·
                  refine ⟨14813386513750184167592725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19751182018333578890123633 14813386513750184167592725)
                  ·
                    refine ⟨694377492832039882855909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14813386513750184167592725 694377492832039882855909)
                    ·
                      rfl

theorem cell23_4056886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_4056886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056886 prefixEnd_4056886 := by exact prefixLift 4056886
  have htrace : WordTrace (prefixWord ++ tailWord_4056886) baseStart_4056886 baseEnd_4056886 := by
    simpa [prefixWord, tailWord_4056886, baseEnd_4056886] using wordTrace_append hprefix tailTrace_4056886
  have hstable : (prefixWord ++ tailWord_4056886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056886).length < 2 ^ (prefixWord ++ tailWord_4056886).sum := by decide
  have hdescent : baseEnd_4056886 < baseStart_4056886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056893 : List Nat := [1, 4, 1, 4, 1, 2, 2, 1, 1, 4, 2]
def baseStart_4056893 : Nat := 118140960795 + 4056893 * 2 ^ 59
def prefixEnd_4056893 : Nat := 4983230072969 + 3 ^ 40 * 4056893 * 2
def baseEnd_4056893 : Nat := 2083136072860701121180195

theorem tailTrace_4056893 : CollatzResearch.WordTrace tailWord_4056893 prefixEnd_4056893 2083136072860701121180195 := by
  unfold tailWord_4056893
  simp only [CollatzResearch.WordTrace]
  refine ⟨147967043691576998007935333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98644695794384665338623555 147967043691576998007935333)
  ·
    refine ⟨27743820692170687126487875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147967043691576998007935333 27743820692170687126487875)
    ·
      refine ⟨41615731038256030689731813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27743820692170687126487875 41615731038256030689731813)
      ·
        refine ⟨7802949569673005754324715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41615731038256030689731813 7802949569673005754324715)
        ·
          refine ⟨11704424354509508631487073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7802949569673005754324715 11704424354509508631487073)
          ·
            refine ⟨8778318265882131473615305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11704424354509508631487073 8778318265882131473615305)
            ·
              refine ⟨6583738699411598605211479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8778318265882131473615305 6583738699411598605211479)
              ·
                refine ⟨9875608049117397907817219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6583738699411598605211479 9875608049117397907817219)
                ·
                  refine ⟨14813412073676096861725829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9875608049117397907817219 14813412073676096861725829)
                  ·
                    refine ⟨2777514763814268161573593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14813412073676096861725829 2777514763814268161573593)
                    ·
                      refine ⟨2083136072860701121180195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2777514763814268161573593 2083136072860701121180195)
                      ·
                        rfl

theorem cell23_4056893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_4056893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056893 prefixEnd_4056893 := by exact prefixLift 4056893
  have htrace : WordTrace (prefixWord ++ tailWord_4056893) baseStart_4056893 baseEnd_4056893 := by
    simpa [prefixWord, tailWord_4056893, baseEnd_4056893] using wordTrace_append hprefix tailTrace_4056893
  have hstable : (prefixWord ++ tailWord_4056893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056893).length < 2 ^ (prefixWord ++ tailWord_4056893).sum := by decide
  have hdescent : baseEnd_4056893 < baseStart_4056893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056916 : List Nat := [2, 4, 1, 1, 3, 1, 1, 5, 5]
def baseStart_4056916 : Nat := 118140960795 + 4056916 * 2 ^ 59
def prefixEnd_4056916 : Nat := 4983230072969 + 3 ^ 40 * 4056916 * 2
def baseEnd_4056916 : Nat := 231460875879528281243621

theorem tailTrace_4056916 : CollatzResearch.WordTrace tailWord_4056916 prefixEnd_4056916 231460875879528281243621 := by
  unfold tailWord_4056916
  simp only [CollatzResearch.WordTrace]
  refine ⟨73983941285246836468011301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98645255046995781957348401 73983941285246836468011301)
  ·
    refine ⟨13871988990983781837752119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73983941285246836468011301 13871988990983781837752119)
    ·
      refine ⟨20807983486475672756628179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13871988990983781837752119 20807983486475672756628179)
      ·
        refine ⟨31211975229713509134942269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20807983486475672756628179 31211975229713509134942269)
        ·
          refine ⟨11704490711142565925603351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31211975229713509134942269 11704490711142565925603351)
          ·
            refine ⟨17556736066713848888405027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11704490711142565925603351 17556736066713848888405027)
            ·
              refine ⟨26335104100070773332607541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17556736066713848888405027 26335104100070773332607541)
              ·
                refine ⟨2468916009381634999931957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26335104100070773332607541 2468916009381634999931957)
                ·
                  refine ⟨231460875879528281243621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2468916009381634999931957 231460875879528281243621)
                  ·
                    rfl

theorem cell23_4056916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_4056916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056916 prefixEnd_4056916 := by exact prefixLift 4056916
  have htrace : WordTrace (prefixWord ++ tailWord_4056916) baseStart_4056916 baseEnd_4056916 := by
    simpa [prefixWord, tailWord_4056916, baseEnd_4056916] using wordTrace_append hprefix tailTrace_4056916
  have hstable : (prefixWord ++ tailWord_4056916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056916).length < 2 ^ (prefixWord ++ tailWord_4056916).sum := by decide
  have hdescent : baseEnd_4056916 < baseStart_4056916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056949 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_4056949 : Nat := 118140960795 + 4056949 * 2 ^ 59
def prefixEnd_4056949 : Nat := 4983230072969 + 3 ^ 40 * 4056949 * 2
def baseEnd_4056949 : Nat := 2083164827777352902079937

theorem tailTrace_4056949 : CollatzResearch.WordTrace tailWord_4056949 prefixEnd_4056949 2083164827777352902079937 := by
  unfold tailWord_4056949
  simp only [CollatzResearch.WordTrace]
  refine ⟨147969086179374119571973901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98646057452916079714649267 147969086179374119571973901)
  ·
    refine ⟨55488407317265294839490213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147969086179374119571973901 55488407317265294839490213)
    ·
      refine ⟨10404076371987242782404415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55488407317265294839490213 10404076371987242782404415)
      ·
        refine ⟨15606114557980864173606623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10404076371987242782404415 15606114557980864173606623)
        ·
          refine ⟨23409171836971296260409935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15606114557980864173606623 23409171836971296260409935)
          ·
            refine ⟨35113757755456944390614903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23409171836971296260409935 35113757755456944390614903)
            ·
              refine ⟨52670636633185416585922355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35113757755456944390614903 52670636633185416585922355)
              ·
                refine ⟨79005954949778124878883533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52670636633185416585922355 79005954949778124878883533)
                ·
                  refine ⟨29627233106166796829581325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79005954949778124878883533 29627233106166796829581325)
                  ·
                    refine ⟨11110212414812548811092997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29627233106166796829581325 11110212414812548811092997)
                    ·
                      refine ⟨2083164827777352902079937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11110212414812548811092997 2083164827777352902079937)
                      ·
                        rfl

theorem cell23_4056949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_4056949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056949 prefixEnd_4056949 := by exact prefixLift 4056949
  have htrace : WordTrace (prefixWord ++ tailWord_4056949) baseStart_4056949 baseEnd_4056949 := by
    simpa [prefixWord, tailWord_4056949, baseEnd_4056949] using wordTrace_append hprefix tailTrace_4056949
  have hstable : (prefixWord ++ tailWord_4056949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056949).length < 2 ^ (prefixWord ++ tailWord_4056949).sum := by decide
  have hdescent : baseEnd_4056949 < baseStart_4056949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056952 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 4, 3, 5]
def baseStart_4056952 : Nat := 118140960795 + 4056952 * 2 ^ 59
def prefixEnd_4056952 : Nat := 4983230072969 + 3 ^ 40 * 4056952 * 2
def baseEnd_4056952 : Nat := 2083166368219316390342423

theorem tailTrace_4056952 : CollatzResearch.WordTrace tailWord_4056952 prefixEnd_4056952 2083166368219316390342423 := by
  unfold tailWord_4056952
  simp only [CollatzResearch.WordTrace]
  refine ⟨73984597799181625542166555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98646130398908834056222073 73984597799181625542166555)
  ·
    refine ⟨110976896698772438313249833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73984597799181625542166555 110976896698772438313249833)
    ·
      refine ⟨83232672524079328734937375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110976896698772438313249833 83232672524079328734937375)
      ·
        refine ⟨124849008786118993102406063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83232672524079328734937375 124849008786118993102406063)
        ·
          refine ⟨187273513179178489653609095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124849008786118993102406063 187273513179178489653609095)
          ·
            refine ⟨280910269768767734480413643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187273513179178489653609095 280910269768767734480413643)
            ·
              refine ⟨421365404653151601720620465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280910269768767734480413643 421365404653151601720620465)
              ·
                refine ⟨316024053489863701290465349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421365404653151601720620465 316024053489863701290465349)
                ·
                  refine ⟨59254510029349443991962253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316024053489863701290465349 59254510029349443991962253)
                  ·
                    refine ⟨22220441261006041496985845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59254510029349443991962253 22220441261006041496985845)
                    ·
                      refine ⟨2083166368219316390342423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22220441261006041496985845 2083166368219316390342423)
                      ·
                        rfl

theorem cell23_4056952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_4056952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056952 prefixEnd_4056952 := by exact prefixLift 4056952
  have htrace : WordTrace (prefixWord ++ tailWord_4056952) baseStart_4056952 baseEnd_4056952 := by
    simpa [prefixWord, tailWord_4056952, baseEnd_4056952] using wordTrace_append hprefix tailTrace_4056952
  have hstable : (prefixWord ++ tailWord_4056952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056952).length < 2 ^ (prefixWord ++ tailWord_4056952).sum := by decide
  have hdescent : baseEnd_4056952 < baseStart_4056952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056969 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 1, 4, 3]
def baseStart_4056969 : Nat := 118140960795 + 4056969 * 2 ^ 59
def prefixEnd_4056969 : Nat := 4983230072969 + 3 ^ 40 * 4056969 * 2
def baseEnd_4056969 : Nat := 2083175097390442823829845

theorem tailTrace_4056969 : CollatzResearch.WordTrace tailWord_4056969 prefixEnd_4056969 2083175097390442823829845 := by
  unfold tailWord_4056969
  simp only [CollatzResearch.WordTrace]
  refine ⟨147969815639301662987701961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98646543759534441991801307 147969815639301662987701961)
  ·
    refine ⟨110977361729476247240776471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147969815639301662987701961 110977361729476247240776471)
    ·
      refine ⟨166466042594214370861164707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110977361729476247240776471 166466042594214370861164707)
      ·
        refine ⟨249699063891321556291747061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166466042594214370861164707 249699063891321556291747061)
        ·
          refine ⟨23409287239811395902351287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249699063891321556291747061 23409287239811395902351287)
          ·
            refine ⟨35113930859717093853526931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23409287239811395902351287 35113930859717093853526931)
            ·
              refine ⟨52670896289575640780290397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35113930859717093853526931 52670896289575640780290397)
              ·
                refine ⟨19751586108590865292608899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52670896289575640780290397 19751586108590865292608899)
                ·
                  refine ⟨29627379162886297938913349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19751586108590865292608899 29627379162886297938913349)
                  ·
                    refine ⟨5555133593041180863546253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29627379162886297938913349 5555133593041180863546253)
                    ·
                      refine ⟨2083175097390442823829845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5555133593041180863546253 2083175097390442823829845)
                      ·
                        rfl

theorem cell23_4056969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 4, 3].length) (baseStart_4056969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056969 prefixEnd_4056969 := by exact prefixLift 4056969
  have htrace : WordTrace (prefixWord ++ tailWord_4056969) baseStart_4056969 baseEnd_4056969 := by
    simpa [prefixWord, tailWord_4056969, baseEnd_4056969] using wordTrace_append hprefix tailTrace_4056969
  have hstable : (prefixWord ++ tailWord_4056969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056969).length < 2 ^ (prefixWord ++ tailWord_4056969).sum := by decide
  have hdescent : baseEnd_4056969 < baseStart_4056969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056986 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3]
def baseStart_4056986 : Nat := 118140960795 + 4056986 * 2 ^ 59
def prefixEnd_4056986 : Nat := 4983230072969 + 3 ^ 40 * 4056986 * 2
def baseEnd_4056986 : Nat := 2083183826561569257317267

theorem tailTrace_4056986 : CollatzResearch.WordTrace tailWord_4056986 prefixEnd_4056986 2083183826561569257317267 := by
  unfold tailWord_4056986
  simp only [CollatzResearch.WordTrace]
  refine ⟨36992608920060018722767703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98646957120160049927380541 36992608920060018722767703)
  ·
    refine ⟨55488913380090028084151555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36992608920060018722767703 55488913380090028084151555)
    ·
      refine ⟨83233370070135042126227333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55488913380090028084151555 83233370070135042126227333)
      ·
        refine ⟨15606256888150320398667625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83233370070135042126227333 15606256888150320398667625)
        ·
          refine ⟨11704692666112740299000719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15606256888150320398667625 11704692666112740299000719)
          ·
            refine ⟨17557038999169110448501079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11704692666112740299000719 17557038999169110448501079)
            ·
              refine ⟨26335558498753665672751619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17557038999169110448501079 26335558498753665672751619)
              ·
                refine ⟨39503337748130498509127429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26335558498753665672751619 39503337748130498509127429)
                ·
                  refine ⟨7406875827774468470461393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39503337748130498509127429 7406875827774468470461393)
                  ·
                    refine ⟨5555156870830851352846045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7406875827774468470461393 5555156870830851352846045)
                    ·
                      refine ⟨2083183826561569257317267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5555156870830851352846045 2083183826561569257317267)
                      ·
                        rfl

theorem cell23_4056986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_4056986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056986 prefixEnd_4056986 := by exact prefixLift 4056986
  have htrace : WordTrace (prefixWord ++ tailWord_4056986) baseStart_4056986 baseEnd_4056986 := by
    simpa [prefixWord, tailWord_4056986, baseEnd_4056986] using wordTrace_append hprefix tailTrace_4056986
  have hstable : (prefixWord ++ tailWord_4056986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056986).length < 2 ^ (prefixWord ++ tailWord_4056986).sum := by decide
  have hdescent : baseEnd_4056986 < baseStart_4056986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056989 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 8]
def baseStart_4056989 : Nat := 118140960795 + 4056989 * 2 ^ 59
def prefixEnd_4056989 : Nat := 4983230072969 + 3 ^ 40 * 4056989 * 2
def baseEnd_4056989 : Nat := 231465040778170305064417

theorem tailTrace_4056989 : CollatzResearch.WordTrace tailWord_4056989 prefixEnd_4056989 231465040778170305064417 := by
  unfold tailWord_4056989
  simp only [CollatzResearch.WordTrace]
  refine ⟨147970545099229206403430021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98647030066152804268953347 147970545099229206403430021)
  ·
    refine ⟨27744477206105476200643129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147970545099229206403430021 27744477206105476200643129)
    ·
      refine ⟨20808357904579107150482347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27744477206105476200643129 20808357904579107150482347)
      ·
        refine ⟨31212536856868660725723521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20808357904579107150482347 31212536856868660725723521)
        ·
          refine ⟨23409402642651495544292641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31212536856868660725723521 23409402642651495544292641)
          ·
            refine ⟨17557051981988621658219481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23409402642651495544292641 17557051981988621658219481)
            ·
              refine ⟨13167788986491466243664611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17557051981988621658219481 13167788986491466243664611)
              ·
                refine ⟨19751683479737199365496917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13167788986491466243664611 19751683479737199365496917)
                ·
                  refine ⟨231465040778170305064417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19751683479737199365496917 231465040778170305064417)
                  ·
                    rfl

theorem cell23_4056989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_4056989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056989 prefixEnd_4056989 := by exact prefixLift 4056989
  have htrace : WordTrace (prefixWord ++ tailWord_4056989) baseStart_4056989 baseEnd_4056989 := by
    simpa [prefixWord, tailWord_4056989, baseEnd_4056989] using wordTrace_append hprefix tailTrace_4056989
  have hstable : (prefixWord ++ tailWord_4056989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056989).length < 2 ^ (prefixWord ++ tailWord_4056989).sum := by decide
  have hdescent : baseEnd_4056989 < baseStart_4056989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057016 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 5, 1, 3]
def baseStart_4057016 : Nat := 118140960795 + 4057016 * 2 ^ 59
def prefixEnd_4057016 : Nat := 4983230072969 + 3 ^ 40 * 4057016 * 2
def baseEnd_4057016 : Nat := 2083199230981204139942129

theorem tailTrace_4057016 : CollatzResearch.WordTrace tailWord_4057016 prefixEnd_4057016 2083199230981204139942129 := by
  unfold tailWord_4057016
  simp only [CollatzResearch.WordTrace]
  refine ⟨73985764935065695007331451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98647686580087593343108601 73985764935065695007331451)
  ·
    refine ⟨110978647402598542510997177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73985764935065695007331451 110978647402598542510997177)
    ·
      refine ⟨83233985551948906883247883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110978647402598542510997177 83233985551948906883247883)
      ·
        refine ⟨124850978327923360324871825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83233985551948906883247883 124850978327923360324871825)
        ·
          refine ⟨93638233745942520243653869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124850978327923360324871825 93638233745942520243653869)
          ·
            refine ⟨35114337654728445091370201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93638233745942520243653869 35114337654728445091370201)
            ·
              refine ⟨26335753241046333818527651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35114337654728445091370201 26335753241046333818527651)
              ·
                refine ⟨39503629861569500727791477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26335753241046333818527651 39503629861569500727791477)
                ·
                  refine ⟨3703465299522140693230451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39503629861569500727791477 3703465299522140693230451)
                  ·
                    refine ⟨5555197949283211039845677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3703465299522140693230451 5555197949283211039845677)
                    ·
                      refine ⟨2083199230981204139942129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5555197949283211039845677 2083199230981204139942129)
                      ·
                        rfl

theorem cell23_4057016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 5, 1, 3].length) (baseStart_4057016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057016 prefixEnd_4057016 := by exact prefixLift 4057016
  have htrace : WordTrace (prefixWord ++ tailWord_4057016) baseStart_4057016 baseEnd_4057016 := by
    simpa [prefixWord, tailWord_4057016, baseEnd_4057016] using wordTrace_append hprefix tailTrace_4057016
  have hstable : (prefixWord ++ tailWord_4057016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057016).length < 2 ^ (prefixWord ++ tailWord_4057016).sum := by decide
  have hdescent : baseEnd_4057016 < baseStart_4057016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057020 : List Nat := [2, 2, 2, 5, 1, 1, 2, 1, 2, 2, 3]
def baseStart_4057020 : Nat := 118140960795 + 4057020 * 2 ^ 59
def prefixEnd_4057020 : Nat := 4983230072969 + 3 ^ 40 * 4057020 * 2
def baseEnd_4057020 : Nat := 2083201284903822124292111

theorem tailTrace_4057020 : CollatzResearch.WordTrace tailWord_4057020 prefixEnd_4057020 2083201284903822124292111 := by
  unfold tailWord_4057020
  simp only [CollatzResearch.WordTrace]
  refine ⟨73985837881058449348904257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98647783841411265798539009 73985837881058449348904257)
  ·
    refine ⟨55489378410793837011678193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73985837881058449348904257 55489378410793837011678193)
    ·
      refine ⟨41617033808095377758758645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55489378410793837011678193 41617033808095377758758645)
      ·
        refine ⟨3901596919508941664883623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41617033808095377758758645 3901596919508941664883623)
        ·
          refine ⟨5852395379263412497325435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3901596919508941664883623 5852395379263412497325435)
          ·
            refine ⟨8778593068895118745988153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5852395379263412497325435 8778593068895118745988153)
            ·
              refine ⟨6583944801671339059491115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8778593068895118745988153 6583944801671339059491115)
              ·
                refine ⟨9875917202507008589236673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6583944801671339059491115 9875917202507008589236673)
                ·
                  refine ⟨7406937901880256441927505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9875917202507008589236673 7406937901880256441927505)
                  ·
                    refine ⟨5555203426410192331445629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7406937901880256441927505 5555203426410192331445629)
                    ·
                      refine ⟨2083201284903822124292111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5555203426410192331445629 2083201284903822124292111)
                      ·
                        rfl

theorem cell23_4057020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_4057020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057020 prefixEnd_4057020 := by exact prefixLift 4057020
  have htrace : WordTrace (prefixWord ++ tailWord_4057020) baseStart_4057020 baseEnd_4057020 := by
    simpa [prefixWord, tailWord_4057020, baseEnd_4057020] using wordTrace_append hprefix tailTrace_4057020
  have hstable : (prefixWord ++ tailWord_4057020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057020).length < 2 ^ (prefixWord ++ tailWord_4057020).sum := by decide
  have hdescent : baseEnd_4057020 < baseStart_4057020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057066 : List Nat := [3, 1, 3, 1, 2, 1, 4, 1, 1, 6]
def baseStart_4057066 : Nat := 118140960795 + 4057066 * 2 ^ 59
def prefixEnd_4057066 : Nat := 4983230072969 + 3 ^ 40 * 4057066 * 2
def baseEnd_4057066 : Nat := 694408301671309648105633

theorem tailTrace_4057066 : CollatzResearch.WordTrace tailWord_4057066 prefixEnd_4057066 694408301671309648105633 := by
  unfold tailWord_4057066
  simp only [CollatzResearch.WordTrace]
  refine ⟨36993338379987562138495763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98648902346633499035988701 36993338379987562138495763)
  ·
    refine ⟨55490007569981343207743645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36993338379987562138495763 55490007569981343207743645)
    ·
      refine ⟨20808752838743003702903867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55490007569981343207743645 20808752838743003702903867)
      ·
        refine ⟨31213129258114505554355801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20808752838743003702903867 31213129258114505554355801)
        ·
          refine ⟨23409846943585879165766851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31213129258114505554355801 23409846943585879165766851)
          ·
            refine ⟨35114770415378818748650277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23409846943585879165766851 35114770415378818748650277)
            ·
              refine ⟨6584019452883528515371927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35114770415378818748650277 6584019452883528515371927)
              ·
                refine ⟨9876029179325292773057891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6584019452883528515371927 9876029179325292773057891)
                ·
                  refine ⟨14814043768987939159586837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9876029179325292773057891 14814043768987939159586837)
                  ·
                    refine ⟨694408301671309648105633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14814043768987939159586837 694408301671309648105633)
                    ·
                      rfl

theorem cell23_4057066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_4057066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057066 prefixEnd_4057066 := by exact prefixLift 4057066
  have htrace : WordTrace (prefixWord ++ tailWord_4057066) baseStart_4057066 baseEnd_4057066 := by
    simpa [prefixWord, tailWord_4057066, baseEnd_4057066] using wordTrace_append hprefix tailTrace_4057066
  have hstable : (prefixWord ++ tailWord_4057066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057066).length < 2 ^ (prefixWord ++ tailWord_4057066).sum := by decide
  have hdescent : baseEnd_4057066 < baseStart_4057066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057093 : List Nat := [1, 3, 1, 1, 2, 5, 1, 3, 1, 2, 3]
def baseStart_4057093 : Nat := 118140960795 + 4057093 * 2 ^ 59
def prefixEnd_4057093 : Nat := 4983230072969 + 3 ^ 40 * 4057093 * 2
def baseEnd_4057093 : Nat := 2083238768991600338679275

theorem tailTrace_4057093 : CollatzResearch.WordTrace tailWord_4057093 prefixEnd_4057093 2083238768991600338679275 := by
  unfold tailWord_4057093
  simp only [CollatzResearch.WordTrace]
  refine ⟨147974338290852432165215933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98649558860568288110143955 147974338290852432165215933)
  ·
    refine ⟨55490376859069662061955975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147974338290852432165215933 55490376859069662061955975)
    ·
      refine ⟨83235565288604493092933963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55490376859069662061955975 83235565288604493092933963)
      ·
        refine ⟨124853347932906739639400945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83235565288604493092933963 124853347932906739639400945)
        ·
          refine ⟨93640010949680054729550709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124853347932906739639400945 93640010949680054729550709)
          ·
            refine ⟨8778751026532505130895379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93640010949680054729550709 8778751026532505130895379)
            ·
              refine ⟨13168126539798757696343069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8778751026532505130895379 13168126539798757696343069)
              ·
                refine ⟨4938047452424534136128651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13168126539798757696343069 4938047452424534136128651)
                ·
                  refine ⟨7407071178636801204192977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4938047452424534136128651 7407071178636801204192977)
                  ·
                    refine ⟨5555303383977600903144733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7407071178636801204192977 5555303383977600903144733)
                    ·
                      refine ⟨2083238768991600338679275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5555303383977600903144733 2083238768991600338679275)
                      ·
                        rfl

theorem cell23_4057093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 2, 3].length) (baseStart_4057093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057093 prefixEnd_4057093 := by exact prefixLift 4057093
  have htrace : WordTrace (prefixWord ++ tailWord_4057093) baseStart_4057093 baseEnd_4057093 := by
    simpa [prefixWord, tailWord_4057093, baseEnd_4057093] using wordTrace_append hprefix tailTrace_4057093
  have hstable : (prefixWord ++ tailWord_4057093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057093).length < 2 ^ (prefixWord ++ tailWord_4057093).sum := by decide
  have hdescent : baseEnd_4057093 < baseStart_4057093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057127 : List Nat := [1, 1, 7, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_4057127 : Nat := 118140960795 + 4057127 * 2 ^ 59
def prefixEnd_4057127 : Nat := 4983230072969 + 3 ^ 40 * 4057127 * 2
def baseEnd_4057127 : Nat := 2083256227333853205654119

theorem tailTrace_4057127 : CollatzResearch.WordTrace tailWord_4057127 prefixEnd_4057127 2083256227333853205654119 := by
  unfold tailWord_4057127
  simp only [CollatzResearch.WordTrace]
  refine ⟨147975578372729255971953635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98650385581819503981302423 147975578372729255971953635)
  ·
    refine ⟨221963367559093883957930453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147975578372729255971953635 221963367559093883957930453)
    ·
      refine ⟨5202266427166262905263995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 221963367559093883957930453 5202266427166262905263995)
      ·
        refine ⟨7803399640749394357895993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5202266427166262905263995 7803399640749394357895993)
        ·
          refine ⟨5852549730562045768421995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7803399640749394357895993 5852549730562045768421995)
          ·
            refine ⟨8778824595843068652632993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5852549730562045768421995 8778824595843068652632993)
            ·
              refine ⟨6584118446882301489474745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8778824595843068652632993 6584118446882301489474745)
              ·
                refine ⟨4938088835161726117106059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6584118446882301489474745 4938088835161726117106059)
                ·
                  refine ⟨7407133252742589175659089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4938088835161726117106059 7407133252742589175659089)
                  ·
                    refine ⟨5555349939556941881744317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7407133252742589175659089 5555349939556941881744317)
                    ·
                      refine ⟨2083256227333853205654119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5555349939556941881744317 2083256227333853205654119)
                      ·
                        rfl

theorem cell23_4057127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_4057127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057127 prefixEnd_4057127 := by exact prefixLift 4057127
  have htrace : WordTrace (prefixWord ++ tailWord_4057127) baseStart_4057127 baseEnd_4057127 := by
    simpa [prefixWord, tailWord_4057127, baseEnd_4057127] using wordTrace_append hprefix tailTrace_4057127
  have hstable : (prefixWord ++ tailWord_4057127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057127).length < 2 ^ (prefixWord ++ tailWord_4057127).sum := by decide
  have hdescent : baseEnd_4057127 < baseStart_4057127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057129 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 5, 5, 4]
def baseStart_4057129 : Nat := 118140960795 + 4057129 * 2 ^ 59
def prefixEnd_4057129 : Nat := 4983230072969 + 3 ^ 40 * 4057129 * 2
def baseEnd_4057129 : Nat := 2083257254295162197829109

theorem tailTrace_4057129 : CollatzResearch.WordTrace tailWord_4057129 prefixEnd_4057129 2083257254295162197829109 := by
  unfold tailWord_4057129
  simp only [CollatzResearch.WordTrace]
  refine ⟨147975651318722010313526441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98650434212481340209017627 147975651318722010313526441)
  ·
    refine ⟨110981738489041507735144831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147975651318722010313526441 110981738489041507735144831)
    ·
      refine ⟨166472607733562261602717247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110981738489041507735144831 166472607733562261602717247)
      ·
        refine ⟨249708911600343392404075871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166472607733562261602717247 249708911600343392404075871)
        ·
          refine ⟨374563367400515088606113807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249708911600343392404075871 374563367400515088606113807)
          ·
            refine ⟨561845051100772632909170711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374563367400515088606113807 561845051100772632909170711)
            ·
              refine ⟨842767576651158949363756067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561845051100772632909170711 842767576651158949363756067)
              ·
                refine ⟨1264151364976738424045634101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842767576651158949363756067 1264151364976738424045634101)
                ·
                  refine ⟨118514190466569227254278197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1264151364976738424045634101 118514190466569227254278197)
                  ·
                    refine ⟨11110705356240865055088581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118514190466569227254278197 11110705356240865055088581)
                    ·
                      refine ⟨2083257254295162197829109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11110705356240865055088581 2083257254295162197829109)
                      ·
                        rfl

theorem cell23_4057129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 5, 4].length) (baseStart_4057129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057129 prefixEnd_4057129 := by exact prefixLift 4057129
  have htrace : WordTrace (prefixWord ++ tailWord_4057129) baseStart_4057129 baseEnd_4057129 := by
    simpa [prefixWord, tailWord_4057129, baseEnd_4057129] using wordTrace_append hprefix tailTrace_4057129
  have hstable : (prefixWord ++ tailWord_4057129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057129).length < 2 ^ (prefixWord ++ tailWord_4057129).sum := by decide
  have hdescent : baseEnd_4057129 < baseStart_4057129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057139 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 1, 8]
def baseStart_4057139 : Nat := 118140960795 + 4057139 * 2 ^ 59
def prefixEnd_4057139 : Nat := 4983230072969 + 3 ^ 40 * 4057139 * 2
def baseEnd_4057139 : Nat := 694420796367235719568021

theorem tailTrace_4057139 : CollatzResearch.WordTrace tailWord_4057139 prefixEnd_4057139 694420796367235719568021 := by
  unfold tailWord_4057139
  simp only [CollatzResearch.WordTrace]
  refine ⟨147976016048685782021390471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98650677365790521347593647 147976016048685782021390471)
  ·
    refine ⟨221964024073028673032085707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147976016048685782021390471 221964024073028673032085707)
    ·
      refine ⟨332946036109543009548128561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221964024073028673032085707 332946036109543009548128561)
      ·
        refine ⟨249709527082157257161096421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332946036109543009548128561 249709527082157257161096421)
        ·
          refine ⟨46820536327904485717705579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249709527082157257161096421 46820536327904485717705579)
          ·
            refine ⟨70230804491856728576558369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46820536327904485717705579 70230804491856728576558369)
            ·
              refine ⟨52673103368892546432418777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70230804491856728576558369 52673103368892546432418777)
              ·
                refine ⟨39504827526669409824314083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52673103368892546432418777 39504827526669409824314083)
                ·
                  refine ⟨59257241290004114736471125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39504827526669409824314083 59257241290004114736471125)
                  ·
                    refine ⟨694420796367235719568021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59257241290004114736471125 694420796367235719568021)
                    ·
                      rfl

theorem cell23_4057139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 8].length) (baseStart_4057139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057139 prefixEnd_4057139 := by exact prefixLift 4057139
  have htrace : WordTrace (prefixWord ++ tailWord_4057139) baseStart_4057139 baseEnd_4057139 := by
    simpa [prefixWord, tailWord_4057139, baseEnd_4057139] using wordTrace_append hprefix tailTrace_4057139
  have hstable : (prefixWord ++ tailWord_4057139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057139).length < 2 ^ (prefixWord ++ tailWord_4057139).sum := by decide
  have hdescent : baseEnd_4057139 < baseStart_4057139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057174 : List Nat := [5, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_4057174 : Nat := 118140960795 + 4057174 * 2 ^ 59
def prefixEnd_4057174 : Nat := 4983230072969 + 3 ^ 40 * 4057174 * 2
def baseEnd_4057174 : Nat := 2083280360924614521766403

theorem tailTrace_4057174 : CollatzResearch.WordTrace tailWord_4057174 prefixEnd_4057174 2083280360924614521766403 := by
  unfold tailWord_4057174
  simp only [CollatzResearch.WordTrace]
  refine ⟨9248580787722436437432161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98651528402372655332609717 9248580787722436437432161)
  ·
    refine ⟨6936435590791827328074121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9248580787722436437432161 6936435590791827328074121)
    ·
      refine ⟨5202326693093870496055591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6936435590791827328074121 5202326693093870496055591)
      ·
        refine ⟨7803490039640805744083387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5202326693093870496055591 7803490039640805744083387)
        ·
          refine ⟨11705235059461208616125081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7803490039640805744083387 11705235059461208616125081)
          ·
            refine ⟨8778926294595906462093811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11705235059461208616125081 8778926294595906462093811)
            ·
              refine ⟨13168389441893859693140717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8778926294595906462093811 13168389441893859693140717)
              ·
                refine ⟨4938146040710197384927769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13168389441893859693140717 4938146040710197384927769)
                ·
                  refine ⟨3703609530532648038695827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4938146040710197384927769 3703609530532648038695827)
                  ·
                    refine ⟨5555414295798972058043741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3703609530532648038695827 5555414295798972058043741)
                    ·
                      refine ⟨2083280360924614521766403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5555414295798972058043741 2083280360924614521766403)
                      ·
                        rfl

theorem cell23_4057174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_4057174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057174 prefixEnd_4057174 := by exact prefixLift 4057174
  have htrace : WordTrace (prefixWord ++ tailWord_4057174) baseStart_4057174 baseEnd_4057174 := by
    simpa [prefixWord, tailWord_4057174, baseEnd_4057174] using wordTrace_append hprefix tailTrace_4057174
  have hstable : (prefixWord ++ tailWord_4057174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057174).length < 2 ^ (prefixWord ++ tailWord_4057174).sum := by decide
  have hdescent : baseEnd_4057174 < baseStart_4057174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057223 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 2, 5, 2]
def baseStart_4057223 : Nat := 118140960795 + 4057223 * 2 ^ 59
def prefixEnd_4057223 : Nat := 4983230072969 + 3 ^ 40 * 4057223 * 2
def baseEnd_4057223 : Nat := 2083305521476684830053677

theorem tailTrace_4057223 : CollatzResearch.WordTrace tailWord_4057223 prefixEnd_4057223 2083305521476684830053677 := by
  unfold tailWord_4057223
  simp only [CollatzResearch.WordTrace]
  refine ⟨147979079780381464367448323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98652719853587642911632215 147979079780381464367448323)
  ·
    refine ⟨221968619670572196551172485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147979079780381464367448323 221968619670572196551172485)
    ·
      refine ⟨41619116188232286853344841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221968619670572196551172485 41619116188232286853344841)
      ·
        refine ⟨31214337141174215140008631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41619116188232286853344841 31214337141174215140008631)
        ·
          refine ⟨46821505711761322710012947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31214337141174215140008631 46821505711761322710012947)
          ·
            refine ⟨70232258567641984065019421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46821505711761322710012947 70232258567641984065019421)
            ·
              refine ⟨26337096962865744024382283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70232258567641984065019421 26337096962865744024382283)
              ·
                refine ⟨39505645444298616036573425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26337096962865744024382283 39505645444298616036573425)
                ·
                  refine ⟨29629234083223962027430069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39505645444298616036573425 29629234083223962027430069)
                  ·
                    refine ⟨2777740695302246440071569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29629234083223962027430069 2777740695302246440071569)
                    ·
                      refine ⟨2083305521476684830053677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2777740695302246440071569 2083305521476684830053677)
                      ·
                        rfl

theorem cell23_4057223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_4057223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057223 prefixEnd_4057223 := by exact prefixLift 4057223
  have htrace : WordTrace (prefixWord ++ tailWord_4057223) baseStart_4057223 baseEnd_4057223 := by
    simpa [prefixWord, tailWord_4057223, baseEnd_4057223] using wordTrace_append hprefix tailTrace_4057223
  have hstable : (prefixWord ++ tailWord_4057223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057223).length < 2 ^ (prefixWord ++ tailWord_4057223).sum := by decide
  have hdescent : baseEnd_4057223 < baseStart_4057223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057230 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3]
def baseStart_4057230 : Nat := 118140960795 + 4057230 * 2 ^ 59
def prefixEnd_4057230 : Nat := 4983230072969 + 3 ^ 40 * 4057230 * 2
def baseEnd_4057230 : Nat := 2083309115841266302666145

theorem tailTrace_4057230 : CollatzResearch.WordTrace tailWord_4057230 prefixEnd_4057230 2083309115841266302666145 := by
  unfold tailWord_4057230
  simp only [CollatzResearch.WordTrace]
  refine ⟨18497416886419513070369143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98652890060904069708635429 18497416886419513070369143)
  ·
    refine ⟨27746125329629269605553715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18497416886419513070369143 27746125329629269605553715)
    ·
      refine ⟨41619187994443904408330573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27746125329629269605553715 41619187994443904408330573)
      ·
        refine ⟨15607195497916464153123965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41619187994443904408330573 15607195497916464153123965)
        ·
          refine ⟨5852698311718674057421487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15607195497916464153123965 5852698311718674057421487)
          ·
            refine ⟨8779047467578011086132231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5852698311718674057421487 8779047467578011086132231)
            ·
              refine ⟨13168571201367016629198347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8779047467578011086132231 13168571201367016629198347)
              ·
                refine ⟨19752856802050524943797521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13168571201367016629198347 19752856802050524943797521)
                ·
                  refine ⟨14814642601537893707848141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19752856802050524943797521 14814642601537893707848141)
                  ·
                    refine ⟨5555490975576710140443053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14814642601537893707848141 5555490975576710140443053)
                    ·
                      refine ⟨2083309115841266302666145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5555490975576710140443053 2083309115841266302666145)
                      ·
                        rfl

theorem cell23_4057230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_4057230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057230 prefixEnd_4057230 := by exact prefixLift 4057230
  have htrace : WordTrace (prefixWord ++ tailWord_4057230) baseStart_4057230 baseEnd_4057230 := by
    simpa [prefixWord, tailWord_4057230, baseEnd_4057230] using wordTrace_append hprefix tailTrace_4057230
  have hstable : (prefixWord ++ tailWord_4057230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057230).length < 2 ^ (prefixWord ++ tailWord_4057230).sum := by decide
  have hdescent : baseEnd_4057230 < baseStart_4057230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057250 : List Nat := [3, 3, 1, 3, 1, 1, 3, 1, 2, 5]
def baseStart_4057250 : Nat := 118140960795 + 4057250 * 2 ^ 59
def prefixEnd_4057250 : Nat := 4983230072969 + 3 ^ 40 * 4057250 * 2
def baseEnd_4057250 : Nat := 694439795151452074805351

theorem tailTrace_4057250 : CollatzResearch.WordTrace tailWord_4057250 prefixEnd_4057250 694439795151452074805351 := by
  unfold tailWord_4057250
  simp only [CollatzResearch.WordTrace]
  refine ⟨36995016137820911994670301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98653376367522431985787469 36995016137820911994670301)
  ·
    refine ⟨13873131051682841998001363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36995016137820911994670301 13873131051682841998001363)
    ·
      refine ⟨20809696577524262997002045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13873131051682841998001363 20809696577524262997002045)
      ·
        refine ⟨7803636216571598623875767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20809696577524262997002045 7803636216571598623875767)
        ·
          refine ⟨11705454324857397935813651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7803636216571598623875767 11705454324857397935813651)
          ·
            refine ⟨17558181487286096903720477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11705454324857397935813651 17558181487286096903720477)
            ·
              refine ⟨6584318057732286338895179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17558181487286096903720477 6584318057732286338895179)
              ·
                refine ⟨9876477086598429508342769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6584318057732286338895179 9876477086598429508342769)
                ·
                  refine ⟨7407357814948822131257077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9876477086598429508342769 7407357814948822131257077)
                  ·
                    refine ⟨694439795151452074805351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7407357814948822131257077 694439795151452074805351)
                    ·
                      rfl

theorem cell23_4057250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_4057250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057250 prefixEnd_4057250 := by exact prefixLift 4057250
  have htrace : WordTrace (prefixWord ++ tailWord_4057250) baseStart_4057250 baseEnd_4057250 := by
    simpa [prefixWord, tailWord_4057250, baseEnd_4057250] using wordTrace_append hprefix tailTrace_4057250
  have hstable : (prefixWord ++ tailWord_4057250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057250).length < 2 ^ (prefixWord ++ tailWord_4057250).sum := by decide
  have hdescent : baseEnd_4057250 < baseStart_4057250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057253 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 1, 6, 2]
def baseStart_4057253 : Nat := 118140960795 + 4057253 * 2 ^ 59
def prefixEnd_4057253 : Nat := 4983230072969 + 3 ^ 40 * 4057253 * 2
def baseEnd_4057253 : Nat := 2083320925896319712678539

theorem tailTrace_4057253 : CollatzResearch.WordTrace tailWord_4057253 prefixEnd_4057253 2083320925896319712678539 := by
  unfold tailWord_4057253
  simp only [CollatzResearch.WordTrace]
  refine ⟨147980173970272779491040413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98653449313515186327360275 147980173970272779491040413)
  ·
    refine ⟨55492565238852292309140155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147980173970272779491040413 55492565238852292309140155)
    ·
      refine ⟨83238847858278438463710233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55492565238852292309140155 83238847858278438463710233)
      ·
        refine ⟨62429135893708828847782675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83238847858278438463710233 62429135893708828847782675)
        ·
          refine ⟨93643703840563243271674013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62429135893708828847782675 93643703840563243271674013)
          ·
            refine ⟨35116388940211216226877755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93643703840563243271674013 35116388940211216226877755)
            ·
              refine ⟨52674583410316824340316633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35116388940211216226877755 52674583410316824340316633)
              ·
                refine ⟨39505937557737618255237475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52674583410316824340316633 39505937557737618255237475)
                ·
                  refine ⟨59258906336606427382856213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39505937557737618255237475 59258906336606427382856213)
                  ·
                    refine ⟨2777761234528426283571385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59258906336606427382856213 2777761234528426283571385)
                    ·
                      refine ⟨2083320925896319712678539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2777761234528426283571385 2083320925896319712678539)
                      ·
                        rfl

theorem cell23_4057253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_4057253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057253 prefixEnd_4057253 := by exact prefixLift 4057253
  have htrace : WordTrace (prefixWord ++ tailWord_4057253) baseStart_4057253 baseEnd_4057253 := by
    simpa [prefixWord, tailWord_4057253, baseEnd_4057253] using wordTrace_append hprefix tailTrace_4057253
  have hstable : (prefixWord ++ tailWord_4057253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057253).length < 2 ^ (prefixWord ++ tailWord_4057253).sum := by decide
  have hdescent : baseEnd_4057253 < baseStart_4057253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057266 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_4057266 : Nat := 118140960795 + 4057266 * 2 ^ 59
def prefixEnd_4057266 : Nat := 4983230072969 + 3 ^ 40 * 4057266 * 2
def baseEnd_4057266 : Nat := 2083327601144828161815979

theorem tailTrace_4057266 : CollatzResearch.WordTrace tailWord_4057266 prefixEnd_4057266 2083327601144828161815979 := by
  unfold tailWord_4057266
  simp only [CollatzResearch.WordTrace]
  refine ⟨36995162029806420677815913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98653765412817121807509101 36995162029806420677815913)
  ·
    refine ⟨27746371522354815508361935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36995162029806420677815913 27746371522354815508361935)
    ·
      refine ⟨41619557283532223262542903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27746371522354815508361935 41619557283532223262542903)
      ·
        refine ⟨62429335925298334893814355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41619557283532223262542903 62429335925298334893814355)
        ·
          refine ⟨93644003887947502340721533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62429335925298334893814355 93644003887947502340721533)
          ·
            refine ⟨35116501457980313377770575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93644003887947502340721533 35116501457980313377770575)
            ·
              refine ⟨52674752186970470066655863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35116501457980313377770575 52674752186970470066655863)
              ·
                refine ⟨79012128280455705099983795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52674752186970470066655863 79012128280455705099983795)
                ·
                  refine ⟨118518192420683557649975693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79012128280455705099983795 118518192420683557649975693)
                  ·
                    refine ⟨44444322157756334118740885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118518192420683557649975693 44444322157756334118740885)
                    ·
                      refine ⟨2083327601144828161815979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44444322157756334118740885 2083327601144828161815979)
                      ·
                        rfl

theorem cell23_4057266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_4057266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057266 prefixEnd_4057266 := by exact prefixLift 4057266
  have htrace : WordTrace (prefixWord ++ tailWord_4057266) baseStart_4057266 baseEnd_4057266 := by
    simpa [prefixWord, tailWord_4057266, baseEnd_4057266] using wordTrace_append hprefix tailTrace_4057266
  have hstable : (prefixWord ++ tailWord_4057266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057266).length < 2 ^ (prefixWord ++ tailWord_4057266).sum := by decide
  have hdescent : baseEnd_4057266 < baseStart_4057266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057273 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 4, 2, 3]
def baseStart_4057273 : Nat := 118140960795 + 4057273 * 2 ^ 59
def prefixEnd_4057273 : Nat := 4983230072969 + 3 ^ 40 * 4057273 * 2
def baseEnd_4057273 : Nat := 2083331195509409634428447

theorem tailTrace_4057273 : CollatzResearch.WordTrace tailWord_4057273 prefixEnd_4057273 2083331195509409634428447 := by
  unfold tailWord_4057273
  simp only [CollatzResearch.WordTrace]
  refine ⟨147980903430200322906768473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98653935620133548604512315 147980903430200322906768473)
  ·
    refine ⟨110985677572650242180076355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147980903430200322906768473 110985677572650242180076355)
    ·
      refine ⟨166478516358975363270114533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110985677572650242180076355 166478516358975363270114533)
      ·
        refine ⟨31214721817307880613146475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166478516358975363270114533 31214721817307880613146475)
        ·
          refine ⟨46822082725961820919719713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31214721817307880613146475 46822082725961820919719713)
          ·
            refine ⟨35116562044471365689789785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46822082725961820919719713 35116562044471365689789785)
            ·
              refine ⟨26337421533353524267342339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35116562044471365689789785 26337421533353524267342339)
              ·
                refine ⟨39506132300030286401013509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26337421533353524267342339 39506132300030286401013509)
                ·
                  refine ⟨7407399806255678700190033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39506132300030286401013509 7407399806255678700190033)
                  ·
                    refine ⟨5555549854691759025142525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7407399806255678700190033 5555549854691759025142525)
                    ·
                      refine ⟨2083331195509409634428447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5555549854691759025142525 2083331195509409634428447)
                      ·
                        rfl

theorem cell23_4057273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_4057273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057273 prefixEnd_4057273 := by exact prefixLift 4057273
  have htrace : WordTrace (prefixWord ++ tailWord_4057273) baseStart_4057273 baseEnd_4057273 := by
    simpa [prefixWord, tailWord_4057273, baseEnd_4057273] using wordTrace_append hprefix tailTrace_4057273
  have hstable : (prefixWord ++ tailWord_4057273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057273).length < 2 ^ (prefixWord ++ tailWord_4057273).sum := by decide
  have hdescent : baseEnd_4057273 < baseStart_4057273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057280 : List Nat := [2, 1, 1, 2, 5, 2, 2, 1, 3, 4]
def baseStart_4057280 : Nat := 118140960795 + 4057280 * 2 ^ 59
def prefixEnd_4057280 : Nat := 4983230072969 + 3 ^ 40 * 4057280 * 2
def baseEnd_4057280 : Nat := 694444929957997035680305

theorem tailTrace_4057280 : CollatzResearch.WordTrace tailWord_4057280 prefixEnd_4057280 694444929957997035680305 := by
  unfold tailWord_4057280
  simp only [CollatzResearch.WordTrace]
  refine ⟨73990579370587481551136647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98654105827449975401515529 73990579370587481551136647)
  ·
    refine ⟨110985869055881222326704971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73990579370587481551136647 110985869055881222326704971)
    ·
      refine ⟨166478803583821833490057457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110985869055881222326704971 166478803583821833490057457)
      ·
        refine ⟨124859102687866375117543093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166478803583821833490057457 124859102687866375117543093)
        ·
          refine ⟨11705540876987472667269665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124859102687866375117543093 11705540876987472667269665)
          ·
            refine ⟨8779155657740604500452249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11705540876987472667269665 8779155657740604500452249)
            ·
              refine ⟨6584366743305453375339187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8779155657740604500452249 6584366743305453375339187)
              ·
                refine ⟨9876550114958180063008781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6584366743305453375339187 9876550114958180063008781)
                ·
                  refine ⟨3703706293109317523628293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9876550114958180063008781 3703706293109317523628293)
                  ·
                    refine ⟨694444929957997035680305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3703706293109317523628293 694444929957997035680305)
                    ·
                      rfl

theorem cell23_4057280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 3, 4].length) (baseStart_4057280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057280 prefixEnd_4057280 := by exact prefixLift 4057280
  have htrace : WordTrace (prefixWord ++ tailWord_4057280) baseStart_4057280 baseEnd_4057280 := by
    simpa [prefixWord, tailWord_4057280, baseEnd_4057280] using wordTrace_append hprefix tailTrace_4057280
  have hstable : (prefixWord ++ tailWord_4057280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057280).length < 2 ^ (prefixWord ++ tailWord_4057280).sum := by decide
  have hdescent : baseEnd_4057280 < baseStart_4057280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057323 : List Nat := [1, 1, 1, 1, 2, 5, 1, 5, 1, 5]
def baseStart_4057323 : Nat := 118140960795 + 4057323 * 2 ^ 59
def prefixEnd_4057323 : Nat := 4983230072969 + 3 ^ 40 * 4057323 * 2
def baseEnd_4057323 : Nat := 694452289847378146267739

theorem tailTrace_4057323 : CollatzResearch.WordTrace tailWord_4057323 prefixEnd_4057323 694452289847378146267739 := by
  unfold tailWord_4057323
  simp only [CollatzResearch.WordTrace]
  refine ⟨147982727080019181446088623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98655151386679454297392415 147982727080019181446088623)
  ·
    refine ⟨221974090620028772169132935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147982727080019181446088623 221974090620028772169132935)
    ·
      refine ⟨332961135930043158253699403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221974090620028772169132935 332961135930043158253699403)
      ·
        refine ⟨499441703895064737380549105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332961135930043158253699403 499441703895064737380549105)
        ·
          refine ⟨374581277921298553035411829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499441703895064737380549105 374581277921298553035411829)
          ·
            refine ⟨35116994805121739347069859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 374581277921298553035411829 35116994805121739347069859)
            ·
              refine ⟨52675492207682609020604789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35116994805121739347069859 52675492207682609020604789)
              ·
                refine ⟨4938327394470244595681699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52675492207682609020604789 4938327394470244595681699)
                ·
                  refine ⟨7407491091705366893522549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4938327394470244595681699 7407491091705366893522549)
                  ·
                    refine ⟨694452289847378146267739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7407491091705366893522549 694452289847378146267739)
                    ·
                      rfl

theorem cell23_4057323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 5].length) (baseStart_4057323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057323 prefixEnd_4057323 := by exact prefixLift 4057323
  have htrace : WordTrace (prefixWord ++ tailWord_4057323) baseStart_4057323 baseEnd_4057323 := by
    simpa [prefixWord, tailWord_4057323, baseEnd_4057323] using wordTrace_append hprefix tailTrace_4057323
  have hstable : (prefixWord ++ tailWord_4057323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057323).length < 2 ^ (prefixWord ++ tailWord_4057323).sum := by decide
  have hdescent : baseEnd_4057323 < baseStart_4057323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057343 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 4]
def baseStart_4057343 : Nat := 118140960795 + 4057343 * 2 ^ 59
def prefixEnd_4057343 : Nat := 4983230072969 + 3 ^ 40 * 4057343 * 2
def baseEnd_4057343 : Nat := 2083367139155224360553125

theorem tailTrace_4057343 : CollatzResearch.WordTrace tailWord_4057343 prefixEnd_4057343 2083367139155224360553125 := by
  unfold tailWord_4057343
  simp only [CollatzResearch.WordTrace]
  refine ⟨147983456539946724861816683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98655637693297816574544455 147983456539946724861816683)
  ·
    refine ⟨221975184809920087292725025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147983456539946724861816683 221975184809920087292725025)
    ·
      refine ⟨166481388607440065469543769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221975184809920087292725025 166481388607440065469543769)
      ·
        refine ⟨124861041455580049102157827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166481388607440065469543769 124861041455580049102157827)
        ·
          refine ⟨187291562183370073653236741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124861041455580049102157827 187291562183370073653236741)
          ·
            refine ⟨35117167909381888809981889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187291562183370073653236741 35117167909381888809981889)
            ·
              refine ⟨26337875932036416607486417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35117167909381888809981889 26337875932036416607486417)
              ·
                refine ⟨19753406949027312455614813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26337875932036416607486417 19753406949027312455614813)
                ·
                  refine ⟨7407527605885242170855555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19753406949027312455614813 7407527605885242170855555)
                  ·
                    refine ⟨11111291408827863256283333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7407527605885242170855555 11111291408827863256283333)
                    ·
                      refine ⟨2083367139155224360553125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11111291408827863256283333 2083367139155224360553125)
                      ·
                        rfl

theorem cell23_4057343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_4057343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057343 prefixEnd_4057343 := by exact prefixLift 4057343
  have htrace : WordTrace (prefixWord ++ tailWord_4057343) baseStart_4057343 baseEnd_4057343 := by
    simpa [prefixWord, tailWord_4057343, baseEnd_4057343] using wordTrace_append hprefix tailTrace_4057343
  have hstable : (prefixWord ++ tailWord_4057343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057343).length < 2 ^ (prefixWord ++ tailWord_4057343).sum := by decide
  have hdescent : baseEnd_4057343 < baseStart_4057343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057370 : List Nat := [3, 1, 1, 3, 4, 1, 1, 2, 1, 6]
def baseStart_4057370 : Nat := 118140960795 + 4057370 * 2 ^ 59
def prefixEnd_4057370 : Nat := 4983230072969 + 3 ^ 40 * 4057370 * 2
def baseEnd_4057370 : Nat := 694460334377631918305167

theorem tailTrace_4057370 : CollatzResearch.WordTrace tailWord_4057370 prefixEnd_4057370 694460334377631918305167 := by
  unfold tailWord_4057370
  simp only [CollatzResearch.WordTrace]
  refine ⟨36996110327712227118262391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98656294207232605648699709 36996110327712227118262391)
  ·
    refine ⟨55494165491568340677393587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36996110327712227118262391 55494165491568340677393587)
    ·
      refine ⟨83241248237352511016090381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55494165491568340677393587 83241248237352511016090381)
      ·
        refine ⟨31215468089007191631033893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83241248237352511016090381 31215468089007191631033893)
        ·
          refine ⟨5852900266688848430818855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31215468089007191631033893 5852900266688848430818855)
          ·
            refine ⟨8779350400033272646228283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5852900266688848430818855 8779350400033272646228283)
            ·
              refine ⟨13169025600049908969342425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8779350400033272646228283 13169025600049908969342425)
              ·
                refine ⟨9876769200037431727006819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13169025600049908969342425 9876769200037431727006819)
                ·
                  refine ⟨14815153800056147590510229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9876769200037431727006819 14815153800056147590510229)
                  ·
                    refine ⟨694460334377631918305167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14815153800056147590510229 694460334377631918305167)
                    ·
                      rfl

theorem cell23_4057370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 1, 6].length) (baseStart_4057370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057370 prefixEnd_4057370 := by exact prefixLift 4057370
  have htrace : WordTrace (prefixWord ++ tailWord_4057370) baseStart_4057370 baseEnd_4057370 := by
    simpa [prefixWord, tailWord_4057370, baseEnd_4057370] using wordTrace_append hprefix tailTrace_4057370
  have hstable : (prefixWord ++ tailWord_4057370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057370).length < 2 ^ (prefixWord ++ tailWord_4057370).sum := by decide
  have hdescent : baseEnd_4057370 < baseStart_4057370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057380 : List Nat := [2, 3, 1, 3, 1, 2, 3, 1, 1, 1, 5]
def baseStart_4057380 : Nat := 118140960795 + 4057380 * 2 ^ 59
def prefixEnd_4057380 : Nat := 4983230072969 + 3 ^ 40 * 4057380 * 2
def baseEnd_4057380 : Nat := 2083386137939440715790455

theorem tailTrace_4057380 : CollatzResearch.WordTrace tailWord_4057380 prefixEnd_4057380 2083386137939440715790455 := by
  unfold tailWord_4057380
  simp only [CollatzResearch.WordTrace]
  refine ⟨73992403020406340090456797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98656537360541786787275729 73992403020406340090456797)
  ·
    refine ⟨27747151132652377533921299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73992403020406340090456797 27747151132652377533921299)
    ·
      refine ⟨41620726698978566300881949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27747151132652377533921299 41620726698978566300881949)
      ·
        refine ⟨15607772512116962362830731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41620726698978566300881949 15607772512116962362830731)
        ·
          refine ⟨23411658768175443544246097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15607772512116962362830731 23411658768175443544246097)
          ·
            refine ⟨17558744076131582658184573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23411658768175443544246097 17558744076131582658184573)
            ·
              refine ⟨6584529028549343496819215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17558744076131582658184573 6584529028549343496819215)
              ·
                refine ⟨9876793542824015245228823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6584529028549343496819215 9876793542824015245228823)
                ·
                  refine ⟨14815190314236022867843235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9876793542824015245228823 14815190314236022867843235)
                  ·
                    refine ⟨22222785471354034301764853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14815190314236022867843235 22222785471354034301764853)
                    ·
                      refine ⟨2083386137939440715790455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22222785471354034301764853 2083386137939440715790455)
                      ·
                        rfl

theorem cell23_4057380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_4057380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057380 prefixEnd_4057380 := by exact prefixLift 4057380
  have htrace : WordTrace (prefixWord ++ tailWord_4057380) baseStart_4057380 baseEnd_4057380 := by
    simpa [prefixWord, tailWord_4057380, baseEnd_4057380] using wordTrace_append hprefix tailTrace_4057380
  have hstable : (prefixWord ++ tailWord_4057380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057380).length < 2 ^ (prefixWord ++ tailWord_4057380).sum := by decide
  have hdescent : baseEnd_4057380 < baseStart_4057380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057438 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_4057438 : Nat := 118140960795 + 4057438 * 2 ^ 59
def prefixEnd_4057438 : Nat := 4983230072969 + 3 ^ 40 * 4057438 * 2
def baseEnd_4057438 : Nat := 694471973272467162955063

theorem tailTrace_4057438 : CollatzResearch.WordTrace tailWord_4057438 prefixEnd_4057438 694471973272467162955063 := by
  unfold tailWord_4057438
  simp only [CollatzResearch.WordTrace]
  refine ⟨18498365184325319510815621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98657947649735037391016645 18498365184325319510815621)
  ·
    refine ⟨3468443472060997408277929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18498365184325319510815621 3468443472060997408277929)
    ·
      refine ⟨2601332604045748056208447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3468443472060997408277929 2601332604045748056208447)
      ·
        refine ⟨3901998906068622084312671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2601332604045748056208447 3901998906068622084312671)
        ·
          refine ⟨5852998359102933126469007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3901998906068622084312671 5852998359102933126469007)
          ·
            refine ⟨8779497538654399689703511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5852998359102933126469007 8779497538654399689703511)
            ·
              refine ⟨13169246307981599534555267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8779497538654399689703511 13169246307981599534555267)
              ·
                refine ⟨19753869461972399301832901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13169246307981599534555267 19753869461972399301832901)
                ·
                  refine ⟨3703850524119824869093669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19753869461972399301832901 3703850524119824869093669)
                  ·
                    refine ⟨694471973272467162955063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3703850524119824869093669 694471973272467162955063)
                    ·
                      rfl

theorem cell23_4057438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_4057438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057438 prefixEnd_4057438 := by exact prefixLift 4057438
  have htrace : WordTrace (prefixWord ++ tailWord_4057438) baseStart_4057438 baseEnd_4057438 := by
    simpa [prefixWord, tailWord_4057438, baseEnd_4057438] using wordTrace_append hprefix tailTrace_4057438
  have hstable : (prefixWord ++ tailWord_4057438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057438).length < 2 ^ (prefixWord ++ tailWord_4057438).sum := by decide
  have hdescent : baseEnd_4057438 < baseStart_4057438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057443 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 4, 6]
def baseStart_4057443 : Nat := 118140960795 + 4057443 * 2 ^ 59
def prefixEnd_4057443 : Nat := 4983230072969 + 3 ^ 40 * 4057443 * 2
def baseEnd_4057443 : Nat := 694472829073557989767555

theorem tailTrace_4057443 : CollatzResearch.WordTrace tailWord_4057443 prefixEnd_4057443 694472829073557989767555 := by
  unfold tailWord_4057443
  simp only [CollatzResearch.WordTrace]
  refine ⟨147987103839584441940456983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98658069226389627960304655 147987103839584441940456983)
  ·
    refine ⟨221980655759376662910685475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147987103839584441940456983 221980655759376662910685475)
    ·
      refine ⟨332970983639064994366028213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221980655759376662910685475 332970983639064994366028213)
      ·
        refine ⟨31216029716162343221815145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 332970983639064994366028213 31216029716162343221815145)
        ·
          refine ⟨23412022287121757416361359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31216029716162343221815145 23412022287121757416361359)
          ·
            refine ⟨35118033430682636124542039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23412022287121757416361359 35118033430682636124542039)
            ·
              refine ⟨52677050146023954186813059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35118033430682636124542039 52677050146023954186813059)
              ·
                refine ⟨79015575219035931280219589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52677050146023954186813059 79015575219035931280219589)
                ·
                  refine ⟨14815420353569237115041173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79015575219035931280219589 14815420353569237115041173)
                  ·
                    refine ⟨694472829073557989767555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14815420353569237115041173 694472829073557989767555)
                    ·
                      rfl

theorem cell23_4057443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 6].length) (baseStart_4057443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057443 prefixEnd_4057443 := by exact prefixLift 4057443
  have htrace : WordTrace (prefixWord ++ tailWord_4057443) baseStart_4057443 baseEnd_4057443 := by
    simpa [prefixWord, tailWord_4057443, baseEnd_4057443] using wordTrace_append hprefix tailTrace_4057443
  have hstable : (prefixWord ++ tailWord_4057443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057443).length < 2 ^ (prefixWord ++ tailWord_4057443).sum := by decide
  have hdescent : baseEnd_4057443 < baseStart_4057443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057461 : List Nat := [1, 3, 4, 1, 2, 2, 3, 1, 2, 1, 3]
def baseStart_4057461 : Nat := 118140960795 + 4057461 * 2 ^ 59
def prefixEnd_4057461 : Nat := 4983230072969 + 3 ^ 40 * 4057461 * 2
def baseEnd_4057461 : Nat := 2083427729872454898877583

theorem tailTrace_4057461 : CollatzResearch.WordTrace tailWord_4057461 prefixEnd_4057461 2083427729872454898877583 := by
  unfold tailWord_4057461
  simp only [CollatzResearch.WordTrace]
  refine ⟨147987760353519231014612237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98658506902346154009741491 147987760353519231014612237)
  ·
    refine ⟨55495410132569711630479589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147987760353519231014612237 55495410132569711630479589)
    ·
      refine ⟨10405389399856820930714923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55495410132569711630479589 10405389399856820930714923)
      ·
        refine ⟨15608084099785231396072385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10405389399856820930714923 15608084099785231396072385)
        ·
          refine ⟨11706063074838923547054289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15608084099785231396072385 11706063074838923547054289)
          ·
            refine ⟨8779547306129192660290717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11706063074838923547054289 8779547306129192660290717)
            ·
              refine ⟨3292330239798447247609019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8779547306129192660290717 3292330239798447247609019)
              ·
                refine ⟨4938495359697670871413529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3292330239798447247609019 4938495359697670871413529)
                ·
                  refine ⟨3703871519773253153560147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4938495359697670871413529 3703871519773253153560147)
                  ·
                    refine ⟨5555807279659879730340221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3703871519773253153560147 5555807279659879730340221)
                    ·
                      refine ⟨2083427729872454898877583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5555807279659879730340221 2083427729872454898877583)
                      ·
                        rfl

theorem cell23_4057461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_4057461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057461 prefixEnd_4057461 := by exact prefixLift 4057461
  have htrace : WordTrace (prefixWord ++ tailWord_4057461) baseStart_4057461 baseEnd_4057461 := by
    simpa [prefixWord, tailWord_4057461, baseEnd_4057461] using wordTrace_append hprefix tailTrace_4057461
  have hstable : (prefixWord ++ tailWord_4057461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057461).length < 2 ^ (prefixWord ++ tailWord_4057461).sum := by decide
  have hdescent : baseEnd_4057461 < baseStart_4057461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057463 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 4]
def baseStart_4057463 : Nat := 118140960795 + 4057463 * 2 ^ 59
def prefixEnd_4057463 : Nat := 4983230072969 + 3 ^ 40 * 4057463 * 2
def baseEnd_4057463 : Nat := 2083428756833763891052573

theorem tailTrace_4057463 : CollatzResearch.WordTrace tailWord_4057463 prefixEnd_4057463 2083428756833763891052573 := by
  unfold tailWord_4057463
  simp only [CollatzResearch.WordTrace]
  refine ⟨147987833299511985356185043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98658555533007990237456695 147987833299511985356185043)
  ·
    refine ⟨221981749949267978034277565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147987833299511985356185043 221981749949267978034277565)
    ·
      refine ⟨83243156230975491762854087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221981749949267978034277565 83243156230975491762854087)
      ·
        refine ⟨124864734346463237644281131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83243156230975491762854087 124864734346463237644281131)
        ·
          refine ⟨187297101519694856466421697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124864734346463237644281131 187297101519694856466421697)
          ·
            refine ⟨140472826139771142349816273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187297101519694856466421697 140472826139771142349816273)
            ·
              refine ⟨105354619604828356762362205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140472826139771142349816273 105354619604828356762362205)
              ·
                refine ⟨39507982351810633785885827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105354619604828356762362205 39507982351810633785885827)
                ·
                  refine ⟨59261973527715950678828741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39507982351810633785885827 59261973527715950678828741)
                  ·
                    refine ⟨11111620036446740752280389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59261973527715950678828741 11111620036446740752280389)
                    ·
                      refine ⟨2083428756833763891052573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11111620036446740752280389 2083428756833763891052573)
                      ·
                        rfl

theorem cell23_4057463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_4057463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057463 prefixEnd_4057463 := by exact prefixLift 4057463
  have htrace : WordTrace (prefixWord ++ tailWord_4057463) baseStart_4057463 baseEnd_4057463 := by
    simpa [prefixWord, tailWord_4057463, baseEnd_4057463] using wordTrace_append hprefix tailTrace_4057463
  have hstable : (prefixWord ++ tailWord_4057463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057463).length < 2 ^ (prefixWord ++ tailWord_4057463).sum := by decide
  have hdescent : baseEnd_4057463 < baseStart_4057463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057467 : List Nat := [1, 1, 1, 1, 1, 7, 3, 1, 1, 4, 2]
def baseStart_4057467 : Nat := 118140960795 + 4057467 * 2 ^ 59
def prefixEnd_4057467 : Nat := 4983230072969 + 3 ^ 40 * 4057467 * 2
def baseEnd_4057467 : Nat := 2083430810756381875402555

theorem tailTrace_4057467 : CollatzResearch.WordTrace tailWord_4057467 prefixEnd_4057467 2083430810756381875402555 := by
  unfold tailWord_4057467
  simp only [CollatzResearch.WordTrace]
  refine ⟨147987979191497494039330655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98658652794331662692887103 147987979191497494039330655)
  ·
    refine ⟨221981968787246241058995983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147987979191497494039330655 221981968787246241058995983)
    ·
      refine ⟨332972953180869361588493975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221981968787246241058995983 332972953180869361588493975)
      ·
        refine ⟨499459429771304042382740963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332972953180869361588493975 499459429771304042382740963)
        ·
          refine ⟨749189144656956063574111445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499459429771304042382740963 749189144656956063574111445)
          ·
            refine ⟨17559120577897407740018237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 749189144656956063574111445 17559120577897407740018237)
            ·
              refine ⟨6584670216711527902506839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17559120577897407740018237 6584670216711527902506839)
              ·
                refine ⟨9877005325067291853760259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6584670216711527902506839 9877005325067291853760259)
                ·
                  refine ⟨14815507987600937780640389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9877005325067291853760259 14815507987600937780640389)
                  ·
                    refine ⟨2777907747675175833870073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14815507987600937780640389 2777907747675175833870073)
                    ·
                      refine ⟨2083430810756381875402555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2777907747675175833870073 2083430810756381875402555)
                      ·
                        rfl

theorem cell23_4057467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 4, 2].length) (baseStart_4057467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057467 prefixEnd_4057467 := by exact prefixLift 4057467
  have htrace : WordTrace (prefixWord ++ tailWord_4057467) baseStart_4057467 baseEnd_4057467 := by
    simpa [prefixWord, tailWord_4057467, baseEnd_4057467] using wordTrace_append hprefix tailTrace_4057467
  have hstable : (prefixWord ++ tailWord_4057467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057467).length < 2 ^ (prefixWord ++ tailWord_4057467).sum := by decide
  have hdescent : baseEnd_4057467 < baseStart_4057467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057557 : List Nat := [1, 3, 2, 3, 1, 2, 2, 2, 2, 1, 4]
def baseStart_4057557 : Nat := 118140960795 + 4057557 * 2 ^ 59
def prefixEnd_4057557 : Nat := 4983230072969 + 3 ^ 40 * 4057557 * 2
def baseEnd_4057557 : Nat := 2083477024015286523277141

theorem tailTrace_4057557 : CollatzResearch.WordTrace tailWord_4057557 prefixEnd_4057557 2083477024015286523277141 := by
  unfold tailWord_4057557
  simp only [CollatzResearch.WordTrace]
  refine ⟨147991261761171439410106925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98660841174114292940071283 147991261761171439410106925)
  ·
    refine ⟨55496723160439289778790097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147991261761171439410106925 55496723160439289778790097)
    ·
      refine ⟨41622542370329467334092573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55496723160439289778790097 41622542370329467334092573)
      ·
        refine ⟨15608453388873550250284715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41622542370329467334092573 15608453388873550250284715)
        ·
          refine ⟨23412680083310325375427073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15608453388873550250284715 23412680083310325375427073)
          ·
            refine ⟨17559510062482744031570305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23412680083310325375427073 17559510062482744031570305)
            ·
              refine ⟨13169632546862058023677729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17559510062482744031570305 13169632546862058023677729)
              ·
                refine ⟨9877224410146543517758297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13169632546862058023677729 9877224410146543517758297)
                ·
                  refine ⟨7407918307609907638318723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9877224410146543517758297 7407918307609907638318723)
                  ·
                    refine ⟨11111877461414861457478085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7407918307609907638318723 11111877461414861457478085)
                    ·
                      refine ⟨2083477024015286523277141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11111877461414861457478085 2083477024015286523277141)
                      ·
                        rfl

theorem cell23_4057557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_4057557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057557 prefixEnd_4057557 := by exact prefixLift 4057557
  have htrace : WordTrace (prefixWord ++ tailWord_4057557) baseStart_4057557 baseEnd_4057557 := by
    simpa [prefixWord, tailWord_4057557, baseEnd_4057557] using wordTrace_append hprefix tailTrace_4057557
  have hstable : (prefixWord ++ tailWord_4057557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057557).length < 2 ^ (prefixWord ++ tailWord_4057557).sum := by decide
  have hdescent : baseEnd_4057557 < baseStart_4057557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057560 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 3, 4, 3]
def baseStart_4057560 : Nat := 118140960795 + 4057560 * 2 ^ 59
def prefixEnd_4057560 : Nat := 4983230072969 + 3 ^ 40 * 4057560 * 2
def baseEnd_4057560 : Nat := 2083478564457250011539627

theorem tailTrace_4057560 : CollatzResearch.WordTrace tailWord_4057560 prefixEnd_4057560 2083478564457250011539627 := by
  unfold tailWord_4057560
  simp only [CollatzResearch.WordTrace]
  refine ⟨73995685590080285461233067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98660914120107047281644089 73995685590080285461233067)
  ·
    refine ⟨110993528385120428191849601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73995685590080285461233067 110993528385120428191849601)
    ·
      refine ⟨83245146288840321143887201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110993528385120428191849601 83245146288840321143887201)
      ·
        refine ⟨62433859716630240857915401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83245146288840321143887201 62433859716630240857915401)
        ·
          refine ⟨46825394787472680643436551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62433859716630240857915401 46825394787472680643436551)
          ·
            refine ⟨70238092181209020965154827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46825394787472680643436551 70238092181209020965154827)
            ·
              refine ⟨105357138271813531447732241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70238092181209020965154827 105357138271813531447732241)
              ·
                refine ⟨79017853703860148585799181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105357138271813531447732241 79017853703860148585799181)
                ·
                  refine ⟨29631695138947555719674693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79017853703860148585799181 29631695138947555719674693)
                  ·
                    refine ⟨5555942838552666697439005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29631695138947555719674693 5555942838552666697439005)
                    ·
                      refine ⟨2083478564457250011539627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5555942838552666697439005 2083478564457250011539627)
                      ·
                        rfl

theorem cell23_4057560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_4057560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057560 prefixEnd_4057560 := by exact prefixLift 4057560
  have htrace : WordTrace (prefixWord ++ tailWord_4057560) baseStart_4057560 baseEnd_4057560 := by
    simpa [prefixWord, tailWord_4057560, baseEnd_4057560] using wordTrace_append hprefix tailTrace_4057560
  have hstable : (prefixWord ++ tailWord_4057560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057560).length < 2 ^ (prefixWord ++ tailWord_4057560).sum := by decide
  have hdescent : baseEnd_4057560 < baseStart_4057560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057580 : List Nat := [2, 2, 1, 1, 2, 1, 3, 5, 6]
def baseStart_4057580 : Nat := 118140960795 + 4057580 * 2 ^ 59
def prefixEnd_4057580 : Nat := 4983230072969 + 3 ^ 40 * 4057580 * 2
def baseEnd_4057580 : Nat := 231498759341148881476615

theorem tailTrace_4057580 : CollatzResearch.WordTrace tailWord_4057580 prefixEnd_4057580 231498759341148881476615 := by
  unfold tailWord_4057580
  simp only [CollatzResearch.WordTrace]
  refine ⟨73996050320044057169097097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98661400426725409558796129 73996050320044057169097097)
  ·
    refine ⟨55497037740033042876822823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73996050320044057169097097 55497037740033042876822823)
    ·
      refine ⟨83245556610049564315234235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55497037740033042876822823 83245556610049564315234235)
      ·
        refine ⟨124868334915074346472851353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83245556610049564315234235 124868334915074346472851353)
        ·
          refine ⟨93651251186305759854638515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124868334915074346472851353 93651251186305759854638515)
          ·
            refine ⟨140476876779458639781957773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93651251186305759854638515 140476876779458639781957773)
            ·
              refine ⟨52678828792296989918234165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140476876779458639781957773 52678828792296989918234165)
              ·
                refine ⟨4938640199277842804834453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52678828792296989918234165 4938640199277842804834453)
                ·
                  refine ⟨231498759341148881476615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4938640199277842804834453 231498759341148881476615)
                  ·
                    rfl

theorem cell23_4057580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 6].length) (baseStart_4057580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057580 prefixEnd_4057580 := by exact prefixLift 4057580
  have htrace : WordTrace (prefixWord ++ tailWord_4057580) baseStart_4057580 baseEnd_4057580 := by
    simpa [prefixWord, tailWord_4057580, baseEnd_4057580] using wordTrace_append hprefix tailTrace_4057580
  have hstable : (prefixWord ++ tailWord_4057580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057580).length < 2 ^ (prefixWord ++ tailWord_4057580).sum := by decide
  have hdescent : baseEnd_4057580 < baseStart_4057580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057601 : List Nat := [1, 2, 4, 1, 3, 2, 2, 3, 1, 4]
def baseStart_4057601 : Nat := 118140960795 + 4057601 * 2 ^ 59
def prefixEnd_4057601 : Nat := 4983230072969 + 3 ^ 40 * 4057601 * 2
def baseEnd_4057601 : Nat := 694499872388028117042313

theorem tailTrace_4057601 : CollatzResearch.WordTrace tailWord_4057601 prefixEnd_4057601 694499872388028117042313 := by
  unfold tailWord_4057601
  simp only [CollatzResearch.WordTrace]
  refine ⟨147992866573012034924708657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98661911048674689949805771 147992866573012034924708657)
  ·
    refine ⟨110994649929759026193531493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147992866573012034924708657 110994649929759026193531493)
    ·
      refine ⟨20811496861829817411287155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110994649929759026193531493 20811496861829817411287155)
      ·
        refine ⟨31217245292744726116930733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20811496861829817411287155 31217245292744726116930733)
        ·
          refine ⟨11706466984779272293849025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31217245292744726116930733 11706466984779272293849025)
          ·
            refine ⟨8779850238584454220386769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11706466984779272293849025 8779850238584454220386769)
            ·
              refine ⟨6584887678938340665290077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8779850238584454220386769 6584887678938340665290077)
              ·
                refine ⟨2469332879601877749483779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6584887678938340665290077 2469332879601877749483779)
                ·
                  refine ⟨3703999319402816624225669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2469332879601877749483779 3703999319402816624225669)
                  ·
                    refine ⟨694499872388028117042313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3703999319402816624225669 694499872388028117042313)
                    ·
                      rfl

theorem cell23_4057601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_4057601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057601 prefixEnd_4057601 := by exact prefixLift 4057601
  have htrace : WordTrace (prefixWord ++ tailWord_4057601) baseStart_4057601 baseEnd_4057601 := by
    simpa [prefixWord, tailWord_4057601, baseEnd_4057601] using wordTrace_append hprefix tailTrace_4057601
  have hstable : (prefixWord ++ tailWord_4057601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057601).length < 2 ^ (prefixWord ++ tailWord_4057601).sum := by decide
  have hdescent : baseEnd_4057601 < baseStart_4057601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057614 : List Nat := [4, 1, 1, 2, 3, 3, 1, 2, 6]
def baseStart_4057614 : Nat := 118140960795 + 4057614 * 2 ^ 59
def prefixEnd_4057614 : Nat := 4983230072969 + 3 ^ 40 * 4057614 * 2
def baseEnd_4057614 : Nat := 231500699156954755584931

theorem tailTrace_4057614 : CollatzResearch.WordTrace tailWord_4057614 prefixEnd_4057614 231500699156954755584931 := by
  unfold tailWord_4057614
  simp only [CollatzResearch.WordTrace]
  refine ⟨18499167590245617268116487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98662227147976625429954597 18499167590245617268116487)
  ·
    refine ⟨27748751385368425902174731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18499167590245617268116487 27748751385368425902174731)
    ·
      refine ⟨41623127078052638853262097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27748751385368425902174731 41623127078052638853262097)
      ·
        refine ⟨31217345308539479139946573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41623127078052638853262097 31217345308539479139946573)
        ·
          refine ⟨11706504490702304677479965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31217345308539479139946573 11706504490702304677479965)
          ·
            refine ⟨4389939184013364254054987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11706504490702304677479965 4389939184013364254054987)
            ·
              refine ⟨6584908776020046381082481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4389939184013364254054987 6584908776020046381082481)
              ·
                refine ⟨4938681582015034785811861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6584908776020046381082481 4938681582015034785811861)
                ·
                  refine ⟨231500699156954755584931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4938681582015034785811861 231500699156954755584931)
                  ·
                    rfl

theorem cell23_4057614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_4057614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057614 prefixEnd_4057614 := by exact prefixLift 4057614
  have htrace : WordTrace (prefixWord ++ tailWord_4057614) baseStart_4057614 baseEnd_4057614 := by
    simpa [prefixWord, tailWord_4057614, baseEnd_4057614] using wordTrace_append hprefix tailTrace_4057614
  have hstable : (prefixWord ++ tailWord_4057614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057614).length < 2 ^ (prefixWord ++ tailWord_4057614).sum := by decide
  have hdescent : baseEnd_4057614 < baseStart_4057614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057624 : List Nat := [2, 1, 2, 3, 3, 1, 1, 3, 3, 1, 3]
def baseStart_4057624 : Nat := 118140960795 + 4057624 * 2 ^ 59
def prefixEnd_4057624 : Nat := 4983230072969 + 3 ^ 40 * 4057624 * 2
def baseEnd_4057624 : Nat := 2083511427219137761139333

theorem tailTrace_4057624 : CollatzResearch.WordTrace tailWord_4057624 prefixEnd_4057624 2083511427219137761139333 := by
  unfold tailWord_4057624
  simp only [CollatzResearch.WordTrace]
  refine ⟨73996852725964354926397963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98662470301285806568530617 73996852725964354926397963)
  ·
    refine ⟨110995279088946532389596945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73996852725964354926397963 110995279088946532389596945)
    ·
      refine ⟨83246459316709899292197709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110995279088946532389596945 83246459316709899292197709)
      ·
        refine ⟨31217422243766212234574141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83246459316709899292197709 31217422243766212234574141)
        ·
          refine ⟨11706533341412329587965303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31217422243766212234574141 11706533341412329587965303)
          ·
            refine ⟨17559800012118494381947955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11706533341412329587965303 17559800012118494381947955)
            ·
              refine ⟨26339700018177741572921933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17559800012118494381947955 26339700018177741572921933)
              ·
                refine ⟨9877387506816653089845725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26339700018177741572921933 9877387506816653089845725)
                ·
                  refine ⟨3704020315056244908692147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9877387506816653089845725 3704020315056244908692147)
                  ·
                    refine ⟨5556030472584367363038221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3704020315056244908692147 5556030472584367363038221)
                    ·
                      refine ⟨2083511427219137761139333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5556030472584367363038221 2083511427219137761139333)
                      ·
                        rfl

theorem cell23_4057624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_4057624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057624 prefixEnd_4057624 := by exact prefixLift 4057624
  have htrace : WordTrace (prefixWord ++ tailWord_4057624) baseStart_4057624 baseEnd_4057624 := by
    simpa [prefixWord, tailWord_4057624, baseEnd_4057624] using wordTrace_append hprefix tailTrace_4057624
  have hstable : (prefixWord ++ tailWord_4057624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057624).length < 2 ^ (prefixWord ++ tailWord_4057624).sum := by decide
  have hdescent : baseEnd_4057624 < baseStart_4057624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057652 : List Nat := [2, 5, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_4057652 : Nat := 118140960795 + 4057652 * 2 ^ 59
def prefixEnd_4057652 : Nat := 4983230072969 + 3 ^ 40 * 4057652 * 2
def baseEnd_4057652 : Nat := 694508601559154550529735

theorem tailTrace_4057652 : CollatzResearch.WordTrace tailWord_4057652 prefixEnd_4057652 694508601559154550529735 := by
  unfold tailWord_4057652
  simp only [CollatzResearch.WordTrace]
  refine ⟨73997363347913635317407605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98663151130551513756543473 73997363347913635317407605)
  ·
    refine ⟨6937252813866903311006963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73997363347913635317407605 6937252813866903311006963)
    ·
      refine ⟨10405879220800354966510445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6937252813866903311006963 10405879220800354966510445)
      ·
        refine ⟨3902204707800133112441417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10405879220800354966510445 3902204707800133112441417)
        ·
          refine ⟨2926653530850099834331063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3902204707800133112441417 2926653530850099834331063)
          ·
            refine ⟨4389980296275149751496595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2926653530850099834331063 4389980296275149751496595)
            ·
              refine ⟨6584970444412724627244893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4389980296275149751496595 6584970444412724627244893)
              ·
                refine ⟨2469363916654771735216835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6584970444412724627244893 2469363916654771735216835)
                ·
                  refine ⟨3704045874982157602825253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2469363916654771735216835 3704045874982157602825253)
                  ·
                    refine ⟨694508601559154550529735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3704045874982157602825253 694508601559154550529735)
                    ·
                      rfl

theorem cell23_4057652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_4057652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057652 prefixEnd_4057652 := by exact prefixLift 4057652
  have htrace : WordTrace (prefixWord ++ tailWord_4057652) baseStart_4057652 baseEnd_4057652 := by
    simpa [prefixWord, tailWord_4057652, baseEnd_4057652] using wordTrace_append hprefix tailTrace_4057652
  have hstable : (prefixWord ++ tailWord_4057652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057652).length < 2 ^ (prefixWord ++ tailWord_4057652).sum := by decide
  have hdescent : baseEnd_4057652 < baseStart_4057652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057657 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 6, 4]
def baseStart_4057657 : Nat := 118140960795 + 4057657 * 2 ^ 59
def prefixEnd_4057657 : Nat := 4983230072969 + 3 ^ 40 * 4057657 * 2
def baseEnd_4057657 : Nat := 694509457360245377342227

theorem tailTrace_4057657 : CollatzResearch.WordTrace tailWord_4057657 prefixEnd_4057657 694509457360245377342227 := by
  unfold tailWord_4057657
  simp only [CollatzResearch.WordTrace]
  refine ⟨147994909060809156488747225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98663272707206104325831483 147994909060809156488747225)
  ·
    refine ⟨110996181795606867366560419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147994909060809156488747225 110996181795606867366560419)
    ·
      refine ⟨166494272693410301049840629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110996181795606867366560419 166494272693410301049840629)
      ·
        refine ⟨15608838065007215723422559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166494272693410301049840629 15608838065007215723422559)
        ·
          refine ⟨23413257097510823585133839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15608838065007215723422559 23413257097510823585133839)
          ·
            refine ⟨35119885646266235377700759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23413257097510823585133839 35119885646266235377700759)
            ·
              refine ⟨52679828469399353066551139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35119885646266235377700759 52679828469399353066551139)
              ·
                refine ⟨79019742704099029599826709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52679828469399353066551139 79019742704099029599826709)
                ·
                  refine ⟨3704050439254642012491877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79019742704099029599826709 3704050439254642012491877)
                  ·
                    refine ⟨694509457360245377342227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3704050439254642012491877 694509457360245377342227)
                    ·
                      rfl

theorem cell23_4057657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 4].length) (baseStart_4057657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057657 prefixEnd_4057657 := by exact prefixLift 4057657
  have htrace : WordTrace (prefixWord ++ tailWord_4057657) baseStart_4057657 baseEnd_4057657 := by
    simpa [prefixWord, tailWord_4057657, baseEnd_4057657] using wordTrace_append hprefix tailTrace_4057657
  have hstable : (prefixWord ++ tailWord_4057657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057657).length < 2 ^ (prefixWord ++ tailWord_4057657).sum := by decide
  have hdescent : baseEnd_4057657 < baseStart_4057657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057658 : List Nat := [3, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3]
def baseStart_4057658 : Nat := 118140960795 + 4057658 * 2 ^ 59
def prefixEnd_4057658 : Nat := 4983230072969 + 3 ^ 40 * 4057658 * 2
def baseEnd_4057658 : Nat := 2083528885561390628114177

theorem tailTrace_4057658 : CollatzResearch.WordTrace tailWord_4057658 prefixEnd_4057658 2083528885561390628114177 := by
  unfold tailWord_4057658
  simp only [CollatzResearch.WordTrace]
  refine ⟨36998736383451383414883407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98663297022537022439689085 36998736383451383414883407)
  ·
    refine ⟨55498104575177075122325111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36998736383451383414883407 55498104575177075122325111)
    ·
      refine ⟨83247156862765612683487667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55498104575177075122325111 83247156862765612683487667)
      ·
        refine ⟨124870735294148419025231501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83247156862765612683487667 124870735294148419025231501)
        ·
          refine ⟨46826525735305657134461813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124870735294148419025231501 46826525735305657134461813)
          ·
            refine ⟨4389986787684905356355795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46826525735305657134461813 4389986787684905356355795)
            ·
              refine ⟨6584980181527358034533693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4389986787684905356355795 6584980181527358034533693)
              ·
                refine ⟨2469367568072759262950135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6584980181527358034533693 2469367568072759262950135)
                ·
                  refine ⟨3704051352109138894425203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2469367568072759262950135 3704051352109138894425203)
                  ·
                    refine ⟨5556077028163708341637805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3704051352109138894425203 5556077028163708341637805)
                    ·
                      refine ⟨2083528885561390628114177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5556077028163708341637805 2083528885561390628114177)
                      ·
                        rfl

theorem cell23_4057658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3].length) (baseStart_4057658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057658 prefixEnd_4057658 := by exact prefixLift 4057658
  have htrace : WordTrace (prefixWord ++ tailWord_4057658) baseStart_4057658 baseEnd_4057658 := by
    simpa [prefixWord, tailWord_4057658, baseEnd_4057658] using wordTrace_append hprefix tailTrace_4057658
  have hstable : (prefixWord ++ tailWord_4057658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057658).length < 2 ^ (prefixWord ++ tailWord_4057658).sum := by decide
  have hdescent : baseEnd_4057658 < baseStart_4057658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057664 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 5, 2, 2]
def baseStart_4057664 : Nat := 118140960795 + 4057664 * 2 ^ 59
def prefixEnd_4057664 : Nat := 4983230072969 + 3 ^ 40 * 4057664 * 2
def baseEnd_4057664 : Nat := 2083531966445317604639149

theorem tailTrace_4057664 : CollatzResearch.WordTrace tailWord_4057664 prefixEnd_4057664 2083531966445317604639149 := by
  unfold tailWord_4057664
  simp only [CollatzResearch.WordTrace]
  refine ⟨73997582185891898342126023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98663442914522531122834697 73997582185891898342126023)
  ·
    refine ⟨110996373278837847513189035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73997582185891898342126023 110996373278837847513189035)
    ·
      refine ⟨166494559918256771269783553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110996373278837847513189035 166494559918256771269783553)
      ·
        refine ⟨124870919938692578452337665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166494559918256771269783553 124870919938692578452337665)
        ·
          refine ⟨93653189954019433839253249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124870919938692578452337665 93653189954019433839253249)
          ·
            refine ⟨70239892465514575379439937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93653189954019433839253249 70239892465514575379439937)
            ·
              refine ⟨52679919349135931534579953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70239892465514575379439937 52679919349135931534579953)
              ·
                refine ⟨39509939511851948650934965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52679919349135931534579953 39509939511851948650934965)
                ·
                  refine ⟨3704056829236120186025153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39509939511851948650934965 3704056829236120186025153)
                  ·
                    refine ⟨2778042621927090139518865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3704056829236120186025153 2778042621927090139518865)
                    ·
                      refine ⟨2083531966445317604639149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2778042621927090139518865 2083531966445317604639149)
                      ·
                        rfl

theorem cell23_4057664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 5, 2, 2].length) (baseStart_4057664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057664 prefixEnd_4057664 := by exact prefixLift 4057664
  have htrace : WordTrace (prefixWord ++ tailWord_4057664) baseStart_4057664 baseEnd_4057664 := by
    simpa [prefixWord, tailWord_4057664, baseEnd_4057664] using wordTrace_append hprefix tailTrace_4057664
  have hstable : (prefixWord ++ tailWord_4057664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057664).length < 2 ^ (prefixWord ++ tailWord_4057664).sum := by decide
  have hdescent : baseEnd_4057664 < baseStart_4057664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057681 : List Nat := [1, 2, 2, 1, 3, 3, 3, 1, 3, 2, 2]
def baseStart_4057681 : Nat := 118140960795 + 4057681 * 2 ^ 59
def prefixEnd_4057681 : Nat := 4983230072969 + 3 ^ 40 * 4057681 * 2
def baseEnd_4057681 : Nat := 2083540695616444038126571

theorem tailTrace_4057681 : CollatzResearch.WordTrace tailWord_4057681 prefixEnd_4057681 2083540695616444038126571 := by
  unfold tailWord_4057681
  simp only [CollatzResearch.WordTrace]
  refine ⟨147995784412722208587620897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98663856275148139058413931 147995784412722208587620897)
  ·
    refine ⟨110996838309541656440715673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147995784412722208587620897 110996838309541656440715673)
    ·
      refine ⟨83247628732156242330536755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110996838309541656440715673 83247628732156242330536755)
      ·
        refine ⟨124871443098234363495805133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83247628732156242330536755 124871443098234363495805133)
        ·
          refine ⟨46826791161837886310926925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124871443098234363495805133 46826791161837886310926925)
          ·
            refine ⟨17560046685689207366597597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46826791161837886310926925 17560046685689207366597597)
            ·
              refine ⟨6585017507133452762474099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17560046685689207366597597 6585017507133452762474099)
              ·
                refine ⟨9877526260700179143711149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6585017507133452762474099 9877526260700179143711149)
                ·
                  refine ⟨3704072347762567178891681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9877526260700179143711149 3704072347762567178891681)
                  ·
                    refine ⟨2778054260821925384168761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3704072347762567178891681 2778054260821925384168761)
                    ·
                      refine ⟨2083540695616444038126571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2778054260821925384168761 2083540695616444038126571)
                      ·
                        rfl

theorem cell23_4057681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 2, 2].length) (baseStart_4057681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057681 prefixEnd_4057681 := by exact prefixLift 4057681
  have htrace : WordTrace (prefixWord ++ tailWord_4057681) baseStart_4057681 baseEnd_4057681 := by
    simpa [prefixWord, tailWord_4057681, baseEnd_4057681] using wordTrace_append hprefix tailTrace_4057681
  have hstable : (prefixWord ++ tailWord_4057681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057681).length < 2 ^ (prefixWord ++ tailWord_4057681).sum := by decide
  have hdescent : baseEnd_4057681 < baseStart_4057681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057718 : List Nat := [5, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5]
def baseStart_4057718 : Nat := 118140960795 + 4057718 * 2 ^ 59
def prefixEnd_4057718 : Nat := 4983230072969 + 3 ^ 40 * 4057718 * 2
def baseEnd_4057718 : Nat := 2083559694400660393363901

theorem tailTrace_4057718 : CollatzResearch.WordTrace tailWord_4057718 prefixEnd_4057718 2083559694400660393363901 := by
  unfold tailWord_4057718
  simp only [CollatzResearch.WordTrace]
  refine ⟨9249820869599260244169863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98664755942392109271145205 9249820869599260244169863)
  ·
    refine ⟨13874731304398890366254795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9249820869599260244169863 13874731304398890366254795)
    ·
      refine ⟨20812096956598335549382193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13874731304398890366254795 20812096956598335549382193)
      ·
        refine ⟨15609072717448751662036645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20812096956598335549382193 15609072717448751662036645)
        ·
          refine ⟨2926701134521640936631871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15609072717448751662036645 2926701134521640936631871)
          ·
            refine ⟨4390051701782461404947807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2926701134521640936631871 4390051701782461404947807)
            ·
              refine ⟨6585077552673692107421711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4390051701782461404947807 6585077552673692107421711)
              ·
                refine ⟨9877616329010538161132567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6585077552673692107421711 9877616329010538161132567)
                ·
                  refine ⟨14816424493515807241698851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9877616329010538161132567 14816424493515807241698851)
                  ·
                    refine ⟨22224636740273710862548277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14816424493515807241698851 22224636740273710862548277)
                    ·
                      refine ⟨2083559694400660393363901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22224636740273710862548277 2083559694400660393363901)
                      ·
                        rfl

theorem cell23_4057718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_4057718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057718 prefixEnd_4057718 := by exact prefixLift 4057718
  have htrace : WordTrace (prefixWord ++ tailWord_4057718) baseStart_4057718 baseEnd_4057718 := by
    simpa [prefixWord, tailWord_4057718, baseEnd_4057718] using wordTrace_append hprefix tailTrace_4057718
  have hstable : (prefixWord ++ tailWord_4057718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057718).length < 2 ^ (prefixWord ++ tailWord_4057718).sum := by decide
  have hdescent : baseEnd_4057718 < baseStart_4057718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057720 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 1, 2, 8]
def baseStart_4057720 : Nat := 118140960795 + 4057720 * 2 ^ 59
def prefixEnd_4057720 : Nat := 4983230072969 + 3 ^ 40 * 4057720 * 2
def baseEnd_4057720 : Nat := 2083560721361969385538891

theorem tailTrace_4057720 : CollatzResearch.WordTrace tailWord_4057720 prefixEnd_4057720 2083560721361969385538891 := by
  unfold tailWord_4057720
  simp only [CollatzResearch.WordTrace]
  refine ⟨73998603429790459124145307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98664804573053945498860409 73998603429790459124145307)
  ·
    refine ⟨110997905144685688686217961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73998603429790459124145307 110997905144685688686217961)
    ·
      refine ⟨83248428858514266514663471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110997905144685688686217961 83248428858514266514663471)
      ·
        refine ⟨124872643287771399771995207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83248428858514266514663471 124872643287771399771995207)
        ·
          refine ⟨187308964931657099657992811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124872643287771399771995207 187308964931657099657992811)
          ·
            refine ⟨280963447397485649486989217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187308964931657099657992811 280963447397485649486989217)
            ·
              refine ⟨210722585548114237115241913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280963447397485649486989217 210722585548114237115241913)
              ·
                refine ⟨158041939161085677836431435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210722585548114237115241913 158041939161085677836431435)
                ·
                  refine ⟨237062908741628516754647153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158041939161085677836431435 237062908741628516754647153)
                  ·
                    refine ⟨177797181556221387565985365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 237062908741628516754647153 177797181556221387565985365)
                    ·
                      refine ⟨2083560721361969385538891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 177797181556221387565985365 2083560721361969385538891)
                      ·
                        rfl

theorem cell23_4057720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_4057720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057720 prefixEnd_4057720 := by exact prefixLift 4057720
  have htrace : WordTrace (prefixWord ++ tailWord_4057720) baseStart_4057720 baseEnd_4057720 := by
    simpa [prefixWord, tailWord_4057720, baseEnd_4057720] using wordTrace_append hprefix tailTrace_4057720
  have hstable : (prefixWord ++ tailWord_4057720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057720).length < 2 ^ (prefixWord ++ tailWord_4057720).sum := by decide
  have hdescent : baseEnd_4057720 < baseStart_4057720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057732 : List Nat := [2, 3, 2, 1, 3, 3, 2, 2, 1, 2, 2]
def baseStart_4057732 : Nat := 118140960795 + 4057732 * 2 ^ 59
def prefixEnd_4057732 : Nat := 4983230072969 + 3 ^ 40 * 4057732 * 2
def baseEnd_4057732 : Nat := 2083566883129823338588837

theorem tailTrace_4057732 : CollatzResearch.WordTrace tailWord_4057732 prefixEnd_4057732 2083566883129823338588837 := by
  unfold tailWord_4057732
  simp only [CollatzResearch.WordTrace]
  refine ⟨73998822267768722148863725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98665096357024962865151633 73998822267768722148863725)
  ·
    refine ⟨27749558350413270805823897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73998822267768722148863725 27749558350413270805823897)
    ·
      refine ⟨20812168762809953104367923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27749558350413270805823897 20812168762809953104367923)
      ·
        refine ⟨31218253144214929656551885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20812168762809953104367923 31218253144214929656551885)
        ·
          refine ⟨11706844929080598621206957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31218253144214929656551885 11706844929080598621206957)
          ·
            refine ⟨4390066848405224482952609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11706844929080598621206957 4390066848405224482952609)
            ·
              refine ⟨3292550136303918362214457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4390066848405224482952609 3292550136303918362214457)
              ·
                refine ⟨2469412602227938771660843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3292550136303918362214457 2469412602227938771660843)
                ·
                  refine ⟨3704118903341908157491265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2469412602227938771660843 3704118903341908157491265)
                  ·
                    refine ⟨2778089177506431118118449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3704118903341908157491265 2778089177506431118118449)
                    ·
                      refine ⟨2083566883129823338588837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2778089177506431118118449 2083566883129823338588837)
                      ·
                        rfl

theorem cell23_4057732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_4057732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057732 prefixEnd_4057732 := by exact prefixLift 4057732
  have htrace : WordTrace (prefixWord ++ tailWord_4057732) baseStart_4057732 baseEnd_4057732 := by
    simpa [prefixWord, tailWord_4057732, baseEnd_4057732] using wordTrace_append hprefix tailTrace_4057732
  have hstable : (prefixWord ++ tailWord_4057732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057732).length < 2 ^ (prefixWord ++ tailWord_4057732).sum := by decide
  have hdescent : baseEnd_4057732 < baseStart_4057732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057748 : List Nat := [2, 4, 2, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_4057748 : Nat := 118140960795 + 4057748 * 2 ^ 59
def prefixEnd_4057748 : Nat := 4983230072969 + 3 ^ 40 * 4057748 * 2
def baseEnd_4057748 : Nat := 2083575098820295275988763

theorem tailTrace_4057748 : CollatzResearch.WordTrace tailWord_4057748 prefixEnd_4057748 2083575098820295275988763 := by
  unfold tailWord_4057748
  simp only [CollatzResearch.WordTrace]
  refine ⟨73999114051739739515154949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98665485402319652686873265 73999114051739739515154949)
  ·
    refine ⟨13874833884701201159091553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73999114051739739515154949 13874833884701201159091553)
    ·
      refine ⟨10406125413525900869318665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13874833884701201159091553 10406125413525900869318665)
      ·
        refine ⟨7804594060144425651988999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10406125413525900869318665 7804594060144425651988999)
        ·
          refine ⟨11706891090216638477983499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7804594060144425651988999 11706891090216638477983499)
          ·
            refine ⟨17560336635324957716975249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11706891090216638477983499 17560336635324957716975249)
            ·
              refine ⟨13170252476493718287731437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17560336635324957716975249 13170252476493718287731437)
              ·
                refine ⟨4938844678685144357899289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13170252476493718287731437 4938844678685144357899289)
                ·
                  refine ⟨3704133509013858268424467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4938844678685144357899289 3704133509013858268424467)
                  ·
                    refine ⟨5556200263520787402636701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3704133509013858268424467 5556200263520787402636701)
                    ·
                      refine ⟨2083575098820295275988763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5556200263520787402636701 2083575098820295275988763)
                      ·
                        rfl

theorem cell23_4057748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_4057748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057748 prefixEnd_4057748 := by exact prefixLift 4057748
  have htrace : WordTrace (prefixWord ++ tailWord_4057748) baseStart_4057748 baseEnd_4057748 := by
    simpa [prefixWord, tailWord_4057748, baseEnd_4057748] using wordTrace_append hprefix tailTrace_4057748
  have hstable : (prefixWord ++ tailWord_4057748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057748).length < 2 ^ (prefixWord ++ tailWord_4057748).sum := by decide
  have hdescent : baseEnd_4057748 < baseStart_4057748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057757 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_4057757 : Nat := 118140960795 + 4057757 * 2 ^ 59
def prefixEnd_4057757 : Nat := 4983230072969 + 3 ^ 40 * 4057757 * 2
def baseEnd_4057757 : Nat := 2083579720146185740776221

theorem tailTrace_4057757 : CollatzResearch.WordTrace tailWord_4057757 prefixEnd_4057757 2083579720146185740776221 := by
  unfold tailWord_4057757
  simp only [CollatzResearch.WordTrace]
  refine ⟨147998556360446873567387525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98665704240297915711591683 147998556360446873567387525)
  ·
    refine ⟨27749729317583788793885161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147998556360446873567387525 27749729317583788793885161)
    ·
      refine ⟨20812296988187841595413871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27749729317583788793885161 20812296988187841595413871)
      ·
        refine ⟨31218445482281762393120807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20812296988187841595413871 31218445482281762393120807)
        ·
          refine ⟨46827668223422643589681211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31218445482281762393120807 46827668223422643589681211)
          ·
            refine ⟨70241502335133965384521817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46827668223422643589681211 70241502335133965384521817)
            ·
              refine ⟨52681126751350474038391363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70241502335133965384521817 52681126751350474038391363)
              ·
                refine ⟨79021690127025711057587045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52681126751350474038391363 79021690127025711057587045)
                ·
                  refine ⟨14816566898817320823297571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79021690127025711057587045 14816566898817320823297571)
                  ·
                    refine ⟨22224850348225981234946357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14816566898817320823297571 22224850348225981234946357)
                    ·
                      refine ⟨2083579720146185740776221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22224850348225981234946357 2083579720146185740776221)
                      ·
                        rfl

theorem cell23_4057757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_4057757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057757 prefixEnd_4057757 := by exact prefixLift 4057757
  have htrace : WordTrace (prefixWord ++ tailWord_4057757) baseStart_4057757 baseEnd_4057757 := by
    simpa [prefixWord, tailWord_4057757, baseEnd_4057757] using wordTrace_append hprefix tailTrace_4057757
  have hstable : (prefixWord ++ tailWord_4057757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057757).length < 2 ^ (prefixWord ++ tailWord_4057757).sum := by decide
  have hdescent : baseEnd_4057757 < baseStart_4057757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057758 : List Nat := [4, 3, 1, 1, 1, 1, 2, 4, 1, 3, 2]
def baseStart_4057758 : Nat := 118140960795 + 4057758 * 2 ^ 59
def prefixEnd_4057758 : Nat := 4983230072969 + 3 ^ 40 * 4057758 * 2
def baseEnd_4057758 : Nat := 2083580233626840236863717

theorem tailTrace_4057758 : CollatzResearch.WordTrace tailWord_4057758 prefixEnd_4057758 2083580233626840236863717 := by
  unfold tailWord_4057758
  simp only [CollatzResearch.WordTrace]
  refine ⟨18499824104180406342271741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98665728555628833825449285 18499824104180406342271741)
  ·
    refine ⟨6937434039067652378351903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18499824104180406342271741 6937434039067652378351903)
    ·
      refine ⟨10406151058601478567527855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6937434039067652378351903 10406151058601478567527855)
      ·
        refine ⟨15609226587902217851291783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10406151058601478567527855 15609226587902217851291783)
        ·
          refine ⟨23413839881853326776937675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15609226587902217851291783 23413839881853326776937675)
          ·
            refine ⟨35120759822779990165406513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23413839881853326776937675 35120759822779990165406513)
            ·
              refine ⟨26340569867084992624054885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35120759822779990165406513 26340569867084992624054885)
              ·
                refine ⟨4938856850078436117010291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26340569867084992624054885 4938856850078436117010291)
                ·
                  refine ⟨7408285275117654175515437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4938856850078436117010291 7408285275117654175515437)
                  ·
                    refine ⟨2778106978169120315818289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7408285275117654175515437 2778106978169120315818289)
                    ·
                      refine ⟨2083580233626840236863717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2778106978169120315818289 2083580233626840236863717)
                      ·
                        rfl

theorem cell23_4057758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_4057758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057758 prefixEnd_4057758 := by exact prefixLift 4057758
  have htrace : WordTrace (prefixWord ++ tailWord_4057758) baseStart_4057758 baseEnd_4057758 := by
    simpa [prefixWord, tailWord_4057758, baseEnd_4057758] using wordTrace_append hprefix tailTrace_4057758
  have hstable : (prefixWord ++ tailWord_4057758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057758).length < 2 ^ (prefixWord ++ tailWord_4057758).sum := by decide
  have hdescent : baseEnd_4057758 < baseStart_4057758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057782 : List Nat := [5, 1, 3, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_4057782 : Nat := 118140960795 + 4057782 * 2 ^ 59
def prefixEnd_4057782 : Nat := 4983230072969 + 3 ^ 40 * 4057782 * 2
def baseEnd_4057782 : Nat := 2083592557162548142963607

theorem tailTrace_4057782 : CollatzResearch.WordTrace tailWord_4057782 prefixEnd_4057782 2083592557162548142963607 := by
  unfold tailWord_4057782
  simp only [CollatzResearch.WordTrace]
  refine ⟨9249966761584768927315475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98666312123570868558031733 9249966761584768927315475)
  ·
    refine ⟨13874950142377153390973213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9249966761584768927315475 13874950142377153390973213)
    ·
      refine ⟨5203106303391432521614955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13874950142377153390973213 5203106303391432521614955)
      ·
        refine ⟨7804659455087148782422433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5203106303391432521614955 7804659455087148782422433)
        ·
          refine ⟨5853494591315361586816825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7804659455087148782422433 5853494591315361586816825)
          ·
            refine ⟨4390120943486521190112619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5853494591315361586816825 4390120943486521190112619)
            ·
              refine ⟨6585181415229781785168929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4390120943486521190112619 6585181415229781785168929)
              ·
                refine ⟨4938886061422336338876697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6585181415229781785168929 4938886061422336338876697)
                ·
                  refine ⟨3704164546066752254157523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4938886061422336338876697 3704164546066752254157523)
                  ·
                    refine ⟨5556246819100128381236285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3704164546066752254157523 5556246819100128381236285)
                    ·
                      refine ⟨2083592557162548142963607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5556246819100128381236285 2083592557162548142963607)
                      ·
                        rfl

theorem cell23_4057782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_4057782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057782 prefixEnd_4057782 := by exact prefixLift 4057782
  have htrace : WordTrace (prefixWord ++ tailWord_4057782) baseStart_4057782 baseEnd_4057782 := by
    simpa [prefixWord, tailWord_4057782, baseEnd_4057782] using wordTrace_append hprefix tailTrace_4057782
  have hstable : (prefixWord ++ tailWord_4057782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057782).length < 2 ^ (prefixWord ++ tailWord_4057782).sum := by decide
  have hdescent : baseEnd_4057782 < baseStart_4057782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057845 : List Nat := [1, 3, 6, 1, 1, 2, 1, 1, 7]
def baseStart_4057845 : Nat := 118140960795 + 4057845 * 2 ^ 59
def prefixEnd_4057845 : Nat := 4983230072969 + 3 ^ 40 * 4057845 * 2
def baseEnd_4057845 : Nat := 231513878493753488497313

theorem tailTrace_4057845 : CollatzResearch.WordTrace tailWord_4057845 prefixEnd_4057845 231513878493753488497313 := by
  unfold tailWord_4057845
  simp only [CollatzResearch.WordTrace]
  refine ⟨148001765984128064596590989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98667843989418709731060659 148001765984128064596590989)
  ·
    refine ⟨55500662244048024223721621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148001765984128064596590989 55500662244048024223721621)
    ·
      refine ⟨2601593542689751135486951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55500662244048024223721621 2601593542689751135486951)
      ·
        refine ⟨3902390314034626703230427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2601593542689751135486951 3902390314034626703230427)
        ·
          refine ⟨5853585471051940054845641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3902390314034626703230427 5853585471051940054845641)
          ·
            refine ⟨4390189103288955041134231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5853585471051940054845641 4390189103288955041134231)
            ·
              refine ⟨6585283654933432561701347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4390189103288955041134231 6585283654933432561701347)
              ·
                refine ⟨9877925482400148842552021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6585283654933432561701347 9877925482400148842552021)
                ·
                  refine ⟨231513878493753488497313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9877925482400148842552021 231513878493753488497313)
                  ·
                    rfl

theorem cell23_4057845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 7].length) (baseStart_4057845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057845 prefixEnd_4057845 := by exact prefixLift 4057845
  have htrace : WordTrace (prefixWord ++ tailWord_4057845) baseStart_4057845 baseEnd_4057845 := by
    simpa [prefixWord, tailWord_4057845, baseEnd_4057845] using wordTrace_append hprefix tailTrace_4057845
  have hstable : (prefixWord ++ tailWord_4057845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057845).length < 2 ^ (prefixWord ++ tailWord_4057845).sum := by decide
  have hdescent : baseEnd_4057845 < baseStart_4057845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057911 : List Nat := [1, 1, 3, 1, 2, 1, 4, 3, 3, 1, 3]
def baseStart_4057911 : Nat := 118140960795 + 4057911 * 2 ^ 59
def prefixEnd_4057911 : Nat := 4983230072969 + 3 ^ 40 * 4057911 * 2
def baseEnd_4057911 : Nat := 2083658796166978138250513

theorem tailTrace_4057911 : CollatzResearch.WordTrace tailWord_4057911 prefixEnd_4057911 2083658796166978138250513 := by
  unfold tailWord_4057911
  simp only [CollatzResearch.WordTrace]
  refine ⟨148004173201888957868493587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98669448801259305245662391 148004173201888957868493587)
  ·
    refine ⟨222006259802833436802740381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148004173201888957868493587 222006259802833436802740381)
    ·
      refine ⟨83252347426062538801027643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222006259802833436802740381 83252347426062538801027643)
      ·
        refine ⟨124878521139093808201541465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83252347426062538801027643 124878521139093808201541465)
        ·
          refine ⟨93658890854320356151156099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124878521139093808201541465 93658890854320356151156099)
          ·
            refine ⟨140488336281480534226734149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93658890854320356151156099 140488336281480534226734149)
            ·
              refine ⟨26341563052777600167512653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140488336281480534226734149 26341563052777600167512653)
              ·
                refine ⟨9878086144791600062817245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26341563052777600167512653 9878086144791600062817245)
                ·
                  refine ⟨3704282304296850023556467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9878086144791600062817245 3704282304296850023556467)
                  ·
                    refine ⟨5556423456445275035334701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3704282304296850023556467 5556423456445275035334701)
                    ·
                      refine ⟨2083658796166978138250513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5556423456445275035334701 2083658796166978138250513)
                      ·
                        rfl

theorem cell23_4057911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 1, 3].length) (baseStart_4057911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057911 prefixEnd_4057911 := by exact prefixLift 4057911
  have htrace : WordTrace (prefixWord ++ tailWord_4057911) baseStart_4057911 baseEnd_4057911 := by
    simpa [prefixWord, tailWord_4057911, baseEnd_4057911] using wordTrace_append hprefix tailTrace_4057911
  have hstable : (prefixWord ++ tailWord_4057911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057911).length < 2 ^ (prefixWord ++ tailWord_4057911).sum := by decide
  have hdescent : baseEnd_4057911 < baseStart_4057911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057945 : List Nat := [1, 2, 1, 2, 2, 5, 2, 3, 1, 1, 3]
def baseStart_4057945 : Nat := 118140960795 + 4057945 * 2 ^ 59
def prefixEnd_4057945 : Nat := 4983230072969 + 3 ^ 40 * 4057945 * 2
def baseEnd_4057945 : Nat := 2083676254509231005225357

theorem tailTrace_4057945 : CollatzResearch.WordTrace tailWord_4057945 prefixEnd_4057945 2083676254509231005225357 := by
  unfold tailWord_4057945
  simp only [CollatzResearch.WordTrace]
  refine ⟨148005413283765781675231289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98670275522510521116820859 148005413283765781675231289)
  ·
    refine ⟨111004059962824336256423467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148005413283765781675231289 111004059962824336256423467)
    ·
      refine ⟨166506089944236504384635201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111004059962824336256423467 166506089944236504384635201)
      ·
        refine ⟨124879567458177378288476401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166506089944236504384635201 124879567458177378288476401)
        ·
          refine ⟨93659675593633033716357301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124879567458177378288476401 93659675593633033716357301)
          ·
            refine ⟨8780594586903096910908497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93659675593633033716357301 8780594586903096910908497)
            ·
              refine ⟨6585445940177322683181373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8780594586903096910908497 6585445940177322683181373)
              ·
                refine ⟨2469542227566496006193015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6585445940177322683181373 2469542227566496006193015)
                ·
                  refine ⟨3704313341349744009289523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2469542227566496006193015 3704313341349744009289523)
                  ·
                    refine ⟨5556470012024616013934285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3704313341349744009289523 5556470012024616013934285)
                    ·
                      refine ⟨2083676254509231005225357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5556470012024616013934285 2083676254509231005225357)
                      ·
                        rfl

theorem cell23_4057945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 1, 1, 3].length) (baseStart_4057945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057945 prefixEnd_4057945 := by exact prefixLift 4057945
  have htrace : WordTrace (prefixWord ++ tailWord_4057945) baseStart_4057945 baseEnd_4057945 := by
    simpa [prefixWord, tailWord_4057945, baseEnd_4057945] using wordTrace_append hprefix tailTrace_4057945
  have hstable : (prefixWord ++ tailWord_4057945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057945).length < 2 ^ (prefixWord ++ tailWord_4057945).sum := by decide
  have hdescent : baseEnd_4057945 < baseStart_4057945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057948 : List Nat := [2, 2, 4, 2, 1, 2, 1, 3, 1, 5]
def baseStart_4057948 : Nat := 118140960795 + 4057948 * 2 ^ 59
def prefixEnd_4057948 : Nat := 4983230072969 + 3 ^ 40 * 4057948 * 2
def baseEnd_4057948 : Nat := 694559264983731497829281

theorem tailTrace_4057948 : CollatzResearch.WordTrace tailWord_4057948 prefixEnd_4057948 694559264983731497829281 := by
  unfold tailWord_4057948
  simp only [CollatzResearch.WordTrace]
  refine ⟨74002761351377456593795249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98670348468503275458393665 74002761351377456593795249)
  ·
    refine ⟨55502071013533092445346437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74002761351377456593795249 55502071013533092445346437)
    ·
      refine ⟨10406638315037454833502457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55502071013533092445346437 10406638315037454833502457)
      ·
        refine ⟨7804978736278091125126843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10406638315037454833502457 7804978736278091125126843)
        ·
          refine ⟨11707468104417136687690265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7804978736278091125126843 11707468104417136687690265)
          ·
            refine ⟨8780601078312852515767699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11707468104417136687690265 8780601078312852515767699)
            ·
              refine ⟨13170901617469278773651549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8780601078312852515767699 13170901617469278773651549)
              ·
                refine ⟨4939088106550979540119331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13170901617469278773651549 4939088106550979540119331)
                ·
                  refine ⟨7408632159826469310178997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4939088106550979540119331 7408632159826469310178997)
                  ·
                    refine ⟨694559264983731497829281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7408632159826469310178997 694559264983731497829281)
                    ·
                      rfl

theorem cell23_4057948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_4057948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057948 prefixEnd_4057948 := by exact prefixLift 4057948
  have htrace : WordTrace (prefixWord ++ tailWord_4057948) baseStart_4057948 baseEnd_4057948 := by
    simpa [prefixWord, tailWord_4057948, baseEnd_4057948] using wordTrace_append hprefix tailTrace_4057948
  have hstable : (prefixWord ++ tailWord_4057948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057948).length < 2 ^ (prefixWord ++ tailWord_4057948).sum := by decide
  have hdescent : baseEnd_4057948 < baseStart_4057948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057951 : List Nat := [1, 1, 2, 3, 1, 3, 3, 3, 1, 1, 4]
def baseStart_4057951 : Nat := 118140960795 + 4057951 * 2 ^ 59
def prefixEnd_4057951 : Nat := 4983230072969 + 3 ^ 40 * 4057951 * 2
def baseEnd_4057951 : Nat := 2083679335393157981750329

theorem tailTrace_4057951 : CollatzResearch.WordTrace tailWord_4057951 prefixEnd_4057951 2083679335393157981750329 := by
  unfold tailWord_4057951
  simp only [CollatzResearch.WordTrace]
  refine ⟨148005632121744044699949707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98670421414496029799966471 148005632121744044699949707)
  ·
    refine ⟨222008448182616067049924561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148005632121744044699949707 222008448182616067049924561)
    ·
      refine ⟨166506336136962050287443421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222008448182616067049924561 166506336136962050287443421)
      ·
        refine ⟨62439876051360768857791283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166506336136962050287443421 62439876051360768857791283)
        ·
          refine ⟨93659814077041153286686925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62439876051360768857791283 93659814077041153286686925)
          ·
            refine ⟨35122430278890432482507597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93659814077041153286686925 35122430278890432482507597)
            ·
              refine ⟨13170911354583912180940349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35122430278890432482507597 13170911354583912180940349)
              ·
                refine ⟨4939091757968967067852631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13170911354583912180940349 4939091757968967067852631)
                ·
                  refine ⟨7408637636953450601778947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4939091757968967067852631 7408637636953450601778947)
                  ·
                    refine ⟨11112956455430175902668421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7408637636953450601778947 11112956455430175902668421)
                    ·
                      refine ⟨2083679335393157981750329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11112956455430175902668421 2083679335393157981750329)
                      ·
                        rfl

theorem cell23_4057951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_4057951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057951 prefixEnd_4057951 := by exact prefixLift 4057951
  have htrace : WordTrace (prefixWord ++ tailWord_4057951) baseStart_4057951 baseEnd_4057951 := by
    simpa [prefixWord, tailWord_4057951, baseEnd_4057951] using wordTrace_append hprefix tailTrace_4057951
  have hstable : (prefixWord ++ tailWord_4057951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057951).length < 2 ^ (prefixWord ++ tailWord_4057951).sum := by decide
  have hdescent : baseEnd_4057951 < baseStart_4057951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057964 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 6]
def baseStart_4057964 : Nat := 118140960795 + 4057964 * 2 ^ 59
def prefixEnd_4057964 : Nat := 4983230072969 + 3 ^ 40 * 4057964 * 2
def baseEnd_4057964 : Nat := 2083686010641666430887769

theorem tailTrace_4057964 : CollatzResearch.WordTrace tailWord_4057964 prefixEnd_4057964 2083686010641666430887769 := by
  unfold tailWord_4057964
  simp only [CollatzResearch.WordTrace]
  refine ⟨74003053135348473960086473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98670737513797965280115297 74003053135348473960086473)
  ·
    refine ⟨55502289851511355470064855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74003053135348473960086473 55502289851511355470064855)
    ·
      refine ⟨83253434777267033205097283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55502289851511355470064855 83253434777267033205097283)
      ·
        refine ⟨124880152165900549807645925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83253434777267033205097283 124880152165900549807645925)
        ·
          refine ⟨23415028531106353088933611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124880152165900549807645925 23415028531106353088933611)
          ·
            refine ⟨35122542796659529633400417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23415028531106353088933611 35122542796659529633400417)
            ·
              refine ⟨26341907097494647225050313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35122542796659529633400417 26341907097494647225050313)
              ·
                refine ⟨19756430323120985418787735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26341907097494647225050313 19756430323120985418787735)
                ·
                  refine ⟨29634645484681478128181603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19756430323120985418787735 29634645484681478128181603)
                  ·
                    refine ⟨44451968227022217192272405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29634645484681478128181603 44451968227022217192272405)
                    ·
                      refine ⟨2083686010641666430887769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44451968227022217192272405 2083686010641666430887769)
                      ·
                        rfl

theorem cell23_4057964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_4057964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057964 prefixEnd_4057964 := by exact prefixLift 4057964
  have htrace : WordTrace (prefixWord ++ tailWord_4057964) baseStart_4057964 baseEnd_4057964 := by
    simpa [prefixWord, tailWord_4057964, baseEnd_4057964] using wordTrace_append hprefix tailTrace_4057964
  have hstable : (prefixWord ++ tailWord_4057964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057964).length < 2 ^ (prefixWord ++ tailWord_4057964).sum := by decide
  have hdescent : baseEnd_4057964 < baseStart_4057964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057968 : List Nat := [2, 1, 1, 1, 4, 1, 3, 3, 3, 2, 2]
def baseStart_4057968 : Nat := 118140960795 + 4057968 * 2 ^ 59
def prefixEnd_4057968 : Nat := 4983230072969 + 3 ^ 40 * 4057968 * 2
def baseEnd_4057968 : Nat := 2083688064564284415237751

theorem tailTrace_4057968 : CollatzResearch.WordTrace tailWord_4057968 prefixEnd_4057968 2083688064564284415237751 := by
  unfold tailWord_4057968
  simp only [CollatzResearch.WordTrace]
  refine ⟨74003126081341228301659279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98670834775121637735545705 74003126081341228301659279)
  ·
    refine ⟨111004689122011842452488919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74003126081341228301659279 111004689122011842452488919)
    ·
      refine ⟨166507033683017763678733379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111004689122011842452488919 166507033683017763678733379)
      ·
        refine ⟨249760550524526645518100069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166507033683017763678733379 249760550524526645518100069)
        ·
          refine ⟨46830103223348746034643763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249760550524526645518100069 46830103223348746034643763)
          ·
            refine ⟨70245154835023119051965645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46830103223348746034643763 70245154835023119051965645)
            ·
              refine ⟨26341933063133669644487117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70245154835023119051965645 26341933063133669644487117)
              ·
                refine ⟨9878224898675126116682669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26341933063133669644487117 9878224898675126116682669)
                ·
                  refine ⟨3704334337003172293756001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9878224898675126116682669 3704334337003172293756001)
                  ·
                    refine ⟨2778250752752379220317001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3704334337003172293756001 2778250752752379220317001)
                    ·
                      refine ⟨2083688064564284415237751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2778250752752379220317001 2083688064564284415237751)
                      ·
                        rfl

theorem cell23_4057968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 3, 2, 2].length) (baseStart_4057968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057968 prefixEnd_4057968 := by exact prefixLift 4057968
  have htrace : WordTrace (prefixWord ++ tailWord_4057968) baseStart_4057968 baseEnd_4057968 := by
    simpa [prefixWord, tailWord_4057968, baseEnd_4057968] using wordTrace_append hprefix tailTrace_4057968
  have hstable : (prefixWord ++ tailWord_4057968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057968).length < 2 ^ (prefixWord ++ tailWord_4057968).sum := by decide
  have hdescent : baseEnd_4057968 < baseStart_4057968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057981 : List Nat := [1, 4, 1, 1, 2, 1, 5, 1, 1, 2, 4]
def baseStart_4057981 : Nat := 118140960795 + 4057981 * 2 ^ 59
def prefixEnd_4057981 : Nat := 4983230072969 + 3 ^ 40 * 4057981 * 2
def baseEnd_4057981 : Nat := 2083694739812792864375191

theorem tailTrace_4057981 : CollatzResearch.WordTrace tailWord_4057981 prefixEnd_4057981 2083694739812792864375191 := by
  unfold tailWord_4057981
  simp only [CollatzResearch.WordTrace]
  refine ⟨148006726311635359823541797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98671150874423573215694531 148006726311635359823541797)
  ·
    refine ⟨27751261183431629966914087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148006726311635359823541797 27751261183431629966914087)
    ·
      refine ⟨41626891775147444950371131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27751261183431629966914087 41626891775147444950371131)
      ·
        refine ⟨62440337662721167425556697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41626891775147444950371131 62440337662721167425556697)
        ·
          refine ⟨46830253247040875569167523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62440337662721167425556697 46830253247040875569167523)
          ·
            refine ⟨70245379870561313353751285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46830253247040875569167523 70245379870561313353751285)
            ·
              refine ⟨6585504362865123126914183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70245379870561313353751285 6585504362865123126914183)
              ·
                refine ⟨9878256544297684690371275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6585504362865123126914183 9878256544297684690371275)
                ·
                  refine ⟨14817384816446527035556913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9878256544297684690371275 14817384816446527035556913)
                  ·
                    refine ⟨11113038612334895276667685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14817384816446527035556913 11113038612334895276667685)
                    ·
                      refine ⟨2083694739812792864375191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11113038612334895276667685 2083694739812792864375191)
                      ·
                        rfl

theorem cell23_4057981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_4057981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057981 prefixEnd_4057981 := by exact prefixLift 4057981
  have htrace : WordTrace (prefixWord ++ tailWord_4057981) baseStart_4057981 baseEnd_4057981 := by
    simpa [prefixWord, tailWord_4057981, baseEnd_4057981] using wordTrace_append hprefix tailTrace_4057981
  have hstable : (prefixWord ++ tailWord_4057981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057981).length < 2 ^ (prefixWord ++ tailWord_4057981).sum := by decide
  have hdescent : baseEnd_4057981 < baseStart_4057981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057991 : List Nat := [1, 1, 4, 2, 3, 1, 4, 7]
def baseStart_4057991 : Nat := 118140960795 + 4057991 * 2 ^ 59
def prefixEnd_4057991 : Nat := 4983230072969 + 3 ^ 40 * 4057991 * 2
def baseEnd_4057991 : Nat := 77174069430345845379635

theorem tailTrace_4057991 : CollatzResearch.WordTrace tailWord_4057991 prefixEnd_4057991 77174069430345845379635 := by
  unfold tailWord_4057991
  simp only [CollatzResearch.WordTrace]
  refine ⟨148007091041599131531405827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98671394027732754354270551 148007091041599131531405827)
  ·
    refine ⟨222010636562398697297108741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148007091041599131531405827 222010636562398697297108741)
    ·
      refine ⟨41626994355449755743207889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222010636562398697297108741 41626994355449755743207889)
      ·
        refine ⟨31220245766587316807405917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41626994355449755743207889 31220245766587316807405917)
        ·
          refine ⟨11707592162470243802777219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31220245766587316807405917 11707592162470243802777219)
          ·
            refine ⟨17561388243705365704165829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11707592162470243802777219 17561388243705365704165829)
            ·
              refine ⟨3292760295694756069531093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17561388243705365704165829 3292760295694756069531093)
              ·
                refine ⟨77174069430345845379635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3292760295694756069531093 77174069430345845379635)
                ·
                  rfl

theorem cell23_4057991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 7].length) (baseStart_4057991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4057991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4057991 prefixEnd_4057991 := by exact prefixLift 4057991
  have htrace : WordTrace (prefixWord ++ tailWord_4057991) baseStart_4057991 baseEnd_4057991 := by
    simpa [prefixWord, tailWord_4057991, baseEnd_4057991] using wordTrace_append hprefix tailTrace_4057991
  have hstable : (prefixWord ++ tailWord_4057991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057991).length < 2 ^ (prefixWord ++ tailWord_4057991).sum := by decide
  have hdescent : baseEnd_4057991 < baseStart_4057991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058029 : List Nat := [1, 5, 2, 3, 1, 2, 2, 1, 2, 4]
def baseStart_4058029 : Nat := 118140960795 + 4058029 * 2 ^ 59
def prefixEnd_4058029 : Nat := 4983230072969 + 3 ^ 40 * 4058029 * 2
def baseEnd_4058029 : Nat := 694573128961402892191657

theorem tailTrace_4058029 : CollatzResearch.WordTrace tailWord_4058029 prefixEnd_4058029 694573128961402892191657 := by
  unfold tailWord_4058029
  simp only [CollatzResearch.WordTrace]
  refine ⟨148008477015461464021289141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98672318010307642680859427 148008477015461464021289141)
  ·
    refine ⟨13875794720199512251995857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148008477015461464021289141 13875794720199512251995857)
    ·
      refine ⟨10406846040149634188996893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13875794720199512251995857 10406846040149634188996893)
      ·
        refine ⟨3902567265056112820873835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10406846040149634188996893 3902567265056112820873835)
        ·
          refine ⟨5853850897584169231310753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3902567265056112820873835 5853850897584169231310753)
          ·
            refine ⟨4390388173188126923483065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5853850897584169231310753 4390388173188126923483065)
            ·
              refine ⟨3292791129891095192612299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4390388173188126923483065 3292791129891095192612299)
              ·
                refine ⟨4939186694836642788918449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3292791129891095192612299 4939186694836642788918449)
                ·
                  refine ⟨3704390021127482091688837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4939186694836642788918449 3704390021127482091688837)
                  ·
                    refine ⟨694573128961402892191657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3704390021127482091688837 694573128961402892191657)
                    ·
                      rfl

theorem cell23_4058029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_4058029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058029 prefixEnd_4058029 := by exact prefixLift 4058029
  have htrace : WordTrace (prefixWord ++ tailWord_4058029) baseStart_4058029 baseEnd_4058029 := by
    simpa [prefixWord, tailWord_4058029, baseEnd_4058029] using wordTrace_append hprefix tailTrace_4058029
  have hstable : (prefixWord ++ tailWord_4058029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058029).length < 2 ^ (prefixWord ++ tailWord_4058029).sum := by decide
  have hdescent : baseEnd_4058029 < baseStart_4058029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058045 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 3, 3, 2]
def baseStart_4058045 : Nat := 118140960795 + 4058045 * 2 ^ 59
def prefixEnd_4058045 : Nat := 4983230072969 + 3 ^ 40 * 4058045 * 2
def baseEnd_4058045 : Nat := 2083727602574680613974897

theorem tailTrace_4058045 : CollatzResearch.WordTrace tailWord_4058045 prefixEnd_4058045 2083727602574680613974897 := by
  unfold tailWord_4058045
  simp only [CollatzResearch.WordTrace]
  refine ⟨148009060583403498753871589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98672707055602332502581059 148009060583403498753871589)
  ·
    refine ⟨27751698859388156016350923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148009060583403498753871589 27751698859388156016350923)
    ·
      refine ⟨41627548289082234024526385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27751698859388156016350923 41627548289082234024526385)
      ·
        refine ⟨31220661216811675518394789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41627548289082234024526385 31220661216811675518394789)
        ·
          refine ⟨5853873978152189159699023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31220661216811675518394789 5853873978152189159699023)
          ·
            refine ⟨8780810967228283739548535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5853873978152189159699023 8780810967228283739548535)
            ·
              refine ⟨13171216450842425609322803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8780810967228283739548535 13171216450842425609322803)
              ·
                refine ⟨19756824676263638413984205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13171216450842425609322803 19756824676263638413984205)
                ·
                  refine ⟨7408809253598864405244077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19756824676263638413984205 7408809253598864405244077)
                  ·
                    refine ⟨2778303470099574151966529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7408809253598864405244077 2778303470099574151966529)
                    ·
                      refine ⟨2083727602574680613974897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2778303470099574151966529 2083727602574680613974897)
                      ·
                        rfl

theorem cell23_4058045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_4058045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058045 prefixEnd_4058045 := by exact prefixLift 4058045
  have htrace : WordTrace (prefixWord ++ tailWord_4058045) baseStart_4058045 baseEnd_4058045 := by
    simpa [prefixWord, tailWord_4058045, baseEnd_4058045] using wordTrace_append hprefix tailTrace_4058045
  have hstable : (prefixWord ++ tailWord_4058045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058045).length < 2 ^ (prefixWord ++ tailWord_4058045).sum := by decide
  have hdescent : baseEnd_4058045 < baseStart_4058045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058062 : List Nat := [4, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2]
def baseStart_4058062 : Nat := 118140960795 + 4058062 * 2 ^ 59
def prefixEnd_4058062 : Nat := 4983230072969 + 3 ^ 40 * 4058062 * 2
def baseEnd_4058062 : Nat := 2083736331745807047462319

theorem tailTrace_4058062 : CollatzResearch.WordTrace tailWord_4058062 prefixEnd_4058062 2083736331745807047462319 := by
  unfold tailWord_4058062
  simp only [CollatzResearch.WordTrace]
  refine ⟨18501210078042738832155055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98673120416227940438160293 18501210078042738832155055)
  ·
    refine ⟨27751815117064108248232583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18501210078042738832155055 27751815117064108248232583)
    ·
      refine ⟨41627722675596162372348875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27751815117064108248232583 41627722675596162372348875)
      ·
        refine ⟨62441584013394243558523313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41627722675596162372348875 62441584013394243558523313)
        ·
          refine ⟨46831188010045682668892485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62441584013394243558523313 46831188010045682668892485)
          ·
            refine ⟨8780847751883565500417341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46831188010045682668892485 8780847751883565500417341)
            ·
              refine ⟨3292817906956337062656503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8780847751883565500417341 3292817906956337062656503)
              ·
                refine ⟨4939226860434505593984755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3292817906956337062656503 4939226860434505593984755)
                ·
                  refine ⟨7408840290651758390977133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4939226860434505593984755 7408840290651758390977133)
                  ·
                    refine ⟨2778315108994409396616425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7408840290651758390977133 2778315108994409396616425)
                    ·
                      refine ⟨2083736331745807047462319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2778315108994409396616425 2083736331745807047462319)
                      ·
                        rfl

theorem cell23_4058062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_4058062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058062 prefixEnd_4058062 := by exact prefixLift 4058062
  have htrace : WordTrace (prefixWord ++ tailWord_4058062) baseStart_4058062 baseEnd_4058062 := by
    simpa [prefixWord, tailWord_4058062, baseEnd_4058062] using wordTrace_append hprefix tailTrace_4058062
  have hstable : (prefixWord ++ tailWord_4058062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058062).length < 2 ^ (prefixWord ++ tailWord_4058062).sum := by decide
  have hdescent : baseEnd_4058062 < baseStart_4058062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058131 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 4]
def baseStart_4058131 : Nat := 118140960795 + 4058131 * 2 ^ 59
def prefixEnd_4058131 : Nat := 4983230072969 + 3 ^ 40 * 4058131 * 2
def baseEnd_4058131 : Nat := 2083771761910967277499501

theorem tailTrace_4058131 : CollatzResearch.WordTrace tailWord_4058131 prefixEnd_4058131 2083771761910967277499501 := by
  unfold tailWord_4058131
  simp only [CollatzResearch.WordTrace]
  refine ⟨148012197261091935441502247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98674798174061290294334831 148012197261091935441502247)
  ·
    refine ⟨222018295891637903162253371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148012197261091935441502247 222018295891637903162253371)
    ·
      refine ⟨333027443837456854743380057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222018295891637903162253371 333027443837456854743380057)
      ·
        refine ⟨249770582878092641057535043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333027443837456854743380057 249770582878092641057535043)
        ·
          refine ⟨374655874317138961586302565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249770582878092641057535043 374655874317138961586302565)
          ·
            refine ⟨70247976434463555297431731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 374655874317138961586302565 70247976434463555297431731)
            ·
              refine ⟨105371964651695332946147597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70247976434463555297431731 105371964651695332946147597)
              ·
                refine ⟨39514486744385749854805349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105371964651695332946147597 39514486744385749854805349)
                ·
                  refine ⟨7408966264572328097776003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39514486744385749854805349 7408966264572328097776003)
                  ·
                    refine ⟨11113449396858492146664005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7408966264572328097776003 11113449396858492146664005)
                    ·
                      refine ⟨2083771761910967277499501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11113449396858492146664005 2083771761910967277499501)
                      ·
                        rfl

theorem cell23_4058131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 4].length) (baseStart_4058131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058131 prefixEnd_4058131 := by exact prefixLift 4058131
  have htrace : WordTrace (prefixWord ++ tailWord_4058131) baseStart_4058131 baseEnd_4058131 := by
    simpa [prefixWord, tailWord_4058131, baseEnd_4058131] using wordTrace_append hprefix tailTrace_4058131
  have hstable : (prefixWord ++ tailWord_4058131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058131).length < 2 ^ (prefixWord ++ tailWord_4058131).sum := by decide
  have hdescent : baseEnd_4058131 < baseStart_4058131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058148 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 1, 3, 4]
def baseStart_4058148 : Nat := 118140960795 + 4058148 * 2 ^ 59
def prefixEnd_4058148 : Nat := 4983230072969 + 3 ^ 40 * 4058148 * 2
def baseEnd_4058148 : Nat := 2083780491082093710986923

theorem tailTrace_4058148 : CollatzResearch.WordTrace tailWord_4058148 prefixEnd_4058148 2083780491082093710986923 := by
  unfold tailWord_4058148
  simp only [CollatzResearch.WordTrace]
  refine ⟨74006408651015173672435549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98675211534686898229914065 74006408651015173672435549)
  ·
    refine ⟨27752403244130690127163331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74006408651015173672435549 27752403244130690127163331)
    ·
      refine ⟨41628604866196035190744997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27752403244130690127163331 41628604866196035190744997)
      ·
        refine ⟨7805363412411756598264687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41628604866196035190744997 7805363412411756598264687)
        ·
          refine ⟨11708045118617634897397031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7805363412411756598264687 11708045118617634897397031)
          ·
            refine ⟨17562067677926452346095547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11708045118617634897397031 17562067677926452346095547)
            ·
              refine ⟨26343101516889678519143321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17562067677926452346095547 26343101516889678519143321)
              ·
                refine ⟨19757326137667258889357491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26343101516889678519143321 19757326137667258889357491)
                ·
                  refine ⟨29635989206500888334036237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19757326137667258889357491 29635989206500888334036237)
                  ·
                    refine ⟨11113495952437833125263589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29635989206500888334036237 11113495952437833125263589)
                    ·
                      refine ⟨2083780491082093710986923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11113495952437833125263589 2083780491082093710986923)
                      ·
                        rfl

theorem cell23_4058148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_4058148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058148 prefixEnd_4058148 := by exact prefixLift 4058148
  have htrace : WordTrace (prefixWord ++ tailWord_4058148) baseStart_4058148 baseEnd_4058148 := by
    simpa [prefixWord, tailWord_4058148, baseEnd_4058148] using wordTrace_append hprefix tailTrace_4058148
  have hstable : (prefixWord ++ tailWord_4058148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058148).length < 2 ^ (prefixWord ++ tailWord_4058148).sum := by decide
  have hdescent : baseEnd_4058148 < baseStart_4058148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058161 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 2, 4, 4]
def baseStart_4058161 : Nat := 118140960795 + 4058161 * 2 ^ 59
def prefixEnd_4058161 : Nat := 4983230072969 + 3 ^ 40 * 4058161 * 2
def baseEnd_4058161 : Nat := 2083787166330602160124363

theorem tailTrace_4058161 : CollatzResearch.WordTrace tailWord_4058161 prefixEnd_4058161 2083787166330602160124363 := by
  unfold tailWord_4058161
  simp only [CollatzResearch.WordTrace]
  refine ⟨148013291450983250565094337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98675527633988833710062891 148013291450983250565094337)
  ·
    refine ⟨111009968588237437923820753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148013291450983250565094337 111009968588237437923820753)
    ·
      refine ⟨83257476441178078442865565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111009968588237437923820753 83257476441178078442865565)
      ·
        refine ⟨31221553665441779416074587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83257476441178078442865565 31221553665441779416074587)
        ·
          refine ⟨46832330498162669124111881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31221553665441779416074587 46832330498162669124111881)
          ·
            refine ⟨35124247873622001843083911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46832330498162669124111881 35124247873622001843083911)
            ·
              refine ⟨52686371810433002764625867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35124247873622001843083911 52686371810433002764625867)
              ·
                refine ⟨79029557715649504146938801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52686371810433002764625867 79029557715649504146938801)
                ·
                  refine ⟨59272168286737128110204101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79029557715649504146938801 59272168286737128110204101)
                  ·
                    refine ⟨11113531553763211520663269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59272168286737128110204101 11113531553763211520663269)
                    ·
                      refine ⟨2083787166330602160124363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11113531553763211520663269 2083787166330602160124363)
                      ·
                        rfl

theorem cell23_4058161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_4058161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058161 prefixEnd_4058161 := by exact prefixLift 4058161
  have htrace : WordTrace (prefixWord ++ tailWord_4058161) baseStart_4058161 baseEnd_4058161 := by
    simpa [prefixWord, tailWord_4058161, baseEnd_4058161] using wordTrace_append hprefix tailTrace_4058161
  have hstable : (prefixWord ++ tailWord_4058161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058161).length < 2 ^ (prefixWord ++ tailWord_4058161).sum := by decide
  have hdescent : baseEnd_4058161 < baseStart_4058161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058168 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 1, 4, 3]
def baseStart_4058168 : Nat := 118140960795 + 4058168 * 2 ^ 59
def prefixEnd_4058168 : Nat := 4983230072969 + 3 ^ 40 * 4058168 * 2
def baseEnd_4058168 : Nat := 2083790760695183632736831

theorem tailTrace_4058168 : CollatzResearch.WordTrace tailWord_4058168 prefixEnd_4058168 2083790760695183632736831 := by
  unfold tailWord_4058168
  simp only [CollatzResearch.WordTrace]
  refine ⟨74006773380978945380299579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98675697841305260507066105 74006773380978945380299579)
  ·
    refine ⟨111010160071468418070449369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74006773380978945380299579 111010160071468418070449369)
    ·
      refine ⟨83257620053601313552837027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111010160071468418070449369 83257620053601313552837027)
      ·
        refine ⟨124886430080401970329255541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83257620053601313552837027 124886430080401970329255541)
        ·
          refine ⟨11708102820037684718367707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124886430080401970329255541 11708102820037684718367707)
          ·
            refine ⟨17562154230056527077551561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11708102820037684718367707 17562154230056527077551561)
            ·
              refine ⟨13171615672542395308163671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17562154230056527077551561 13171615672542395308163671)
              ·
                refine ⟨19757423508813592962245507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13171615672542395308163671 19757423508813592962245507)
                ·
                  refine ⟨29636135263220389443368261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19757423508813592962245507 29636135263220389443368261)
                  ·
                    refine ⟨5556775361853823020631549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29636135263220389443368261 5556775361853823020631549)
                    ·
                      refine ⟨2083790760695183632736831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5556775361853823020631549 2083790760695183632736831)
                      ·
                        rfl

theorem cell23_4058168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 1, 4, 3].length) (baseStart_4058168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058168 prefixEnd_4058168 := by exact prefixLift 4058168
  have htrace : WordTrace (prefixWord ++ tailWord_4058168) baseStart_4058168 baseEnd_4058168 := by
    simpa [prefixWord, tailWord_4058168, baseEnd_4058168] using wordTrace_append hprefix tailTrace_4058168
  have hstable : (prefixWord ++ tailWord_4058168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058168).length < 2 ^ (prefixWord ++ tailWord_4058168).sum := by decide
  have hdescent : baseEnd_4058168 < baseStart_4058168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058182 : List Nat := [6, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_4058182 : Nat := 118140960795 + 4058182 * 2 ^ 59
def prefixEnd_4058182 : Nat := 4983230072969 + 3 ^ 40 * 4058182 * 2
def baseEnd_4058182 : Nat := 2083797949424346577961767

theorem tailTrace_4058182 : CollatzResearch.WordTrace tailWord_4058182 prefixEnd_4058182 2083797949424346577961767 := by
  unfold tailWord_4058182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4625439293247099098487775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98676038255938114101072533 4625439293247099098487775)
  ·
    refine ⟨6938158939870648647731663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4625439293247099098487775 6938158939870648647731663)
    ·
      refine ⟨10407238409805972971597495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6938158939870648647731663 10407238409805972971597495)
      ·
        refine ⟨15610857614708959457396243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10407238409805972971597495 15610857614708959457396243)
        ·
          refine ⟨23416286422063439186094365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15610857614708959457396243 23416286422063439186094365)
          ·
            refine ⟨8781107408273789694785387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23416286422063439186094365 8781107408273789694785387)
            ·
              refine ⟨13171661112410684542178081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8781107408273789694785387 13171661112410684542178081)
              ·
                refine ⟨9878745834308013406633561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13171661112410684542178081 9878745834308013406633561)
                ·
                  refine ⟨7409059375731010054975171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9878745834308013406633561 7409059375731010054975171)
                  ·
                    refine ⟨11113589063596515082462757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7409059375731010054975171 11113589063596515082462757)
                    ·
                      refine ⟨2083797949424346577961767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11113589063596515082462757 2083797949424346577961767)
                      ·
                        rfl

theorem cell23_4058182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_4058182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058182 prefixEnd_4058182 := by exact prefixLift 4058182
  have htrace : WordTrace (prefixWord ++ tailWord_4058182) baseStart_4058182 baseEnd_4058182 := by
    simpa [prefixWord, tailWord_4058182, baseEnd_4058182] using wordTrace_append hprefix tailTrace_4058182
  have hstable : (prefixWord ++ tailWord_4058182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058182).length < 2 ^ (prefixWord ++ tailWord_4058182).sum := by decide
  have hdescent : baseEnd_4058182 < baseStart_4058182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058249 : List Nat := [1, 2, 1, 1, 4, 3, 4, 2, 1, 1, 3]
def baseStart_4058249 : Nat := 118140960795 + 4058249 * 2 ^ 59
def prefixEnd_4058249 : Nat := 4983230072969 + 3 ^ 40 * 4058249 * 2
def baseEnd_4058249 : Nat := 2083832352628197815823959

theorem tailTrace_4058249 : CollatzResearch.WordTrace tailWord_4058249 prefixEnd_4058249 2083832352628197815823959 := by
  unfold tailWord_4058249
  simp only [CollatzResearch.WordTrace]
  refine ⟨148016501074664441594297801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98677667383109627729531867 148016501074664441594297801)
  ·
    refine ⟨111012375805998331195723351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148016501074664441594297801 111012375805998331195723351)
    ·
      refine ⟨166518563708997496793585027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111012375805998331195723351 166518563708997496793585027)
      ·
        refine ⟨249777845563496245190377541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166518563708997496793585027 249777845563496245190377541)
        ·
          refine ⟨46833346043155545973195789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249777845563496245190377541 46833346043155545973195789)
          ·
            refine ⟨17562504766183329739948421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46833346043155545973195789 17562504766183329739948421)
            ·
              refine ⟨3292969643659374326240329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17562504766183329739948421 3292969643659374326240329)
              ·
                refine ⟨2469727232744530744680247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3292969643659374326240329 2469727232744530744680247)
                ·
                  refine ⟨3704590849116796117020371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2469727232744530744680247 3704590849116796117020371)
                  ·
                    refine ⟨5556886273675194175530557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3704590849116796117020371 5556886273675194175530557)
                    ·
                      refine ⟨2083832352628197815823959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5556886273675194175530557 2083832352628197815823959)
                      ·
                        rfl

theorem cell23_4058249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 1, 1, 3].length) (baseStart_4058249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058249 prefixEnd_4058249 := by exact prefixLift 4058249
  have htrace : WordTrace (prefixWord ++ tailWord_4058249) baseStart_4058249 baseEnd_4058249 := by
    simpa [prefixWord, tailWord_4058249, baseEnd_4058249] using wordTrace_append hprefix tailTrace_4058249
  have hstable : (prefixWord ++ tailWord_4058249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058249).length < 2 ^ (prefixWord ++ tailWord_4058249).sum := by decide
  have hdescent : baseEnd_4058249 < baseStart_4058249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058251 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 6]
def baseStart_4058251 : Nat := 118140960795 + 4058251 * 2 ^ 59
def prefixEnd_4058251 : Nat := 4983230072969 + 3 ^ 40 * 4058251 * 2
def baseEnd_4058251 : Nat := 2083833379589506807998949

theorem tailTrace_4058251 : CollatzResearch.WordTrace tailWord_4058251 prefixEnd_4058251 2083833379589506807998949 := by
  unfold tailWord_4058251
  simp only [CollatzResearch.WordTrace]
  refine ⟨148016574020657195935870607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98677716013771463957247071 148016574020657195935870607)
  ·
    refine ⟨222024861030985793903805911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148016574020657195935870607 222024861030985793903805911)
    ·
      refine ⟨333037291546478690855708867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222024861030985793903805911 333037291546478690855708867)
      ·
        refine ⟨499555937319718036283563301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333037291546478690855708867 499555937319718036283563301)
        ·
          refine ⟨93666738247447131803168119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 499555937319718036283563301 93666738247447131803168119)
          ·
            refine ⟨140500107371170697704752179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93666738247447131803168119 140500107371170697704752179)
            ·
              refine ⟨210750161056756046557128269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140500107371170697704752179 210750161056756046557128269)
              ·
                refine ⟨79031310396283517458923101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210750161056756046557128269 79031310396283517458923101)
                ·
                  refine ⟨29636741398606319047096163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79031310396283517458923101 29636741398606319047096163)
                  ·
                    refine ⟨44455112097909478570644245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29636741398606319047096163 44455112097909478570644245)
                    ·
                      refine ⟨2083833379589506807998949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44455112097909478570644245 2083833379589506807998949)
                      ·
                        rfl

theorem cell23_4058251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 6].length) (baseStart_4058251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058251 prefixEnd_4058251 := by exact prefixLift 4058251
  have htrace : WordTrace (prefixWord ++ tailWord_4058251) baseStart_4058251 baseEnd_4058251 := by
    simpa [prefixWord, tailWord_4058251, baseEnd_4058251] using wordTrace_append hprefix tailTrace_4058251
  have hstable : (prefixWord ++ tailWord_4058251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058251).length < 2 ^ (prefixWord ++ tailWord_4058251).sum := by decide
  have hdescent : baseEnd_4058251 < baseStart_4058251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058261 : List Nat := [1, 3, 2, 1, 1, 1, 2, 12]
def baseStart_4058261 : Nat := 118140960795 + 4058261 * 2 ^ 59
def prefixEnd_4058261 : Nat := 4983230072969 + 3 ^ 40 * 4058261 * 2
def baseEnd_4058261 : Nat := 77179204236890806254589

theorem tailTrace_4058261 : CollatzResearch.WordTrace tailWord_4058261 prefixEnd_4058261 77179204236890806254589 := by
  unfold tailWord_4058261
  simp only [CollatzResearch.WordTrace]
  refine ⟨148016938750620967643734637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98677959167080645095823091 148016938750620967643734637)
  ·
    refine ⟨55506352031482862866400489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148016938750620967643734637 55506352031482862866400489)
    ·
      refine ⟨41629764023612147149800367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55506352031482862866400489 41629764023612147149800367)
      ·
        refine ⟨62444646035418220724700551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41629764023612147149800367 62444646035418220724700551)
        ·
          refine ⟨93666969053127331087050827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62444646035418220724700551 93666969053127331087050827)
          ·
            refine ⟨140500453579690996630576241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93666969053127331087050827 140500453579690996630576241)
            ·
              refine ⟨105375340184768247472932181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140500453579690996630576241 105375340184768247472932181)
              ·
                refine ⟨77179204236890806254589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 105375340184768247472932181 77179204236890806254589)
                ·
                  rfl

theorem cell23_4058261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 12].length) (baseStart_4058261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058261 prefixEnd_4058261 := by exact prefixLift 4058261
  have htrace : WordTrace (prefixWord ++ tailWord_4058261) baseStart_4058261 baseEnd_4058261 := by
    simpa [prefixWord, tailWord_4058261, baseEnd_4058261] using wordTrace_append hprefix tailTrace_4058261
  have hstable : (prefixWord ++ tailWord_4058261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058261).length < 2 ^ (prefixWord ++ tailWord_4058261).sum := by decide
  have hdescent : baseEnd_4058261 < baseStart_4058261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058272 : List Nat := [2, 1, 1, 4, 2, 1, 3, 2, 3, 2, 2]
def baseStart_4058272 : Nat := 118140960795 + 4058272 * 2 ^ 59
def prefixEnd_4058272 : Nat := 4983230072969 + 3 ^ 40 * 4058272 * 2
def baseEnd_4058272 : Nat := 2083844162683251225836353

theorem tailTrace_4058272 : CollatzResearch.WordTrace tailWord_4058272 prefixEnd_4058272 2083844162683251225836353 := by
  unfold tailWord_4058272
  simp only [CollatzResearch.WordTrace]
  refine ⟨74008669976790558261192535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98678226635720744348256713 74008669976790558261192535)
  ·
    refine ⟨111013004965185837391788803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74008669976790558261192535 111013004965185837391788803)
    ·
      refine ⟨166519507447778756087683205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111013004965185837391788803 166519507447778756087683205)
      ·
        refine ⟨31222407646458516766440601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166519507447778756087683205 31222407646458516766440601)
        ·
          refine ⟨23416805734843887574830451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31222407646458516766440601 23416805734843887574830451)
          ·
            refine ⟨35125208602265831362245677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23416805734843887574830451 35125208602265831362245677)
            ·
              refine ⟨13171953225849686760842129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35125208602265831362245677 13171953225849686760842129)
              ·
                refine ⟨9878964919387265070631597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13171953225849686760842129 9878964919387265070631597)
                ·
                  refine ⟨3704611844770224401486849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9878964919387265070631597 3704611844770224401486849)
                  ·
                    refine ⟨2778458883577668301115137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3704611844770224401486849 2778458883577668301115137)
                    ·
                      refine ⟨2083844162683251225836353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2778458883577668301115137 2083844162683251225836353)
                      ·
                        rfl

theorem cell23_4058272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_4058272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058272 prefixEnd_4058272 := by exact prefixLift 4058272
  have htrace : WordTrace (prefixWord ++ tailWord_4058272) baseStart_4058272 baseEnd_4058272 := by
    simpa [prefixWord, tailWord_4058272, baseEnd_4058272] using wordTrace_append hprefix tailTrace_4058272
  have hstable : (prefixWord ++ tailWord_4058272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058272).length < 2 ^ (prefixWord ++ tailWord_4058272).sum := by decide
  have hdescent : baseEnd_4058272 < baseStart_4058272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058281 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 3, 4, 6]
def baseStart_4058281 : Nat := 118140960795 + 4058281 * 2 ^ 59
def prefixEnd_4058281 : Nat := 4983230072969 + 3 ^ 40 * 4058281 * 2
def baseEnd_4058281 : Nat := 2083848784009141690623811

theorem tailTrace_4058281 : CollatzResearch.WordTrace tailWord_4058281 prefixEnd_4058281 2083848784009141690623811 := by
  unfold tailWord_4058281
  simp only [CollatzResearch.WordTrace]
  refine ⟨148017668210548511059462697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98678445473699007372975131 148017668210548511059462697)
  ·
    refine ⟨111013251157911383294597023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148017668210548511059462697 111013251157911383294597023)
    ·
      refine ⟨166519876736867074941895535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111013251157911383294597023 166519876736867074941895535)
      ·
        refine ⟨249779815105300612412843303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166519876736867074941895535 249779815105300612412843303)
        ·
          refine ⟨374669722657950918619264955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249779815105300612412843303 374669722657950918619264955)
          ·
            refine ⟨562004583986926377928897433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374669722657950918619264955 562004583986926377928897433)
            ·
              refine ⟨421503437990194783446673075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562004583986926377928897433 421503437990194783446673075)
              ·
                refine ⟨632255156985292175170009613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421503437990194783446673075 632255156985292175170009613)
                ·
                  refine ⟨237095683869484565688753605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632255156985292175170009613 237095683869484565688753605)
                  ·
                    refine ⟨44455440725528356066641301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 237095683869484565688753605 44455440725528356066641301)
                    ·
                      refine ⟨2083848784009141690623811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44455440725528356066641301 2083848784009141690623811)
                      ·
                        rfl

theorem cell23_4058281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_4058281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058281 prefixEnd_4058281 := by exact prefixLift 4058281
  have htrace : WordTrace (prefixWord ++ tailWord_4058281) baseStart_4058281 baseEnd_4058281 := by
    simpa [prefixWord, tailWord_4058281, baseEnd_4058281] using wordTrace_append hprefix tailTrace_4058281
  have hstable : (prefixWord ++ tailWord_4058281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058281).length < 2 ^ (prefixWord ++ tailWord_4058281).sum := by decide
  have hdescent : baseEnd_4058281 < baseStart_4058281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058289 : List Nat := [1, 2, 2, 5, 1, 3, 2, 1, 1, 1, 4]
def baseStart_4058289 : Nat := 118140960795 + 4058289 * 2 ^ 59
def prefixEnd_4058289 : Nat := 4983230072969 + 3 ^ 40 * 4058289 * 2
def baseEnd_4058289 : Nat := 2083852891854377659323775

theorem tailTrace_4058289 : CollatzResearch.WordTrace tailWord_4058289 prefixEnd_4058289 2083852891854377659323775 := by
  unfold tailWord_4058289
  simp only [CollatzResearch.WordTrace]
  refine ⟨148017959994519528425753921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98678639996346352283835947 148017959994519528425753921)
  ·
    refine ⟨111013469995889646319315441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148017959994519528425753921 111013469995889646319315441)
    ·
      refine ⟨83260102496917234739486581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111013469995889646319315441 83260102496917234739486581)
      ·
        refine ⟨7805634609085990756826867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83260102496917234739486581 7805634609085990756826867)
        ·
          refine ⟨11708451913628986135240301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7805634609085990756826867 11708451913628986135240301)
          ·
            refine ⟨4390669467610869800715113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11708451913628986135240301 4390669467610869800715113)
            ·
              refine ⟨3293002100708152350536335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4390669467610869800715113 3293002100708152350536335)
              ·
                refine ⟨4939503151062228525804503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3293002100708152350536335 4939503151062228525804503)
                ·
                  refine ⟨7409254726593342788706755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4939503151062228525804503 7409254726593342788706755)
                  ·
                    refine ⟨11113882089890014183060133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7409254726593342788706755 11113882089890014183060133)
                    ·
                      refine ⟨2083852891854377659323775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11113882089890014183060133 2083852891854377659323775)
                      ·
                        rfl

theorem cell23_4058289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_4058289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058289 prefixEnd_4058289 := by exact prefixLift 4058289
  have htrace : WordTrace (prefixWord ++ tailWord_4058289) baseStart_4058289 baseEnd_4058289 := by
    simpa [prefixWord, tailWord_4058289, baseEnd_4058289] using wordTrace_append hprefix tailTrace_4058289
  have hstable : (prefixWord ++ tailWord_4058289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058289).length < 2 ^ (prefixWord ++ tailWord_4058289).sum := by decide
  have hdescent : baseEnd_4058289 < baseStart_4058289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058315 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 3, 3, 2]
def baseStart_4058315 : Nat := 118140960795 + 4058315 * 2 ^ 59
def prefixEnd_4058315 : Nat := 4983230072969 + 3 ^ 40 * 4058315 * 2
def baseEnd_4058315 : Nat := 2083866242351394557598655

theorem tailTrace_4058315 : CollatzResearch.WordTrace tailWord_4058315 prefixEnd_4058315 2083866242351394557598655 := by
  unfold tailWord_4058315
  simp only [CollatzResearch.WordTrace]
  refine ⟨148018908292425334866200399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98679272194950223244133599 148018908292425334866200399)
  ·
    refine ⟨222028362438638002299300599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148018908292425334866200399 222028362438638002299300599)
    ·
      refine ⟨333042543657957003448950899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222028362438638002299300599 333042543657957003448950899)
      ·
        refine ⟨499563815486935505173426349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333042543657957003448950899 499563815486935505173426349)
        ·
          refine ⟨187336430807600814440034881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 499563815486935505173426349 187336430807600814440034881)
          ·
            refine ⟨140502323105700610830026161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187336430807600814440034881 140502323105700610830026161)
            ·
              refine ⟨105376742329275458122519621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140502323105700610830026161 105376742329275458122519621)
              ·
                refine ⟨19758139186739148397972429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105376742329275458122519621 19758139186739148397972429)
                ·
                  refine ⟨7409302195027180649239661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19758139186739148397972429 7409302195027180649239661)
                  ·
                    refine ⟨2778488323135192743464873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7409302195027180649239661 2778488323135192743464873)
                    ·
                      refine ⟨2083866242351394557598655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2778488323135192743464873 2083866242351394557598655)
                      ·
                        rfl

theorem cell23_4058315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 3, 2].length) (baseStart_4058315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058315 prefixEnd_4058315 := by exact prefixLift 4058315
  have htrace : WordTrace (prefixWord ++ tailWord_4058315) baseStart_4058315 baseEnd_4058315 := by
    simpa [prefixWord, tailWord_4058315, baseEnd_4058315] using wordTrace_append hprefix tailTrace_4058315
  have hstable : (prefixWord ++ tailWord_4058315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058315).length < 2 ^ (prefixWord ++ tailWord_4058315).sum := by decide
  have hdescent : baseEnd_4058315 < baseStart_4058315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058326 : List Nat := [5, 2, 1, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_4058326 : Nat := 118140960795 + 4058326 * 2 ^ 59
def prefixEnd_4058326 : Nat := 4983230072969 + 3 ^ 40 * 4058326 * 2
def baseEnd_4058326 : Nat := 2083871890638594014561105

theorem tailTrace_4058326 : CollatzResearch.WordTrace tailWord_4058326 prefixEnd_4058326 2083871890638594014561105 := by
  unfold tailWord_4058326
  simp only [CollatzResearch.WordTrace]
  refine ⟨9251206843461592734053177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98679539663590322496567221 9251206843461592734053177)
  ·
    refine ⟨6938405132596194550539883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9251206843461592734053177 6938405132596194550539883)
    ·
      refine ⟨10407607698894291825809825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6938405132596194550539883 10407607698894291825809825)
      ·
        refine ⟨7805705774170718869357369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10407607698894291825809825 7805705774170718869357369)
        ·
          refine ⟨5854279330628039152018027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7805705774170718869357369 5854279330628039152018027)
          ·
            refine ⟨8781418995942058728027041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5854279330628039152018027 8781418995942058728027041)
            ·
              refine ⟨6586064246956544046020281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8781418995942058728027041 6586064246956544046020281)
              ·
                refine ⟨4939548185217408034515211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6586064246956544046020281 4939548185217408034515211)
                ·
                  refine ⟨7409322277826112051772817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4939548185217408034515211 7409322277826112051772817)
                  ·
                    refine ⟨5556991708369584038829613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7409322277826112051772817 5556991708369584038829613)
                    ·
                      refine ⟨2083871890638594014561105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5556991708369584038829613 2083871890638594014561105)
                      ·
                        rfl

theorem cell23_4058326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_4058326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058326 prefixEnd_4058326 := by exact prefixLift 4058326
  have htrace : WordTrace (prefixWord ++ tailWord_4058326) baseStart_4058326 baseEnd_4058326 := by
    simpa [prefixWord, tailWord_4058326, baseEnd_4058326] using wordTrace_append hprefix tailTrace_4058326
  have hstable : (prefixWord ++ tailWord_4058326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058326).length < 2 ^ (prefixWord ++ tailWord_4058326).sum := by decide
  have hdescent : baseEnd_4058326 < baseStart_4058326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058348 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 5]
def baseStart_4058348 : Nat := 118140960795 + 4058348 * 2 ^ 59
def prefixEnd_4058348 : Nat := 4983230072969 + 3 ^ 40 * 4058348 * 2
def baseEnd_4058348 : Nat := 2083883187212992928486003

theorem tailTrace_4058348 : CollatzResearch.WordTrace tailWord_4058348 prefixEnd_4058348 2083883187212992928486003 := by
  unfold tailWord_4058348
  simp only [CollatzResearch.WordTrace]
  refine ⟨74010055950652890751075849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98680074600870521001434465 74010055950652890751075849)
  ·
    refine ⟨55507541962989668063306887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74010055950652890751075849 55507541962989668063306887)
    ·
      refine ⟨83261312944484502094960331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55507541962989668063306887 83261312944484502094960331)
      ·
        refine ⟨124891969416726753142440497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83261312944484502094960331 124891969416726753142440497)
        ·
          refine ⟨93668977062545064856830373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124891969416726753142440497 93668977062545064856830373)
          ·
            refine ⟨17562933199227199660655695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93668977062545064856830373 17562933199227199660655695)
            ·
              refine ⟨26344399798840799490983543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17562933199227199660655695 26344399798840799490983543)
              ·
                refine ⟨39516599698261199236475315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26344399798840799490983543 39516599698261199236475315)
                ·
                  refine ⟨59274899547391798854712973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39516599698261199236475315 59274899547391798854712973)
                  ·
                    refine ⟨22228087330271924570517365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59274899547391798854712973 22228087330271924570517365)
                    ·
                      refine ⟨2083883187212992928486003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22228087330271924570517365 2083883187212992928486003)
                      ·
                        rfl

theorem cell23_4058348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_4058348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058348 prefixEnd_4058348 := by exact prefixLift 4058348
  have htrace : WordTrace (prefixWord ++ tailWord_4058348) baseStart_4058348 baseEnd_4058348 := by
    simpa [prefixWord, tailWord_4058348, baseEnd_4058348] using wordTrace_append hprefix tailTrace_4058348
  have hstable : (prefixWord ++ tailWord_4058348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058348).length < 2 ^ (prefixWord ++ tailWord_4058348).sum := by decide
  have hdescent : baseEnd_4058348 < baseStart_4058348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058349 : List Nat := [1, 5, 1, 2, 2, 1, 2, 3, 1, 3, 2]
def baseStart_4058349 : Nat := 118140960795 + 4058349 * 2 ^ 59
def prefixEnd_4058349 : Nat := 4983230072969 + 3 ^ 40 * 4058349 * 2
def baseEnd_4058349 : Nat := 2083883700693647424573499

theorem tailTrace_4058349 : CollatzResearch.WordTrace tailWord_4058349 prefixEnd_4058349 2083883700693647424573499 := by
  unfold tailWord_4058349
  simp only [CollatzResearch.WordTrace]
  refine ⟨148020148374302158672938101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98680098916201439115292067 148020148374302158672938101)
  ·
    refine ⟨13876888910090827375587947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148020148374302158672938101 13876888910090827375587947)
    ·
      refine ⟨20815333365136241063381921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13876888910090827375587947 20815333365136241063381921)
      ·
        refine ⟨15611500023852180797536441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20815333365136241063381921 15611500023852180797536441)
        ·
          refine ⟨11708625017889135598152331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15611500023852180797536441 11708625017889135598152331)
          ·
            refine ⟨17562937526833703397228497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11708625017889135598152331 17562937526833703397228497)
            ·
              refine ⟨13172203145125277547921373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17562937526833703397228497 13172203145125277547921373)
              ·
                refine ⟨4939576179421979080470515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13172203145125277547921373 4939576179421979080470515)
                ·
                  refine ⟨7409364269132968620705773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4939576179421979080470515 7409364269132968620705773)
                  ·
                    refine ⟨2778511600924863232764665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7409364269132968620705773 2778511600924863232764665)
                    ·
                      refine ⟨2083883700693647424573499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2778511600924863232764665 2083883700693647424573499)
                      ·
                        rfl

theorem cell23_4058349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_4058349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058349 prefixEnd_4058349 := by exact prefixLift 4058349
  have htrace : WordTrace (prefixWord ++ tailWord_4058349) baseStart_4058349 baseEnd_4058349 := by
    simpa [prefixWord, tailWord_4058349, baseEnd_4058349] using wordTrace_append hprefix tailTrace_4058349
  have hstable : (prefixWord ++ tailWord_4058349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058349).length < 2 ^ (prefixWord ++ tailWord_4058349).sum := by decide
  have hdescent : baseEnd_4058349 < baseStart_4058349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058362 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2]
def baseStart_4058362 : Nat := 118140960795 + 4058362 * 2 ^ 59
def prefixEnd_4058362 : Nat := 4983230072969 + 3 ^ 40 * 4058362 * 2
def baseEnd_4058362 : Nat := 2083890375942155873710939

theorem tailTrace_4058362 : CollatzResearch.WordTrace tailWord_4058362 prefixEnd_4058362 2083890375942155873710939 := by
  unfold tailWord_4058362
  simp only [CollatzResearch.WordTrace]
  refine ⟨37005155630813765473290335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98680415015503374595440893 37005155630813765473290335)
  ·
    refine ⟨55507733446220648209935503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37005155630813765473290335 55507733446220648209935503)
    ·
      refine ⟨83261600169330972314903255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55507733446220648209935503 83261600169330972314903255)
      ·
        refine ⟨124892400253996458472354883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83261600169330972314903255 124892400253996458472354883)
        ·
          refine ⟨187338600380994687708532325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124892400253996458472354883 187338600380994687708532325)
          ·
            refine ⟨35125987571436503945349811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187338600380994687708532325 35125987571436503945349811)
            ·
              refine ⟨52688981357154755918024717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35125987571436503945349811 52688981357154755918024717)
              ·
                refine ⟨19758368008933033469259269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52688981357154755918024717 19758368008933033469259269)
                ·
                  refine ⟨3704694001674943775486113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19758368008933033469259269 3704694001674943775486113)
                  ·
                    refine ⟨2778520501256207831614585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3704694001674943775486113 2778520501256207831614585)
                    ·
                      refine ⟨2083890375942155873710939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2778520501256207831614585 2083890375942155873710939)
                      ·
                        rfl

theorem cell23_4058362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2].length) (baseStart_4058362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058362 prefixEnd_4058362 := by exact prefixLift 4058362
  have htrace : WordTrace (prefixWord ++ tailWord_4058362) baseStart_4058362 baseEnd_4058362 := by
    simpa [prefixWord, tailWord_4058362, baseEnd_4058362] using wordTrace_append hprefix tailTrace_4058362
  have hstable : (prefixWord ++ tailWord_4058362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058362).length < 2 ^ (prefixWord ++ tailWord_4058362).sum := by decide
  have hdescent : baseEnd_4058362 < baseStart_4058362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058379 : List Nat := [1, 1, 1, 1, 5, 4, 1, 3, 2, 2, 2]
def baseStart_4058379 : Nat := 118140960795 + 4058379 * 2 ^ 59
def prefixEnd_4058379 : Nat := 4983230072969 + 3 ^ 40 * 4058379 * 2
def baseEnd_4058379 : Nat := 2083899105113282307198361

theorem tailTrace_4058379 : CollatzResearch.WordTrace tailWord_4058379 prefixEnd_4058379 2083899105113282307198361 := by
  unfold tailWord_4058379
  simp only [CollatzResearch.WordTrace]
  refine ⟨148021242564193473796530191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98680828376128982531020127 148021242564193473796530191)
  ·
    refine ⟨222031863846290210694795287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148021242564193473796530191 222031863846290210694795287)
    ·
      refine ⟨333047795769435316042192931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222031863846290210694795287 333047795769435316042192931)
      ·
        refine ⟨499571693654152974063289397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333047795769435316042192931 499571693654152974063289397)
        ·
          refine ⟨46834846280076841318433381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 499571693654152974063289397 46834846280076841318433381)
          ·
            refine ⟨8781533677514407747206259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46834846280076841318433381 8781533677514407747206259)
            ·
              refine ⟨13172300516271611620809389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8781533677514407747206259 13172300516271611620809389)
              ·
                refine ⟨4939612693601854357803521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13172300516271611620809389 4939612693601854357803521)
                ·
                  refine ⟨3704709520201390768352641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4939612693601854357803521 3704709520201390768352641)
                  ·
                    refine ⟨2778532140151043076264481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3704709520201390768352641 2778532140151043076264481)
                    ·
                      refine ⟨2083899105113282307198361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2778532140151043076264481 2083899105113282307198361)
                      ·
                        rfl

theorem cell23_4058379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 2, 2].length) (baseStart_4058379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058379 prefixEnd_4058379 := by exact prefixLift 4058379
  have htrace : WordTrace (prefixWord ++ tailWord_4058379) baseStart_4058379 baseEnd_4058379 := by
    simpa [prefixWord, tailWord_4058379, baseEnd_4058379] using wordTrace_append hprefix tailTrace_4058379
  have hstable : (prefixWord ++ tailWord_4058379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058379).length < 2 ^ (prefixWord ++ tailWord_4058379).sum := by decide
  have hdescent : baseEnd_4058379 < baseStart_4058379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058413 : List Nat := [1, 5, 3, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_4058413 : Nat := 118140960795 + 4058413 * 2 ^ 59
def prefixEnd_4058413 : Nat := 4983230072969 + 3 ^ 40 * 4058413 * 2
def baseEnd_4058413 : Nat := 2083916563455535174173205

theorem tailTrace_4058413 : CollatzResearch.WordTrace tailWord_4058413 prefixEnd_4058413 2083916563455535174173205 := by
  unfold tailWord_4058413
  simp only [CollatzResearch.WordTrace]
  refine ⟨148022482646070297603267893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98681655097380198402178595 148022482646070297603267893)
  ·
    refine ⟨13877107748069090400306365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148022482646070297603267893 13877107748069090400306365)
    ·
      refine ⟨5203915405525908900114887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13877107748069090400306365 5203915405525908900114887)
      ·
        refine ⟨7805873108288863350172331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5203915405525908900114887 7805873108288863350172331)
        ·
          refine ⟨11708809662433295025258497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7805873108288863350172331 11708809662433295025258497)
          ·
            refine ⟨8781607246824971268943873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11708809662433295025258497 8781607246824971268943873)
            ·
              refine ⟨6586205435118728451707905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8781607246824971268943873 6586205435118728451707905)
              ·
                refine ⟨4939654076339046338780929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6586205435118728451707905 4939654076339046338780929)
                ·
                  refine ⟨3704740557254284754085697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4939654076339046338780929 3704740557254284754085697)
                  ·
                    refine ⟨2778555417940713565564273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3704740557254284754085697 2778555417940713565564273)
                    ·
                      refine ⟨2083916563455535174173205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2778555417940713565564273 2083916563455535174173205)
                      ·
                        rfl

theorem cell23_4058413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_4058413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058413 prefixEnd_4058413 := by exact prefixLift 4058413
  have htrace : WordTrace (prefixWord ++ tailWord_4058413) baseStart_4058413 baseEnd_4058413 := by
    simpa [prefixWord, tailWord_4058413, baseEnd_4058413] using wordTrace_append hprefix tailTrace_4058413
  have hstable : (prefixWord ++ tailWord_4058413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058413).length < 2 ^ (prefixWord ++ tailWord_4058413).sum := by decide
  have hdescent : baseEnd_4058413 < baseStart_4058413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058419 : List Nat := [1, 1, 1, 2, 5, 4, 2, 2, 5]
def baseStart_4058419 : Nat := 118140960795 + 4058419 * 2 ^ 59
def prefixEnd_4058419 : Nat := 4983230072969 + 3 ^ 40 * 4058419 * 2
def baseEnd_4058419 : Nat := 231546627148829127855353

theorem tailTrace_4058419 : CollatzResearch.WordTrace tailWord_4058419 prefixEnd_4058419 231546627148829127855353 := by
  unfold tailWord_4058419
  simp only [CollatzResearch.WordTrace]
  refine ⟨148022701484048560627986311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98681800989365707085324207 148022701484048560627986311)
  ·
    refine ⟨222034052226072840941979467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148022701484048560627986311 222034052226072840941979467)
    ·
      refine ⟨333051078339109261412969201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222034052226072840941979467 333051078339109261412969201)
      ·
        refine ⟨249788308754331946059726901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333051078339109261412969201 249788308754331946059726901)
        ·
          refine ⟨23417653945718619943099397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249788308754331946059726901 23417653945718619943099397)
          ·
            refine ⟨4390810114822241239331137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23417653945718619943099397 4390810114822241239331137)
            ·
              refine ⟨3293107586116680929498353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4390810114822241239331137 3293107586116680929498353)
              ·
                refine ⟨2469830689587510697123765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3293107586116680929498353 2469830689587510697123765)
                ·
                  refine ⟨231546627148829127855353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2469830689587510697123765 231546627148829127855353)
                  ·
                    rfl

theorem cell23_4058419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 5].length) (baseStart_4058419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058419 prefixEnd_4058419 := by exact prefixLift 4058419
  have htrace : WordTrace (prefixWord ++ tailWord_4058419) baseStart_4058419 baseEnd_4058419 := by
    simpa [prefixWord, tailWord_4058419, baseEnd_4058419] using wordTrace_append hprefix tailTrace_4058419
  have hstable : (prefixWord ++ tailWord_4058419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058419).length < 2 ^ (prefixWord ++ tailWord_4058419).sum := by decide
  have hdescent : baseEnd_4058419 < baseStart_4058419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058429 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 2, 3, 3]
def baseStart_4058429 : Nat := 118140960795 + 4058429 * 2 ^ 59
def prefixEnd_4058429 : Nat := 4983230072969 + 3 ^ 40 * 4058429 * 2
def baseEnd_4058429 : Nat := 2083924779146007111573131

theorem tailTrace_4058429 : CollatzResearch.WordTrace tailWord_4058429 prefixEnd_4058429 2083924779146007111573131 := by
  unfold tailWord_4058429
  simp only [CollatzResearch.WordTrace]
  refine ⟨148023066214012332335850341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98682044142674888223900227 148023066214012332335850341)
  ·
    refine ⟨27754324915127312312971939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148023066214012332335850341 27754324915127312312971939)
    ·
      refine ⟨41631487372690968469457909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27754324915127312312971939 41631487372690968469457909)
      ·
        refine ⟨3902951941189778294011679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41631487372690968469457909 3902951941189778294011679)
        ·
          refine ⟨5854427911784667441017519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3902951941189778294011679 5854427911784667441017519)
          ·
            refine ⟨8781641867677001161526279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5854427911784667441017519 8781641867677001161526279)
            ·
              refine ⟨13172462801515501742289419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8781641867677001161526279 13172462801515501742289419)
              ·
                refine ⟨19758694202273252613434129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13172462801515501742289419 19758694202273252613434129)
                ·
                  refine ⟨14819020651704939460075597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19758694202273252613434129 14819020651704939460075597)
                  ·
                    refine ⟨5557132744389352297528349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14819020651704939460075597 5557132744389352297528349)
                    ·
                      refine ⟨2083924779146007111573131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5557132744389352297528349 2083924779146007111573131)
                      ·
                        rfl

theorem cell23_4058429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_4058429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058429 prefixEnd_4058429 := by exact prefixLift 4058429
  have htrace : WordTrace (prefixWord ++ tailWord_4058429) baseStart_4058429 baseEnd_4058429 := by
    simpa [prefixWord, tailWord_4058429, baseEnd_4058429] using wordTrace_append hprefix tailTrace_4058429
  have hstable : (prefixWord ++ tailWord_4058429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058429).length < 2 ^ (prefixWord ++ tailWord_4058429).sum := by decide
  have hdescent : baseEnd_4058429 < baseStart_4058429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058452 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 1, 6, 2]
def baseStart_4058452 : Nat := 118140960795 + 4058452 * 2 ^ 59
def prefixEnd_4058452 : Nat := 4983230072969 + 3 ^ 40 * 4058452 * 2
def baseEnd_4058452 : Nat := 2083936589201060521585525

theorem tailTrace_4058452 : CollatzResearch.WordTrace tailWord_4058452 prefixEnd_4058452 2083936589201060521585525 := by
  unfold tailWord_4058452
  simp only [CollatzResearch.WordTrace]
  refine ⟨74011952546464503631968805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98682603395286004842625073 74011952546464503631968805)
  ·
    refine ⟨13877241102462094430994151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74011952546464503631968805 13877241102462094430994151)
    ·
      refine ⟨20815861653693141646491227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13877241102462094430994151 20815861653693141646491227)
      ·
        refine ⟨31223792480539712469736841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20815861653693141646491227 31223792480539712469736841)
        ·
          refine ⟨23417844360404784352302631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31223792480539712469736841 23417844360404784352302631)
          ·
            refine ⟨35126766540607176528453947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23417844360404784352302631 35126766540607176528453947)
            ·
              refine ⟨52690149810910764792680921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35126766540607176528453947 52690149810910764792680921)
              ·
                refine ⟨39517612358183073594510691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52690149810910764792680921 39517612358183073594510691)
                ·
                  refine ⟨59276418537274610391766037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39517612358183073594510691 59276418537274610391766037)
                  ·
                    refine ⟨2778582118934747362114033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59276418537274610391766037 2778582118934747362114033)
                    ·
                      refine ⟨2083936589201060521585525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2778582118934747362114033 2083936589201060521585525)
                      ·
                        rfl

theorem cell23_4058452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_4058452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058452 prefixEnd_4058452 := by exact prefixLift 4058452
  have htrace : WordTrace (prefixWord ++ tailWord_4058452) baseStart_4058452 baseEnd_4058452 := by
    simpa [prefixWord, tailWord_4058452, baseEnd_4058452] using wordTrace_append hprefix tailTrace_4058452
  have hstable : (prefixWord ++ tailWord_4058452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058452).length < 2 ^ (prefixWord ++ tailWord_4058452).sum := by decide
  have hdescent : baseEnd_4058452 < baseStart_4058452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058492 : List Nat := [2, 2, 2, 1, 1, 1, 7, 1, 6]
def baseStart_4058492 : Nat := 118140960795 + 4058492 * 2 ^ 59
def prefixEnd_4058492 : Nat := 4983230072969 + 3 ^ 40 * 4058492 * 2
def baseEnd_4058492 : Nat := 231550792047471151676149

theorem tailTrace_4058492 : CollatzResearch.WordTrace tailWord_4058492 prefixEnd_4058492 231550792047471151676149 := by
  unfold tailWord_4058492
  simp only [CollatzResearch.WordTrace]
  refine ⟨74012682006392047047696865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98683576008522729396929153 74012682006392047047696865)
  ·
    refine ⟨55509511504794035285772649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74012682006392047047696865 55509511504794035285772649)
    ·
      refine ⟨41632133628595526464329487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55509511504794035285772649 41632133628595526464329487)
      ·
        refine ⟨62448200442893289696494231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41632133628595526464329487 62448200442893289696494231)
        ·
          refine ⟨93672300664339934544741347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62448200442893289696494231 93672300664339934544741347)
          ·
            refine ⟨140508450996509901817112021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93672300664339934544741347 140508450996509901817112021)
            ·
              refine ⟨3293166820230700823838563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 140508450996509901817112021 3293166820230700823838563)
              ·
                refine ⟨4939750230346051235757845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3293166820230700823838563 4939750230346051235757845)
                ·
                  refine ⟨231550792047471151676149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4939750230346051235757845 231550792047471151676149)
                  ·
                    rfl

theorem cell23_4058492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 6].length) (baseStart_4058492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058492 prefixEnd_4058492 := by exact prefixLift 4058492
  have htrace : WordTrace (prefixWord ++ tailWord_4058492) baseStart_4058492 baseEnd_4058492 := by
    simpa [prefixWord, tailWord_4058492, baseEnd_4058492] using wordTrace_append hprefix tailTrace_4058492
  have hstable : (prefixWord ++ tailWord_4058492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058492).length < 2 ^ (prefixWord ++ tailWord_4058492).sum := by decide
  have hdescent : baseEnd_4058492 < baseStart_4058492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058522 : List Nat := [3, 1, 1, 4, 1, 1, 1, 5, 1, 5]
def baseStart_4058522 : Nat := 118140960795 + 4058522 * 2 ^ 59
def prefixEnd_4058522 : Nat := 4983230072969 + 3 ^ 40 * 4058522 * 2
def baseEnd_4058522 : Nat := 694657510948958415903401

theorem tailTrace_4058522 : CollatzResearch.WordTrace tailWord_4058522 prefixEnd_4058522 694657510948958415903401 := by
  unfold tailWord_4058522
  simp only [CollatzResearch.WordTrace]
  refine ⟨37006614550668852304746455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98684305468450272812657213 37006614550668852304746455)
  ·
    refine ⟨55509921826003278457119683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37006614550668852304746455 55509921826003278457119683)
    ·
      refine ⟨83264882739004917685679525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55509921826003278457119683 83264882739004917685679525)
      ·
        refine ⟨15612165513563422066064911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83264882739004917685679525 15612165513563422066064911)
        ·
          refine ⟨23418248270345133099097367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15612165513563422066064911 23418248270345133099097367)
          ·
            refine ⟨35127372405517699648646051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23418248270345133099097367 35127372405517699648646051)
            ·
              refine ⟨52691058608276549472969077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35127372405517699648646051 52691058608276549472969077)
              ·
                refine ⟨4939786744525926513090851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52691058608276549472969077 4939786744525926513090851)
                ·
                  refine ⟨7409680116788889769636277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4939786744525926513090851 7409680116788889769636277)
                  ·
                    refine ⟨694657510948958415903401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7409680116788889769636277 694657510948958415903401)
                    ·
                      rfl

theorem cell23_4058522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 1, 5].length) (baseStart_4058522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058522 prefixEnd_4058522 := by exact prefixLift 4058522
  have htrace : WordTrace (prefixWord ++ tailWord_4058522) baseStart_4058522 baseEnd_4058522 := by
    simpa [prefixWord, tailWord_4058522, baseEnd_4058522] using wordTrace_append hprefix tailTrace_4058522
  have hstable : (prefixWord ++ tailWord_4058522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058522).length < 2 ^ (prefixWord ++ tailWord_4058522).sum := by decide
  have hdescent : baseEnd_4058522 < baseStart_4058522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058556 : List Nat := [2, 2, 2, 4, 2, 2, 1, 2, 1, 5]
def baseStart_4058556 : Nat := 118140960795 + 4058556 * 2 ^ 59
def prefixEnd_4058556 : Nat := 4983230072969 + 3 ^ 40 * 4058556 * 2
def baseEnd_4058556 : Nat := 694663330396376038228349

theorem tailTrace_4058556 : CollatzResearch.WordTrace tailWord_4058556 prefixEnd_4058556 694663330396376038228349 := by
  unfold tailWord_4058556
  simp only [CollatzResearch.WordTrace]
  refine ⟨74013849142276116512861761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98685132189701488683815681 74013849142276116512861761)
  ·
    refine ⟨55510386856707087384646321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74013849142276116512861761 55510386856707087384646321)
    ·
      refine ⟨41632790142530315538484741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55510386856707087384646321 41632790142530315538484741)
      ·
        refine ⟨7806148151724434163465889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41632790142530315538484741 7806148151724434163465889)
        ·
          refine ⟨5854611113793325622599417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7806148151724434163465889 5854611113793325622599417)
          ·
            refine ⟨4390958335344994216949563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5854611113793325622599417 4390958335344994216949563)
            ·
              refine ⟨6586437503017491325424345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4390958335344994216949563 6586437503017491325424345)
              ·
                refine ⟨4939828127263118494068259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6586437503017491325424345 4939828127263118494068259)
                ·
                  refine ⟨7409742190894677741102389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4939828127263118494068259 7409742190894677741102389)
                  ·
                    refine ⟨694663330396376038228349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7409742190894677741102389 694663330396376038228349)
                    ·
                      rfl

theorem cell23_4058556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_4058556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058556 prefixEnd_4058556 := by exact prefixLift 4058556
  have htrace : WordTrace (prefixWord ++ tailWord_4058556) baseStart_4058556 baseEnd_4058556 := by
    simpa [prefixWord, tailWord_4058556, baseEnd_4058556] using wordTrace_append hprefix tailTrace_4058556
  have hstable : (prefixWord ++ tailWord_4058556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058556).length < 2 ^ (prefixWord ++ tailWord_4058556).sum := by decide
  have hdescent : baseEnd_4058556 < baseStart_4058556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058559 : List Nat := [1, 1, 2, 2, 2, 1, 1, 6, 3, 2, 2]
def baseStart_4058559 : Nat := 118140960795 + 4058559 * 2 ^ 59
def prefixEnd_4058559 : Nat := 4983230072969 + 3 ^ 40 * 4058559 * 2
def baseEnd_4058559 : Nat := 2083991531631091602947533

theorem tailTrace_4058559 : CollatzResearch.WordTrace tailWord_4058559 prefixEnd_4058559 2083991531631091602947533 := by
  unfold tailWord_4058559
  simp only [CollatzResearch.WordTrace]
  refine ⟨148027807703541364538082731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98685205135694243025388487 148027807703541364538082731)
  ·
    refine ⟨222041711555312046807124097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148027807703541364538082731 222041711555312046807124097)
    ·
      refine ⟨166531283666484035105343073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222041711555312046807124097 166531283666484035105343073)
      ·
        refine ⟨124898462749863026329007305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166531283666484035105343073 124898462749863026329007305)
        ·
          refine ⟨93673847062397269746755479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124898462749863026329007305 93673847062397269746755479)
          ·
            refine ⟨140510770593595904620133219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93673847062397269746755479 140510770593595904620133219)
            ·
              refine ⟨210766155890393856930199829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140510770593595904620133219 210766155890393856930199829)
              ·
                refine ⟨9879663557362212043603117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 210766155890393856930199829 9879663557362212043603117)
                ·
                  refine ⟨3704873834010829516351169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9879663557362212043603117 3704873834010829516351169)
                  ·
                    refine ⟨2778655375508122137263377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3704873834010829516351169 2778655375508122137263377)
                    ·
                      refine ⟨2083991531631091602947533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2778655375508122137263377 2083991531631091602947533)
                      ·
                        rfl

theorem cell23_4058559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 2, 2].length) (baseStart_4058559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058559 prefixEnd_4058559 := by exact prefixLift 4058559
  have htrace : WordTrace (prefixWord ++ tailWord_4058559) baseStart_4058559 baseEnd_4058559 := by
    simpa [prefixWord, tailWord_4058559, baseEnd_4058559] using wordTrace_append hprefix tailTrace_4058559
  have hstable : (prefixWord ++ tailWord_4058559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058559).length < 2 ^ (prefixWord ++ tailWord_4058559).sum := by decide
  have hdescent : baseEnd_4058559 < baseStart_4058559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058572 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 3, 2, 4]
def baseStart_4058572 : Nat := 118140960795 + 4058572 * 2 ^ 59
def prefixEnd_4058572 : Nat := 4983230072969 + 3 ^ 40 * 4058572 * 2
def baseEnd_4058572 : Nat := 2083998206879600052084973

theorem tailTrace_4058572 : CollatzResearch.WordTrace tailWord_4058572 prefixEnd_4058572 2083998206879600052084973 := by
  unfold tailWord_4058572
  simp only [CollatzResearch.WordTrace]
  refine ⟨74014140926247133879152985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98685521234996178505537313 74014140926247133879152985)
  ·
    refine ⟨55510605694685350409364739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74014140926247133879152985 55510605694685350409364739)
    ·
      refine ⟨83265908542028025614047109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55510605694685350409364739 83265908542028025614047109)
      ·
        refine ⟨15612357851630254802633833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83265908542028025614047109 15612357851630254802633833)
        ·
          refine ⟨11709268388722691101975375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15612357851630254802633833 11709268388722691101975375)
          ·
            refine ⟨17563902583084036652963063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11709268388722691101975375 17563902583084036652963063)
            ·
              refine ⟨26345853874626054979444595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17563902583084036652963063 26345853874626054979444595)
              ·
                refine ⟨39518780811939082469166893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26345853874626054979444595 39518780811939082469166893)
                ·
                  refine ⟨14819542804477155925937585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39518780811939082469166893 14819542804477155925937585)
                  ·
                    refine ⟨11114657103357866944453189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14819542804477155925937585 11114657103357866944453189)
                    ·
                      refine ⟨2083998206879600052084973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11114657103357866944453189 2083998206879600052084973)
                      ·
                        rfl

theorem cell23_4058572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_4058572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058572 prefixEnd_4058572 := by exact prefixLift 4058572
  have htrace : WordTrace (prefixWord ++ tailWord_4058572) baseStart_4058572 baseEnd_4058572 := by
    simpa [prefixWord, tailWord_4058572, baseEnd_4058572] using wordTrace_append hprefix tailTrace_4058572
  have hstable : (prefixWord ++ tailWord_4058572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058572).length < 2 ^ (prefixWord ++ tailWord_4058572).sum := by decide
  have hdescent : baseEnd_4058572 < baseStart_4058572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058582 : List Nat := [5, 2, 1, 1, 1, 13]
def baseStart_4058582 : Nat := 118140960795 + 4058582 * 2 ^ 59
def prefixEnd_4058582 : Nat := 4983230072969 + 3 ^ 40 * 4058582 * 2
def baseEnd_4058582 : Nat := 8576145439037633798189

theorem tailTrace_4058582 : CollatzResearch.WordTrace tailWord_4058582 prefixEnd_4058582 8576145439037633798189 := by
  unfold tailWord_4058582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9251790411403627466635625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98685764388305359644113333 9251790411403627466635625)
  ·
    refine ⟨6938842808552720599976719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9251790411403627466635625 6938842808552720599976719)
    ·
      refine ⟨10408264212829080899965079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6938842808552720599976719 10408264212829080899965079)
      ·
        refine ⟨15612396319243621349947619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10408264212829080899965079 15612396319243621349947619)
        ·
          refine ⟨23418594478865432024921429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15612396319243621349947619 23418594478865432024921429)
          ·
            refine ⟨8576145439037633798189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 23418594478865432024921429 8576145439037633798189)
            ·
              rfl

theorem cell23_4058582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 13].length) (baseStart_4058582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058582 prefixEnd_4058582 := by exact prefixLift 4058582
  have htrace : WordTrace (prefixWord ++ tailWord_4058582) baseStart_4058582 baseEnd_4058582 := by
    simpa [prefixWord, tailWord_4058582, baseEnd_4058582] using wordTrace_append hprefix tailTrace_4058582
  have hstable : (prefixWord ++ tailWord_4058582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058582).length < 2 ^ (prefixWord ++ tailWord_4058582).sum := by decide
  have hdescent : baseEnd_4058582 < baseStart_4058582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058593 : List Nat := [1, 2, 3, 1, 2, 4, 1, 4, 1, 2, 2]
def baseStart_4058593 : Nat := 118140960795 + 4058593 * 2 ^ 59
def prefixEnd_4058593 : Nat := 4983230072969 + 3 ^ 40 * 4058593 * 2
def baseEnd_4058593 : Nat := 2084008989973344469922377

theorem tailTrace_4058593 : CollatzResearch.WordTrace tailWord_4058593 prefixEnd_4058593 2084008989973344469922377 := by
  unfold tailWord_4058593
  simp only [CollatzResearch.WordTrace]
  refine ⟨148029047785418188344820433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98686031856945458896546955 148029047785418188344820433)
  ·
    refine ⟨111021785839063641258615325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148029047785418188344820433 111021785839063641258615325)
    ·
      refine ⟨41633169689648865471980747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111021785839063641258615325 41633169689648865471980747)
      ·
        refine ⟨62449754534473298207971121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41633169689648865471980747 62449754534473298207971121)
        ·
          refine ⟨46837315900854973655978341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62449754534473298207971121 46837315900854973655978341)
          ·
            refine ⟨8781996731410307560495939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46837315900854973655978341 8781996731410307560495939)
            ·
              refine ⟨13172995097115461340743909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8781996731410307560495939 13172995097115461340743909)
              ·
                refine ⟨2469936580709149001389483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13172995097115461340743909 2469936580709149001389483)
                ·
                  refine ⟨3704904871063723502084225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2469936580709149001389483 3704904871063723502084225)
                  ·
                    refine ⟨2778678653297792626563169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3704904871063723502084225 2778678653297792626563169)
                    ·
                      refine ⟨2084008989973344469922377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2778678653297792626563169 2084008989973344469922377)
                      ·
                        rfl

theorem cell23_4058593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 1, 2, 2].length) (baseStart_4058593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058593 prefixEnd_4058593 := by exact prefixLift 4058593
  have htrace : WordTrace (prefixWord ++ tailWord_4058593) baseStart_4058593 baseEnd_4058593 := by
    simpa [prefixWord, tailWord_4058593, baseEnd_4058593] using wordTrace_append hprefix tailTrace_4058593
  have hstable : (prefixWord ++ tailWord_4058593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058593).length < 2 ^ (prefixWord ++ tailWord_4058593).sum := by decide
  have hdescent : baseEnd_4058593 < baseStart_4058593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058609 : List Nat := [1, 2, 2, 2, 3, 3, 2, 1, 1, 3, 3]
def baseStart_4058609 : Nat := 118140960795 + 4058609 * 2 ^ 59
def prefixEnd_4058609 : Nat := 4983230072969 + 3 ^ 40 * 4058609 * 2
def baseEnd_4058609 : Nat := 2084017205663816407322303

theorem tailTrace_4058609 : CollatzResearch.WordTrace tailWord_4058609 prefixEnd_4058609 2084017205663816407322303 := by
  unfold tailWord_4058609
  simp only [CollatzResearch.WordTrace]
  refine ⟨148029631353360223077402881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98686420902240148718268587 148029631353360223077402881)
  ·
    refine ⟨111022223515020167308052161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148029631353360223077402881 111022223515020167308052161)
    ·
      refine ⟨83266667636265125481039121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111022223515020167308052161 83266667636265125481039121)
      ·
        refine ⟨62450000727198844110779341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83266667636265125481039121 62450000727198844110779341)
        ·
          refine ⟨23418750272699566541542253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62450000727198844110779341 23418750272699566541542253)
          ·
            refine ⟨8782031352262337453078345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23418750272699566541542253 8782031352262337453078345)
            ·
              refine ⟨6586523514196753089808759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8782031352262337453078345 6586523514196753089808759)
              ·
                refine ⟨9879785271295129634713139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6586523514196753089808759 9879785271295129634713139)
                ·
                  refine ⟨14819677906942694452069709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9879785271295129634713139 14819677906942694452069709)
                  ·
                    refine ⟨5557379215103510419526141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14819677906942694452069709 5557379215103510419526141)
                    ·
                      refine ⟨2084017205663816407322303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5557379215103510419526141 2084017205663816407322303)
                      ·
                        rfl

theorem cell23_4058609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_4058609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058609 prefixEnd_4058609 := by exact prefixLift 4058609
  have htrace : WordTrace (prefixWord ++ tailWord_4058609) baseStart_4058609 baseEnd_4058609 := by
    simpa [prefixWord, tailWord_4058609, baseEnd_4058609] using wordTrace_append hprefix tailTrace_4058609
  have hstable : (prefixWord ++ tailWord_4058609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058609).length < 2 ^ (prefixWord ++ tailWord_4058609).sum := by decide
  have hdescent : baseEnd_4058609 < baseStart_4058609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058626 : List Nat := [3, 4, 1, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_4058626 : Nat := 118140960795 + 4058626 * 2 ^ 59
def prefixEnd_4058626 : Nat := 4983230072969 + 3 ^ 40 * 4058626 * 2
def baseEnd_4058626 : Nat := 2084025934834942840809725

theorem tailTrace_4058626 : CollatzResearch.WordTrace tailWord_4058626 prefixEnd_4058626 2084025934834942840809725 := by
  unfold tailWord_4058626
  simp only [CollatzResearch.WordTrace]
  refine ⟨37007562848574658745192933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98686834262865756653847821 37007562848574658745192933)
  ·
    refine ⟨6938918034107748514723675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37007562848574658745192933 6938918034107748514723675)
    ·
      refine ⟨10408377051161622772085513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6938918034107748514723675 10408377051161622772085513)
      ·
        refine ⟨7806282788371217079064135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10408377051161622772085513 7806282788371217079064135)
        ·
          refine ⟨11709424182556825618596203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7806282788371217079064135 11709424182556825618596203)
          ·
            refine ⟨17564136273835238427894305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11709424182556825618596203 17564136273835238427894305)
            ·
              refine ⟨13173102205376428820920729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17564136273835238427894305 13173102205376428820920729)
              ·
                refine ⟨9879826654032321615690547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13173102205376428820920729 9879826654032321615690547)
                ·
                  refine ⟨14819739981048482423535821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9879826654032321615690547 14819739981048482423535821)
                  ·
                    refine ⟨5557402492893180908825933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14819739981048482423535821 5557402492893180908825933)
                    ·
                      refine ⟨2084025934834942840809725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5557402492893180908825933 2084025934834942840809725)
                      ·
                        rfl

theorem cell23_4058626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_4058626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058626 prefixEnd_4058626 := by exact prefixLift 4058626
  have htrace : WordTrace (prefixWord ++ tailWord_4058626) baseStart_4058626 baseEnd_4058626 := by
    simpa [prefixWord, tailWord_4058626, baseEnd_4058626] using wordTrace_append hprefix tailTrace_4058626
  have hstable : (prefixWord ++ tailWord_4058626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058626).length < 2 ^ (prefixWord ++ tailWord_4058626).sum := by decide
  have hdescent : baseEnd_4058626 < baseStart_4058626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058637 : List Nat := [1, 7, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_4058637 : Nat := 118140960795 + 4058637 * 2 ^ 59
def prefixEnd_4058637 : Nat := 4983230072969 + 3 ^ 40 * 4058637 * 2
def baseEnd_4058637 : Nat := 694677194374047432590725

theorem tailTrace_4058637 : CollatzResearch.WordTrace tailWord_4058637 prefixEnd_4058637 694677194374047432590725 := by
  unfold tailWord_4058637
  simp only [CollatzResearch.WordTrace]
  refine ⟨148030652597258783859422165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98687101731505855906281443 148030652597258783859422165)
  ·
    refine ⟨3469468420248252746705207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 148030652597258783859422165 3469468420248252746705207)
    ·
      refine ⟨5204202630372379120057811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3469468420248252746705207 5204202630372379120057811)
      ·
        refine ⟨7806303945558568680086717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5204202630372379120057811 7806303945558568680086717)
        ·
          refine ⟨2927363979584463255032519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7806303945558568680086717 2927363979584463255032519)
          ·
            refine ⟨4391045969376694882548779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2927363979584463255032519 4391045969376694882548779)
            ·
              refine ⟨6586568954065042323823169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4391045969376694882548779 6586568954065042323823169)
              ·
                refine ⟨4939926715548781742867377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6586568954065042323823169 4939926715548781742867377)
                ·
                  refine ⟨3704945036661586307150533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4939926715548781742867377 3704945036661586307150533)
                  ·
                    refine ⟨694677194374047432590725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3704945036661586307150533 694677194374047432590725)
                    ·
                      rfl

theorem cell23_4058637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_4058637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058637 prefixEnd_4058637 := by exact prefixLift 4058637
  have htrace : WordTrace (prefixWord ++ tailWord_4058637) baseStart_4058637 baseEnd_4058637 := by
    simpa [prefixWord, tailWord_4058637, baseEnd_4058637] using wordTrace_append hprefix tailTrace_4058637
  have hstable : (prefixWord ++ tailWord_4058637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058637).length < 2 ^ (prefixWord ++ tailWord_4058637).sum := by decide
  have hdescent : baseEnd_4058637 < baseStart_4058637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058709 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 2, 5, 2]
def baseStart_4058709 : Nat := 118140960795 + 4058709 * 2 ^ 59
def prefixEnd_4058709 : Nat := 4983230072969 + 3 ^ 40 * 4058709 * 2
def baseEnd_4058709 : Nat := 2084068553729266016071843

theorem tailTrace_4058709 : CollatzResearch.WordTrace tailWord_4058709 prefixEnd_4058709 2084068553729266016071843 := by
  unfold tailWord_4058709
  simp only [CollatzResearch.WordTrace]
  refine ⟨148033278652997940156043181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98688852435331960104028787 148033278652997940156043181)
  ·
    refine ⟨55512479494874227558516193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148033278652997940156043181 55512479494874227558516193)
    ·
      refine ⟨41634359621155670668887145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55512479494874227558516193 41634359621155670668887145)
      ·
        refine ⟨31225769715866753001665359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41634359621155670668887145 31225769715866753001665359)
        ·
          refine ⟨46838654573800129502498039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31225769715866753001665359 46838654573800129502498039)
          ·
            refine ⟨70257981860700194253747059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46838654573800129502498039 70257981860700194253747059)
            ·
              refine ⟨105386972791050291380620589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70257981860700194253747059 105386972791050291380620589)
              ·
                refine ⟨39520114796643859267732721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105386972791050291380620589 39520114796643859267732721)
                ·
                  refine ⟨29640086097482894450799541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39520114796643859267732721 29640086097482894450799541)
                  ·
                    refine ⟨2778758071639021354762457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29640086097482894450799541 2778758071639021354762457)
                    ·
                      refine ⟨2084068553729266016071843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2778758071639021354762457 2084068553729266016071843)
                      ·
                        rfl

theorem cell23_4058709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_4058709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058709 prefixEnd_4058709 := by exact prefixLift 4058709
  have htrace : WordTrace (prefixWord ++ tailWord_4058709) baseStart_4058709 baseEnd_4058709 := by
    simpa [prefixWord, tailWord_4058709, baseEnd_4058709] using wordTrace_append hprefix tailTrace_4058709
  have hstable : (prefixWord ++ tailWord_4058709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058709).length < 2 ^ (prefixWord ++ tailWord_4058709).sum := by decide
  have hdescent : baseEnd_4058709 < baseStart_4058709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058717 : List Nat := [1, 4, 4, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_4058717 : Nat := 118140960795 + 4058717 * 2 ^ 59
def prefixEnd_4058717 : Nat := 4983230072969 + 3 ^ 40 * 4058717 * 2
def baseEnd_4058717 : Nat := 2084072661574501984771807

theorem tailTrace_4058717 : CollatzResearch.WordTrace tailWord_4058717 prefixEnd_4058717 2084072661574501984771807 := by
  unfold tailWord_4058717
  simp only [CollatzResearch.WordTrace]
  refine ⟨148033570436968957522334405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98689046957979305014889603 148033570436968957522334405)
  ·
    refine ⟨27756294456931679535437701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148033570436968957522334405 27756294456931679535437701)
    ·
      refine ⟨5204305210674689912894569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27756294456931679535437701 5204305210674689912894569)
      ·
        refine ⟨3903228908006017434670927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5204305210674689912894569 3903228908006017434670927)
        ·
          refine ⟨5854843362009026152006391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3903228908006017434670927 5854843362009026152006391)
          ·
            refine ⟨8782265043013539228009587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5854843362009026152006391 8782265043013539228009587)
            ·
              refine ⟨13173397564520308842014381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8782265043013539228009587 13173397564520308842014381)
              ·
                refine ⟨4940024086695115815755393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13173397564520308842014381 4940024086695115815755393)
                ·
                  refine ⟨3705018065021336861816545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4940024086695115815755393 3705018065021336861816545)
                  ·
                    refine ⟨2778763548766002646362409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3705018065021336861816545 2778763548766002646362409)
                    ·
                      refine ⟨2084072661574501984771807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2778763548766002646362409 2084072661574501984771807)
                      ·
                        rfl

theorem cell23_4058717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_4058717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058717 prefixEnd_4058717 := by exact prefixLift 4058717
  have htrace : WordTrace (prefixWord ++ tailWord_4058717) baseStart_4058717 baseEnd_4058717 := by
    simpa [prefixWord, tailWord_4058717, baseEnd_4058717] using wordTrace_append hprefix tailTrace_4058717
  have hstable : (prefixWord ++ tailWord_4058717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058717).length < 2 ^ (prefixWord ++ tailWord_4058717).sum := by decide
  have hdescent : baseEnd_4058717 < baseStart_4058717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058752 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 6]
def baseStart_4058752 : Nat := 118140960795 + 4058752 * 2 ^ 59
def prefixEnd_4058752 : Nat := 4983230072969 + 3 ^ 40 * 4058752 * 2
def baseEnd_4058752 : Nat := 2084090633397409347834145

theorem tailTrace_4058752 : CollatzResearch.WordTrace tailWord_4058752 prefixEnd_4058752 2084090633397409347834145 := by
  unfold tailWord_4058752
  simp only [CollatzResearch.WordTrace]
  refine ⟨74017423495921079249929255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98689897994561438999905673 74017423495921079249929255)
  ·
    refine ⟨111026135243881618874893883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74017423495921079249929255 111026135243881618874893883)
    ·
      refine ⟨166539202865822428312340825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111026135243881618874893883 166539202865822428312340825)
      ·
        refine ⟨124904402149366821234255619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166539202865822428312340825 124904402149366821234255619)
        ·
          refine ⟨187356603224050231851383429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124904402149366821234255619 187356603224050231851383429)
          ·
            refine ⟨35129363104509418472134393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187356603224050231851383429 35129363104509418472134393)
            ·
              refine ⟨26347022328382063854100795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35129363104509418472134393 26347022328382063854100795)
              ·
                refine ⟨39520533492573095781151193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26347022328382063854100795 39520533492573095781151193)
                ·
                  refine ⟨29640400119429821835863395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39520533492573095781151193 29640400119429821835863395)
                  ·
                    refine ⟨44460600179144732753795093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29640400119429821835863395 44460600179144732753795093)
                    ·
                      refine ⟨2084090633397409347834145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44460600179144732753795093 2084090633397409347834145)
                      ·
                        rfl

theorem cell23_4058752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_4058752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058752 prefixEnd_4058752 := by exact prefixLift 4058752
  have htrace : WordTrace (prefixWord ++ tailWord_4058752) baseStart_4058752 baseEnd_4058752 := by
    simpa [prefixWord, tailWord_4058752, baseEnd_4058752] using wordTrace_append hprefix tailTrace_4058752
  have hstable : (prefixWord ++ tailWord_4058752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058752).length < 2 ^ (prefixWord ++ tailWord_4058752).sum := by decide
  have hdescent : baseEnd_4058752 < baseStart_4058752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058783 : List Nat := [1, 1, 2, 7, 1, 1, 1, 2, 3, 4]
def baseStart_4058783 : Nat := 118140960795 + 4058783 * 2 ^ 59
def prefixEnd_4058783 : Nat := 4983230072969 + 3 ^ 40 * 4058783 * 2
def baseEnd_4058783 : Nat := 694702183765899575515501

theorem tailTrace_4058783 : CollatzResearch.WordTrace tailWord_4058783 prefixEnd_4058783 694702183765899575515501 := by
  unfold tailWord_4058783
  simp only [CollatzResearch.WordTrace]
  refine ⟨148035977654729850794237003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98690651769819900529491335 148035977654729850794237003)
  ·
    refine ⟨222053966482094776191355505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148035977654729850794237003 222053966482094776191355505)
    ·
      refine ⟨166540474861571082143516629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222053966482094776191355505 166540474861571082143516629)
      ·
        refine ⟨3903292379568072237738671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 166540474861571082143516629 3903292379568072237738671)
        ·
          refine ⟨5854938569352108356608007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3903292379568072237738671 5854938569352108356608007)
          ·
            refine ⟨8782407854028162534912011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5854938569352108356608007 8782407854028162534912011)
            ·
              refine ⟨13173611781042243802368017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8782407854028162534912011 13173611781042243802368017)
              ·
                refine ⟨9880208835781682851776013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13173611781042243802368017 9880208835781682851776013)
                ·
                  refine ⟨3705078313418131069416005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9880208835781682851776013 3705078313418131069416005)
                  ·
                    refine ⟨694702183765899575515501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3705078313418131069416005 694702183765899575515501)
                    ·
                      rfl

theorem cell23_4058783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 4].length) (baseStart_4058783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058783 prefixEnd_4058783 := by exact prefixLift 4058783
  have htrace : WordTrace (prefixWord ++ tailWord_4058783) baseStart_4058783 baseEnd_4058783 := by
    simpa [prefixWord, tailWord_4058783, baseEnd_4058783] using wordTrace_append hprefix tailTrace_4058783
  have hstable : (prefixWord ++ tailWord_4058783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058783).length < 2 ^ (prefixWord ++ tailWord_4058783).sum := by decide
  have hdescent : baseEnd_4058783 < baseStart_4058783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058816 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 4, 3, 2]
def baseStart_4058816 : Nat := 118140960795 + 4058816 * 2 ^ 59
def prefixEnd_4058816 : Nat := 4983230072969 + 3 ^ 40 * 4058816 * 2
def baseEnd_4058816 : Nat := 2084123496159297097433851

theorem tailTrace_4058816 : CollatzResearch.WordTrace tailWord_4058816 prefixEnd_4058816 2084123496159297097433851 := by
  unfold tailWord_4058816
  simp only [CollatzResearch.WordTrace]
  refine ⟨74018590631805148715094151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98691454175740198286792201 74018590631805148715094151)
  ·
    refine ⟨111027885947707723072641227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74018590631805148715094151 111027885947707723072641227)
    ·
      refine ⟨166541828921561584608961841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111027885947707723072641227 166541828921561584608961841)
      ·
        refine ⟨124906371691171188456721381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166541828921561584608961841 124906371691171188456721381)
        ·
          refine ⟨23419944692094597835635259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124906371691171188456721381 23419944692094597835635259)
          ·
            refine ⟨35129917038141896753452889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23419944692094597835635259 35129917038141896753452889)
            ·
              refine ⟨26347437778606422565089667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35129917038141896753452889 26347437778606422565089667)
              ·
                refine ⟨39521156667909633847634501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26347437778606422565089667 39521156667909633847634501)
                ·
                  refine ⟨7410216875233056346431469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39521156667909633847634501 7410216875233056346431469)
                  ·
                    refine ⟨2778831328212396129911801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7410216875233056346431469 2778831328212396129911801)
                    ·
                      refine ⟨2084123496159297097433851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2778831328212396129911801 2084123496159297097433851)
                      ·
                        rfl

theorem cell23_4058816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 4, 3, 2].length) (baseStart_4058816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058816 prefixEnd_4058816 := by exact prefixLift 4058816
  have htrace : WordTrace (prefixWord ++ tailWord_4058816) baseStart_4058816 baseEnd_4058816 := by
    simpa [prefixWord, tailWord_4058816, baseEnd_4058816] using wordTrace_append hprefix tailTrace_4058816
  have hstable : (prefixWord ++ tailWord_4058816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058816).length < 2 ^ (prefixWord ++ tailWord_4058816).sum := by decide
  have hdescent : baseEnd_4058816 < baseStart_4058816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058823 : List Nat := [1, 1, 4, 1, 1, 1, 3, 6, 1, 1, 3]
def baseStart_4058823 : Nat := 118140960795 + 4058823 * 2 ^ 59
def prefixEnd_4058823 : Nat := 4983230072969 + 3 ^ 40 * 4058823 * 2
def baseEnd_4058823 : Nat := 2084127090523878570046319

theorem tailTrace_4058823 : CollatzResearch.WordTrace tailWord_4058823 prefixEnd_4058823 2084127090523878570046319 := by
  unfold tailWord_4058823
  simp only [CollatzResearch.WordTrace]
  refine ⟨148037436574584937625693123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98691624383056625083795415 148037436574584937625693123)
  ·
    refine ⟨222056154861877406438539685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148037436574584937625693123 222056154861877406438539685)
    ·
      refine ⟨41635529036602013707226191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222056154861877406438539685 41635529036602013707226191)
      ·
        refine ⟨62453293554903020560839287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41635529036602013707226191 62453293554903020560839287)
        ·
          refine ⟨93679940332354530841258931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62453293554903020560839287 93679940332354530841258931)
          ·
            refine ⟨140519910498531796261888397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93679940332354530841258931 140519910498531796261888397)
            ·
              refine ⟨52694966436949423598208149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140519910498531796261888397 52694966436949423598208149)
              ·
                refine ⟨2470076551732004231166007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52694966436949423598208149 2470076551732004231166007)
                ·
                  refine ⟨3705114827598006346749011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2470076551732004231166007 3705114827598006346749011)
                  ·
                    refine ⟨5557672241397009520123517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3705114827598006346749011 5557672241397009520123517)
                    ·
                      refine ⟨2084127090523878570046319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5557672241397009520123517 2084127090523878570046319)
                      ·
                        rfl

theorem cell23_4058823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 1, 1, 3].length) (baseStart_4058823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058823 prefixEnd_4058823 := by exact prefixLift 4058823
  have htrace : WordTrace (prefixWord ++ tailWord_4058823) baseStart_4058823 baseEnd_4058823 := by
    simpa [prefixWord, tailWord_4058823, baseEnd_4058823] using wordTrace_append hprefix tailTrace_4058823
  have hstable : (prefixWord ++ tailWord_4058823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058823).length < 2 ^ (prefixWord ++ tailWord_4058823).sum := by decide
  have hdescent : baseEnd_4058823 < baseStart_4058823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058856 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 4, 4]
def baseStart_4058856 : Nat := 118140960795 + 4058856 * 2 ^ 59
def prefixEnd_4058856 : Nat := 4983230072969 + 3 ^ 40 * 4058856 * 2
def baseEnd_4058856 : Nat := 694714678461825646977889

theorem tailTrace_4058856 : CollatzResearch.WordTrace tailWord_4058856 prefixEnd_4058856 694714678461825646977889 := by
  unfold tailWord_4058856
  simp only [CollatzResearch.WordTrace]
  refine ⟨74019320091732692130822211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98692426788976922841096281 74019320091732692130822211)
  ·
    refine ⟨111028980137599038196233317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74019320091732692130822211 111028980137599038196233317)
    ·
      refine ⟨20817933775799819661793747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111028980137599038196233317 20817933775799819661793747)
      ·
        refine ⟨31226900663699729492690621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20817933775799819661793747 31226900663699729492690621)
        ·
          refine ⟨11710087748887398559758983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31226900663699729492690621 11710087748887398559758983)
          ·
            refine ⟨17565131623331097839638475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11710087748887398559758983 17565131623331097839638475)
            ·
              refine ⟨26347697434996646759457713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17565131623331097839638475 26347697434996646759457713)
              ·
                refine ⟨19760773076247485069593285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26347697434996646759457713 19760773076247485069593285)
                ·
                  refine ⟨3705144951796403450548741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19760773076247485069593285 3705144951796403450548741)
                  ·
                    refine ⟨694714678461825646977889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3705144951796403450548741 694714678461825646977889)
                    ·
                      rfl

theorem cell23_4058856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_4058856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058856 prefixEnd_4058856 := by exact prefixLift 4058856
  have htrace : WordTrace (prefixWord ++ tailWord_4058856) baseStart_4058856 baseEnd_4058856 := by
    simpa [prefixWord, tailWord_4058856, baseEnd_4058856] using wordTrace_append hprefix tailTrace_4058856
  have hstable : (prefixWord ++ tailWord_4058856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058856).length < 2 ^ (prefixWord ++ tailWord_4058856).sum := by decide
  have hdescent : baseEnd_4058856 < baseStart_4058856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058859 : List Nat := [1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 4]
def baseStart_4058859 : Nat := 118140960795 + 4058859 * 2 ^ 59
def prefixEnd_4058859 : Nat := 4983230072969 + 3 ^ 40 * 4058859 * 2
def baseEnd_4058859 : Nat := 2084145575827440429196153

theorem tailTrace_4058859 : CollatzResearch.WordTrace tailWord_4058859 prefixEnd_4058859 2084145575827440429196153 := by
  unfold tailWord_4058859
  simp only [CollatzResearch.WordTrace]
  refine ⟨148038749602454515774003631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98692499734969677182669087 148038749602454515774003631)
  ·
    refine ⟨222058124403681773661005447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148038749602454515774003631 222058124403681773661005447)
    ·
      refine ⟨333087186605522660491508171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222058124403681773661005447 333087186605522660491508171)
      ·
        refine ⟨499630779908283990737262257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333087186605522660491508171 499630779908283990737262257)
        ·
          refine ⟨374723084931212993052946693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499630779908283990737262257 374723084931212993052946693)
          ·
            refine ⟨70260578424602436197427505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 374723084931212993052946693 70260578424602436197427505)
            ·
              refine ⟨52695433818451827148070629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70260578424602436197427505 52695433818451827148070629)
              ·
                refine ⟨9880393840959717590263243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52695433818451827148070629 9880393840959717590263243)
                ·
                  refine ⟨14820590761439576385394865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9880393840959717590263243 14820590761439576385394865)
                  ·
                    refine ⟨11115443071079682289046149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14820590761439576385394865 11115443071079682289046149)
                    ·
                      refine ⟨2084145575827440429196153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11115443071079682289046149 2084145575827440429196153)
                      ·
                        rfl

theorem cell23_4058859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 4].length) (baseStart_4058859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058859 prefixEnd_4058859 := by exact prefixLift 4058859
  have htrace : WordTrace (prefixWord ++ tailWord_4058859) baseStart_4058859 baseEnd_4058859 := by
    simpa [prefixWord, tailWord_4058859, baseEnd_4058859] using wordTrace_append hprefix tailTrace_4058859
  have hstable : (prefixWord ++ tailWord_4058859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058859).length < 2 ^ (prefixWord ++ tailWord_4058859).sum := by decide
  have hdescent : baseEnd_4058859 < baseStart_4058859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058866 : List Nat := [3, 2, 1, 3, 1, 1, 4, 1, 1, 1, 5]
def baseStart_4058866 : Nat := 118140960795 + 4058866 * 2 ^ 59
def prefixEnd_4058866 : Nat := 4983230072969 + 3 ^ 40 * 4058866 * 2
def baseEnd_4058866 : Nat := 2084149170192021901808621

theorem tailTrace_4058866 : CollatzResearch.WordTrace tailWord_4058866 prefixEnd_4058866 2084149170192021901808621 := by
  unfold tailWord_4058866
  simp only [CollatzResearch.WordTrace]
  refine ⟨37009751228357288992377113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98692669942286103979672301 37009751228357288992377113)
  ·
    refine ⟨27757313421267966744282835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37009751228357288992377113 27757313421267966744282835)
    ·
      refine ⟨41635970131901950116424253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27757313421267966744282835 41635970131901950116424253)
      ·
        refine ⟨15613488799463231293659095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41635970131901950116424253 15613488799463231293659095)
        ·
          refine ⟨23420233199194846940488643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15613488799463231293659095 23420233199194846940488643)
          ·
            refine ⟨35130349798792270410732965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23420233199194846940488643 35130349798792270410732965)
            ·
              refine ⟨6586940587273550702012431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35130349798792270410732965 6586940587273550702012431)
              ·
                refine ⟨9880410880910326053018647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6586940587273550702012431 9880410880910326053018647)
                ·
                  refine ⟨14820616321365489079527971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9880410880910326053018647 14820616321365489079527971)
                  ·
                    refine ⟨22230924482048233619291957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14820616321365489079527971 22230924482048233619291957)
                    ·
                      refine ⟨2084149170192021901808621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22230924482048233619291957 2084149170192021901808621)
                      ·
                        rfl

theorem cell23_4058866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_4058866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058866 prefixEnd_4058866 := by exact prefixLift 4058866
  have htrace : WordTrace (prefixWord ++ tailWord_4058866) baseStart_4058866 baseEnd_4058866 := by
    simpa [prefixWord, tailWord_4058866, baseEnd_4058866] using wordTrace_append hprefix tailTrace_4058866
  have hstable : (prefixWord ++ tailWord_4058866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058866).length < 2 ^ (prefixWord ++ tailWord_4058866).sum := by decide
  have hdescent : baseEnd_4058866 < baseStart_4058866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058890 : List Nat := [3, 1, 2, 2, 1, 5, 2, 1, 2, 4]
def baseStart_4058890 : Nat := 118140960795 + 4058890 * 2 ^ 59
def prefixEnd_4058890 : Nat := 4983230072969 + 3 ^ 40 * 4058890 * 2
def baseEnd_4058890 : Nat := 694720497909243269302837

theorem tailTrace_4058890 : CollatzResearch.WordTrace tailWord_4058890 prefixEnd_4058890 694720497909243269302837 := by
  unfold tailWord_4058890
  simp only [CollatzResearch.WordTrace]
  refine ⟨37009970066335552017095531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98693253510228138712254749 37009970066335552017095531)
  ·
    refine ⟨55514955099503328025643297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37009970066335552017095531 55514955099503328025643297)
    ·
      refine ⟨41636216324627496019232473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55514955099503328025643297 41636216324627496019232473)
      ·
        refine ⟨31227162243470622014424355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41636216324627496019232473 31227162243470622014424355)
        ·
          refine ⟨46840743365205933021636533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31227162243470622014424355 46840743365205933021636533)
          ·
            refine ⟨4391319690488056220778425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46840743365205933021636533 4391319690488056220778425)
            ·
              refine ⟨3293489767866042165583819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4391319690488056220778425 3293489767866042165583819)
              ·
                refine ⟨4940234651799063248375729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3293489767866042165583819 4940234651799063248375729)
                ·
                  refine ⟨3705175988849297436281797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4940234651799063248375729 3705175988849297436281797)
                  ·
                    refine ⟨694720497909243269302837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3705175988849297436281797 694720497909243269302837)
                    ·
                      rfl

theorem cell23_4058890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_4058890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058890 prefixEnd_4058890 := by exact prefixLift 4058890
  have htrace : WordTrace (prefixWord ++ tailWord_4058890) baseStart_4058890 baseEnd_4058890 := by
    simpa [prefixWord, tailWord_4058890, baseEnd_4058890] using wordTrace_append hprefix tailTrace_4058890
  have hstable : (prefixWord ++ tailWord_4058890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058890).length < 2 ^ (prefixWord ++ tailWord_4058890).sum := by decide
  have hdescent : baseEnd_4058890 < baseStart_4058890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058930 : List Nat := [3, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3]
def baseStart_4058930 : Nat := 118140960795 + 4058930 * 2 ^ 59
def prefixEnd_4058930 : Nat := 4983230072969 + 3 ^ 40 * 4058930 * 2
def baseEnd_4058930 : Nat := 2084182032953909651408327

theorem tailTrace_4058930 : CollatzResearch.WordTrace tailWord_4058930 prefixEnd_4058930 2084182032953909651408327 := by
  unfold tailWord_4058930
  simp only [CollatzResearch.WordTrace]
  refine ⟨37010334796299323724959561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98694226123464863266558829 37010334796299323724959561)
  ·
    refine ⟨27757751097224492793719671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37010334796299323724959561 27757751097224492793719671)
    ·
      refine ⟨41636626645836739190579507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27757751097224492793719671 41636626645836739190579507)
      ·
        refine ⟨62454939968755108785869261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41636626645836739190579507 62454939968755108785869261)
        ·
          refine ⟨23420602488283165794700973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62454939968755108785869261 23420602488283165794700973)
          ·
            refine ⟨8782725933106187173012865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23420602488283165794700973 8782725933106187173012865)
            ·
              refine ⟨6587044449829640379759649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8782725933106187173012865 6587044449829640379759649)
              ·
                refine ⟨4940283337372230284819737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6587044449829640379759649 4940283337372230284819737)
                ·
                  refine ⟨3705212503029172713614803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4940283337372230284819737 3705212503029172713614803)
                  ·
                    refine ⟨5557818754543759070422205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3705212503029172713614803 5557818754543759070422205)
                    ·
                      refine ⟨2084182032953909651408327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5557818754543759070422205 2084182032953909651408327)
                      ·
                        rfl

theorem cell23_4058930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_4058930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058930 prefixEnd_4058930 := by exact prefixLift 4058930
  have htrace : WordTrace (prefixWord ++ tailWord_4058930) baseStart_4058930 baseEnd_4058930 := by
    simpa [prefixWord, tailWord_4058930, baseEnd_4058930] using wordTrace_append hprefix tailTrace_4058930
  have hstable : (prefixWord ++ tailWord_4058930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058930).length < 2 ^ (prefixWord ++ tailWord_4058930).sum := by decide
  have hdescent : baseEnd_4058930 < baseStart_4058930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058931 : List Nat := [1, 1, 1, 2, 8, 1, 2, 2, 1, 2, 2]
def baseStart_4058931 : Nat := 118140960795 + 4058931 * 2 ^ 59
def prefixEnd_4058931 : Nat := 4983230072969 + 3 ^ 40 * 4058931 * 2
def baseEnd_4058931 : Nat := 2084182546434564147495823

theorem tailTrace_4058931 : CollatzResearch.WordTrace tailWord_4058931 prefixEnd_4058931 2084182546434564147495823 := by
  unfold tailWord_4058931
  simp only [CollatzResearch.WordTrace]
  refine ⟨148041375658193672070624647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98694250438795781380416431 148041375658193672070624647)
  ·
    refine ⟨222062063487290508105936971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148041375658193672070624647 222062063487290508105936971)
    ·
      refine ⟨333093095230935762158905457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222062063487290508105936971 333093095230935762158905457)
      ·
        refine ⟨249819821423201821619179093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333093095230935762158905457 249819821423201821619179093)
        ·
          refine ⟨2927576032303146347099755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 249819821423201821619179093 2927576032303146347099755)
          ·
            refine ⟨4391364048454719520649633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2927576032303146347099755 4391364048454719520649633)
            ·
              refine ⟨3293523036341039640487225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4391364048454719520649633 3293523036341039640487225)
              ·
                refine ⟨2470142277255779730365419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3293523036341039640487225 2470142277255779730365419)
                ·
                  refine ⟨3705213415883669595548129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2470142277255779730365419 3705213415883669595548129)
                  ·
                    refine ⟨2778910061912752196661097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3705213415883669595548129 2778910061912752196661097)
                    ·
                      refine ⟨2084182546434564147495823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2778910061912752196661097 2084182546434564147495823)
                      ·
                        rfl

theorem cell23_4058931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 1, 2, 2].length) (baseStart_4058931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058931 prefixEnd_4058931 := by exact prefixLift 4058931
  have htrace : WordTrace (prefixWord ++ tailWord_4058931) baseStart_4058931 baseEnd_4058931 := by
    simpa [prefixWord, tailWord_4058931, baseEnd_4058931] using wordTrace_append hprefix tailTrace_4058931
  have hstable : (prefixWord ++ tailWord_4058931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058931).length < 2 ^ (prefixWord ++ tailWord_4058931).sum := by decide
  have hdescent : baseEnd_4058931 < baseStart_4058931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058953 : List Nat := [1, 2, 1, 1, 2, 4, 4, 1, 1, 4, 2]
def baseStart_4058953 : Nat := 118140960795 + 4058953 * 2 ^ 59
def prefixEnd_4058953 : Nat := 4983230072969 + 3 ^ 40 * 4058953 * 2
def baseEnd_4058953 : Nat := 2084193843008963061420721

theorem tailTrace_4058953 : CollatzResearch.WordTrace tailWord_4058953 prefixEnd_4058953 2084193843008963061420721 := by
  unfold tailWord_4058953
  simp only [CollatzResearch.WordTrace]
  refine ⟨148042178064113969827925513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98694785376075979885283675 148042178064113969827925513)
  ·
    refine ⟨111031633548085477370944135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148042178064113969827925513 111031633548085477370944135)
    ·
      refine ⟨166547450322128216056416203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111031633548085477370944135 166547450322128216056416203)
      ·
        refine ⟨249821175483192324084624305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166547450322128216056416203 249821175483192324084624305)
        ·
          refine ⟨187365881612394243063468229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249821175483192324084624305 187365881612394243063468229)
          ·
            refine ⟨35131102802323920574400293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187365881612394243063468229 35131102802323920574400293)
            ·
              refine ⟨6587081775435735107700055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35131102802323920574400293 6587081775435735107700055)
              ·
                refine ⟨9880622663153602661550083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6587081775435735107700055 9880622663153602661550083)
                ·
                  refine ⟨14820933994730403992325125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9880622663153602661550083 14820933994730403992325125)
                  ·
                    refine ⟨2778925124011950748560961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14820933994730403992325125 2778925124011950748560961)
                    ·
                      refine ⟨2084193843008963061420721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2778925124011950748560961 2084193843008963061420721)
                      ·
                        rfl

theorem cell23_4058953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 4, 2].length) (baseStart_4058953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4058953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4058953 prefixEnd_4058953 := by exact prefixLift 4058953
  have htrace : WordTrace (prefixWord ++ tailWord_4058953) baseStart_4058953 baseEnd_4058953 := by
    simpa [prefixWord, tailWord_4058953, baseEnd_4058953] using wordTrace_append hprefix tailTrace_4058953
  have hstable : (prefixWord ++ tailWord_4058953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058953).length < 2 ^ (prefixWord ++ tailWord_4058953).sum := by decide
  have hdescent : baseEnd_4058953 < baseStart_4058953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059019 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 1, 10]
def baseStart_4059019 : Nat := 118140960795 + 4059019 * 2 ^ 59
def prefixEnd_4059019 : Nat := 4983230072969 + 3 ^ 40 * 4059019 * 2
def baseEnd_4059019 : Nat := 694742577577386601065139

theorem tailTrace_4059019 : CollatzResearch.WordTrace tailWord_4059019 prefixEnd_4059019 694742577577386601065139 := by
  unfold tailWord_4059019
  simp only [CollatzResearch.WordTrace]
  refine ⟨148044585281874863099828111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98696390187916575399885407 148044585281874863099828111)
  ·
    refine ⟨222066877922812294649742167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148044585281874863099828111 222066877922812294649742167)
    ·
      refine ⟨333100316884218441974613251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222066877922812294649742167 333100316884218441974613251)
      ·
        refine ⟨499650475326327662961919877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333100316884218441974613251 499650475326327662961919877)
        ·
          refine ⟨93684464123686436805359977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 499650475326327662961919877 93684464123686436805359977)
          ·
            refine ⟨70263348092764827604019983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93684464123686436805359977 70263348092764827604019983)
            ·
              refine ⟨105395022139147241406029975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70263348092764827604019983 105395022139147241406029975)
              ·
                refine ⟨158092533208720862109044963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105395022139147241406029975 158092533208720862109044963)
                ·
                  refine ⟨237138799813081293163567445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158092533208720862109044963 237138799813081293163567445)
                  ·
                    refine ⟨694742577577386601065139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 237138799813081293163567445 694742577577386601065139)
                    ·
                      rfl

theorem cell23_4059019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 10].length) (baseStart_4059019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059019 prefixEnd_4059019 := by exact prefixLift 4059019
  have htrace : WordTrace (prefixWord ++ tailWord_4059019) baseStart_4059019 baseEnd_4059019 := by
    simpa [prefixWord, tailWord_4059019, baseEnd_4059019] using wordTrace_append hprefix tailTrace_4059019
  have hstable : (prefixWord ++ tailWord_4059019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059019).length < 2 ^ (prefixWord ++ tailWord_4059019).sum := by decide
  have hdescent : baseEnd_4059019 < baseStart_4059019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059080 : List Nat := [2, 1, 3, 1, 4, 2, 2, 1, 2, 2, 3]
def baseStart_4059080 : Nat := 118140960795 + 4059080 * 2 ^ 59
def prefixEnd_4059080 : Nat := 4983230072969 + 3 ^ 40 * 4059080 * 2
def baseEnd_4059080 : Nat := 2084259055052084064532637

theorem tailTrace_4059080 : CollatzResearch.WordTrace tailWord_4059080 prefixEnd_4059080 2084259055052084064532637 := by
  unfold tailWord_4059080
  simp only [CollatzResearch.WordTrace]
  refine ⟨74023405067326935258899347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98697873423102580345199129 74023405067326935258899347)
  ·
    refine ⟨111035107600990402888349021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74023405067326935258899347 111035107600990402888349021)
    ·
      refine ⟨41638165350371401083130883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111035107600990402888349021 41638165350371401083130883)
      ·
        refine ⟨62457248025557101624696325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41638165350371401083130883 62457248025557101624696325)
        ·
          refine ⟨11710734004791956554630561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62457248025557101624696325 11710734004791956554630561)
          ·
            refine ⟨8783050503593967415972921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11710734004791956554630561 8783050503593967415972921)
            ·
              refine ⟨6587287877695475561979691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8783050503593967415972921 6587287877695475561979691)
              ·
                refine ⟨9880931816543213342969537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6587287877695475561979691 9880931816543213342969537)
                ·
                  refine ⟨7410698862407410007227153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9880931816543213342969537 7410698862407410007227153)
                  ·
                    refine ⟨5558024146805557505420365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7410698862407410007227153 5558024146805557505420365)
                    ·
                      refine ⟨2084259055052084064532637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5558024146805557505420365 2084259055052084064532637)
                      ·
                        rfl

theorem cell23_4059080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_4059080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059080 prefixEnd_4059080 := by exact prefixLift 4059080
  have htrace : WordTrace (prefixWord ++ tailWord_4059080) baseStart_4059080 baseEnd_4059080 := by
    simpa [prefixWord, tailWord_4059080, baseEnd_4059080] using wordTrace_append hprefix tailTrace_4059080
  have hstable : (prefixWord ++ tailWord_4059080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059080).length < 2 ^ (prefixWord ++ tailWord_4059080).sum := by decide
  have hdescent : baseEnd_4059080 < baseStart_4059080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059133 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 3, 1, 4]
def baseStart_4059133 : Nat := 118140960795 + 4059133 * 2 ^ 59
def prefixEnd_4059133 : Nat := 4983230072969 + 3 ^ 40 * 4059133 * 2
def baseEnd_4059133 : Nat := 2084286269526772357169893

theorem tailTrace_4059133 : CollatzResearch.WordTrace tailWord_4059133 prefixEnd_4059133 2084286269526772357169893 := by
  unfold tailWord_4059133
  simp only [CollatzResearch.WordTrace]
  refine ⟨148048743203461860569478053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98699162135641240379652035 148048743203461860569478053)
  ·
    refine ⟨27759139350649098856777135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148048743203461860569478053 27759139350649098856777135)
    ·
      refine ⟨41638709025973648285165703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27759139350649098856777135 41638709025973648285165703)
      ·
        refine ⟨62458063538960472427748555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41638709025973648285165703 62458063538960472427748555)
        ·
          refine ⟨93687095308440708641622833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62458063538960472427748555 93687095308440708641622833)
          ·
            refine ⟨70265321481330531481217125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93687095308440708641622833 70265321481330531481217125)
            ·
              refine ⟨13174747777749474652728211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70265321481330531481217125 13174747777749474652728211)
              ·
                refine ⟨19762121666624211979092317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13174747777749474652728211 19762121666624211979092317)
                ·
                  refine ⟨7410795624984079492159619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19762121666624211979092317 7410795624984079492159619)
                  ·
                    refine ⟨11116193437476119238239429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7410795624984079492159619 11116193437476119238239429)
                    ·
                      refine ⟨2084286269526772357169893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11116193437476119238239429 2084286269526772357169893)
                      ·
                        rfl

theorem cell23_4059133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_4059133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059133 prefixEnd_4059133 := by exact prefixLift 4059133
  have htrace : WordTrace (prefixWord ++ tailWord_4059133) baseStart_4059133 baseEnd_4059133 := by
    simpa [prefixWord, tailWord_4059133, baseEnd_4059133] using wordTrace_append hprefix tailTrace_4059133
  have hstable : (prefixWord ++ tailWord_4059133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059133).length < 2 ^ (prefixWord ++ tailWord_4059133).sum := by decide
  have hdescent : baseEnd_4059133 < baseStart_4059133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059136 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 5]
def baseStart_4059136 : Nat := 118140960795 + 4059136 * 2 ^ 59
def prefixEnd_4059136 : Nat := 4983230072969 + 3 ^ 40 * 4059136 * 2
def baseEnd_4059136 : Nat := 2084287809968735845432379

theorem tailTrace_4059136 : CollatzResearch.WordTrace tailWord_4059136 prefixEnd_4059136 2084287809968735845432379 := by
  unfold tailWord_4059136
  simp only [CollatzResearch.WordTrace]
  refine ⟨74024426311225496040918631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98699235081633994721224841 74024426311225496040918631)
  ·
    refine ⟨111036639466838244061377947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74024426311225496040918631 111036639466838244061377947)
    ·
      refine ⟨166554959200257366092066921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111036639466838244061377947 166554959200257366092066921)
      ·
        refine ⟨124916219400193024569050191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166554959200257366092066921 124916219400193024569050191)
        ·
          refine ⟨187374329100289536853575287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124916219400193024569050191 187374329100289536853575287)
          ·
            refine ⟨281061493650434305280362931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187374329100289536853575287 281061493650434305280362931)
            ·
              refine ⟨421592240475651457920544397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281061493650434305280362931 421592240475651457920544397)
              ·
                refine ⟨158097090178369296720204149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421592240475651457920544397 158097090178369296720204149)
                ·
                  refine ⟨14821602204222121567519139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158097090178369296720204149 14821602204222121567519139)
                  ·
                    refine ⟨22232403306333182351278709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14821602204222121567519139 22232403306333182351278709)
                    ·
                      refine ⟨2084287809968735845432379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22232403306333182351278709 2084287809968735845432379)
                      ·
                        rfl

theorem cell23_4059136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_4059136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059136 prefixEnd_4059136 := by exact prefixLift 4059136
  have htrace : WordTrace (prefixWord ++ tailWord_4059136) baseStart_4059136 baseEnd_4059136 := by
    simpa [prefixWord, tailWord_4059136, baseEnd_4059136] using wordTrace_append hprefix tailTrace_4059136
  have hstable : (prefixWord ++ tailWord_4059136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059136).length < 2 ^ (prefixWord ++ tailWord_4059136).sum := by decide
  have hdescent : baseEnd_4059136 < baseStart_4059136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059143 : List Nat := [1, 1, 4, 3, 1, 2, 2, 2, 1, 6]
def baseStart_4059143 : Nat := 118140960795 + 4059143 * 2 ^ 59
def prefixEnd_4059143 : Nat := 4983230072969 + 3 ^ 40 * 4059143 * 2
def baseEnd_4059143 : Nat := 694763801444439106014949

theorem tailTrace_4059143 : CollatzResearch.WordTrace tailWord_4059143 prefixEnd_4059143 694763801444439106014949 := by
  unfold tailWord_4059143
  simp only [CollatzResearch.WordTrace]
  refine ⟨148049107933425632277342083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98699405288950421518228055 148049107933425632277342083)
  ·
    refine ⟨222073661900138448416013125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148049107933425632277342083 222073661900138448416013125)
    ·
      refine ⟨41638811606275959078002461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222073661900138448416013125 41638811606275959078002461)
      ·
        refine ⟨15614554352353484654250923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41638811606275959078002461 15614554352353484654250923)
        ·
          refine ⟨23421831528530226981376385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15614554352353484654250923 23421831528530226981376385)
          ·
            refine ⟨17566373646397670236032289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23421831528530226981376385 17566373646397670236032289)
            ·
              refine ⟨13174780234798252677024217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17566373646397670236032289 13174780234798252677024217)
              ·
                refine ⟨9881085176098689507768163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13174780234798252677024217 9881085176098689507768163)
                ·
                  refine ⟨14821627764148034261652245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9881085176098689507768163 14821627764148034261652245)
                  ·
                    refine ⟨694763801444439106014949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14821627764148034261652245 694763801444439106014949)
                    ·
                      rfl

theorem cell23_4059143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_4059143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059143 prefixEnd_4059143 := by exact prefixLift 4059143
  have htrace : WordTrace (prefixWord ++ tailWord_4059143) baseStart_4059143 baseEnd_4059143 := by
    simpa [prefixWord, tailWord_4059143, baseEnd_4059143] using wordTrace_append hprefix tailTrace_4059143
  have hstable : (prefixWord ++ tailWord_4059143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059143).length < 2 ^ (prefixWord ++ tailWord_4059143).sum := by decide
  have hdescent : baseEnd_4059143 < baseStart_4059143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059150 : List Nat := [4, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4]
def baseStart_4059150 : Nat := 118140960795 + 4059150 * 2 ^ 59
def prefixEnd_4059150 : Nat := 4983230072969 + 3 ^ 40 * 4059150 * 2
def baseEnd_4059150 : Nat := 2084294998697898790657315

theorem tailTrace_4059150 : CollatzResearch.WordTrace tailWord_4059150 prefixEnd_4059150 2084294998697898790657315 := by
  unfold tailWord_4059150
  simp only [CollatzResearch.WordTrace]
  refine ⟨18506170405550034059105863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98699575496266848315231269 18506170405550034059105863)
  ·
    refine ⟨27759255608325051088658795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18506170405550034059105863 27759255608325051088658795)
    ·
      refine ⟨41638883412487576632988193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27759255608325051088658795 41638883412487576632988193)
      ·
        refine ⟨31229162559365682474741145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41638883412487576632988193 31229162559365682474741145)
        ·
          refine ⟨23421871919524261856055859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31229162559365682474741145 23421871919524261856055859)
          ·
            refine ⟨35132807879286392784083789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23421871919524261856055859 35132807879286392784083789)
            ·
              refine ⟨13174802954732397294031421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35132807879286392784083789 13174802954732397294031421)
              ·
                refine ⟨4940551108024648985261783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13174802954732397294031421 4940551108024648985261783)
                ·
                  refine ⟨7410826662036973477892675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4940551108024648985261783 7410826662036973477892675)
                  ·
                    refine ⟨11116239993055460216839013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7410826662036973477892675 11116239993055460216839013)
                    ·
                      refine ⟨2084294998697898790657315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11116239993055460216839013 2084294998697898790657315)
                      ·
                        rfl

theorem cell23_4059150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_4059150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059150 prefixEnd_4059150 := by exact prefixLift 4059150
  have htrace : WordTrace (prefixWord ++ tailWord_4059150) baseStart_4059150 baseEnd_4059150 := by
    simpa [prefixWord, tailWord_4059150, baseEnd_4059150] using wordTrace_append hprefix tailTrace_4059150
  have hstable : (prefixWord ++ tailWord_4059150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059150).length < 2 ^ (prefixWord ++ tailWord_4059150).sum := by decide
  have hdescent : baseEnd_4059150 < baseStart_4059150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059167 : List Nat := [1, 1, 2, 4, 1, 2, 4, 1, 3, 2, 2]
def baseStart_4059167 : Nat := 118140960795 + 4059167 * 2 ^ 59
def prefixEnd_4059167 : Nat := 4983230072969 + 3 ^ 40 * 4059167 * 2
def baseEnd_4059167 : Nat := 2084303727869025224144737

theorem tailTrace_4059167 : CollatzResearch.WordTrace tailWord_4059167 prefixEnd_4059167 2084303727869025224144737 := by
  unfold tailWord_4059167
  simp only [CollatzResearch.WordTrace]
  refine ⟨148049983285338684376215755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98699988856892456250810503 148049983285338684376215755)
  ·
    refine ⟨222074974928008026564323633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148049983285338684376215755 222074974928008026564323633)
    ·
      refine ⟨166556231196006019923242725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222074974928008026564323633 166556231196006019923242725)
      ·
        refine ⟨31229293349251128735608011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166556231196006019923242725 31229293349251128735608011)
        ·
          refine ⟨46843940023876693103412017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31229293349251128735608011 46843940023876693103412017)
          ·
            refine ⟨35132955017907519827559013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46843940023876693103412017 35132955017907519827559013)
            ·
              refine ⟨6587429065857659967667315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35132955017907519827559013 6587429065857659967667315)
              ·
                refine ⟨9881143598786489951500973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6587429065857659967667315 9881143598786489951500973)
                ·
                  refine ⟨3705428849544933731812865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9881143598786489951500973 3705428849544933731812865)
                  ·
                    refine ⟨2779071637158700298859649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3705428849544933731812865 2779071637158700298859649)
                    ·
                      refine ⟨2084303727869025224144737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2779071637158700298859649 2084303727869025224144737)
                      ·
                        rfl

theorem cell23_4059167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_4059167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059167 prefixEnd_4059167 := by exact prefixLift 4059167
  have htrace : WordTrace (prefixWord ++ tailWord_4059167) baseStart_4059167 baseEnd_4059167 := by
    simpa [prefixWord, tailWord_4059167, baseEnd_4059167] using wordTrace_append hprefix tailTrace_4059167
  have hstable : (prefixWord ++ tailWord_4059167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059167).length < 2 ^ (prefixWord ++ tailWord_4059167).sum := by decide
  have hdescent : baseEnd_4059167 < baseStart_4059167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059183 : List Nat := [1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 3]
def baseStart_4059183 : Nat := 118140960795 + 4059183 * 2 ^ 59
def prefixEnd_4059183 : Nat := 4983230072969 + 3 ^ 40 * 4059183 * 2
def baseEnd_4059183 : Nat := 2084311943559497161544663

theorem tailTrace_4059183 : CollatzResearch.WordTrace tailWord_4059183 prefixEnd_4059183 2084311943559497161544663 := by
  unfold tailWord_4059183
  simp only [CollatzResearch.WordTrace]
  refine ⟨148050566853280719108798203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98700377902187146072532135 148050566853280719108798203)
  ·
    refine ⟨222075850279921078663197305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148050566853280719108798203 222075850279921078663197305)
    ·
      refine ⟨166556887709940808997397979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222075850279921078663197305 166556887709940808997397979)
      ·
        refine ⟨249835331564911213496096969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166556887709940808997397979 249835331564911213496096969)
        ·
          refine ⟨187376498673683410122072727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249835331564911213496096969 187376498673683410122072727)
          ·
            refine ⟨281064748010525115183109091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187376498673683410122072727 281064748010525115183109091)
            ·
              refine ⟨421597122015787672774663637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281064748010525115183109091 421597122015787672774663637)
              ·
                refine ⟨9881182547245023580656179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 421597122015787672774663637 9881182547245023580656179)
                ·
                  refine ⟨14821773820867535370984269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9881182547245023580656179 14821773820867535370984269)
                  ·
                    refine ⟨5558165182825325764119101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14821773820867535370984269 5558165182825325764119101)
                    ·
                      refine ⟨2084311943559497161544663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5558165182825325764119101 2084311943559497161544663)
                      ·
                        rfl

theorem cell23_4059183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 3].length) (baseStart_4059183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059183 prefixEnd_4059183 := by exact prefixLift 4059183
  have htrace : WordTrace (prefixWord ++ tailWord_4059183) baseStart_4059183 baseEnd_4059183 := by
    simpa [prefixWord, tailWord_4059183, baseEnd_4059183] using wordTrace_append hprefix tailTrace_4059183
  have hstable : (prefixWord ++ tailWord_4059183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059183).length < 2 ^ (prefixWord ++ tailWord_4059183).sum := by decide
  have hdescent : baseEnd_4059183 < baseStart_4059183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059200 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 4, 1, 3]
def baseStart_4059200 : Nat := 118140960795 + 4059200 * 2 ^ 59
def prefixEnd_4059200 : Nat := 4983230072969 + 3 ^ 40 * 4059200 * 2
def baseEnd_4059200 : Nat := 2084320672730623595032085

theorem tailTrace_4059200 : CollatzResearch.WordTrace tailWord_4059200 prefixEnd_4059200 2084320672730623595032085 := by
  unfold tailWord_4059200
  simp only [CollatzResearch.WordTrace]
  refine ⟨74025593447109565506083527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98700791262812754008111369 74025593447109565506083527)
  ·
    refine ⟨111038390170664348259125291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74025593447109565506083527 111038390170664348259125291)
    ·
      refine ⟨166557585255996522388687937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111038390170664348259125291 166557585255996522388687937)
      ·
        refine ⟨124918188941997391791515953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166557585255996522388687937 124918188941997391791515953)
        ·
          refine ⟨93688641706498043843636965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124918188941997391791515953 93688641706498043843636965)
          ·
            refine ⟨17566620319968383220681931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93688641706498043843636965 17566620319968383220681931)
            ·
              refine ⟨26349930479952574831022897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17566620319968383220681931 26349930479952574831022897)
              ·
                refine ⟨19762447859964431123267173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26349930479952574831022897 19762447859964431123267173)
                ·
                  refine ⟨3705458973743330835612595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19762447859964431123267173 3705458973743330835612595)
                  ·
                    refine ⟨5558188460614996253418893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3705458973743330835612595 5558188460614996253418893)
                    ·
                      refine ⟨2084320672730623595032085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5558188460614996253418893 2084320672730623595032085)
                      ·
                        rfl

theorem cell23_4059200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 4, 1, 3].length) (baseStart_4059200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059200 prefixEnd_4059200 := by exact prefixLift 4059200
  have htrace : WordTrace (prefixWord ++ tailWord_4059200) baseStart_4059200 baseEnd_4059200 := by
    simpa [prefixWord, tailWord_4059200, baseEnd_4059200] using wordTrace_append hprefix tailTrace_4059200
  have hstable : (prefixWord ++ tailWord_4059200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059200).length < 2 ^ (prefixWord ++ tailWord_4059200).sum := by decide
  have hdescent : baseEnd_4059200 < baseStart_4059200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059201 : List Nat := [1, 2, 5, 1, 2, 1, 3, 3, 1, 2, 2]
def baseStart_4059201 : Nat := 118140960795 + 4059201 * 2 ^ 59
def prefixEnd_4059201 : Nat := 4983230072969 + 3 ^ 40 * 4059201 * 2
def baseEnd_4059201 : Nat := 2084321186211278091119581

theorem tailTrace_4059201 : CollatzResearch.WordTrace tailWord_4059201 prefixEnd_4059201 2084321186211278091119581 := by
  unfold tailWord_4059201
  simp only [CollatzResearch.WordTrace]
  refine ⟨148051223367215508182953457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98700815578143672121968971 148051223367215508182953457)
  ·
    refine ⟨111038417525411631137215093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148051223367215508182953457 111038417525411631137215093)
    ·
      refine ⟨10409851643007340419113915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111038417525411631137215093 10409851643007340419113915)
      ·
        refine ⟨15614777464511010628670873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10409851643007340419113915 15614777464511010628670873)
        ·
          refine ⟨11711083098383257971503155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15614777464511010628670873 11711083098383257971503155)
          ·
            refine ⟨17566624647574886957254733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11711083098383257971503155 17566624647574886957254733)
            ·
              refine ⟨6587484242840582608970525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17566624647574886957254733 6587484242840582608970525)
              ·
                refine ⟨2470306591065218478363947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6587484242840582608970525 2470306591065218478363947)
                ·
                  refine ⟨3705459886597827717545921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2470306591065218478363947 3705459886597827717545921)
                  ·
                    refine ⟨2779094914948370788159441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3705459886597827717545921 2779094914948370788159441)
                    ·
                      refine ⟨2084321186211278091119581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2779094914948370788159441 2084321186211278091119581)
                      ·
                        rfl

theorem cell23_4059201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_4059201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059201 prefixEnd_4059201 := by exact prefixLift 4059201
  have htrace : WordTrace (prefixWord ++ tailWord_4059201) baseStart_4059201 baseEnd_4059201 := by
    simpa [prefixWord, tailWord_4059201, baseEnd_4059201] using wordTrace_append hprefix tailTrace_4059201
  have hstable : (prefixWord ++ tailWord_4059201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059201).length < 2 ^ (prefixWord ++ tailWord_4059201).sum := by decide
  have hdescent : baseEnd_4059201 < baseStart_4059201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059210 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 5, 3, 2]
def baseStart_4059210 : Nat := 118140960795 + 4059210 * 2 ^ 59
def prefixEnd_4059210 : Nat := 4983230072969 + 3 ^ 40 * 4059210 * 2
def baseEnd_4059210 : Nat := 2084325807537168555907039

theorem tailTrace_4059210 : CollatzResearch.WordTrace tailWord_4059210 prefixEnd_4059210 2084325807537168555907039 := by
  unfold tailWord_4059210
  simp only [CollatzResearch.WordTrace]
  refine ⟨37012887906045725680007771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98701034416121935146687389 37012887906045725680007771)
  ·
    refine ⟨55519331859068588520011657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37012887906045725680007771 55519331859068588520011657)
    ·
      refine ⟨41639498894301441390008743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55519331859068588520011657 41639498894301441390008743)
      ·
        refine ⟨62459248341452162085013115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41639498894301441390008743 62459248341452162085013115)
        ·
          refine ⟨93688872512178243127519673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62459248341452162085013115 93688872512178243127519673)
          ·
            refine ⟨70266654384133682345639755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93688872512178243127519673 70266654384133682345639755)
            ·
              refine ⟨105399981576200523518459633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70266654384133682345639755 105399981576200523518459633)
              ·
                refine ⟨79049986182150392638844725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105399981576200523518459633 79049986182150392638844725)
                ·
                  refine ⟨7410936204576599309891693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79049986182150392638844725 7410936204576599309891693)
                  ·
                    refine ⟨2779101076716224741209385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7410936204576599309891693 2779101076716224741209385)
                    ·
                      refine ⟨2084325807537168555907039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2779101076716224741209385 2084325807537168555907039)
                      ·
                        rfl

theorem cell23_4059210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_4059210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059210 prefixEnd_4059210 := by exact prefixLift 4059210
  have htrace : WordTrace (prefixWord ++ tailWord_4059210) baseStart_4059210 baseEnd_4059210 := by
    simpa [prefixWord, tailWord_4059210, baseEnd_4059210] using wordTrace_append hprefix tailTrace_4059210
  have hstable : (prefixWord ++ tailWord_4059210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059210).length < 2 ^ (prefixWord ++ tailWord_4059210).sum := by decide
  have hdescent : baseEnd_4059210 < baseStart_4059210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059218 : List Nat := [3, 2, 2, 1, 4, 1, 3, 2, 1, 2, 2]
def baseStart_4059218 : Nat := 118140960795 + 4059218 * 2 ^ 59
def prefixEnd_4059218 : Nat := 4983230072969 + 3 ^ 40 * 4059218 * 2
def baseEnd_4059218 : Nat := 2084329915382404524607003

theorem tailTrace_4059218 : CollatzResearch.WordTrace tailWord_4059218 prefixEnd_4059218 2084329915382404524607003 := by
  unfold tailWord_4059218
  simp only [CollatzResearch.WordTrace]
  refine ⟨37012960852038480021580577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98701228938769280057548205 37012960852038480021580577)
  ·
    refine ⟨27759720639028860016185433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37012960852038480021580577 27759720639028860016185433)
    ·
      refine ⟨20819790479271645012139075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27759720639028860016185433 20819790479271645012139075)
      ·
        refine ⟨31229685718907467518208613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20819790479271645012139075 31229685718907467518208613)
        ·
          refine ⟨5855566072295150159664115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31229685718907467518208613 5855566072295150159664115)
          ·
            refine ⟨8783349108442725239496173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5855566072295150159664115 8783349108442725239496173)
            ·
              refine ⟨3293755915666021964811065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8783349108442725239496173 3293755915666021964811065)
              ·
                refine ⟨2470316936749516473608299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3293755915666021964811065 2470316936749516473608299)
                ·
                  refine ⟨3705475405124274710412449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2470316936749516473608299 3705475405124274710412449)
                  ·
                    refine ⟨2779106553843206032809337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3705475405124274710412449 2779106553843206032809337)
                    ·
                      refine ⟨2084329915382404524607003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2779106553843206032809337 2084329915382404524607003)
                      ·
                        rfl

theorem cell23_4059218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_4059218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059218 prefixEnd_4059218 := by exact prefixLift 4059218
  have htrace : WordTrace (prefixWord ++ tailWord_4059218) baseStart_4059218 baseEnd_4059218 := by
    simpa [prefixWord, tailWord_4059218, baseEnd_4059218] using wordTrace_append hprefix tailTrace_4059218
  have hstable : (prefixWord ++ tailWord_4059218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059218).length < 2 ^ (prefixWord ++ tailWord_4059218).sum := by decide
  have hdescent : baseEnd_4059218 < baseStart_4059218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059244 : List Nat := [2, 2, 1, 1, 3, 5, 1, 2, 1, 3, 2]
def baseStart_4059244 : Nat := 118140960795 + 4059244 * 2 ^ 59
def prefixEnd_4059244 : Nat := 4983230072969 + 3 ^ 40 * 4059244 * 2
def baseEnd_4059244 : Nat := 2084343265879421422881883

theorem tailTrace_4059244 : CollatzResearch.WordTrace tailWord_4059244 prefixEnd_4059244 2084343265879421422881883 := by
  unfold tailWord_4059244
  simp only [CollatzResearch.WordTrace]
  refine ⟨74026395853029863263384393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98701861137373151017845857 74026395853029863263384393)
  ·
    refine ⟨55519796889772397447538295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74026395853029863263384393 55519796889772397447538295)
    ·
      refine ⟨83279695334658596171307443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55519796889772397447538295 83279695334658596171307443)
      ·
        refine ⟨124919543001987894256961165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83279695334658596171307443 124919543001987894256961165)
        ·
          refine ⟨46844828625745460346360437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124919543001987894256961165 46844828625745460346360437)
          ·
            refine ⟨4391702683663636907471291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46844828625745460346360437 4391702683663636907471291)
            ·
              refine ⟨6587554025495455361206937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4391702683663636907471291 6587554025495455361206937)
              ·
                refine ⟨4940665519121591520905203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6587554025495455361206937 4940665519121591520905203)
                ·
                  refine ⟨7410998278682387281357805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4940665519121591520905203 7410998278682387281357805)
                  ·
                    refine ⟨2779124354505895230509177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7410998278682387281357805 2779124354505895230509177)
                    ·
                      refine ⟨2084343265879421422881883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2779124354505895230509177 2084343265879421422881883)
                      ·
                        rfl

theorem cell23_4059244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 3, 2].length) (baseStart_4059244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059244 prefixEnd_4059244 := by exact prefixLift 4059244
  have htrace : WordTrace (prefixWord ++ tailWord_4059244) baseStart_4059244 baseEnd_4059244 := by
    simpa [prefixWord, tailWord_4059244, baseEnd_4059244] using wordTrace_append hprefix tailTrace_4059244
  have hstable : (prefixWord ++ tailWord_4059244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059244).length < 2 ^ (prefixWord ++ tailWord_4059244).sum := by decide
  have hdescent : baseEnd_4059244 < baseStart_4059244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059257 : List Nat := [1, 2, 1, 3, 4, 2, 1, 2, 1, 4, 2]
def baseStart_4059257 : Nat := 118140960795 + 4059257 * 2 ^ 59
def prefixEnd_4059257 : Nat := 4983230072969 + 3 ^ 40 * 4059257 * 2
def baseEnd_4059257 : Nat := 2084349941127929872019323

theorem tailTrace_4059257 : CollatzResearch.WordTrace tailWord_4059257 prefixEnd_4059257 2084349941127929872019323 := by
  unfold tailWord_4059257
  simp only [CollatzResearch.WordTrace]
  refine ⟨148053265855012629746992025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98702177236675086497994683 148053265855012629746992025)
  ·
    refine ⟨111039949391259472310244019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148053265855012629746992025 111039949391259472310244019)
    ·
      refine ⟨166559924086889208465366029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111039949391259472310244019 166559924086889208465366029)
      ·
        refine ⟨62459971532583453174512261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166559924086889208465366029 62459971532583453174512261)
        ·
          refine ⟨11711244662359397470221049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62459971532583453174512261 11711244662359397470221049)
          ·
            refine ⟨8783433496769548102665787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11711244662359397470221049 8783433496769548102665787)
            ·
              refine ⟨13175150245154322153998681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8783433496769548102665787 13175150245154322153998681)
              ·
                refine ⟨9881362683865741615499011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13175150245154322153998681 9881362683865741615499011)
                ·
                  refine ⟨14822044025798612423248517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9881362683865741615499011 14822044025798612423248517)
                  ·
                    refine ⟨2779133254837239829359097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14822044025798612423248517 2779133254837239829359097)
                    ·
                      refine ⟨2084349941127929872019323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2779133254837239829359097 2084349941127929872019323)
                      ·
                        rfl

theorem cell23_4059257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_4059257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059257 prefixEnd_4059257 := by exact prefixLift 4059257
  have htrace : WordTrace (prefixWord ++ tailWord_4059257) baseStart_4059257 baseEnd_4059257 := by
    simpa [prefixWord, tailWord_4059257, baseEnd_4059257] using wordTrace_append hprefix tailTrace_4059257
  have hstable : (prefixWord ++ tailWord_4059257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059257).length < 2 ^ (prefixWord ++ tailWord_4059257).sum := by decide
  have hdescent : baseEnd_4059257 < baseStart_4059257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059274 : List Nat := [3, 1, 2, 3, 1, 2, 1, 4, 2, 2, 2]
def baseStart_4059274 : Nat := 118140960795 + 4059274 * 2 ^ 59
def prefixEnd_4059274 : Nat := 4983230072969 + 3 ^ 40 * 4059274 * 2
def baseEnd_4059274 : Nat := 2084358670299056305506745

theorem tailTrace_4059274 : CollatzResearch.WordTrace tailWord_4059274 prefixEnd_4059274 2084358670299056305506745 := by
  unfold tailWord_4059274
  simp only [CollatzResearch.WordTrace]
  refine ⟨37013471473987760412590219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98702590597300694433573917 37013471473987760412590219)
  ·
    refine ⟨55520207210981640618885329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37013471473987760412590219 55520207210981640618885329)
    ·
      refine ⟨41640155408236230464163997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55520207210981640618885329 41640155408236230464163997)
      ·
        refine ⟨15615058278088586424061499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41640155408236230464163997 15615058278088586424061499)
        ·
          refine ⟨23422587417132879636092249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15615058278088586424061499 23422587417132879636092249)
          ·
            refine ⟨17566940562849659727069187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23422587417132879636092249 17566940562849659727069187)
            ·
              refine ⟨26350410844274489590603781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17566940562849659727069187 26350410844274489590603781)
              ·
                refine ⟨4940702033301466798238209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26350410844274489590603781 4940702033301466798238209)
                ·
                  refine ⟨3705526524976100098678657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4940702033301466798238209 3705526524976100098678657)
                  ·
                    refine ⟨2779144893732075074008993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3705526524976100098678657 2779144893732075074008993)
                    ·
                      refine ⟨2084358670299056305506745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2779144893732075074008993 2084358670299056305506745)
                      ·
                        rfl

theorem cell23_4059274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_4059274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059274 prefixEnd_4059274 := by exact prefixLift 4059274
  have htrace : WordTrace (prefixWord ++ tailWord_4059274) baseStart_4059274 baseEnd_4059274 := by
    simpa [prefixWord, tailWord_4059274, baseEnd_4059274] using wordTrace_append hprefix tailTrace_4059274
  have hstable : (prefixWord ++ tailWord_4059274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059274).length < 2 ^ (prefixWord ++ tailWord_4059274).sum := by decide
  have hdescent : baseEnd_4059274 < baseStart_4059274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059280 : List Nat := [2, 1, 1, 1, 1, 1, 7, 4, 5]
def baseStart_4059280 : Nat := 118140960795 + 4059280 * 2 ^ 59
def prefixEnd_4059280 : Nat := 4983230072969 + 3 ^ 40 * 4059280 * 2
def baseEnd_4059280 : Nat := 231595750131442586892413

theorem tailTrace_4059280 : CollatzResearch.WordTrace tailWord_4059280 prefixEnd_4059280 231595750131442586892413 := by
  unfold tailWord_4059280
  simp only [CollatzResearch.WordTrace]
  refine ⟨74027052366964652337539647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98702736489286203116719529 74027052366964652337539647)
  ·
    refine ⟨111040578550446978506309471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74027052366964652337539647 111040578550446978506309471)
    ·
      refine ⟨166560867825670467759464207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111040578550446978506309471 166560867825670467759464207)
      ·
        refine ⟨249841301738505701639196311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166560867825670467759464207 249841301738505701639196311)
        ·
          refine ⟨374761952607758552458794467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249841301738505701639196311 374761952607758552458794467)
          ·
            refine ⟨562142928911637828688191701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374761952607758552458794467 562142928911637828688191701)
            ·
              refine ⟨13175224896366511609879493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 562142928911637828688191701 13175224896366511609879493)
              ·
                refine ⟨2470354668068720926852405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13175224896366511609879493 2470354668068720926852405)
                ·
                  refine ⟨231595750131442586892413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2470354668068720926852405 231595750131442586892413)
                  ·
                    rfl

theorem cell23_4059280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 5].length) (baseStart_4059280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059280 prefixEnd_4059280 := by exact prefixLift 4059280
  have htrace : WordTrace (prefixWord ++ tailWord_4059280) baseStart_4059280 baseEnd_4059280 := by
    simpa [prefixWord, tailWord_4059280, baseEnd_4059280] using wordTrace_append hprefix tailTrace_4059280
  have hstable : (prefixWord ++ tailWord_4059280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059280).length < 2 ^ (prefixWord ++ tailWord_4059280).sum := by decide
  have hdescent : baseEnd_4059280 < baseStart_4059280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059333 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 2, 3, 5]
def baseStart_4059333 : Nat := 118140960795 + 4059333 * 2 ^ 59
def prefixEnd_4059333 : Nat := 4983230072969 + 3 ^ 40 * 4059333 * 2
def baseEnd_4059333 : Nat := 2084388965657671574668973

theorem tailTrace_4059333 : CollatzResearch.WordTrace tailWord_4059333 prefixEnd_4059333 2084388965657671574668973 := by
  unfold tailWord_4059333
  simp only [CollatzResearch.WordTrace]
  refine ⟨148056037802737294726758653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98704025201824863151172435 148056037802737294726758653)
  ·
    refine ⟨55521014176026485522534495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148056037802737294726758653 55521014176026485522534495)
    ·
      refine ⟨83281521264039728283801743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55521014176026485522534495 83281521264039728283801743)
      ·
        refine ⟨124922281896059592425702615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83281521264039728283801743 124922281896059592425702615)
        ·
          refine ⟨187383422844089388638553923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124922281896059592425702615 187383422844089388638553923)
          ·
            refine ⟨281075134266134082957830885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187383422844089388638553923 281075134266134082957830885)
            ·
              refine ⟨52701587674900140554593291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281075134266134082957830885 52701587674900140554593291)
              ·
                refine ⟨79052381512350210831889937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52701587674900140554593291 79052381512350210831889937)
                ·
                  refine ⟨59289286134262658123917453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79052381512350210831889937 59289286134262658123917453)
                  ·
                    refine ⟨22233482300348496796469045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59289286134262658123917453 22233482300348496796469045)
                    ·
                      refine ⟨2084388965657671574668973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22233482300348496796469045 2084388965657671574668973)
                      ·
                        rfl

theorem cell23_4059333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_4059333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059333 prefixEnd_4059333 := by exact prefixLift 4059333
  have htrace : WordTrace (prefixWord ++ tailWord_4059333) baseStart_4059333 baseEnd_4059333 := by
    simpa [prefixWord, tailWord_4059333, baseEnd_4059333] using wordTrace_append hprefix tailTrace_4059333
  have hstable : (prefixWord ++ tailWord_4059333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059333).length < 2 ^ (prefixWord ++ tailWord_4059333).sum := by decide
  have hdescent : baseEnd_4059333 < baseStart_4059333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059343 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 6]
def baseStart_4059343 : Nat := 118140960795 + 4059343 * 2 ^ 59
def prefixEnd_4059343 : Nat := 4983230072969 + 3 ^ 40 * 4059343 * 2
def baseEnd_4059343 : Nat := 2084394100464216535543927

theorem tailTrace_4059343 : CollatzResearch.WordTrace tailWord_4059343 prefixEnd_4059343 2084394100464216535543927 := by
  unfold tailWord_4059343
  simp only [CollatzResearch.WordTrace]
  refine ⟨148056402532701066434622683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98704268355134044289748455 148056402532701066434622683)
  ·
    refine ⟨222084603799051599651934025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148056402532701066434622683 222084603799051599651934025)
    ·
      refine ⟨166563452849288699738950519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222084603799051599651934025 166563452849288699738950519)
      ·
        refine ⟨249845179273933049608425779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166563452849288699738950519 249845179273933049608425779)
        ·
          refine ⟨374767768910899574412638669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249845179273933049608425779 374767768910899574412638669)
          ·
            refine ⟨140537913341587340404739501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374767768910899574412638669 140537913341587340404739501)
            ·
              refine ⟨52701717503095252651777313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140537913341587340404739501 52701717503095252651777313)
              ·
                refine ⟨39526288127321439488832985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52701717503095252651777313 39526288127321439488832985)
                ·
                  refine ⟨29644716095491079616624739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39526288127321439488832985 29644716095491079616624739)
                  ·
                    refine ⟨44467074143236619424937109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29644716095491079616624739 44467074143236619424937109)
                    ·
                      refine ⟨2084394100464216535543927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44467074143236619424937109 2084394100464216535543927)
                      ·
                        rfl

theorem cell23_4059343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_4059343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059343 prefixEnd_4059343 := by exact prefixLift 4059343
  have htrace : WordTrace (prefixWord ++ tailWord_4059343) baseStart_4059343 baseEnd_4059343 := by
    simpa [prefixWord, tailWord_4059343, baseEnd_4059343] using wordTrace_append hprefix tailTrace_4059343
  have hstable : (prefixWord ++ tailWord_4059343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059343).length < 2 ^ (prefixWord ++ tailWord_4059343).sum := by decide
  have hdescent : baseEnd_4059343 < baseStart_4059343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059367 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 3]
def baseStart_4059367 : Nat := 118140960795 + 4059367 * 2 ^ 59
def prefixEnd_4059367 : Nat := 4983230072969 + 3 ^ 40 * 4059367 * 2
def baseEnd_4059367 : Nat := 2084406423999924441643817

theorem tailTrace_4059367 : CollatzResearch.WordTrace tailWord_4059367 prefixEnd_4059367 2084406423999924441643817 := by
  unfold tailWord_4059367
  simp only [CollatzResearch.WordTrace]
  refine ⟨148057277884614118533496355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98704851923076079022330903 148057277884614118533496355)
  ·
    refine ⟨222085916826921177800244533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148057277884614118533496355 222085916826921177800244533)
    ·
      refine ⟨20820554702523860418772925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222085916826921177800244533 20820554702523860418772925)
      ·
        refine ⟨7807708013446447657039847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20820554702523860418772925 7807708013446447657039847)
        ·
          refine ⟨11711562020169671485559771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7807708013446447657039847 11711562020169671485559771)
          ·
            refine ⟨17567343030254507228339657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11711562020169671485559771 17567343030254507228339657)
            ·
              refine ⟨13175507272690880421254743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17567343030254507228339657 13175507272690880421254743)
              ·
                refine ⟨19763260909036320631882115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13175507272690880421254743 19763260909036320631882115)
                ·
                  refine ⟨29644891363554480947823173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19763260909036320631882115 29644891363554480947823173)
                  ·
                    refine ⟨5558417130666465177716845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29644891363554480947823173 5558417130666465177716845)
                    ·
                      refine ⟨2084406423999924441643817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5558417130666465177716845 2084406423999924441643817)
                      ·
                        rfl

theorem cell23_4059367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_4059367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059367 prefixEnd_4059367 := by exact prefixLift 4059367
  have htrace : WordTrace (prefixWord ++ tailWord_4059367) baseStart_4059367 baseEnd_4059367 := by
    simpa [prefixWord, tailWord_4059367, baseEnd_4059367] using wordTrace_append hprefix tailTrace_4059367
  have hstable : (prefixWord ++ tailWord_4059367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059367).length < 2 ^ (prefixWord ++ tailWord_4059367).sum := by decide
  have hdescent : baseEnd_4059367 < baseStart_4059367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059397 : List Nat := [1, 3, 1, 1, 2, 1, 2, 5, 3, 1, 3]
def baseStart_4059397 : Nat := 118140960795 + 4059397 * 2 ^ 59
def prefixEnd_4059397 : Nat := 4983230072969 + 3 ^ 40 * 4059397 * 2
def baseEnd_4059397 : Nat := 2084421828419559324268679

theorem tailTrace_4059397 : CollatzResearch.WordTrace tailWord_4059397 prefixEnd_4059397 2084421828419559324268679 := by
  unfold tailWord_4059397
  simp only [CollatzResearch.WordTrace]
  refine ⟨148058372074505433657088445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98705581383003622438058963 148058372074505433657088445)
  ·
    refine ⟨55521889527939537621408167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148058372074505433657088445 55521889527939537621408167)
    ·
      refine ⟨83282834291909306432112251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55521889527939537621408167 83282834291909306432112251)
      ·
        refine ⟨124924251437863959648168377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83282834291909306432112251 124924251437863959648168377)
        ·
          refine ⟨93693188578397969736126283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124924251437863959648168377 93693188578397969736126283)
          ·
            refine ⟨140539782867596954604189425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93693188578397969736126283 140539782867596954604189425)
            ·
              refine ⟨105404837150697715953142069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140539782867596954604189425 105404837150697715953142069)
              ·
                refine ⟨9881703482877910870607069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105404837150697715953142069 9881703482877910870607069)
                ·
                  refine ⟨3705638806079216576477651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9881703482877910870607069 3705638806079216576477651)
                  ·
                    refine ⟨5558458209118824864716477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3705638806079216576477651 5558458209118824864716477)
                    ·
                      refine ⟨2084421828419559324268679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5558458209118824864716477 2084421828419559324268679)
                      ·
                        rfl

theorem cell23_4059397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 1, 3].length) (baseStart_4059397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059397 prefixEnd_4059397 := by exact prefixLift 4059397
  have htrace : WordTrace (prefixWord ++ tailWord_4059397) baseStart_4059397 baseEnd_4059397 := by
    simpa [prefixWord, tailWord_4059397, baseEnd_4059397] using wordTrace_append hprefix tailTrace_4059397
  have hstable : (prefixWord ++ tailWord_4059397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059397).length < 2 ^ (prefixWord ++ tailWord_4059397).sum := by decide
  have hdescent : baseEnd_4059397 < baseStart_4059397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059424 : List Nat := [2, 1, 1, 5, 2, 1, 1, 3, 2, 3, 2]
def baseStart_4059424 : Nat := 118140960795 + 4059424 * 2 ^ 59
def prefixEnd_4059424 : Nat := 4983230072969 + 3 ^ 40 * 4059424 * 2
def baseEnd_4059424 : Nat := 2084435692397230718631055

theorem tailTrace_4059424 : CollatzResearch.WordTrace tailWord_4059424 prefixEnd_4059424 2084435692397230718631055 := by
  unfold tailWord_4059424
  simp only [CollatzResearch.WordTrace]
  refine ⟨74029678422703808634160663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98706237896938411512214217 74029678422703808634160663)
  ·
    refine ⟨111044517634055712951240995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74029678422703808634160663 111044517634055712951240995)
    ·
      refine ⟨166566776451083569426861493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111044517634055712951240995 166566776451083569426861493)
      ·
        refine ⟨15615635292289084633768265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166566776451083569426861493 15615635292289084633768265)
        ·
          refine ⟨11711726469216813475326199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15615635292289084633768265 11711726469216813475326199)
          ·
            refine ⟨17567589703825220212989299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11711726469216813475326199 17567589703825220212989299)
            ·
              refine ⟨26351384555737830319483949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17567589703825220212989299 26351384555737830319483949)
              ·
                refine ⟨9881769208401686369806481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26351384555737830319483949 9881769208401686369806481)
                ·
                  refine ⟨7411326906301264777354861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9881769208401686369806481 7411326906301264777354861)
                  ·
                    refine ⟨2779247589862974291508073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7411326906301264777354861 2779247589862974291508073)
                    ·
                      refine ⟨2084435692397230718631055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2779247589862974291508073 2084435692397230718631055)
                      ·
                        rfl

theorem cell23_4059424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_4059424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059424 prefixEnd_4059424 := by exact prefixLift 4059424
  have htrace : WordTrace (prefixWord ++ tailWord_4059424) baseStart_4059424 baseEnd_4059424 := by
    simpa [prefixWord, tailWord_4059424, baseEnd_4059424] using wordTrace_append hprefix tailTrace_4059424
  have hstable : (prefixWord ++ tailWord_4059424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059424).length < 2 ^ (prefixWord ++ tailWord_4059424).sum := by decide
  have hdescent : baseEnd_4059424 < baseStart_4059424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059440 : List Nat := [2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 5]
def baseStart_4059440 : Nat := 118140960795 + 4059440 * 2 ^ 59
def prefixEnd_4059440 : Nat := 4983230072969 + 3 ^ 40 * 4059440 * 2
def baseEnd_4059440 : Nat := 2084443908087702656030981

theorem tailTrace_4059440 : CollatzResearch.WordTrace tailWord_4059440 prefixEnd_4059440 2084443908087702656030981 := by
  unfold tailWord_4059440
  simp only [CollatzResearch.WordTrace]
  refine ⟨74029970206674826000451887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98706626942233101333935849 74029970206674826000451887)
  ·
    refine ⟨111044955310012239000677831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74029970206674826000451887 111044955310012239000677831)
    ·
      refine ⟨166567432965018358501016747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111044955310012239000677831 166567432965018358501016747)
      ·
        refine ⟨249851149447527537751525121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166567432965018358501016747 249851149447527537751525121)
        ·
          refine ⟨187388362085645653313643841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249851149447527537751525121 187388362085645653313643841)
          ·
            refine ⟨140541271564234239985232881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187388362085645653313643841 140541271564234239985232881)
            ·
              refine ⟨105405953673175679988924661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140541271564234239985232881 105405953673175679988924661)
              ·
                refine ⟨9881808156860219998961687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105405953673175679988924661 9881808156860219998961687)
                ·
                  refine ⟨14822712235290329998442531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9881808156860219998961687 14822712235290329998442531)
                  ·
                    refine ⟨22234068352935494997663797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14822712235290329998442531 22234068352935494997663797)
                    ·
                      refine ⟨2084443908087702656030981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22234068352935494997663797 2084443908087702656030981)
                      ·
                        rfl

theorem cell23_4059440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 5].length) (baseStart_4059440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059440 prefixEnd_4059440 := by exact prefixLift 4059440
  have htrace : WordTrace (prefixWord ++ tailWord_4059440) baseStart_4059440 baseEnd_4059440 := by
    simpa [prefixWord, tailWord_4059440, baseEnd_4059440] using wordTrace_append hprefix tailTrace_4059440
  have hstable : (prefixWord ++ tailWord_4059440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059440).length < 2 ^ (prefixWord ++ tailWord_4059440).sum := by decide
  have hdescent : baseEnd_4059440 < baseStart_4059440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059487 : List Nat := [1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 3]
def baseStart_4059487 : Nat := 118140960795 + 4059487 * 2 ^ 59
def prefixEnd_4059487 : Nat := 4983230072969 + 3 ^ 40 * 4059487 * 2
def baseEnd_4059487 : Nat := 2084468041678463972143265

theorem tailTrace_4059487 : CollatzResearch.WordTrace tailWord_4059487 prefixEnd_4059487 2084468041678463972143265 := by
  unfold tailWord_4059487
  simp only [CollatzResearch.WordTrace]
  refine ⟨148061654644179379027864715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98707769762786252685243143 148061654644179379027864715)
  ·
    refine ⟨222092481966269068541797073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148061654644179379027864715 222092481966269068541797073)
    ·
      refine ⟨166569361474701801406347805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222092481966269068541797073 166569361474701801406347805)
      ·
        refine ⟨62463510553013175527380427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166569361474701801406347805 62463510553013175527380427)
        ·
          refine ⟨93695265829519763291070641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62463510553013175527380427 93695265829519763291070641)
          ·
            refine ⟨70271449372139822468302981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93695265829519763291070641 70271449372139822468302981)
            ·
              refine ⟨13175896757276216712806809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70271449372139822468302981 13175896757276216712806809)
              ·
                refine ⟨9881922567957162534605107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13175896757276216712806809 9881922567957162534605107)
                ·
                  refine ⟨14822883851935743801907661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9881922567957162534605107 14822883851935743801907661)
                  ·
                    refine ⟨5558581444475903925715373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14822883851935743801907661 5558581444475903925715373)
                    ·
                      refine ⟨2084468041678463972143265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5558581444475903925715373 2084468041678463972143265)
                      ·
                        rfl

theorem cell23_4059487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_4059487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059487 prefixEnd_4059487 := by exact prefixLift 4059487
  have htrace : WordTrace (prefixWord ++ tailWord_4059487) baseStart_4059487 baseEnd_4059487 := by
    simpa [prefixWord, tailWord_4059487, baseEnd_4059487] using wordTrace_append hprefix tailTrace_4059487
  have hstable : (prefixWord ++ tailWord_4059487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059487).length < 2 ^ (prefixWord ++ tailWord_4059487).sum := by decide
  have hdescent : baseEnd_4059487 < baseStart_4059487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059488 : List Nat := [2, 1, 1, 3, 6, 1, 2, 1, 1, 1, 4]
def baseStart_4059488 : Nat := 118140960795 + 4059488 * 2 ^ 59
def prefixEnd_4059488 : Nat := 4983230072969 + 3 ^ 40 * 4059488 * 2
def baseEnd_4059488 : Nat := 2084468555159118468230761

theorem tailTrace_4059488 : CollatzResearch.WordTrace tailWord_4059488 prefixEnd_4059488 2084468555159118468230761 := by
  unfold tailWord_4059488
  simp only [CollatzResearch.WordTrace]
  refine ⟨74030845558587878099325559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98707794078117170799100745 74030845558587878099325559)
  ·
    refine ⟨111046268337881817148988339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74030845558587878099325559 111046268337881817148988339)
    ·
      refine ⟨166569402506822725723482509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111046268337881817148988339 166569402506822725723482509)
      ·
        refine ⟨62463525940058522146305941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166569402506822725723482509 62463525940058522146305941)
        ·
          refine ⟨2927977778440243225608091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62463525940058522146305941 2927977778440243225608091)
          ·
            refine ⟨4391966667660364838412137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2927977778440243225608091 4391966667660364838412137)
            ·
              refine ⟨3293975000745273628809103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4391966667660364838412137 3293975000745273628809103)
              ·
                refine ⟨4940962501117910443213655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3293975000745273628809103 4940962501117910443213655)
                ·
                  refine ⟨7411443751676865664820483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4940962501117910443213655 7411443751676865664820483)
                  ·
                    refine ⟨11117165627515298497230725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7411443751676865664820483 11117165627515298497230725)
                    ·
                      refine ⟨2084468555159118468230761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11117165627515298497230725 2084468555159118468230761)
                      ·
                        rfl

theorem cell23_4059488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_4059488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059488 prefixEnd_4059488 := by exact prefixLift 4059488
  have htrace : WordTrace (prefixWord ++ tailWord_4059488) baseStart_4059488 baseEnd_4059488 := by
    simpa [prefixWord, tailWord_4059488, baseEnd_4059488] using wordTrace_append hprefix tailTrace_4059488
  have hstable : (prefixWord ++ tailWord_4059488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059488).length < 2 ^ (prefixWord ++ tailWord_4059488).sum := by decide
  have hdescent : baseEnd_4059488 < baseStart_4059488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059504 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 4, 1, 3]
def baseStart_4059504 : Nat := 118140960795 + 4059504 * 2 ^ 59
def prefixEnd_4059504 : Nat := 4983230072969 + 3 ^ 40 * 4059504 * 2
def baseEnd_4059504 : Nat := 2084476770849590405630687

theorem tailTrace_4059504 : CollatzResearch.WordTrace tailWord_4059504 prefixEnd_4059504 2084476770849590405630687 := by
  unfold tailWord_4059504
  simp only [CollatzResearch.WordTrace]
  refine ⟨74031137342558895465616783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98708183123411860620822377 74031137342558895465616783)
  ·
    refine ⟨111046706013838343198425175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74031137342558895465616783 111046706013838343198425175)
    ·
      refine ⟨166570059020757514797637763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111046706013838343198425175 166570059020757514797637763)
      ·
        refine ⟨249855088531136272196456645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166570059020757514797637763 249855088531136272196456645)
        ·
          refine ⟨46847829099588051036835621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249855088531136272196456645 46847829099588051036835621)
          ·
            refine ⟨8783967956172759569406679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46847829099588051036835621 8783967956172759569406679)
            ·
              refine ⟨13175951934259139354110019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8783967956172759569406679 13175951934259139354110019)
              ·
                refine ⟨19763927901388709031165029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13175951934259139354110019 19763927901388709031165029)
                ·
                  refine ⟨3705736481510382943343443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19763927901388709031165029 3705736481510382943343443)
                  ·
                    refine ⟨5558604722265574415015165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3705736481510382943343443 5558604722265574415015165)
                    ·
                      refine ⟨2084476770849590405630687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5558604722265574415015165 2084476770849590405630687)
                      ·
                        rfl

theorem cell23_4059504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 4, 1, 3].length) (baseStart_4059504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059504 prefixEnd_4059504 := by exact prefixLift 4059504
  have htrace : WordTrace (prefixWord ++ tailWord_4059504) baseStart_4059504 baseEnd_4059504 := by
    simpa [prefixWord, tailWord_4059504, baseEnd_4059504] using wordTrace_append hprefix tailTrace_4059504
  have hstable : (prefixWord ++ tailWord_4059504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059504).length < 2 ^ (prefixWord ++ tailWord_4059504).sum := by decide
  have hdescent : baseEnd_4059504 < baseStart_4059504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059521 : List Nat := [1, 2, 4, 3, 1, 3, 1, 1, 1, 3, 3]
def baseStart_4059521 : Nat := 118140960795 + 4059521 * 2 ^ 59
def prefixEnd_4059521 : Nat := 4983230072969 + 3 ^ 40 * 4059521 * 2
def baseEnd_4059521 : Nat := 2084485500020716839118109

theorem tailTrace_4059521 : CollatzResearch.WordTrace tailWord_4059521 prefixEnd_4059521 2084485500020716839118109 := by
  unfold tailWord_4059521
  simp only [CollatzResearch.WordTrace]
  refine ⟨148062894726056202834602417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98708596484037468556401611 148062894726056202834602417)
  ·
    refine ⟨111047171044542152125951813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148062894726056202834602417 111047171044542152125951813)
    ·
      refine ⟨20821344570851653523615965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111047171044542152125951813 20821344570851653523615965)
      ·
        refine ⟨7808004214069370071355987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20821344570851653523615965 7808004214069370071355987)
        ·
          refine ⟨11712006321104055107033981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7808004214069370071355987 11712006321104055107033981)
          ·
            refine ⟨4392002370414020665137743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11712006321104055107033981 4392002370414020665137743)
            ·
              refine ⟨6588003555621030997706615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4392002370414020665137743 6588003555621030997706615)
              ·
                refine ⟨9882005333431546496559923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6588003555621030997706615 9882005333431546496559923)
                ·
                  refine ⟨14823008000147319744839885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9882005333431546496559923 14823008000147319744839885)
                  ·
                    refine ⟨5558628000055244904314957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14823008000147319744839885 5558628000055244904314957)
                    ·
                      refine ⟨2084485500020716839118109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5558628000055244904314957 2084485500020716839118109)
                      ·
                        rfl

theorem cell23_4059521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_4059521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059521 prefixEnd_4059521 := by exact prefixLift 4059521
  have htrace : WordTrace (prefixWord ++ tailWord_4059521) baseStart_4059521 baseEnd_4059521 := by
    simpa [prefixWord, tailWord_4059521, baseEnd_4059521] using wordTrace_append hprefix tailTrace_4059521
  have hstable : (prefixWord ++ tailWord_4059521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059521).length < 2 ^ (prefixWord ++ tailWord_4059521).sum := by decide
  have hdescent : baseEnd_4059521 < baseStart_4059521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059531 : List Nat := [1, 1, 1, 1, 4, 5, 2, 2, 1, 3, 2]
def baseStart_4059531 : Nat := 118140960795 + 4059531 * 2 ^ 59
def prefixEnd_4059531 : Nat := 4983230072969 + 3 ^ 40 * 4059531 * 2
def baseEnd_4059531 : Nat := 2084490634827261799993063

theorem tailTrace_4059531 : CollatzResearch.WordTrace tailWord_4059531 prefixEnd_4059531 2084490634827261799993063 := by
  unfold tailWord_4059531
  simp only [CollatzResearch.WordTrace]
  refine ⟨148063259456019974542466447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98708839637346649694977631 148063259456019974542466447)
  ·
    refine ⟨222094889184029961813699671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148063259456019974542466447 222094889184029961813699671)
    ·
      refine ⟨333142333776044942720549507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222094889184029961813699671 333142333776044942720549507)
      ·
        refine ⟨499713500664067414080824261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333142333776044942720549507 499713500664067414080824261)
        ·
          refine ⟨93696281374512640140154549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 499713500664067414080824261 93696281374512640140154549)
          ·
            refine ⟨8784026378860560013139489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93696281374512640140154549 8784026378860560013139489)
            ·
              refine ⟨6588019784145420009854617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8784026378860560013139489 6588019784145420009854617)
              ·
                refine ⟨4941014838109065007390963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6588019784145420009854617 4941014838109065007390963)
                ·
                  refine ⟨7411522257163597511086445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4941014838109065007390963 7411522257163597511086445)
                  ·
                    refine ⟨2779320846436349066657417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7411522257163597511086445 2779320846436349066657417)
                    ·
                      refine ⟨2084490634827261799993063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2779320846436349066657417 2084490634827261799993063)
                      ·
                        rfl

theorem cell23_4059531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 3, 2].length) (baseStart_4059531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059531 prefixEnd_4059531 := by exact prefixLift 4059531
  have htrace : WordTrace (prefixWord ++ tailWord_4059531) baseStart_4059531 baseEnd_4059531 := by
    simpa [prefixWord, tailWord_4059531, baseEnd_4059531] using wordTrace_append hprefix tailTrace_4059531
  have hstable : (prefixWord ++ tailWord_4059531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059531).length < 2 ^ (prefixWord ++ tailWord_4059531).sum := by decide
  have hdescent : baseEnd_4059531 < baseStart_4059531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059668 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_4059668 : Nat := 118140960795 + 4059668 * 2 ^ 59
def prefixEnd_4059668 : Nat := 4983230072969 + 3 ^ 40 * 4059668 * 2
def baseEnd_4059668 : Nat := 2084560981676927763979933

theorem tailTrace_4059668 : CollatzResearch.WordTrace tailWord_4059668 prefixEnd_4059668 2084560981676927763979933 := by
  unfold tailWord_4059668
  simp only [CollatzResearch.WordTrace]
  refine ⟨74034128128261823470101829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98712170837682431293469105 74034128128261823470101829)
  ·
    refine ⟨13881399024049091900644093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74034128128261823470101829 13881399024049091900644093)
    ·
      refine ⟨5205524634018409462741535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13881399024049091900644093 5205524634018409462741535)
      ·
        refine ⟨7808286951027614194112303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5205524634018409462741535 7808286951027614194112303)
        ·
          refine ⟨11712430426541421291168455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7808286951027614194112303 11712430426541421291168455)
          ·
            refine ⟨17568645639812131936752683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11712430426541421291168455 17568645639812131936752683)
            ·
              refine ⟨26352968459718197905129025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17568645639812131936752683 26352968459718197905129025)
              ·
                refine ⟨19764726344788648428846769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26352968459718197905129025 19764726344788648428846769)
                ·
                  refine ⟨14823544758591486321635077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19764726344788648428846769 14823544758591486321635077)
                  ·
                    refine ⟨2779414642235903685306577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14823544758591486321635077 2779414642235903685306577)
                    ·
                      refine ⟨2084560981676927763979933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2779414642235903685306577 2084560981676927763979933)
                      ·
                        rfl

theorem cell23_4059668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_4059668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059668 prefixEnd_4059668 := by exact prefixLift 4059668
  have htrace : WordTrace (prefixWord ++ tailWord_4059668) baseStart_4059668 baseEnd_4059668 := by
    simpa [prefixWord, tailWord_4059668, baseEnd_4059668] using wordTrace_append hprefix tailTrace_4059668
  have hstable : (prefixWord ++ tailWord_4059668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059668).length < 2 ^ (prefixWord ++ tailWord_4059668).sum := by decide
  have hdescent : baseEnd_4059668 < baseStart_4059668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059674 : List Nat := [3, 1, 1, 3, 1, 1, 5, 2, 6]
def baseStart_4059674 : Nat := 118140960795 + 4059674 * 2 ^ 59
def prefixEnd_4059674 : Nat := 4983230072969 + 3 ^ 40 * 4059674 * 2
def baseEnd_4059674 : Nat := 231618229173428304500545

theorem tailTrace_4059674 : CollatzResearch.WordTrace tailWord_4059674 prefixEnd_4059674 231618229173428304500545 := by
  unfold tailWord_4059674
  simp only [CollatzResearch.WordTrace]
  refine ⟨37017118773625477491230519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98712316729667939976614717 37017118773625477491230519)
  ·
    refine ⟨55525678160438216236845779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37017118773625477491230519 55525678160438216236845779)
    ·
      refine ⟨83288517240657324355268669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55525678160438216236845779 83288517240657324355268669)
      ·
        refine ⟨31233193965246496633225751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83288517240657324355268669 31233193965246496633225751)
        ·
          refine ⟨46849790947869744949838627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31233193965246496633225751 46849790947869744949838627)
          ·
            refine ⟨70274686421804617424757941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46849790947869744949838627 70274686421804617424757941)
            ·
              refine ⟨6588251852044182883571057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70274686421804617424757941 6588251852044182883571057)
              ·
                refine ⟨4941188889033137162678293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6588251852044182883571057 4941188889033137162678293)
                ·
                  refine ⟨231618229173428304500545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4941188889033137162678293 231618229173428304500545)
                  ·
                    rfl

theorem cell23_4059674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 6].length) (baseStart_4059674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059674 prefixEnd_4059674 := by exact prefixLift 4059674
  have htrace : WordTrace (prefixWord ++ tailWord_4059674) baseStart_4059674 baseEnd_4059674 := by
    simpa [prefixWord, tailWord_4059674, baseEnd_4059674] using wordTrace_append hprefix tailTrace_4059674
  have hstable : (prefixWord ++ tailWord_4059674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059674).length < 2 ^ (prefixWord ++ tailWord_4059674).sum := by decide
  have hdescent : baseEnd_4059674 < baseStart_4059674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059697 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 2, 1, 7]
def baseStart_4059697 : Nat := 118140960795 + 4059697 * 2 ^ 59
def prefixEnd_4059697 : Nat := 4983230072969 + 3 ^ 40 * 4059697 * 2
def baseEnd_4059697 : Nat := 2084575872615908150517299

theorem tailTrace_4059697 : CollatzResearch.WordTrace tailWord_4059697 prefixEnd_4059697 2084575872615908150517299 := by
  unfold tailWord_4059697
  simp only [CollatzResearch.WordTrace]
  refine ⟨148069313973418584893009345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98712875982279056595339563 148069313973418584893009345)
  ·
    refine ⟨111051985480063938669757009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148069313973418584893009345 111051985480063938669757009)
    ·
      refine ⟨83288989110047954002317757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111051985480063938669757009 83288989110047954002317757)
      ·
        refine ⟨31233370916267982750869159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83288989110047954002317757 31233370916267982750869159)
        ·
          refine ⟨46850056374401974126303739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31233370916267982750869159 46850056374401974126303739)
          ·
            refine ⟨70275084561602961189455609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46850056374401974126303739 70275084561602961189455609)
            ·
              refine ⟨52706313421202220892091707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70275084561602961189455609 52706313421202220892091707)
              ·
                refine ⟨79059470131803331338137561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52706313421202220892091707 79059470131803331338137561)
                ·
                  refine ⟨59294602598852498503603171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79059470131803331338137561 59294602598852498503603171)
                  ·
                    refine ⟨88941903898278747755404757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59294602598852498503603171 88941903898278747755404757)
                    ·
                      refine ⟨2084575872615908150517299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88941903898278747755404757 2084575872615908150517299)
                      ·
                        rfl

theorem cell23_4059697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_4059697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059697 prefixEnd_4059697 := by exact prefixLift 4059697
  have htrace : WordTrace (prefixWord ++ tailWord_4059697) baseStart_4059697 baseEnd_4059697 := by
    simpa [prefixWord, tailWord_4059697, baseEnd_4059697] using wordTrace_append hprefix tailTrace_4059697
  have hstable : (prefixWord ++ tailWord_4059697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059697).length < 2 ^ (prefixWord ++ tailWord_4059697).sum := by decide
  have hdescent : baseEnd_4059697 < baseStart_4059697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059701 : List Nat := [1, 3, 3, 1, 1, 2, 1, 4, 3, 1, 3]
def baseStart_4059701 : Nat := 118140960795 + 4059701 * 2 ^ 59
def prefixEnd_4059701 : Nat := 4983230072969 + 3 ^ 40 * 4059701 * 2
def baseEnd_4059701 : Nat := 2084577926538526134867281

theorem tailTrace_4059701 : CollatzResearch.WordTrace tailWord_4059701 prefixEnd_4059701 2084577926538526134867281 := by
  unfold tailWord_4059701
  simp only [CollatzResearch.WordTrace]
  refine ⟨148069459865404093576154957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98712973243602729050769971 148069459865404093576154957)
  ·
    refine ⟨55526047449526535091058109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148069459865404093576154957 55526047449526535091058109)
    ·
      refine ⟨20822267793572450659146791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55526047449526535091058109 20822267793572450659146791)
      ·
        refine ⟨31233401690358675988720187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20822267793572450659146791 31233401690358675988720187)
        ·
          refine ⟨46850102535538013983080281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31233401690358675988720187 46850102535538013983080281)
          ·
            refine ⟨35137576901653510487310211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46850102535538013983080281 35137576901653510487310211)
            ·
              refine ⟨52706365352480265730965317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35137576901653510487310211 52706365352480265730965317)
              ·
                refine ⟨9882443503590049824555997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52706365352480265730965317 9882443503590049824555997)
                ·
                  refine ⟨3705916313846268684208499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9882443503590049824555997 3705916313846268684208499)
                  ·
                    refine ⟨5558874470769403026312749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3705916313846268684208499 5558874470769403026312749)
                    ·
                      refine ⟨2084577926538526134867281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5558874470769403026312749 2084577926538526134867281)
                      ·
                        rfl

theorem cell23_4059701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_4059701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059701 prefixEnd_4059701 := by exact prefixLift 4059701
  have htrace : WordTrace (prefixWord ++ tailWord_4059701) baseStart_4059701 baseEnd_4059701 := by
    simpa [prefixWord, tailWord_4059701, baseEnd_4059701] using wordTrace_append hprefix tailTrace_4059701
  have hstable : (prefixWord ++ tailWord_4059701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059701).length < 2 ^ (prefixWord ++ tailWord_4059701).sum := by decide
  have hdescent : baseEnd_4059701 < baseStart_4059701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059711 : List Nat := [1, 1, 2, 2, 3, 2, 2, 3, 2, 3, 2]
def baseStart_4059711 : Nat := 118140960795 + 4059711 * 2 ^ 59
def prefixEnd_4059711 : Nat := 4983230072969 + 3 ^ 40 * 4059711 * 2
def baseEnd_4059711 : Nat := 2084583061345071095742235

theorem tailTrace_4059711 : CollatzResearch.WordTrace tailWord_4059711 prefixEnd_4059711 2084583061345071095742235 := by
  unfold tailWord_4059711
  simp only [CollatzResearch.WordTrace]
  refine ⟨148069824595367865284018987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98713216396911910189345991 148069824595367865284018987)
  ·
    refine ⟨222104736893051797926028481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148069824595367865284018987 222104736893051797926028481)
    ·
      refine ⟨166578552669788848444521361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222104736893051797926028481 166578552669788848444521361)
      ·
        refine ⟨124933914502341636333391021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166578552669788848444521361 124933914502341636333391021)
        ·
          refine ⟨46850217938378113625021633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124933914502341636333391021 46850217938378113625021633)
          ·
            refine ⟨35137663453783585218766225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46850217938378113625021633 35137663453783585218766225)
            ·
              refine ⟨26353247590337688914074669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35137663453783585218766225 26353247590337688914074669)
              ·
                refine ⟨9882467846376633342778001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26353247590337688914074669 9882467846376633342778001)
                ·
                  refine ⟨7411850884782475007083501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9882467846376633342778001 7411850884782475007083501)
                  ·
                    refine ⟨2779444081793428127656313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7411850884782475007083501 2779444081793428127656313)
                    ·
                      refine ⟨2084583061345071095742235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2779444081793428127656313 2084583061345071095742235)
                      ·
                        rfl

theorem cell23_4059711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 3, 2].length) (baseStart_4059711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059711 prefixEnd_4059711 := by exact prefixLift 4059711
  have htrace : WordTrace (prefixWord ++ tailWord_4059711) baseStart_4059711 baseEnd_4059711 := by
    simpa [prefixWord, tailWord_4059711, baseEnd_4059711] using wordTrace_append hprefix tailTrace_4059711
  have hstable : (prefixWord ++ tailWord_4059711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059711).length < 2 ^ (prefixWord ++ tailWord_4059711).sum := by decide
  have hdescent : baseEnd_4059711 < baseStart_4059711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059735 : List Nat := [1, 1, 3, 2, 2, 2, 5, 2, 1, 1, 3]
def baseStart_4059735 : Nat := 118140960795 + 4059735 * 2 ^ 59
def prefixEnd_4059735 : Nat := 4983230072969 + 3 ^ 40 * 4059735 * 2
def baseEnd_4059735 : Nat := 2084595384880779001842125

theorem tailTrace_4059735 : CollatzResearch.WordTrace tailWord_4059735 prefixEnd_4059735 2084595384880779001842125 := by
  unfold tailWord_4059735
  simp only [CollatzResearch.WordTrace]
  refine ⟨148070699947280917382892659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98713799964853944921928439 148070699947280917382892659)
  ·
    refine ⟨222106049920921376074338989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148070699947280917382892659 222106049920921376074338989)
    ·
      refine ⟨83289768720345516027877121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222106049920921376074338989 83289768720345516027877121)
      ·
        refine ⟨62467326540259137020907841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83289768720345516027877121 62467326540259137020907841)
        ·
          refine ⟨46850494905194352765680881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62467326540259137020907841 46850494905194352765680881)
          ·
            refine ⟨35137871178895764574260661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46850494905194352765680881 35137871178895764574260661)
            ·
              refine ⟨3294175423021477928836937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35137871178895764574260661 3294175423021477928836937)
              ·
                refine ⟨2470631567266108446627703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3294175423021477928836937 2470631567266108446627703)
                ·
                  refine ⟨3705947350899162669941555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2470631567266108446627703 3705947350899162669941555)
                  ·
                    refine ⟨5558921026348744004912333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3705947350899162669941555 5558921026348744004912333)
                    ·
                      refine ⟨2084595384880779001842125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5558921026348744004912333 2084595384880779001842125)
                      ·
                        rfl

theorem cell23_4059735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 1, 1, 3].length) (baseStart_4059735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059735 prefixEnd_4059735 := by exact prefixLift 4059735
  have htrace : WordTrace (prefixWord ++ tailWord_4059735) baseStart_4059735 baseEnd_4059735 := by
    simpa [prefixWord, tailWord_4059735, baseEnd_4059735] using wordTrace_append hprefix tailTrace_4059735
  have hstable : (prefixWord ++ tailWord_4059735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059735).length < 2 ^ (prefixWord ++ tailWord_4059735).sum := by decide
  have hdescent : baseEnd_4059735 < baseStart_4059735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059744 : List Nat := [2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 5]
def baseStart_4059744 : Nat := 118140960795 + 4059744 * 2 ^ 59
def prefixEnd_4059744 : Nat := 4983230072969 + 3 ^ 40 * 4059744 * 2
def baseEnd_4059744 : Nat := 2084600006206669466629583

theorem tailTrace_4059744 : CollatzResearch.WordTrace tailWord_4059744 prefixEnd_4059744 2084600006206669466629583 := by
  unfold tailWord_4059744
  simp only [CollatzResearch.WordTrace]
  refine ⟨74035514102124155959985143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98714018802832207946646857 74035514102124155959985143)
  ·
    refine ⟨111053271153186233939977715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74035514102124155959985143 111053271153186233939977715)
    ·
      refine ⟨166579906729779350909966573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111053271153186233939977715 166579906729779350909966573)
      ·
        refine ⟨62467465023667256591237465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166579906729779350909966573 62467465023667256591237465)
        ·
          refine ⟨46850598767750442443428099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62467465023667256591237465 46850598767750442443428099)
          ·
            refine ⟨70275898151625663665142149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46850598767750442443428099 70275898151625663665142149)
            ·
              refine ⟨13176730903429811937214153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70275898151625663665142149 13176730903429811937214153)
              ·
                refine ⟨9882548177572358952910615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13176730903429811937214153 9882548177572358952910615)
                ·
                  refine ⟨14823822266358538429365923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9882548177572358952910615 14823822266358538429365923)
                  ·
                    refine ⟨22235733399537807644048885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14823822266358538429365923 22235733399537807644048885)
                    ·
                      refine ⟨2084600006206669466629583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22235733399537807644048885 2084600006206669466629583)
                      ·
                        rfl

theorem cell23_4059744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_4059744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059744 prefixEnd_4059744 := by exact prefixLift 4059744
  have htrace : WordTrace (prefixWord ++ tailWord_4059744) baseStart_4059744 baseEnd_4059744 := by
    simpa [prefixWord, tailWord_4059744, baseEnd_4059744] using wordTrace_append hprefix tailTrace_4059744
  have hstable : (prefixWord ++ tailWord_4059744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059744).length < 2 ^ (prefixWord ++ tailWord_4059744).sum := by decide
  have hdescent : baseEnd_4059744 < baseStart_4059744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059754 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_4059754 : Nat := 118140960795 + 4059754 * 2 ^ 59
def prefixEnd_4059754 : Nat := 4983230072969 + 3 ^ 40 * 4059754 * 2
def baseEnd_4059754 : Nat := 2084605141013214427504537

theorem tailTrace_4059754 : CollatzResearch.WordTrace tailWord_4059754 prefixEnd_4059754 2084605141013214427504537 := by
  unfold tailWord_4059754
  simp only [CollatzResearch.WordTrace]
  refine ⟨37017848233553020906958579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98714261956141389085222877 37017848233553020906958579)
  ·
    refine ⟨55526772350329531360437869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37017848233553020906958579 55526772350329531360437869)
    ·
      refine ⟨20822539631373574260164201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55526772350329531360437869 20822539631373574260164201)
      ·
        refine ⟨15616904723530180695123151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20822539631373574260164201 15616904723530180695123151)
        ·
          refine ⟨23425357085295271042684727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15616904723530180695123151 23425357085295271042684727)
          ·
            refine ⟨35138035627942906564027091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23425357085295271042684727 35138035627942906564027091)
            ·
              refine ⟨52707053441914359846040637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35138035627942906564027091 52707053441914359846040637)
              ·
                refine ⟨19765145040717884942265239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52707053441914359846040637 19765145040717884942265239)
                ·
                  refine ⟨29647717561076827413397859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19765145040717884942265239 29647717561076827413397859)
                  ·
                    refine ⟨44471576341615241120096789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29647717561076827413397859 44471576341615241120096789)
                    ·
                      refine ⟨2084605141013214427504537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44471576341615241120096789 2084605141013214427504537)
                      ·
                        rfl

theorem cell23_4059754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_4059754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059754 prefixEnd_4059754 := by exact prefixLift 4059754
  have htrace : WordTrace (prefixWord ++ tailWord_4059754) baseStart_4059754 baseEnd_4059754 := by
    simpa [prefixWord, tailWord_4059754, baseEnd_4059754] using wordTrace_append hprefix tailTrace_4059754
  have hstable : (prefixWord ++ tailWord_4059754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059754).length < 2 ^ (prefixWord ++ tailWord_4059754).sum := by decide
  have hdescent : baseEnd_4059754 < baseStart_4059754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059758 : List Nat := [4, 1, 2, 2, 2, 1, 3, 2, 1, 1, 4]
def baseStart_4059758 : Nat := 118140960795 + 4059758 * 2 ^ 59
def prefixEnd_4059758 : Nat := 4983230072969 + 3 ^ 40 * 4059758 * 2
def baseEnd_4059758 : Nat := 2084607194935832411854519

theorem tailTrace_4059758 : CollatzResearch.WordTrace tailWord_4059758 prefixEnd_4059758 2084607194935832411854519 := by
  unfold tailWord_4059758
  simp only [CollatzResearch.WordTrace]
  refine ⟨18508942353274699038872491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98714359217465061540653285 18508942353274699038872491)
  ·
    refine ⟨27763413529912048558308737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18508942353274699038872491 27763413529912048558308737)
    ·
      refine ⟨20822560147434036418731553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27763413529912048558308737 20822560147434036418731553)
      ·
        refine ⟨15616920110575527314048665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20822560147434036418731553 15616920110575527314048665)
        ·
          refine ⟨11712690082931645485536499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15616920110575527314048665 11712690082931645485536499)
          ·
            refine ⟨17569035124397468228304749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11712690082931645485536499 17569035124397468228304749)
            ·
              refine ⟨6588388171649050585614281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17569035124397468228304749 6588388171649050585614281)
              ·
                refine ⟨4941291128736787939210711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6588388171649050585614281 4941291128736787939210711)
                ·
                  refine ⟨7411936693105181908816067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4941291128736787939210711 7411936693105181908816067)
                  ·
                    refine ⟨11117905039657772863224101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7411936693105181908816067 11117905039657772863224101)
                    ·
                      refine ⟨2084607194935832411854519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11117905039657772863224101 2084607194935832411854519)
                      ·
                        rfl

theorem cell23_4059758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_4059758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059758 prefixEnd_4059758 := by exact prefixLift 4059758
  have htrace : WordTrace (prefixWord ++ tailWord_4059758) baseStart_4059758 baseEnd_4059758 := by
    simpa [prefixWord, tailWord_4059758, baseEnd_4059758] using wordTrace_append hprefix tailTrace_4059758
  have hstable : (prefixWord ++ tailWord_4059758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059758).length < 2 ^ (prefixWord ++ tailWord_4059758).sum := by decide
  have hdescent : baseEnd_4059758 < baseStart_4059758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059801 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 5, 3, 2]
def baseStart_4059801 : Nat := 118140960795 + 4059801 * 2 ^ 59
def prefixEnd_4059801 : Nat := 4983230072969 + 3 ^ 40 * 4059801 * 2
def baseEnd_4059801 : Nat := 2084629274603975743616821

theorem tailTrace_4059801 : CollatzResearch.WordTrace tailWord_4059801 prefixEnd_4059801 2084629274603975743616821 := by
  unfold tailWord_4059801
  simp only [CollatzResearch.WordTrace]
  refine ⟨148073107165041810654795257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98715404776694540436530171 148073107165041810654795257)
  ·
    refine ⟨111054830373781357991096443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148073107165041810654795257 111054830373781357991096443)
    ·
      refine ⟨166582245560672036986644665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111054830373781357991096443 166582245560672036986644665)
      ·
        refine ⟨124936684170504027739983499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166582245560672036986644665 124936684170504027739983499)
        ·
          refine ⟨187405026255756041609975249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124936684170504027739983499 187405026255756041609975249)
          ·
            refine ⟨140553769691817031207481437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187405026255756041609975249 140553769691817031207481437)
            ·
              refine ⟨52707663634431386702805539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140553769691817031207481437 52707663634431386702805539)
              ·
                refine ⟨79061495451647080054208309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52707663634431386702805539 79061495451647080054208309)
                ·
                  refine ⟨7412015198591913755082029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79061495451647080054208309 7412015198591913755082029)
                  ·
                    refine ⟨2779505699471967658155761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7412015198591913755082029 2779505699471967658155761)
                    ·
                      refine ⟨2084629274603975743616821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2779505699471967658155761 2084629274603975743616821)
                      ·
                        rfl

theorem cell23_4059801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 3, 2].length) (baseStart_4059801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059801 prefixEnd_4059801 := by exact prefixLift 4059801
  have htrace : WordTrace (prefixWord ++ tailWord_4059801) baseStart_4059801 baseEnd_4059801 := by
    simpa [prefixWord, tailWord_4059801, baseEnd_4059801] using wordTrace_append hprefix tailTrace_4059801
  have hstable : (prefixWord ++ tailWord_4059801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059801).length < 2 ^ (prefixWord ++ tailWord_4059801).sum := by decide
  have hdescent : baseEnd_4059801 < baseStart_4059801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059808 : List Nat := [2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 3]
def baseStart_4059808 : Nat := 118140960795 + 4059808 * 2 ^ 59
def prefixEnd_4059808 : Nat := 4983230072969 + 3 ^ 40 * 4059808 * 2
def baseEnd_4059808 : Nat := 2084632868968557216229289

theorem tailTrace_4059808 : CollatzResearch.WordTrace tailWord_4059808 prefixEnd_4059808 2084632868968557216229289 := by
  unfold tailWord_4059808
  simp only [CollatzResearch.WordTrace]
  refine ⟨74036681238008225425150039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98715574984010967233533385 74036681238008225425150039)
  ·
    refine ⟨111055021857012338137725059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74036681238008225425150039 111055021857012338137725059)
    ·
      refine ⟨166582532785518507206587589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111055021857012338137725059 166582532785518507206587589)
      ·
        refine ⟨31234224897284720101235173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166582532785518507206587589 31234224897284720101235173)
        ·
          refine ⟨5856417168240885018981595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31234224897284720101235173 5856417168240885018981595)
          ·
            refine ⟨8784625752361327528472393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5856417168240885018981595 8784625752361327528472393)
            ·
              refine ⟨6588469314270995646354295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8784625752361327528472393 6588469314270995646354295)
              ·
                refine ⟨9882703971406493469531443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6588469314270995646354295 9882703971406493469531443)
                ·
                  refine ⟨14824055957109740204297165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9882703971406493469531443 14824055957109740204297165)
                  ·
                    refine ⟨5559020983916152576611437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14824055957109740204297165 5559020983916152576611437)
                    ·
                      refine ⟨2084632868968557216229289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5559020983916152576611437 2084632868968557216229289)
                      ·
                        rfl

theorem cell23_4059808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_4059808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059808 prefixEnd_4059808 := by exact prefixLift 4059808
  have htrace : WordTrace (prefixWord ++ tailWord_4059808) baseStart_4059808 baseEnd_4059808 := by
    simpa [prefixWord, tailWord_4059808, baseEnd_4059808] using wordTrace_append hprefix tailTrace_4059808
  have hstable : (prefixWord ++ tailWord_4059808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059808).length < 2 ^ (prefixWord ++ tailWord_4059808).sum := by decide
  have hdescent : baseEnd_4059808 < baseStart_4059808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059834 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5]
def baseStart_4059834 : Nat := 118140960795 + 4059834 * 2 ^ 59
def prefixEnd_4059834 : Nat := 4983230072969 + 3 ^ 40 * 4059834 * 2
def baseEnd_4059834 : Nat := 2084646219465574114504169

theorem tailTrace_4059834 : CollatzResearch.WordTrace tailWord_4059834 prefixEnd_4059834 2084646219465574114504169 := by
  unfold tailWord_4059834
  simp only [CollatzResearch.WordTrace]
  refine ⟨37018577693480564322686639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98716207182614838193831037 37018577693480564322686639)
  ·
    refine ⟨55527866540220846484029959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37018577693480564322686639 55527866540220846484029959)
    ·
      refine ⟨83291799810331269726044939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55527866540220846484029959 83291799810331269726044939)
      ·
        refine ⟨124937699715496904589067409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83291799810331269726044939 124937699715496904589067409)
        ·
          refine ⟨93703274786622678441800557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124937699715496904589067409 93703274786622678441800557)
          ·
            refine ⟨35138728044983504415675209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93703274786622678441800557 35138728044983504415675209)
            ·
              refine ⟨26354046033737628311756407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35138728044983504415675209 26354046033737628311756407)
              ·
                refine ⟨39531069050606442467634611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26354046033737628311756407 39531069050606442467634611)
                ·
                  refine ⟨59296603575909663701451917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39531069050606442467634611 59296603575909663701451917)
                  ·
                    refine ⟨22236226340966123888044469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59296603575909663701451917 22236226340966123888044469)
                    ·
                      refine ⟨2084646219465574114504169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22236226340966123888044469 2084646219465574114504169)
                      ·
                        rfl

theorem cell23_4059834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_4059834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059834 prefixEnd_4059834 := by exact prefixLift 4059834
  have htrace : WordTrace (prefixWord ++ tailWord_4059834) baseStart_4059834 baseEnd_4059834 := by
    simpa [prefixWord, tailWord_4059834, baseEnd_4059834] using wordTrace_append hprefix tailTrace_4059834
  have hstable : (prefixWord ++ tailWord_4059834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059834).length < 2 ^ (prefixWord ++ tailWord_4059834).sum := by decide
  have hdescent : baseEnd_4059834 < baseStart_4059834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059891 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 1, 7, 2]
def baseStart_4059891 : Nat := 118140960795 + 4059891 * 2 ^ 59
def prefixEnd_4059891 : Nat := 4983230072969 + 3 ^ 40 * 4059891 * 2
def baseEnd_4059891 : Nat := 2084675487862880391491407

theorem tailTrace_4059891 : CollatzResearch.WordTrace tailWord_4059891 prefixEnd_4059891 2084675487862880391491407 := by
  unfold tailWord_4059891
  simp only [CollatzResearch.WordTrace]
  refine ⟨148076389734715756025571527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98717593156477170683714351 148076389734715756025571527)
  ·
    refine ⟨222114584602073634038357291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148076389734715756025571527 222114584602073634038357291)
    ·
      refine ⟨333171876903110451057535937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222114584602073634038357291 333171876903110451057535937)
      ·
        refine ⟨249878907677332838293151953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333171876903110451057535937 249878907677332838293151953)
        ·
          refine ⟨187409180757999628719863965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249878907677332838293151953 187409180757999628719863965)
          ·
            refine ⟨70278442784249860769948987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187409180757999628719863965 70278442784249860769948987)
            ·
              refine ⟨105417664176374791154923481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70278442784249860769948987 105417664176374791154923481)
              ·
                refine ⟨79063248132281093366192611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105417664176374791154923481 79063248132281093366192611)
                ·
                  refine ⟨118594872198421640049288917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79063248132281093366192611 118594872198421640049288917)
                  ·
                    refine ⟨2779567317150507188655209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 118594872198421640049288917 2779567317150507188655209)
                    ·
                      refine ⟨2084675487862880391491407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2779567317150507188655209 2084675487862880391491407)
                      ·
                        rfl

theorem cell23_4059891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 7, 2].length) (baseStart_4059891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059891 prefixEnd_4059891 := by exact prefixLift 4059891
  have htrace : WordTrace (prefixWord ++ tailWord_4059891) baseStart_4059891 baseEnd_4059891 := by
    simpa [prefixWord, tailWord_4059891, baseEnd_4059891] using wordTrace_append hprefix tailTrace_4059891
  have hstable : (prefixWord ++ tailWord_4059891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059891).length < 2 ^ (prefixWord ++ tailWord_4059891).sum := by decide
  have hdescent : baseEnd_4059891 < baseStart_4059891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059901 : List Nat := [1, 4, 1, 1, 1, 1, 5, 2, 2, 5]
def baseStart_4059901 : Nat := 118140960795 + 4059901 * 2 ^ 59
def prefixEnd_4059901 : Nat := 4983230072969 + 3 ^ 40 * 4059901 * 2
def baseEnd_4059901 : Nat := 694893540889808450788787

theorem tailTrace_4059901 : CollatzResearch.WordTrace tailWord_4059901 prefixEnd_4059901 694893540889808450788787 := by
  unfold tailWord_4059901
  simp only [CollatzResearch.WordTrace]
  refine ⟨148076754464679527733435557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98717836309786351822290371 148076754464679527733435557)
  ·
    refine ⟨27764391462127411450019167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148076754464679527733435557 27764391462127411450019167)
    ·
      refine ⟨41646587193191117175028751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27764391462127411450019167 41646587193191117175028751)
      ·
        refine ⟨62469880789786675762543127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41646587193191117175028751 62469880789786675762543127)
        ·
          refine ⟨93704821184680013643814691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62469880789786675762543127 93704821184680013643814691)
          ·
            refine ⟨140557231777020020465722037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93704821184680013643814691 140557231777020020465722037)
            ·
              refine ⟨13177240479095626918661441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140557231777020020465722037 13177240479095626918661441)
              ·
                refine ⟨9882930359321720188996081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13177240479095626918661441 9882930359321720188996081)
                ·
                  refine ⟨7412197769491290141747061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9882930359321720188996081 7412197769491290141747061)
                  ·
                    refine ⟨694893540889808450788787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7412197769491290141747061 694893540889808450788787)
                    ·
                      rfl

theorem cell23_4059901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_4059901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059901 prefixEnd_4059901 := by exact prefixLift 4059901
  have htrace : WordTrace (prefixWord ++ tailWord_4059901) baseStart_4059901 baseEnd_4059901 := by
    simpa [prefixWord, tailWord_4059901, baseEnd_4059901] using wordTrace_append hprefix tailTrace_4059901
  have hstable : (prefixWord ++ tailWord_4059901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059901).length < 2 ^ (prefixWord ++ tailWord_4059901).sum := by decide
  have hdescent : baseEnd_4059901 < baseStart_4059901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059908 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 2, 5, 2]
def baseStart_4059908 : Nat := 118140960795 + 4059908 * 2 ^ 59
def prefixEnd_4059908 : Nat := 4983230072969 + 3 ^ 40 * 4059908 * 2
def baseEnd_4059908 : Nat := 2084684217034006824978829

theorem tailTrace_4059908 : CollatzResearch.WordTrace tailWord_4059908 prefixEnd_4059908 2084684217034006824978829 := by
  unfold tailWord_4059908
  simp only [CollatzResearch.WordTrace]
  refine ⟨74038504887827083964470189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98718006517102778619293585 74038504887827083964470189)
  ·
    refine ⟨27764439332935156486676321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74038504887827083964470189 27764439332935156486676321)
    ·
      refine ⟨20823329499701367365007241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27764439332935156486676321 20823329499701367365007241)
      ·
        refine ⟨15617497124776025523755431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20823329499701367365007241 15617497124776025523755431)
        ·
          refine ⟨23426245687164038285633147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15617497124776025523755431 23426245687164038285633147)
          ·
            refine ⟨35139368530746057428449721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23426245687164038285633147 35139368530746057428449721)
            ·
              refine ⟨26354526398059543071337291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35139368530746057428449721 26354526398059543071337291)
              ·
                refine ⟨39531789597089314607005937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26354526398059543071337291 39531789597089314607005937)
                ·
                  refine ⟨29648842197816985955254453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39531789597089314607005937 29648842197816985955254453)
                  ·
                    refine ⟨2779578956045342433305105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29648842197816985955254453 2779578956045342433305105)
                    ·
                      refine ⟨2084684217034006824978829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2779578956045342433305105 2084684217034006824978829)
                      ·
                        rfl

theorem cell23_4059908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_4059908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059908 prefixEnd_4059908 := by exact prefixLift 4059908
  have htrace : WordTrace (prefixWord ++ tailWord_4059908) baseStart_4059908 baseEnd_4059908 := by
    simpa [prefixWord, tailWord_4059908, baseEnd_4059908] using wordTrace_append hprefix tailTrace_4059908
  have hstable : (prefixWord ++ tailWord_4059908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059908).length < 2 ^ (prefixWord ++ tailWord_4059908).sum := by decide
  have hdescent : baseEnd_4059908 < baseStart_4059908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059911 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 7]
def baseStart_4059911 : Nat := 118140960795 + 4059911 * 2 ^ 59
def prefixEnd_4059911 : Nat := 4983230072969 + 3 ^ 40 * 4059911 * 2
def baseEnd_4059911 : Nat := 2084685757475970313241315

theorem tailTrace_4059911 : CollatzResearch.WordTrace tailWord_4059911 prefixEnd_4059911 2084685757475970313241315 := by
  unfold tailWord_4059911
  simp only [CollatzResearch.WordTrace]
  refine ⟨148077119194643299441299587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98718079463095532960866391 148077119194643299441299587)
  ·
    refine ⟨222115678791964949161949381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148077119194643299441299587 222115678791964949161949381)
    ·
      refine ⟨41646689773493427967865509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222115678791964949161949381 41646689773493427967865509)
      ·
        refine ⟨7808754332530017743974783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41646689773493427967865509 7808754332530017743974783)
        ·
          refine ⟨11713131498795026615962175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7808754332530017743974783 11713131498795026615962175)
          ·
            refine ⟨17569697248192539923943263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11713131498795026615962175 17569697248192539923943263)
            ·
              refine ⟨26354545872288809885914895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17569697248192539923943263 26354545872288809885914895)
              ·
                refine ⟨39531818808433214828872343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26354545872288809885914895 39531818808433214828872343)
                ·
                  refine ⟨59297728212649822243308515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39531818808433214828872343 59297728212649822243308515)
                  ·
                    refine ⟨88946592318974733364962773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59297728212649822243308515 88946592318974733364962773)
                    ·
                      refine ⟨2084685757475970313241315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88946592318974733364962773 2084685757475970313241315)
                      ·
                        rfl

theorem cell23_4059911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_4059911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059911 prefixEnd_4059911 := by exact prefixLift 4059911
  have htrace : WordTrace (prefixWord ++ tailWord_4059911) baseStart_4059911 baseEnd_4059911 := by
    simpa [prefixWord, tailWord_4059911, baseEnd_4059911] using wordTrace_append hprefix tailTrace_4059911
  have hstable : (prefixWord ++ tailWord_4059911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059911).length < 2 ^ (prefixWord ++ tailWord_4059911).sum := by decide
  have hdescent : baseEnd_4059911 < baseStart_4059911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059938 : List Nat := [3, 3, 1, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_4059938 : Nat := 118140960795 + 4059938 * 2 ^ 59
def prefixEnd_4059938 : Nat := 4983230072969 + 3 ^ 40 * 4059938 * 2
def baseEnd_4059938 : Nat := 2084699621453641707603691

theorem tailTrace_4059938 : CollatzResearch.WordTrace tailWord_4059938 prefixEnd_4059938 2084699621453641707603691 := by
  unfold tailWord_4059938
  simp only [CollatzResearch.WordTrace]
  refine ⟨37019525991386370763133117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98718735977030322035021645 37019525991386370763133117)
  ·
    refine ⟨13882322246769889036174919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37019525991386370763133117 13882322246769889036174919)
    ·
      refine ⟨20823483370154833554262379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13882322246769889036174919 20823483370154833554262379)
      ·
        refine ⟨31235225055232250331393569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20823483370154833554262379 31235225055232250331393569)
        ·
          refine ⟨23426418791424187748545177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31235225055232250331393569 23426418791424187748545177)
          ·
            refine ⟨17569814093568140811408883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23426418791424187748545177 17569814093568140811408883)
            ·
              refine ⟨26354721140352211217113325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17569814093568140811408883 26354721140352211217113325)
              ·
                refine ⟨9883020427632079206417497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26354721140352211217113325 9883020427632079206417497)
                ·
                  refine ⟨7412265320724059404813123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9883020427632079206417497 7412265320724059404813123)
                  ·
                    refine ⟨11118397981086089107219685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7412265320724059404813123 11118397981086089107219685)
                    ·
                      refine ⟨2084699621453641707603691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11118397981086089107219685 2084699621453641707603691)
                      ·
                        rfl

theorem cell23_4059938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_4059938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4059938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4059938 prefixEnd_4059938 := by exact prefixLift 4059938
  have htrace : WordTrace (prefixWord ++ tailWord_4059938) baseStart_4059938 baseEnd_4059938 := by
    simpa [prefixWord, tailWord_4059938, baseEnd_4059938] using wordTrace_append hprefix tailTrace_4059938
  have hstable : (prefixWord ++ tailWord_4059938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059938).length < 2 ^ (prefixWord ++ tailWord_4059938).sum := by decide
  have hdescent : baseEnd_4059938 < baseStart_4059938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060022 : List Nat := [5, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3]
def baseStart_4060022 : Nat := 118140960795 + 4060022 * 2 ^ 59
def prefixEnd_4060022 : Nat := 4983230072969 + 3 ^ 40 * 4060022 * 2
def baseEnd_4060022 : Nat := 2084742753828619378953305

theorem tailTrace_4060022 : CollatzResearch.WordTrace tailWord_4060022 prefixEnd_4060022 2084742753828619378953305 := by
  unfold tailWord_4060022
  simp only [CollatzResearch.WordTrace]
  refine ⟨9255072981077572837411895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98720778464827443599060213 9255072981077572837411895)
  ·
    refine ⟨13882609471616359256117843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9255072981077572837411895 13882609471616359256117843)
    ·
      refine ⟨20823914207424538884176765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13882609471616359256117843 20823914207424538884176765)
      ·
        refine ⟨7808967827784202081566287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20823914207424538884176765 7808967827784202081566287)
        ·
          refine ⟨11713451741676303122349431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7808967827784202081566287 11713451741676303122349431)
          ·
            refine ⟨17570177612514454683524147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11713451741676303122349431 17570177612514454683524147)
            ·
              refine ⟨26355266418771682025286221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17570177612514454683524147 26355266418771682025286221)
              ·
                refine ⟨9883224907039380759482333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26355266418771682025286221 9883224907039380759482333)
                ·
                  refine ⟨3706209340139767784805875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9883224907039380759482333 3706209340139767784805875)
                  ·
                    refine ⟨5559314010209651677208813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3706209340139767784805875 5559314010209651677208813)
                    ·
                      refine ⟨2084742753828619378953305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5559314010209651677208813 2084742753828619378953305)
                      ·
                        rfl

theorem cell23_4060022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_4060022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060022 prefixEnd_4060022 := by exact prefixLift 4060022
  have htrace : WordTrace (prefixWord ++ tailWord_4060022) baseStart_4060022 baseEnd_4060022 := by
    simpa [prefixWord, tailWord_4060022, baseEnd_4060022] using wordTrace_append hprefix tailTrace_4060022
  have hstable : (prefixWord ++ tailWord_4060022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060022).length < 2 ^ (prefixWord ++ tailWord_4060022).sum := by decide
  have hdescent : baseEnd_4060022 < baseStart_4060022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060031 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 5]
def baseStart_4060031 : Nat := 118140960795 + 4060031 * 2 ^ 59
def prefixEnd_4060031 : Nat := 4983230072969 + 3 ^ 40 * 4060031 * 2
def baseEnd_4060031 : Nat := 2084747375154509843740763

theorem tailTrace_4060031 : CollatzResearch.WordTrace tailWord_4060031 prefixEnd_4060031 2084747375154509843740763 := by
  unfold tailWord_4060031
  simp only [CollatzResearch.WordTrace]
  refine ⟨148081495954208559935667947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98720997302805706623778631 148081495954208559935667947)
  ·
    refine ⟨222122243931312839903501921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148081495954208559935667947 222122243931312839903501921)
    ·
      refine ⟨166591682948484629927626441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222122243931312839903501921 166591682948484629927626441)
      ·
        refine ⟨124943762211363472445719831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166591682948484629927626441 124943762211363472445719831)
        ·
          refine ⟨187415643317045208668579747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124943762211363472445719831 187415643317045208668579747)
          ·
            refine ⟨281123464975567813002869621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187415643317045208668579747 281123464975567813002869621)
            ·
              refine ⟨26355324841459482469019027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 281123464975567813002869621 26355324841459482469019027)
              ·
                refine ⟨39532987262189223703528541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26355324841459482469019027 39532987262189223703528541)
                ·
                  refine ⟨14824870223320958888823203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39532987262189223703528541 14824870223320958888823203)
                  ·
                    refine ⟨22237305334981438333234805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14824870223320958888823203 22237305334981438333234805)
                    ·
                      refine ⟨2084747375154509843740763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22237305334981438333234805 2084747375154509843740763)
                      ·
                        rfl

theorem cell23_4060031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_4060031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060031 prefixEnd_4060031 := by exact prefixLift 4060031
  have htrace : WordTrace (prefixWord ++ tailWord_4060031) baseStart_4060031 baseEnd_4060031 := by
    simpa [prefixWord, tailWord_4060031, baseEnd_4060031] using wordTrace_append hprefix tailTrace_4060031
  have hstable : (prefixWord ++ tailWord_4060031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060031).length < 2 ^ (prefixWord ++ tailWord_4060031).sum := by decide
  have hdescent : baseEnd_4060031 < baseStart_4060031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060065 : List Nat := [1, 2, 3, 4, 1, 2, 2, 1, 1, 1, 5]
def baseStart_4060065 : Nat := 118140960795 + 4060065 * 2 ^ 59
def prefixEnd_4060065 : Nat := 4983230072969 + 3 ^ 40 * 4060065 * 2
def baseEnd_4060065 : Nat := 2084764833496762710715607

theorem tailTrace_4060065 : CollatzResearch.WordTrace tailWord_4060065 prefixEnd_4060065 2084764833496762710715607 := by
  unfold tailWord_4060065
  simp only [CollatzResearch.WordTrace]
  refine ⟨148082736036085383742405649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98721824024056922494937099 148082736036085383742405649)
  ·
    refine ⟨111062052027064037806804237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148082736036085383742405649 111062052027064037806804237)
    ·
      refine ⟨41648269510149014177551589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111062052027064037806804237 41648269510149014177551589)
      ·
        refine ⟨7809050533152940158290923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41648269510149014177551589 7809050533152940158290923)
        ·
          refine ⟨11713575799729410237436385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7809050533152940158290923 11713575799729410237436385)
          ·
            refine ⟨8785181849797057678077289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11713575799729410237436385 8785181849797057678077289)
            ·
              refine ⟨6588886387347793258557967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8785181849797057678077289 6588886387347793258557967)
              ·
                refine ⟨9883329581021689887836951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6588886387347793258557967 9883329581021689887836951)
                ·
                  refine ⟨14824994371532534831755427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9883329581021689887836951 14824994371532534831755427)
                  ·
                    refine ⟨22237491557298802247633141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14824994371532534831755427 22237491557298802247633141)
                    ·
                      refine ⟨2084764833496762710715607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22237491557298802247633141 2084764833496762710715607)
                      ·
                        rfl

theorem cell23_4060065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_4060065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060065 prefixEnd_4060065 := by exact prefixLift 4060065
  have htrace : WordTrace (prefixWord ++ tailWord_4060065) baseStart_4060065 baseEnd_4060065 := by
    simpa [prefixWord, tailWord_4060065, baseEnd_4060065] using wordTrace_append hprefix tailTrace_4060065
  have hstable : (prefixWord ++ tailWord_4060065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060065).length < 2 ^ (prefixWord ++ tailWord_4060065).sum := by decide
  have hdescent : baseEnd_4060065 < baseStart_4060065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060130 : List Nat := [3, 3, 3, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_4060130 : Nat := 118140960795 + 4060130 * 2 ^ 59
def prefixEnd_4060130 : Nat := 4983230072969 + 3 ^ 40 * 4060130 * 2
def baseEnd_4060130 : Nat := 2084798209739304956402809

theorem tailTrace_4060130 : CollatzResearch.WordTrace tailWord_4060130 prefixEnd_4060130 2084798209739304956402809 := by
  unfold tailWord_4060130
  simp only [CollatzResearch.WordTrace]
  refine ⟨37021276695212474960880461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98723404520566599895681229 37021276695212474960880461)
  ·
    refine ⟨13882978760704678110330173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37021276695212474960880461 13882978760704678110330173)
    ·
      refine ⟨5206117035264254291373815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13882978760704678110330173 5206117035264254291373815)
      ·
        refine ⟨7809175552896381437060723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5206117035264254291373815 7809175552896381437060723)
        ·
          refine ⟨11713763329344572155591085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7809175552896381437060723 11713763329344572155591085)
          ·
            refine ⟨4392661248504214558346657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11713763329344572155591085 4392661248504214558346657)
            ·
              refine ⟨3294495936378160918759993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4392661248504214558346657 3294495936378160918759993)
              ·
                refine ⟨2470871952283620689069995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3294495936378160918759993 2470871952283620689069995)
                ·
                  refine ⟨3706307928425431033604993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2470871952283620689069995 3706307928425431033604993)
                  ·
                    refine ⟨2779730946319073275203745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3706307928425431033604993 2779730946319073275203745)
                    ·
                      refine ⟨2084798209739304956402809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2779730946319073275203745 2084798209739304956402809)
                      ·
                        rfl

theorem cell23_4060130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_4060130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060130 prefixEnd_4060130 := by exact prefixLift 4060130
  have htrace : WordTrace (prefixWord ++ tailWord_4060130) baseStart_4060130 baseEnd_4060130 := by
    simpa [prefixWord, tailWord_4060130, baseEnd_4060130] using wordTrace_append hprefix tailTrace_4060130
  have hstable : (prefixWord ++ tailWord_4060130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060130).length < 2 ^ (prefixWord ++ tailWord_4060130).sum := by decide
  have hdescent : baseEnd_4060130 < baseStart_4060130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060192 : List Nat := [2, 1, 1, 7, 1, 1, 2, 1, 7]
def baseStart_4060192 : Nat := 118140960795 + 4060192 * 2 ^ 59
def prefixEnd_4060192 : Nat := 4983230072969 + 3 ^ 40 * 4060192 * 2
def baseEnd_4060192 : Nat := 231647782837764857091947

theorem tailTrace_4060192 : CollatzResearch.WordTrace tailWord_4060192 prefixEnd_4060192 231647782837764857091947 := by
  unfold tailWord_4060192
  simp only [CollatzResearch.WordTrace]
  refine ⟨74043684053312642216139415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98724912071083522954852553 74043684053312642216139415)
  ·
    refine ⟨111065526079968963324209123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74043684053312642216139415 111065526079968963324209123)
    ·
      refine ⟨166598289119953444986313685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111065526079968963324209123 166598289119953444986313685)
      ·
        refine ⟨3904647401248908866866727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 166598289119953444986313685 3904647401248908866866727)
        ·
          refine ⟨5856971101873363300300091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3904647401248908866866727 5856971101873363300300091)
          ·
            refine ⟨8785456652810044950450137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5856971101873363300300091 8785456652810044950450137)
            ·
              refine ⟨6589092489607533712837603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8785456652810044950450137 6589092489607533712837603)
              ·
                refine ⟨9883638734411300569256405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6589092489607533712837603 9883638734411300569256405)
                ·
                  refine ⟨231647782837764857091947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9883638734411300569256405 231647782837764857091947)
                  ·
                    rfl

theorem cell23_4060192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 7].length) (baseStart_4060192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060192 prefixEnd_4060192 := by exact prefixLift 4060192
  have htrace : WordTrace (prefixWord ++ tailWord_4060192) baseStart_4060192 baseEnd_4060192 := by
    simpa [prefixWord, tailWord_4060192, baseEnd_4060192] using wordTrace_append hprefix tailTrace_4060192
  have hstable : (prefixWord ++ tailWord_4060192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060192).length < 2 ^ (prefixWord ++ tailWord_4060192).sum := by decide
  have hdescent : baseEnd_4060192 < baseStart_4060192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060208 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 4]
def baseStart_4060208 : Nat := 118140960795 + 4060208 * 2 ^ 59
def prefixEnd_4060208 : Nat := 4983230072969 + 3 ^ 40 * 4060208 * 2
def baseEnd_4060208 : Nat := 2084838261230355651227449

theorem tailTrace_4060208 : CollatzResearch.WordTrace tailWord_4060208 prefixEnd_4060208 2084838261230355651227449 := by
  unfold tailWord_4060208
  simp only [CollatzResearch.WordTrace]
  refine ⟨74043975837283659582430639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98725301116378212776574185 74043975837283659582430639)
  ·
    refine ⟨111065963755925489373645959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74043975837283659582430639 111065963755925489373645959)
    ·
      refine ⟨166598945633888234060468939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111065963755925489373645959 166598945633888234060468939)
      ·
        refine ⟨249898418450832351090703409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166598945633888234060468939 249898418450832351090703409)
        ·
          refine ⟨187423813838124263318027557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249898418450832351090703409 187423813838124263318027557)
          ·
            refine ⟨35141965094648299372130167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187423813838124263318027557 35141965094648299372130167)
            ·
              refine ⟨52712947641972449058195251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35141965094648299372130167 52712947641972449058195251)
              ·
                refine ⟨79069421462958673587292877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52712947641972449058195251 79069421462958673587292877)
                ·
                  refine ⟨29651033048609502595234829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79069421462958673587292877 29651033048609502595234829)
                  ·
                    refine ⟨11119137393228563473213061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29651033048609502595234829 11119137393228563473213061)
                    ·
                      refine ⟨2084838261230355651227449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11119137393228563473213061 2084838261230355651227449)
                      ·
                        rfl

theorem cell23_4060208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 4].length) (baseStart_4060208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060208 prefixEnd_4060208 := by exact prefixLift 4060208
  have htrace : WordTrace (prefixWord ++ tailWord_4060208) baseStart_4060208 baseEnd_4060208 := by
    simpa [prefixWord, tailWord_4060208, baseEnd_4060208] using wordTrace_append hprefix tailTrace_4060208
  have hstable : (prefixWord ++ tailWord_4060208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060208).length < 2 ^ (prefixWord ++ tailWord_4060208).sum := by decide
  have hdescent : baseEnd_4060208 < baseStart_4060208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060242 : List Nat := [3, 2, 2, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_4060242 : Nat := 118140960795 + 4060242 * 2 ^ 59
def prefixEnd_4060242 : Nat := 4983230072969 + 3 ^ 40 * 4060242 * 2
def baseEnd_4060242 : Nat := 2084855719572608518202293

theorem tailTrace_4060242 : CollatzResearch.WordTrace tailWord_4060242 prefixEnd_4060242 2084855719572608518202293 := by
  unfold tailWord_4060242
  simp only [CollatzResearch.WordTrace]
  refine ⟨37022297939111035742899745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98726127837629428647732653 37022297939111035742899745)
  ·
    refine ⟨27766723454333276807174809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37022297939111035742899745 27766723454333276807174809)
    ·
      refine ⟨20825042590749957605381107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27766723454333276807174809 20825042590749957605381107)
      ·
        refine ⟨31237563886124936408071661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20825042590749957605381107 31237563886124936408071661)
        ·
          refine ⟨11714086457296851153026873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31237563886124936408071661 11714086457296851153026873)
          ·
            refine ⟨8785564842972638364770155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11714086457296851153026873 8785564842972638364770155)
            ·
              refine ⟨13178347264458957547155233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8785564842972638364770155 13178347264458957547155233)
              ·
                refine ⟨9883760448344218160366425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13178347264458957547155233 9883760448344218160366425)
                ·
                  refine ⟨7412820336258163620274819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9883760448344218160366425 7412820336258163620274819)
                  ·
                    refine ⟨11119230504387245430412229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7412820336258163620274819 11119230504387245430412229)
                    ·
                      refine ⟨2084855719572608518202293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11119230504387245430412229 2084855719572608518202293)
                      ·
                        rfl

theorem cell23_4060242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_4060242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060242 prefixEnd_4060242 := by exact prefixLift 4060242
  have htrace : WordTrace (prefixWord ++ tailWord_4060242) baseStart_4060242 baseEnd_4060242 := by
    simpa [prefixWord, tailWord_4060242, baseEnd_4060242] using wordTrace_append hprefix tailTrace_4060242
  have hstable : (prefixWord ++ tailWord_4060242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060242).length < 2 ^ (prefixWord ++ tailWord_4060242).sum := by decide
  have hdescent : baseEnd_4060242 < baseStart_4060242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060248 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 8]
def baseStart_4060248 : Nat := 118140960795 + 4060248 * 2 ^ 59
def prefixEnd_4060248 : Nat := 4983230072969 + 3 ^ 40 * 4060248 * 2
def baseEnd_4060248 : Nat := 231650977828503943858585

theorem tailTrace_4060248 : CollatzResearch.WordTrace tailWord_4060248 prefixEnd_4060248 231650977828503943858585 := by
  unfold tailWord_4060248
  simp only [CollatzResearch.WordTrace]
  refine ⟨74044705297211202998158699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98726273729614937330878265 74044705297211202998158699)
  ·
    refine ⟨111067057945816804497238049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74044705297211202998158699 111067057945816804497238049)
    ·
      refine ⟨83300293459362603372928537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111067057945816804497238049 83300293459362603372928537)
      ·
        refine ⟨62475220094521952529696403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83300293459362603372928537 62475220094521952529696403)
        ·
          refine ⟨93712830141782928794544605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62475220094521952529696403 93712830141782928794544605)
          ·
            refine ⟨35142311303168598297954227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93712830141782928794544605 35142311303168598297954227)
            ·
              refine ⟨52713466954752897446931341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35142311303168598297954227 52713466954752897446931341)
              ·
                refine ⟨19767550108032336542599253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52713466954752897446931341 19767550108032336542599253)
                ·
                  refine ⟨231650977828503943858585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19767550108032336542599253 231650977828503943858585)
                  ·
                    rfl

theorem cell23_4060248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 8].length) (baseStart_4060248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060248 prefixEnd_4060248 := by exact prefixLift 4060248
  have htrace : WordTrace (prefixWord ++ tailWord_4060248) baseStart_4060248 baseEnd_4060248 := by
    simpa [prefixWord, tailWord_4060248, baseEnd_4060248] using wordTrace_append hprefix tailTrace_4060248
  have hstable : (prefixWord ++ tailWord_4060248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060248).length < 2 ^ (prefixWord ++ tailWord_4060248).sum := by decide
  have hdescent : baseEnd_4060248 < baseStart_4060248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060265 : List Nat := [1, 2, 1, 1, 1, 7, 1, 3, 6]
def baseStart_4060265 : Nat := 118140960795 + 4060265 * 2 ^ 59
def prefixEnd_4060265 : Nat := 4983230072969 + 3 ^ 40 * 4060265 * 2
def baseEnd_4060265 : Nat := 231651947736406880912743

theorem tailTrace_4060265 : CollatzResearch.WordTrace tailWord_4060265 prefixEnd_4060265 231651947736406880912743 := by
  unfold tailWord_4060265
  simp only [CollatzResearch.WordTrace]
  refine ⟨148090030635360817899686249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98726687090240545266457499 148090030635360817899686249)
  ·
    refine ⟨111067522976520613424764687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148090030635360817899686249 111067522976520613424764687)
    ·
      refine ⟨166601284464780920137147031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111067522976520613424764687 166601284464780920137147031)
      ·
        refine ⟨249901926697171380205720547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166601284464780920137147031 249901926697171380205720547)
        ·
          refine ⟨374852890045757070308580821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249901926697171380205720547 374852890045757070308580821)
          ·
            refine ⟨8785614610447431335357363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 374852890045757070308580821 8785614610447431335357363)
            ·
              refine ⟨13178421915671147003036045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8785614610447431335357363 13178421915671147003036045)
              ·
                refine ⟨4941908218376680126138517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13178421915671147003036045 4941908218376680126138517)
                ·
                  refine ⟨231651947736406880912743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4941908218376680126138517 231651947736406880912743)
                  ·
                    rfl

theorem cell23_4060265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 6].length) (baseStart_4060265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060265 prefixEnd_4060265 := by exact prefixLift 4060265
  have htrace : WordTrace (prefixWord ++ tailWord_4060265) baseStart_4060265 baseEnd_4060265 := by
    simpa [prefixWord, tailWord_4060265, baseEnd_4060265] using wordTrace_append hprefix tailTrace_4060265
  have hstable : (prefixWord ++ tailWord_4060265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060265).length < 2 ^ (prefixWord ++ tailWord_4060265).sum := by decide
  have hdescent : baseEnd_4060265 < baseStart_4060265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060325 : List Nat := [1, 3, 1, 2, 1, 4, 1, 3, 1, 6]
def baseStart_4060325 : Nat := 118140960795 + 4060325 * 2 ^ 59
def prefixEnd_4060325 : Nat := 4983230072969 + 3 ^ 40 * 4060325 * 2
def baseEnd_4060325 : Nat := 694966112822310564488137

theorem tailTrace_4060325 : CollatzResearch.WordTrace tailWord_4060325 prefixEnd_4060325 694966112822310564488137 := by
  unfold tailWord_4060325
  simp only [CollatzResearch.WordTrace]
  refine ⟨148092219015143448146870429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98728146010095632097913619 148092219015143448146870429)
  ·
    refine ⟨55534582130678793055076411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148092219015143448146870429 55534582130678793055076411)
    ·
      refine ⟨83301873196018189582614617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55534582130678793055076411 83301873196018189582614617)
      ·
        refine ⟨62476404897013642186960963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83301873196018189582614617 62476404897013642186960963)
        ·
          refine ⟨93714607345520463280441445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62476404897013642186960963 93714607345520463280441445)
          ·
            refine ⟨17571488877285086865082771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93714607345520463280441445 17571488877285086865082771)
            ·
              refine ⟨26357233315927630297624157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17571488877285086865082771 26357233315927630297624157)
              ·
                refine ⟨9883962493472861361609059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26357233315927630297624157 9883962493472861361609059)
                ·
                  refine ⟨14825943740209292042413589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9883962493472861361609059 14825943740209292042413589)
                  ·
                    refine ⟨694966112822310564488137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14825943740209292042413589 694966112822310564488137)
                    ·
                      rfl

theorem cell23_4060325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_4060325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060325 prefixEnd_4060325 := by exact prefixLift 4060325
  have htrace : WordTrace (prefixWord ++ tailWord_4060325) baseStart_4060325 baseEnd_4060325 := by
    simpa [prefixWord, tailWord_4060325, baseEnd_4060325] using wordTrace_append hprefix tailTrace_4060325
  have hstable : (prefixWord ++ tailWord_4060325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060325).length < 2 ^ (prefixWord ++ tailWord_4060325).sum := by decide
  have hdescent : baseEnd_4060325 < baseStart_4060325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060349 : List Nat := [1, 4, 1, 2, 1, 1, 6, 1, 1, 1, 4]
def baseStart_4060349 : Nat := 118140960795 + 4060349 * 2 ^ 59
def prefixEnd_4060349 : Nat := 4983230072969 + 3 ^ 40 * 4060349 * 2
def baseEnd_4060349 : Nat := 2084910662002639599564301

theorem tailTrace_4060349 : CollatzResearch.WordTrace tailWord_4060349 prefixEnd_4060349 2084910662002639599564301 := by
  unfold tailWord_4060349
  simp only [CollatzResearch.WordTrace]
  refine ⟨148093094367056500245744101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98728729578037666830496067 148093094367056500245744101)
  ·
    refine ⟨27767455193823093796077019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148093094367056500245744101 27767455193823093796077019)
    ·
      refine ⟨41651182790734640694115529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27767455193823093796077019 41651182790734640694115529)
      ·
        refine ⟨31238387093050980520586647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41651182790734640694115529 31238387093050980520586647)
        ·
          refine ⟨46857580639576470780879971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31238387093050980520586647 46857580639576470780879971)
          ·
            refine ⟨70286370959364706171319957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46857580639576470780879971 70286370959364706171319957)
            ·
              refine ⟨3294673638720220601780623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70286370959364706171319957 3294673638720220601780623)
              ·
                refine ⟨4942010458080330902670935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3294673638720220601780623 4942010458080330902670935)
                ·
                  refine ⟨7413015687120496354006403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4942010458080330902670935 7413015687120496354006403)
                  ·
                    refine ⟨11119523530680744531009605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7413015687120496354006403 11119523530680744531009605)
                    ·
                      refine ⟨2084910662002639599564301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11119523530680744531009605 2084910662002639599564301)
                      ·
                        rfl

theorem cell23_4060349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_4060349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060349 prefixEnd_4060349 := by exact prefixLift 4060349
  have htrace : WordTrace (prefixWord ++ tailWord_4060349) baseStart_4060349 baseEnd_4060349 := by
    simpa [prefixWord, tailWord_4060349, baseEnd_4060349] using wordTrace_append hprefix tailTrace_4060349
  have hstable : (prefixWord ++ tailWord_4060349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060349).length < 2 ^ (prefixWord ++ tailWord_4060349).sum := by decide
  have hdescent : baseEnd_4060349 < baseStart_4060349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060376 : List Nat := [2, 1, 2, 2, 5, 1, 3, 1, 2, 4]
def baseStart_4060376 : Nat := 118140960795 + 4060376 * 2 ^ 59
def prefixEnd_4060376 : Nat := 4983230072969 + 3 ^ 40 * 4060376 * 2
def baseEnd_4060376 : Nat := 694974841993436997975559

theorem tailTrace_4060376 : CollatzResearch.WordTrace tailWord_4060376 prefixEnd_4060376 694974841993436997975559 := by
  unfold tailWord_4060376
  simp only [CollatzResearch.WordTrace]
  refine ⟨74047039568979341928488491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98729386091972455904651321 74047039568979341928488491)
  ·
    refine ⟨111070559353469012892732737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74047039568979341928488491 111070559353469012892732737)
    ·
      refine ⟨83302919515101759669549553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111070559353469012892732737 83302919515101759669549553)
      ·
        refine ⟨62477189636326319752162165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83302919515101759669549553 62477189636326319752162165)
        ·
          refine ⟨5857236528405592476765203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62477189636326319752162165 5857236528405592476765203)
          ·
            refine ⟨8785854792608388715147805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5857236528405592476765203 8785854792608388715147805)
            ·
              refine ⟨3294695547228145768180427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8785854792608388715147805 3294695547228145768180427)
              ·
                refine ⟨4942043320842218652270641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3294695547228145768180427 4942043320842218652270641)
                ·
                  refine ⟨3706532490631663989202981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4942043320842218652270641 3706532490631663989202981)
                  ·
                    refine ⟨694974841993436997975559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3706532490631663989202981 694974841993436997975559)
                    ·
                      rfl

theorem cell23_4060376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 2, 4].length) (baseStart_4060376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060376 prefixEnd_4060376 := by exact prefixLift 4060376
  have htrace : WordTrace (prefixWord ++ tailWord_4060376) baseStart_4060376 baseEnd_4060376 := by
    simpa [prefixWord, tailWord_4060376, baseEnd_4060376] using wordTrace_append hprefix tailTrace_4060376
  have hstable : (prefixWord ++ tailWord_4060376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060376).length < 2 ^ (prefixWord ++ tailWord_4060376).sum := by decide
  have hdescent : baseEnd_4060376 < baseStart_4060376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060389 : List Nat := [1, 3, 1, 4, 3, 2, 2, 7]
def baseStart_4060389 : Nat := 118140960795 + 4060389 * 2 ^ 59
def prefixEnd_4060389 : Nat := 4983230072969 + 3 ^ 40 * 4060389 * 2
def baseEnd_4060389 : Nat := 77219674119585905298671

theorem tailTrace_4060389 : CollatzResearch.WordTrace tailWord_4060389 prefixEnd_4060389 77219674119585905298671 := by
  unfold tailWord_4060389
  simp only [CollatzResearch.WordTrace]
  refine ⟨148094553286911587077200221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98729702191274391384800147 148094553286911587077200221)
  ·
    refine ⟨55535457482591845153950083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148094553286911587077200221 55535457482591845153950083)
    ·
      refine ⟨83303186223887767730925125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55535457482591845153950083 83303186223887767730925125)
      ·
        refine ⟨15619347416978956449548461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83303186223887767730925125 15619347416978956449548461)
        ·
          refine ⟨5857255281367108668580673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15619347416978956449548461 5857255281367108668580673)
          ·
            refine ⟨4392941461025331501435505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5857255281367108668580673 4392941461025331501435505)
            ·
              refine ⟨3294706095768998626076629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4392941461025331501435505 3294706095768998626076629)
              ·
                refine ⟨77219674119585905298671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3294706095768998626076629 77219674119585905298671)
                ·
                  rfl

theorem cell23_4060389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 7].length) (baseStart_4060389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060389 prefixEnd_4060389 := by exact prefixLift 4060389
  have htrace : WordTrace (prefixWord ++ tailWord_4060389) baseStart_4060389 baseEnd_4060389 := by
    simpa [prefixWord, tailWord_4060389, baseEnd_4060389] using wordTrace_append hprefix tailTrace_4060389
  have hstable : (prefixWord ++ tailWord_4060389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060389).length < 2 ^ (prefixWord ++ tailWord_4060389).sum := by decide
  have hdescent : baseEnd_4060389 < baseStart_4060389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060395 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 5]
def baseStart_4060395 : Nat := 118140960795 + 4060395 * 2 ^ 59
def prefixEnd_4060395 : Nat := 4983230072969 + 3 ^ 40 * 4060395 * 2
def baseEnd_4060395 : Nat := 2084934282112746419589089

theorem tailTrace_4060395 : CollatzResearch.WordTrace tailWord_4060395 prefixEnd_4060395 2084934282112746419589089 := by
  unfold tailWord_4060395
  simp only [CollatzResearch.WordTrace]
  refine ⟨148094772124889850101918639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98729848083259900067945759 148094772124889850101918639)
  ·
    refine ⟨222142158187334775152877959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148094772124889850101918639 222142158187334775152877959)
    ·
      refine ⟨333213237281002162729316939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222142158187334775152877959 333213237281002162729316939)
      ·
        refine ⟨499819855921503244093975409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333213237281002162729316939 499819855921503244093975409)
        ·
          refine ⟨374864891941127433070481557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499819855921503244093975409 374864891941127433070481557)
          ·
            refine ⟨17571791809740348425178823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 374864891941127433070481557 17571791809740348425178823)
            ·
              refine ⟨26357687714610522637768235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17571791809740348425178823 26357687714610522637768235)
              ·
                refine ⟨39536531571915783956652353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26357687714610522637768235 39536531571915783956652353)
                ·
                  refine ⟨29652398678936837967489265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39536531571915783956652353 29652398678936837967489265)
                  ·
                    refine ⟨22239299009202628475616949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29652398678936837967489265 22239299009202628475616949)
                    ·
                      refine ⟨2084934282112746419589089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22239299009202628475616949 2084934282112746419589089)
                      ·
                        rfl

theorem cell23_4060395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 5].length) (baseStart_4060395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060395 prefixEnd_4060395 := by exact prefixLift 4060395
  have htrace : WordTrace (prefixWord ++ tailWord_4060395) baseStart_4060395 baseEnd_4060395 := by
    simpa [prefixWord, tailWord_4060395, baseEnd_4060395] using wordTrace_append hprefix tailTrace_4060395
  have hstable : (prefixWord ++ tailWord_4060395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060395).length < 2 ^ (prefixWord ++ tailWord_4060395).sum := by decide
  have hdescent : baseEnd_4060395 < baseStart_4060395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060409 : List Nat := [1, 2, 1, 3, 1, 1, 3, 5, 1, 3, 2]
def baseStart_4060409 : Nat := 118140960795 + 4060409 * 2 ^ 59
def prefixEnd_4060409 : Nat := 4983230072969 + 3 ^ 40 * 4060409 * 2
def baseEnd_4060409 : Nat := 2084941470841909364814025

theorem tailTrace_4060409 : CollatzResearch.WordTrace tailWord_4060409 prefixEnd_4060409 2084941470841909364814025 := by
  unfold tailWord_4060409
  simp only [CollatzResearch.WordTrace]
  refine ⟨148095282746839130492928281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98730188497892753661952187 148095282746839130492928281)
  ·
    refine ⟨111071462060129347869696211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148095282746839130492928281 111071462060129347869696211)
    ·
      refine ⟨166607193090194021804544317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111071462060129347869696211 166607193090194021804544317)
      ·
        refine ⟨62477697408822758176704119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166607193090194021804544317 62477697408822758176704119)
        ·
          refine ⟨93716546113234137265056179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62477697408822758176704119 93716546113234137265056179)
          ·
            refine ⟨140574819169851205897584269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93716546113234137265056179 140574819169851205897584269)
            ·
              refine ⟨52715557188694202211594101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140574819169851205897584269 52715557188694202211594101)
              ·
                refine ⟨4942083486440081457336947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52715557188694202211594101 4942083486440081457336947)
                ·
                  refine ⟨7413125229660122186005421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4942083486440081457336947 7413125229660122186005421)
                  ·
                    refine ⟨2779921961122545819752033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7413125229660122186005421 2779921961122545819752033)
                    ·
                      refine ⟨2084941470841909364814025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2779921961122545819752033 2084941470841909364814025)
                      ·
                        rfl

theorem cell23_4060409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_4060409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060409 prefixEnd_4060409 := by exact prefixLift 4060409
  have htrace : WordTrace (prefixWord ++ tailWord_4060409) baseStart_4060409 baseEnd_4060409 := by
    simpa [prefixWord, tailWord_4060409, baseEnd_4060409] using wordTrace_append hprefix tailTrace_4060409
  have hstable : (prefixWord ++ tailWord_4060409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060409).length < 2 ^ (prefixWord ++ tailWord_4060409).sum := by decide
  have hdescent : baseEnd_4060409 < baseStart_4060409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060425 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 1, 3, 5]
def baseStart_4060425 : Nat := 118140960795 + 4060425 * 2 ^ 59
def prefixEnd_4060425 : Nat := 4983230072969 + 3 ^ 40 * 4060425 * 2
def baseEnd_4060425 : Nat := 2084949686532381302213951

theorem tailTrace_4060425 : CollatzResearch.WordTrace tailWord_4060425 prefixEnd_4060425 2084949686532381302213951 := by
  unfold tailWord_4060425
  simp only [CollatzResearch.WordTrace]
  refine ⟨148095866314781165225510729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98730577543187443483673819 148095866314781165225510729)
  ·
    refine ⟨111071899736085873919133047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148095866314781165225510729 111071899736085873919133047)
    ·
      refine ⟨166607849604128810878699571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111071899736085873919133047 166607849604128810878699571)
      ·
        refine ⟨249911774406193216318049357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166607849604128810878699571 249911774406193216318049357)
        ·
          refine ⟨93716915402322456119268509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249911774406193216318049357 93716915402322456119268509)
          ·
            refine ⟨35143843275870921044725691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93716915402322456119268509 35143843275870921044725691)
            ·
              refine ⟨52715764913806381567088537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35143843275870921044725691 52715764913806381567088537)
              ·
                refine ⟨39536823685354786175316403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52715764913806381567088537 39536823685354786175316403)
                ·
                  refine ⟨59305235528032179262974605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39536823685354786175316403 59305235528032179262974605)
                  ·
                    refine ⟨22239463323012067223615477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59305235528032179262974605 22239463323012067223615477)
                    ·
                      refine ⟨2084949686532381302213951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22239463323012067223615477 2084949686532381302213951)
                      ·
                        rfl

theorem cell23_4060425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_4060425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060425 prefixEnd_4060425 := by exact prefixLift 4060425
  have htrace : WordTrace (prefixWord ++ tailWord_4060425) baseStart_4060425 baseEnd_4060425 := by
    simpa [prefixWord, tailWord_4060425, baseEnd_4060425] using wordTrace_append hprefix tailTrace_4060425
  have hstable : (prefixWord ++ tailWord_4060425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060425).length < 2 ^ (prefixWord ++ tailWord_4060425).sum := by decide
  have hdescent : baseEnd_4060425 < baseStart_4060425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060439 : List Nat := [1, 1, 3, 4, 1, 1, 2, 3, 1, 4, 2]
def baseStart_4060439 : Nat := 118140960795 + 4060439 * 2 ^ 59
def prefixEnd_4060439 : Nat := 4983230072969 + 3 ^ 40 * 4060439 * 2
def baseEnd_4060439 : Nat := 2084956875261544247438887

theorem tailTrace_4060439 : CollatzResearch.WordTrace tailWord_4060439 prefixEnd_4060439 2084956875261544247438887 := by
  unfold tailWord_4060439
  simp only [CollatzResearch.WordTrace]
  refine ⟨148096376936730445616520371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98730917957820297077680247 148096376936730445616520371)
  ·
    refine ⟨222144565405095668424780557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148096376936730445616520371 222144565405095668424780557)
    ·
      refine ⟨83304212026910875659292709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222144565405095668424780557 83304212026910875659292709)
      ·
        refine ⟨15619539755045789186117383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83304212026910875659292709 15619539755045789186117383)
        ·
          refine ⟨23429309632568683779176075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15619539755045789186117383 23429309632568683779176075)
          ·
            refine ⟨35143964448853025668764113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23429309632568683779176075 35143964448853025668764113)
            ·
              refine ⟨26357973336639769251573085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35143964448853025668764113 26357973336639769251573085)
              ·
                refine ⟨9884240001239913469339907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26357973336639769251573085 9884240001239913469339907)
                ·
                  refine ⟨14826360001859870204009861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9884240001239913469339907 14826360001859870204009861)
                  ·
                    refine ⟨2779942500348725663251849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14826360001859870204009861 2779942500348725663251849)
                    ·
                      refine ⟨2084956875261544247438887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2779942500348725663251849 2084956875261544247438887)
                      ·
                        rfl

theorem cell23_4060439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_4060439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060439 prefixEnd_4060439 := by exact prefixLift 4060439
  have htrace : WordTrace (prefixWord ++ tailWord_4060439) baseStart_4060439 baseEnd_4060439 := by
    simpa [prefixWord, tailWord_4060439, baseEnd_4060439] using wordTrace_append hprefix tailTrace_4060439
  have hstable : (prefixWord ++ tailWord_4060439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060439).length < 2 ^ (prefixWord ++ tailWord_4060439).sum := by decide
  have hdescent : baseEnd_4060439 < baseStart_4060439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060442 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5]
def baseStart_4060442 : Nat := 118140960795 + 4060442 * 2 ^ 59
def prefixEnd_4060442 : Nat := 4983230072969 + 3 ^ 40 * 4060442 * 2
def baseEnd_4060442 : Nat := 2084958415703507735701373

theorem tailTrace_4060442 : CollatzResearch.WordTrace tailWord_4060442 prefixEnd_4060442 2084958415703507735701373 := by
  unfold tailWord_4060442
  simp only [CollatzResearch.WordTrace]
  refine ⟨37024121588929894282219895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98730990903813051419253053 37024121588929894282219895)
  ·
    refine ⟨55536182383394841423329843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37024121588929894282219895 55536182383394841423329843)
    ·
      refine ⟨83304273575092262134994765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55536182383394841423329843 83304273575092262134994765)
      ·
        refine ⟨31239102590659598300623037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83304273575092262134994765 31239102590659598300623037)
        ·
          refine ⟨11714663471497349362733639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31239102590659598300623037 11714663471497349362733639)
          ·
            refine ⟨17571995207246024044100459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11714663471497349362733639 17571995207246024044100459)
            ·
              refine ⟨26357992810869036066150689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17571995207246024044100459 26357992810869036066150689)
              ·
                refine ⟨19768494608151777049613017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26357992810869036066150689 19768494608151777049613017)
                ·
                  refine ⟨14826370956113832787209763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19768494608151777049613017 14826370956113832787209763)
                  ·
                    refine ⟨22239556434170749180814645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14826370956113832787209763 22239556434170749180814645)
                    ·
                      refine ⟨2084958415703507735701373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22239556434170749180814645 2084958415703507735701373)
                      ·
                        rfl

theorem cell23_4060442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_4060442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060442 prefixEnd_4060442 := by exact prefixLift 4060442
  have htrace : WordTrace (prefixWord ++ tailWord_4060442) baseStart_4060442 baseEnd_4060442 := by
    simpa [prefixWord, tailWord_4060442, baseEnd_4060442] using wordTrace_append hprefix tailTrace_4060442
  have hstable : (prefixWord ++ tailWord_4060442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060442).length < 2 ^ (prefixWord ++ tailWord_4060442).sum := by decide
  have hdescent : baseEnd_4060442 < baseStart_4060442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060456 : List Nat := [2, 1, 5, 1, 2, 2, 1, 2, 1, 4, 2]
def baseStart_4060456 : Nat := 118140960795 + 4060456 * 2 ^ 59
def prefixEnd_4060456 : Nat := 4983230072969 + 3 ^ 40 * 4060456 * 2
def baseEnd_4060456 : Nat := 2084965604432670680926309

theorem tailTrace_4060456 : CollatzResearch.WordTrace tailWord_4060456 prefixEnd_4060456 2084965604432670680926309 := by
  unfold tailWord_4060456
  simp only [CollatzResearch.WordTrace]
  refine ⟨74048498488834428759944611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98731331318445905013259481 74048498488834428759944611)
  ·
    refine ⟨111072747733251643139916917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74048498488834428759944611 111072747733251643139916917)
    ·
      refine ⟨10413070099992341544367211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111072747733251643139916917 10413070099992341544367211)
      ·
        refine ⟨15619605149988512316550817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10413070099992341544367211 15619605149988512316550817)
        ·
          refine ⟨11714703862491384237413113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15619605149988512316550817 11714703862491384237413113)
          ·
            refine ⟨8786027896868538178059835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11714703862491384237413113 8786027896868538178059835)
            ·
              refine ⟨13179041845302807267089753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8786027896868538178059835 13179041845302807267089753)
              ·
                refine ⟨9884281383977105450317315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13179041845302807267089753 9884281383977105450317315)
                ·
                  refine ⟨14826422075965658175475973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9884281383977105450317315 14826422075965658175475973)
                  ·
                    refine ⟨2779954139243560907901745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14826422075965658175475973 2779954139243560907901745)
                    ·
                      refine ⟨2084965604432670680926309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2779954139243560907901745 2084965604432670680926309)
                      ·
                        rfl

theorem cell23_4060456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_4060456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060456 prefixEnd_4060456 := by exact prefixLift 4060456
  have htrace : WordTrace (prefixWord ++ tailWord_4060456) baseStart_4060456 baseEnd_4060456 := by
    simpa [prefixWord, tailWord_4060456, baseEnd_4060456] using wordTrace_append hprefix tailTrace_4060456
  have hstable : (prefixWord ++ tailWord_4060456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060456).length < 2 ^ (prefixWord ++ tailWord_4060456).sum := by decide
  have hdescent : baseEnd_4060456 < baseStart_4060456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060472 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 2, 3, 3]
def baseStart_4060472 : Nat := 118140960795 + 4060472 * 2 ^ 59
def prefixEnd_4060472 : Nat := 4983230072969 + 3 ^ 40 * 4060472 * 2
def baseEnd_4060472 : Nat := 2084973820123142618326235

theorem tailTrace_4060472 : CollatzResearch.WordTrace tailWord_4060472 prefixEnd_4060472 2084973820123142618326235 := by
  unfold tailWord_4060472
  simp only [CollatzResearch.WordTrace]
  refine ⟨74048790272805446126235835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98731720363740594834981113 74048790272805446126235835)
  ·
    refine ⟨111073185409208169189353753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74048790272805446126235835 111073185409208169189353753)
    ·
      refine ⟨83304889056906126892015315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111073185409208169189353753 83304889056906126892015315)
      ·
        refine ⟨124957333585359190338022973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83304889056906126892015315 124957333585359190338022973)
        ·
          refine ⟨46859000094509696376758615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124957333585359190338022973 46859000094509696376758615)
          ·
            refine ⟨70288500141764544565137923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46859000094509696376758615 70288500141764544565137923)
            ·
              refine ⟨105432750212646816847706885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70288500141764544565137923 105432750212646816847706885)
              ·
                refine ⟨19768640664871278158945041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105432750212646816847706885 19768640664871278158945041)
                ·
                  refine ⟨14826480498653458619208781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19768640664871278158945041 14826480498653458619208781)
                  ·
                    refine ⟨5559930186995046982203293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14826480498653458619208781 5559930186995046982203293)
                    ·
                      refine ⟨2084973820123142618326235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5559930186995046982203293 2084973820123142618326235)
                      ·
                        rfl

theorem cell23_4060472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 2, 3, 3].length) (baseStart_4060472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060472 prefixEnd_4060472 := by exact prefixLift 4060472
  have htrace : WordTrace (prefixWord ++ tailWord_4060472) baseStart_4060472 baseEnd_4060472 := by
    simpa [prefixWord, tailWord_4060472, baseEnd_4060472] using wordTrace_append hprefix tailTrace_4060472
  have hstable : (prefixWord ++ tailWord_4060472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060472).length < 2 ^ (prefixWord ++ tailWord_4060472).sum := by decide
  have hdescent : baseEnd_4060472 < baseStart_4060472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060479 : List Nat := [1, 1, 2, 2, 4, 3, 1, 4, 5]
def baseStart_4060479 : Nat := 118140960795 + 4060479 * 2 ^ 59
def prefixEnd_4060479 : Nat := 4983230072969 + 3 ^ 40 * 4060479 * 2
def baseEnd_4060479 : Nat := 231664157165302676770967

theorem tailTrace_4060479 : CollatzResearch.WordTrace tailWord_4060479 prefixEnd_4060479 231664157165302676770967 := by
  unfold tailWord_4060479
  simp only [CollatzResearch.WordTrace]
  refine ⟨148097835856585532447976491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98731890571057021631984327 148097835856585532447976491)
  ·
    refine ⟨222146753784878298671964737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148097835856585532447976491 222146753784878298671964737)
    ·
      refine ⟨166610065338658724003973553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222146753784878298671964737 166610065338658724003973553)
      ·
        refine ⟨124957549003994043002980165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166610065338658724003973553 124957549003994043002980165)
        ·
          refine ⟨23429540438248883063058781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124957549003994043002980165 23429540438248883063058781)
          ·
            refine ⟨8786077664343331148647043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23429540438248883063058781 8786077664343331148647043)
            ·
              refine ⟨13179116496514996722970565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8786077664343331148647043 13179116496514996722970565)
              ·
                refine ⟨2471084343096561885556981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13179116496514996722970565 2471084343096561885556981)
                ·
                  refine ⟨231664157165302676770967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2471084343096561885556981 231664157165302676770967)
                  ·
                    rfl

theorem cell23_4060479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 5].length) (baseStart_4060479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060479 prefixEnd_4060479 := by exact prefixLift 4060479
  have htrace : WordTrace (prefixWord ++ tailWord_4060479) baseStart_4060479 baseEnd_4060479 := by
    simpa [prefixWord, tailWord_4060479, baseEnd_4060479] using wordTrace_append hprefix tailTrace_4060479
  have hstable : (prefixWord ++ tailWord_4060479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060479).length < 2 ^ (prefixWord ++ tailWord_4060479).sum := by decide
  have hdescent : baseEnd_4060479 < baseStart_4060479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060529 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 2, 4, 2]
def baseStart_4060529 : Nat := 118140960795 + 4060529 * 2 ^ 59
def prefixEnd_4060529 : Nat := 4983230072969 + 3 ^ 40 * 4060529 * 2
def baseEnd_4060529 : Nat := 2085003088520448895313473

theorem tailTrace_4060529 : CollatzResearch.WordTrace tailWord_4060529 prefixEnd_4060529 2085003088520448895313473 := by
  unfold tailWord_4060529
  simp only [CollatzResearch.WordTrace]
  refine ⟨148099659506404390987296641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98733106337602927324864427 148099659506404390987296641)
  ·
    refine ⟨111074744629803293240472481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148099659506404390987296641 111074744629803293240472481)
    ·
      refine ⟨83306058472352469930354361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111074744629803293240472481 83306058472352469930354361)
      ·
        refine ⟨62479543854264352447765771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83306058472352469930354361 62479543854264352447765771)
        ·
          refine ⟨93719315781396528671648657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62479543854264352447765771 93719315781396528671648657)
          ·
            refine ⟨70289486836047396503736493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93719315781396528671648657 70289486836047396503736493)
            ·
              refine ⟨26358557563517773688901185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70289486836047396503736493 26358557563517773688901185)
              ·
                refine ⟨19768918172638330266675889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26358557563517773688901185 19768918172638330266675889)
                ·
                  refine ⟨14826688629478747700006917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19768918172638330266675889 14826688629478747700006917)
                  ·
                    refine ⟨2780004118027265193751297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14826688629478747700006917 2780004118027265193751297)
                    ·
                      refine ⟨2085003088520448895313473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2780004118027265193751297 2085003088520448895313473)
                      ·
                        rfl

theorem cell23_4060529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_4060529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060529 prefixEnd_4060529 := by exact prefixLift 4060529
  have htrace : WordTrace (prefixWord ++ tailWord_4060529) baseStart_4060529 baseEnd_4060529 := by
    simpa [prefixWord, tailWord_4060529, baseEnd_4060529] using wordTrace_append hprefix tailTrace_4060529
  have hstable : (prefixWord ++ tailWord_4060529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060529).length < 2 ^ (prefixWord ++ tailWord_4060529).sum := by decide
  have hdescent : baseEnd_4060529 < baseStart_4060529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060539 : List Nat := [1, 1, 1, 1, 1, 6, 4, 1, 3, 4]
def baseStart_4060539 : Nat := 118140960795 + 4060539 * 2 ^ 59
def prefixEnd_4060539 : Nat := 4983230072969 + 3 ^ 40 * 4060539 * 2
def baseEnd_4060539 : Nat := 695002741108997952062809

theorem tailTrace_4060539 : CollatzResearch.WordTrace tailWord_4060539 prefixEnd_4060539 695002741108997952062809 := by
  unfold tailWord_4060539
  simp only [CollatzResearch.WordTrace]
  refine ⟨148100024236368162695160671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98733349490912108463440447 148100024236368162695160671)
  ·
    refine ⟨222150036354552244042741007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148100024236368162695160671 222150036354552244042741007)
    ·
      refine ⟨333225054531828366064111511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222150036354552244042741007 333225054531828366064111511)
      ·
        refine ⟨499837581797742549096167267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333225054531828366064111511 499837581797742549096167267)
        ·
          refine ⟨749756372696613823644250901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499837581797742549096167267 749756372696613823644250901)
          ·
            refine ⟨35144829970153772983324261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 749756372696613823644250901 35144829970153772983324261)
            ·
              refine ⟨6589655619403832434373299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35144829970153772983324261 6589655619403832434373299)
              ·
                refine ⟨9884483429105748651559949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6589655619403832434373299 9884483429105748651559949)
                ·
                  refine ⟨3706681285914655744334981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9884483429105748651559949 3706681285914655744334981)
                  ·
                    refine ⟨695002741108997952062809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3706681285914655744334981 695002741108997952062809)
                    ·
                      rfl

theorem cell23_4060539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 4].length) (baseStart_4060539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060539 prefixEnd_4060539 := by exact prefixLift 4060539
  have htrace : WordTrace (prefixWord ++ tailWord_4060539) baseStart_4060539 baseEnd_4060539 := by
    simpa [prefixWord, tailWord_4060539, baseEnd_4060539] using wordTrace_append hprefix tailTrace_4060539
  have hstable : (prefixWord ++ tailWord_4060539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060539).length < 2 ^ (prefixWord ++ tailWord_4060539).sum := by decide
  have hdescent : baseEnd_4060539 < baseStart_4060539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060546 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_4060546 : Nat := 118140960795 + 4060546 * 2 ^ 59
def prefixEnd_4060546 : Nat := 4983230072969 + 3 ^ 40 * 4060546 * 2
def baseEnd_4060546 : Nat := 2085011817691575328800895

theorem tailTrace_4060546 : CollatzResearch.WordTrace tailWord_4060546 prefixEnd_4060546 2085011817691575328800895 := by
  unfold tailWord_4060546
  simp only [CollatzResearch.WordTrace]
  refine ⟨37025069886835700722666373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98733519698228535260443661 37025069886835700722666373)
  ·
    refine ⟨6942200603781693885499945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37025069886835700722666373 6942200603781693885499945)
    ·
      refine ⟨5206650452836270414124959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6942200603781693885499945 5206650452836270414124959)
      ·
        refine ⟨7809975679254405621187439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5206650452836270414124959 7809975679254405621187439)
        ·
          refine ⟨11714963518881608431781159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7809975679254405621187439 11714963518881608431781159)
          ·
            refine ⟨17572445278322412647671739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11714963518881608431781159 17572445278322412647671739)
            ·
              refine ⟨26358667917483618971507609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17572445278322412647671739 26358667917483618971507609)
              ·
                refine ⟨19769000938112714228630707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26358667917483618971507609 19769000938112714228630707)
                ·
                  refine ⟨29653501407169071342946061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19769000938112714228630707 29653501407169071342946061)
                  ·
                    refine ⟨11120063027688401753604773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29653501407169071342946061 11120063027688401753604773)
                    ·
                      refine ⟨2085011817691575328800895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11120063027688401753604773 2085011817691575328800895)
                      ·
                        rfl

theorem cell23_4060546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_4060546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060546 prefixEnd_4060546 := by exact prefixLift 4060546
  have htrace : WordTrace (prefixWord ++ tailWord_4060546) baseStart_4060546 baseEnd_4060546 := by
    simpa [prefixWord, tailWord_4060546, baseEnd_4060546] using wordTrace_append hprefix tailTrace_4060546
  have hstable : (prefixWord ++ tailWord_4060546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060546).length < 2 ^ (prefixWord ++ tailWord_4060546).sum := by decide
  have hdescent : baseEnd_4060546 < baseStart_4060546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060573 : List Nat := [1, 4, 2, 1, 3, 1, 3, 3, 1, 4]
def baseStart_4060573 : Nat := 118140960795 + 4060573 * 2 ^ 59
def prefixEnd_4060573 : Nat := 4983230072969 + 3 ^ 40 * 4060573 * 2
def baseEnd_4060573 : Nat := 695008560556415574387757

theorem tailTrace_4060573 : CollatzResearch.WordTrace tailWord_4060573 prefixEnd_4060573 695008560556415574387757 := by
  unfold tailWord_4060573
  simp only [CollatzResearch.WordTrace]
  refine ⟨148101264318244986501898373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98734176212163324334598915 148101264318244986501898373)
  ·
    refine ⟨27768987059670934969105945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148101264318244986501898373 27768987059670934969105945)
    ·
      refine ⟨20826740294753201226829459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27768987059670934969105945 20826740294753201226829459)
      ·
        refine ⟨31240110442129801840244189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20826740294753201226829459 31240110442129801840244189)
        ·
          refine ⟨11715041415798675690091571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31240110442129801840244189 11715041415798675690091571)
          ·
            refine ⟨17572562123698013535137357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11715041415798675690091571 17572562123698013535137357)
            ·
              refine ⟨6589710796386755075676509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17572562123698013535137357 6589710796386755075676509)
              ·
                refine ⟨2471141548645033153378691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6589710796386755075676509 2471141548645033153378691)
                ·
                  refine ⟨3706712322967549730068037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2471141548645033153378691 3706712322967549730068037)
                  ·
                    refine ⟨695008560556415574387757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3706712322967549730068037 695008560556415574387757)
                    ·
                      rfl

theorem cell23_4060573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_4060573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060573 prefixEnd_4060573 := by exact prefixLift 4060573
  have htrace : WordTrace (prefixWord ++ tailWord_4060573) baseStart_4060573 baseEnd_4060573 := by
    simpa [prefixWord, tailWord_4060573, baseEnd_4060573] using wordTrace_append hprefix tailTrace_4060573
  have hstable : (prefixWord ++ tailWord_4060573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060573).length < 2 ^ (prefixWord ++ tailWord_4060573).sum := by decide
  have hdescent : baseEnd_4060573 < baseStart_4060573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060602 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4]
def baseStart_4060602 : Nat := 118140960795 + 4060602 * 2 ^ 59
def prefixEnd_4060602 : Nat := 4983230072969 + 3 ^ 40 * 4060602 * 2
def baseEnd_4060602 : Nat := 2085040572608227109700637

theorem tailTrace_4060602 : CollatzResearch.WordTrace tailWord_4060602 prefixEnd_4060602 2085040572608227109700637 := by
  unfold tailWord_4060602
  simp only [CollatzResearch.WordTrace]
  refine ⟨37025580508784981113676015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98734881356759949636469373 37025580508784981113676015)
  ·
    refine ⟨55538370763177471670514023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37025580508784981113676015 55538370763177471670514023)
    ·
      refine ⟨83307556144766207505771035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55538370763177471670514023 83307556144766207505771035)
      ·
        refine ⟨124961334217149311258656553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83307556144766207505771035 124961334217149311258656553)
        ·
          refine ⟨93721000662861983443992415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124961334217149311258656553 93721000662861983443992415)
          ·
            refine ⟨140581500994292975165988623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93721000662861983443992415 140581500994292975165988623)
            ·
              refine ⟨210872251491439462748982935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140581500994292975165988623 210872251491439462748982935)
              ·
                refine ⟨316308377237159194123474403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210872251491439462748982935 316308377237159194123474403)
                ·
                  refine ⟨474462565855738791185211605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316308377237159194123474403 474462565855738791185211605)
                  ·
                    refine ⟨11120216387243877918403397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 474462565855738791185211605 11120216387243877918403397)
                    ·
                      refine ⟨2085040572608227109700637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11120216387243877918403397 2085040572608227109700637)
                      ·
                        rfl

theorem cell23_4060602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_4060602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060602 prefixEnd_4060602 := by exact prefixLift 4060602
  have htrace : WordTrace (prefixWord ++ tailWord_4060602) baseStart_4060602 baseEnd_4060602 := by
    simpa [prefixWord, tailWord_4060602, baseEnd_4060602] using wordTrace_append hprefix tailTrace_4060602
  have hstable : (prefixWord ++ tailWord_4060602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060602).length < 2 ^ (prefixWord ++ tailWord_4060602).sum := by decide
  have hdescent : baseEnd_4060602 < baseStart_4060602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060606 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2]
def baseStart_4060606 : Nat := 118140960795 + 4060606 * 2 ^ 59
def prefixEnd_4060606 : Nat := 4983230072969 + 3 ^ 40 * 4060606 * 2
def baseEnd_4060606 : Nat := 2085042626530845094050619

theorem tailTrace_4060606 : CollatzResearch.WordTrace tailWord_4060606 prefixEnd_4060606 2085042626530845094050619 := by
  unfold tailWord_4060606
  simp only [CollatzResearch.WordTrace]
  refine ⟨18512808490890679142231209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98734978618083622091899781 18512808490890679142231209)
  ·
    refine ⟨13884606368168009356673407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18512808490890679142231209 13884606368168009356673407)
    ·
      refine ⟨20826909552252014035010111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13884606368168009356673407 20826909552252014035010111)
      ·
        refine ⟨31240364328378021052515167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20826909552252014035010111 31240364328378021052515167)
        ·
          refine ⟨46860546492567031578772751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31240364328378021052515167 46860546492567031578772751)
          ·
            refine ⟨70290819738850547368159127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46860546492567031578772751 70290819738850547368159127)
            ·
              refine ⟨105436229608275821052238691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70290819738850547368159127 105436229608275821052238691)
              ·
                refine ⟨158154344412413731578358037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105436229608275821052238691 158154344412413731578358037)
                ·
                  refine ⟨7413484894331893667735533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158154344412413731578358037 7413484894331893667735533)
                  ·
                    refine ⟨2780056835374460125400825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7413484894331893667735533 2780056835374460125400825)
                    ·
                      refine ⟨2085042626530845094050619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2780056835374460125400825 2085042626530845094050619)
                      ·
                        rfl

theorem cell23_4060606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_4060606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060606 prefixEnd_4060606 := by exact prefixLift 4060606
  have htrace : WordTrace (prefixWord ++ tailWord_4060606) baseStart_4060606 baseEnd_4060606 := by
    simpa [prefixWord, tailWord_4060606, baseEnd_4060606] using wordTrace_append hprefix tailTrace_4060606
  have hstable : (prefixWord ++ tailWord_4060606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060606).length < 2 ^ (prefixWord ++ tailWord_4060606).sum := by decide
  have hdescent : baseEnd_4060606 < baseStart_4060606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060619 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 2, 6, 2]
def baseStart_4060619 : Nat := 118140960795 + 4060619 * 2 ^ 59
def prefixEnd_4060619 : Nat := 4983230072969 + 3 ^ 40 * 4060619 * 2
def baseEnd_4060619 : Nat := 2085049301779353543188059

theorem tailTrace_4060619 : CollatzResearch.WordTrace tailWord_4060619 prefixEnd_4060619 2085049301779353543188059 := by
  unfold tailWord_4060619
  simp only [CollatzResearch.WordTrace]
  refine ⟨148102942076078336358072911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98735294717385557572048607 148102942076078336358072911)
  ·
    refine ⟨222154413114117504537109367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148102942076078336358072911 222154413114117504537109367)
    ·
      refine ⟨333231619671176256805664051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222154413114117504537109367 333231619671176256805664051)
      ·
        refine ⟨499847429506764385208496077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333231619671176256805664051 499847429506764385208496077)
        ·
          refine ⟨187442786065036644453186029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 499847429506764385208496077 187442786065036644453186029)
          ·
            refine ⟨70291044774388741669944761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187442786065036644453186029 70291044774388741669944761)
            ·
              refine ⟨52718283580791556252458571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70291044774388741669944761 52718283580791556252458571)
              ·
                refine ⟨79077425371187334378687857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52718283580791556252458571 79077425371187334378687857)
                ·
                  refine ⟨59308069028390500784015893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79077425371187334378687857 59308069028390500784015893)
                  ·
                    refine ⟨2780065735705804724250745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59308069028390500784015893 2780065735705804724250745)
                    ·
                      refine ⟨2085049301779353543188059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2780065735705804724250745 2085049301779353543188059)
                      ·
                        rfl

theorem cell23_4060619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 6, 2].length) (baseStart_4060619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060619 prefixEnd_4060619 := by exact prefixLift 4060619
  have htrace : WordTrace (prefixWord ++ tailWord_4060619) baseStart_4060619 baseEnd_4060619 := by
    simpa [prefixWord, tailWord_4060619, baseEnd_4060619] using wordTrace_append hprefix tailTrace_4060619
  have hstable : (prefixWord ++ tailWord_4060619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060619).length < 2 ^ (prefixWord ++ tailWord_4060619).sum := by decide
  have hdescent : baseEnd_4060619 < baseStart_4060619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060629 : List Nat := [1, 3, 2, 3, 1, 1, 3, 2, 1, 6]
def baseStart_4060629 : Nat := 118140960795 + 4060629 * 2 ^ 59
def prefixEnd_4060629 : Nat := 4983230072969 + 3 ^ 40 * 4060629 * 2
def baseEnd_4060629 : Nat := 695018145528632834687671

theorem tailTrace_4060629 : CollatzResearch.WordTrace tailWord_4060629 prefixEnd_4060629 695018145528632834687671 := by
  unfold tailWord_4060629
  simp only [CollatzResearch.WordTrace]
  refine ⟨148103306806042108065936941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98735537870694738710624627 148103306806042108065936941)
  ·
    refine ⟨55538740052265790524726353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148103306806042108065936941 55538740052265790524726353)
    ·
      refine ⟨41654055039199342893544765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55538740052265790524726353 41654055039199342893544765)
      ·
        refine ⟨15620270639699753585079287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41654055039199342893544765 15620270639699753585079287)
        ·
          refine ⟨23430405959549630377618931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15620270639699753585079287 23430405959549630377618931)
          ·
            refine ⟨35145608939324445566428397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23430405959549630377618931 35145608939324445566428397)
            ·
              refine ⟨13179603352246667087410649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35145608939324445566428397 13179603352246667087410649)
              ·
                refine ⟨9884702514185000315557987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13179603352246667087410649 9884702514185000315557987)
                ·
                  refine ⟨14827053771277500473336981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9884702514185000315557987 14827053771277500473336981)
                  ·
                    refine ⟨695018145528632834687671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14827053771277500473336981 695018145528632834687671)
                    ·
                      rfl

theorem cell23_4060629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_4060629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060629 prefixEnd_4060629 := by exact prefixLift 4060629
  have htrace : WordTrace (prefixWord ++ tailWord_4060629) baseStart_4060629 baseEnd_4060629 := by
    simpa [prefixWord, tailWord_4060629, baseEnd_4060629] using wordTrace_append hprefix tailTrace_4060629
  have hstable : (prefixWord ++ tailWord_4060629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060629).length < 2 ^ (prefixWord ++ tailWord_4060629).sum := by decide
  have hdescent : baseEnd_4060629 < baseStart_4060629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060647 : List Nat := [1, 1, 5, 2, 1, 4, 2, 2, 1, 1, 3]
def baseStart_4060647 : Nat := 118140960795 + 4060647 * 2 ^ 59
def prefixEnd_4060647 : Nat := 4983230072969 + 3 ^ 40 * 4060647 * 2
def baseEnd_4060647 : Nat := 2085063679237679433637931

theorem tailTrace_4060647 : CollatzResearch.WordTrace tailWord_4060647 prefixEnd_4060647 2085063679237679433637931 := by
  unfold tailWord_4060647
  simp only [CollatzResearch.WordTrace]
  refine ⟨148103963319976897140092195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98735975546651264760061463 148103963319976897140092195)
  ·
    refine ⟨222155944979965345710138293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148103963319976897140092195 222155944979965345710138293)
    ·
      refine ⟨20827119841871751160325465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222155944979965345710138293 20827119841871751160325465)
      ·
        refine ⟨15620339881403813370244099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20827119841871751160325465 15620339881403813370244099)
        ·
          refine ⟨23430509822105720055366149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15620339881403813370244099 23430509822105720055366149)
          ·
            refine ⟨4393220591644822510381153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23430509822105720055366149 4393220591644822510381153)
            ·
              refine ⟨3294915443733616882785865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4393220591644822510381153 3294915443733616882785865)
              ·
                refine ⟨2471186582800212662089399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3294915443733616882785865 2471186582800212662089399)
                ·
                  refine ⟨3706779874200318993134099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2471186582800212662089399 3706779874200318993134099)
                  ·
                    refine ⟨5560169811300478489701149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3706779874200318993134099 5560169811300478489701149)
                    ·
                      refine ⟨2085063679237679433637931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5560169811300478489701149 2085063679237679433637931)
                      ·
                        rfl

theorem cell23_4060647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_4060647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060647 prefixEnd_4060647 := by exact prefixLift 4060647
  have htrace : WordTrace (prefixWord ++ tailWord_4060647) baseStart_4060647 baseEnd_4060647 := by
    simpa [prefixWord, tailWord_4060647, baseEnd_4060647] using wordTrace_append hprefix tailTrace_4060647
  have hstable : (prefixWord ++ tailWord_4060647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060647).length < 2 ^ (prefixWord ++ tailWord_4060647).sum := by decide
  have hdescent : baseEnd_4060647 < baseStart_4060647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060652 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 7]
def baseStart_4060652 : Nat := 118140960795 + 4060652 * 2 ^ 59
def prefixEnd_4060652 : Nat := 4983230072969 + 3 ^ 40 * 4060652 * 2
def baseEnd_4060652 : Nat := 2085066246640951914075407

theorem tailTrace_4060652 : CollatzResearch.WordTrace tailWord_4060652 prefixEnd_4060652 2085066246640951914075407 := by
  unfold tailWord_4060652
  simp only [CollatzResearch.WordTrace]
  refine ⟨74052072842479391497012105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98736097123305855329349473 74052072842479391497012105)
  ·
    refine ⟨55539054631859543622759079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74052072842479391497012105 55539054631859543622759079)
    ·
      refine ⟨83308581947789315434138619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55539054631859543622759079 83308581947789315434138619)
      ·
        refine ⟨124962872921683973151207929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83308581947789315434138619 124962872921683973151207929)
        ·
          refine ⟨93722154691262979863405947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124962872921683973151207929 93722154691262979863405947)
          ·
            refine ⟨140583232036894469795108921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93722154691262979863405947 140583232036894469795108921)
            ·
              refine ⟨105437424027670852346331691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140583232036894469795108921 105437424027670852346331691)
              ·
                refine ⟨158156136041506278519497537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105437424027670852346331691 158156136041506278519497537)
                ·
                  refine ⟨118617102031129708889623153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158156136041506278519497537 118617102031129708889623153)
                  ·
                    refine ⟨88962826523347281667217365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118617102031129708889623153 88962826523347281667217365)
                    ·
                      refine ⟨2085066246640951914075407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88962826523347281667217365 2085066246640951914075407)
                      ·
                        rfl

theorem cell23_4060652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_4060652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060652 prefixEnd_4060652 := by exact prefixLift 4060652
  have htrace : WordTrace (prefixWord ++ tailWord_4060652) baseStart_4060652 baseEnd_4060652 := by
    simpa [prefixWord, tailWord_4060652, baseEnd_4060652] using wordTrace_append hprefix tailTrace_4060652
  have hstable : (prefixWord ++ tailWord_4060652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060652).length < 2 ^ (prefixWord ++ tailWord_4060652).sum := by decide
  have hdescent : baseEnd_4060652 < baseStart_4060652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060703 : List Nat := [1, 1, 2, 4, 1, 1, 5, 2, 2, 1, 3]
def baseStart_4060703 : Nat := 118140960795 + 4060703 * 2 ^ 59
def prefixEnd_4060703 : Nat := 4983230072969 + 3 ^ 40 * 4060703 * 2
def baseEnd_4060703 : Nat := 2085092434154331214537673

theorem tailTrace_4060703 : CollatzResearch.WordTrace tailWord_4060703 prefixEnd_4060703 2085092434154331214537673 := by
  unfold tailWord_4060703
  simp only [CollatzResearch.WordTrace]
  refine ⟨148106005807774018704130763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98737337205182679136087175 148106005807774018704130763)
  ·
    refine ⟨222159008711661028056196145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148106005807774018704130763 222159008711661028056196145)
    ·
      refine ⟨166619256533745771042147109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222159008711661028056196145 166619256533745771042147109)
      ·
        refine ⟨31241110600077332070402583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166619256533745771042147109 31241110600077332070402583)
        ·
          refine ⟨46861665900115998105603875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31241110600077332070402583 46861665900115998105603875)
          ·
            refine ⟨70292498850173997158405813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46861665900115998105603875 70292498850173997158405813)
            ·
              refine ⟨6589921767203812233600545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70292498850173997158405813 6589921767203812233600545)
              ·
                refine ⟨4942441325402859175200409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6589921767203812233600545 4942441325402859175200409)
                ·
                  refine ⟨3706830994052144381400307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4942441325402859175200409 3706830994052144381400307)
                  ·
                    refine ⟨5560246491078216572100461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3706830994052144381400307 5560246491078216572100461)
                    ·
                      refine ⟨2085092434154331214537673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5560246491078216572100461 2085092434154331214537673)
                      ·
                        rfl

theorem cell23_4060703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_4060703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060703 prefixEnd_4060703 := by exact prefixLift 4060703
  have htrace : WordTrace (prefixWord ++ tailWord_4060703) baseStart_4060703 baseEnd_4060703 := by
    simpa [prefixWord, tailWord_4060703, baseEnd_4060703] using wordTrace_append hprefix tailTrace_4060703
  have hstable : (prefixWord ++ tailWord_4060703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060703).length < 2 ^ (prefixWord ++ tailWord_4060703).sum := by decide
  have hdescent : baseEnd_4060703 < baseStart_4060703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060799 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 4]
def baseStart_4060799 : Nat := 118140960795 + 4060799 * 2 ^ 59
def prefixEnd_4060799 : Nat := 4983230072969 + 3 ^ 40 * 4060799 * 2
def baseEnd_4060799 : Nat := 2085141728297162838937231

theorem tailTrace_4060799 : CollatzResearch.WordTrace tailWord_4060799 prefixEnd_4060799 2085141728297162838937231 := by
  unfold tailWord_4060799
  simp only [CollatzResearch.WordTrace]
  refine ⟨148109507215426227099625451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98739671476950818066416967 148109507215426227099625451)
  ·
    refine ⟨222164260823139340649438177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148109507215426227099625451 222164260823139340649438177)
    ·
      refine ⟨166623195617354505487078633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222164260823139340649438177 166623195617354505487078633)
      ·
        refine ⟨124967396713015879115308975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166623195617354505487078633 124967396713015879115308975)
        ·
          refine ⟨187451095069523818672963463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124967396713015879115308975 187451095069523818672963463)
          ·
            refine ⟨281176642604285728009445195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187451095069523818672963463 281176642604285728009445195)
            ·
              refine ⟨421764963906428592014167793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281176642604285728009445195 421764963906428592014167793)
              ·
                refine ⟨316323722929821444010625845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421764963906428592014167793 316323722929821444010625845)
                ·
                  refine ⟨29655349024670760375996173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 316323722929821444010625845 29655349024670760375996173)
                  ·
                    refine ⟨11120755884251535140998565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29655349024670760375996173 11120755884251535140998565)
                    ·
                      refine ⟨2085141728297162838937231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11120755884251535140998565 2085141728297162838937231)
                      ·
                        rfl

theorem cell23_4060799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_4060799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060799 prefixEnd_4060799 := by exact prefixLift 4060799
  have htrace : WordTrace (prefixWord ++ tailWord_4060799) baseStart_4060799 baseEnd_4060799 := by
    simpa [prefixWord, tailWord_4060799, baseEnd_4060799] using wordTrace_append hprefix tailTrace_4060799
  have hstable : (prefixWord ++ tailWord_4060799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060799).length < 2 ^ (prefixWord ++ tailWord_4060799).sum := by decide
  have hdescent : baseEnd_4060799 < baseStart_4060799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060816 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 3, 6, 2]
def baseStart_4060816 : Nat := 118140960795 + 4060816 * 2 ^ 59
def prefixEnd_4060816 : Nat := 4983230072969 + 3 ^ 40 * 4060816 * 2
def baseEnd_4060816 : Nat := 2085150457468289272424653

theorem tailTrace_4060816 : CollatzResearch.WordTrace tailWord_4060816 prefixEnd_4060816 2085150457468289272424653 := by
  unfold tailWord_4060816
  simp only [CollatzResearch.WordTrace]
  refine ⟨74055063628182319501497151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98740084837576426001996201 74055063628182319501497151)
  ·
    refine ⟨111082595442273479252245727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74055063628182319501497151 111082595442273479252245727)
    ·
      refine ⟨166623893163410218878368591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111082595442273479252245727 166623893163410218878368591)
      ·
        refine ⟨249935839745115328317552887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166623893163410218878368591 249935839745115328317552887)
        ·
          refine ⟨374903759617672992476329331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249935839745115328317552887 374903759617672992476329331)
          ·
            refine ⟨562355639426509488714493997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374903759617672992476329331 562355639426509488714493997)
            ·
              refine ⟨210883364784941058267935249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 562355639426509488714493997 210883364784941058267935249)
              ·
                refine ⟨158162523588705793700951437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210883364784941058267935249 158162523588705793700951437)
                ·
                  refine ⟨59310946345764672637856789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158162523588705793700951437 59310946345764672637856789)
                  ·
                    refine ⟨2780200609957719029899537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59310946345764672637856789 2780200609957719029899537)
                    ·
                      refine ⟨2085150457468289272424653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2780200609957719029899537 2085150457468289272424653)
                      ·
                        rfl

theorem cell23_4060816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 6, 2].length) (baseStart_4060816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060816 prefixEnd_4060816 := by exact prefixLift 4060816
  have htrace : WordTrace (prefixWord ++ tailWord_4060816) baseStart_4060816 baseEnd_4060816 := by
    simpa [prefixWord, tailWord_4060816, baseEnd_4060816] using wordTrace_append hprefix tailTrace_4060816
  have hstable : (prefixWord ++ tailWord_4060816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060816).length < 2 ^ (prefixWord ++ tailWord_4060816).sum := by decide
  have hdescent : baseEnd_4060816 < baseStart_4060816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060833 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 1, 6, 2]
def baseStart_4060833 : Nat := 118140960795 + 4060833 * 2 ^ 59
def prefixEnd_4060833 : Nat := 4983230072969 + 3 ^ 40 * 4060833 * 2
def baseEnd_4060833 : Nat := 2085159186639415705912075

theorem tailTrace_4060833 : CollatzResearch.WordTrace tailWord_4060833 prefixEnd_4060833 2085159186639415705912075 := by
  unfold tailWord_4060833
  simp only [CollatzResearch.WordTrace]
  refine ⟨148110747297303050906363153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98740498198202033937575435 148110747297303050906363153)
  ·
    refine ⟨111083060472977288179772365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148110747297303050906363153 111083060472977288179772365)
    ·
      refine ⟨41656147677366483067414637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111083060472977288179772365 41656147677366483067414637)
      ·
        refine ⟨15621055379012431150280489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41656147677366483067414637 15621055379012431150280489)
        ·
          refine ⟨11715791534259323362710367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15621055379012431150280489 11715791534259323362710367)
          ·
            refine ⟨17573687301388985044065551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11715791534259323362710367 17573687301388985044065551)
            ·
              refine ⟨26360530952083477566098327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17573687301388985044065551 26360530952083477566098327)
              ·
                refine ⟨39540796428125216349147491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26360530952083477566098327 39540796428125216349147491)
                ·
                  refine ⟨59311194642187824523721237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39540796428125216349147491 59311194642187824523721237)
                  ·
                    refine ⟨2780212248852554274549433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59311194642187824523721237 2780212248852554274549433)
                    ·
                      refine ⟨2085159186639415705912075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2780212248852554274549433 2085159186639415705912075)
                      ·
                        rfl

theorem cell23_4060833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_4060833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060833 prefixEnd_4060833 := by exact prefixLift 4060833
  have htrace : WordTrace (prefixWord ++ tailWord_4060833) baseStart_4060833 baseEnd_4060833 := by
    simpa [prefixWord, tailWord_4060833, baseEnd_4060833] using wordTrace_append hprefix tailTrace_4060833
  have hstable : (prefixWord ++ tailWord_4060833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060833).length < 2 ^ (prefixWord ++ tailWord_4060833).sum := by decide
  have hdescent : baseEnd_4060833 < baseStart_4060833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060859 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 6]
def baseStart_4060859 : Nat := 118140960795 + 4060859 * 2 ^ 59
def prefixEnd_4060859 : Nat := 4983230072969 + 3 ^ 40 * 4060859 * 2
def baseEnd_4060859 : Nat := 2085172537136432604186955

theorem tailTrace_4060859 : CollatzResearch.WordTrace tailWord_4060859 prefixEnd_4060859 2085172537136432604186955 := by
  unfold tailWord_4060859
  simp only [CollatzResearch.WordTrace]
  refine ⟨148111695595208857346809631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98741130396805904897873087 148111695595208857346809631)
  ·
    refine ⟨222167543392813286020214447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148111695595208857346809631 222167543392813286020214447)
    ·
      refine ⟨333251315089219929030321671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222167543392813286020214447 333251315089219929030321671)
      ·
        refine ⟨499876972633829893545482507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333251315089219929030321671 499876972633829893545482507)
        ·
          refine ⟨749815458950744840318223761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499876972633829893545482507 749815458950744840318223761)
          ·
            refine ⟨562361594213058630238667821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 749815458950744840318223761 562361594213058630238667821)
            ·
              refine ⟨210885597829896986339500433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 562361594213058630238667821 210885597829896986339500433)
              ·
                refine ⟨158164198372422739754625325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210885597829896986339500433 158164198372422739754625325)
                ·
                  refine ⟨59311574389658527407984497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158164198372422739754625325 59311574389658527407984497)
                  ·
                    refine ⟨44483680792243895555988373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59311574389658527407984497 44483680792243895555988373)
                    ·
                      refine ⟨2085172537136432604186955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44483680792243895555988373 2085172537136432604186955)
                      ·
                        rfl

theorem cell23_4060859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 6].length) (baseStart_4060859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060859 prefixEnd_4060859 := by exact prefixLift 4060859
  have htrace : WordTrace (prefixWord ++ tailWord_4060859) baseStart_4060859 baseEnd_4060859 := by
    simpa [prefixWord, tailWord_4060859, baseEnd_4060859] using wordTrace_append hprefix tailTrace_4060859
  have hstable : (prefixWord ++ tailWord_4060859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060859).length < 2 ^ (prefixWord ++ tailWord_4060859).sum := by decide
  have hdescent : baseEnd_4060859 < baseStart_4060859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060860 : List Nat := [2, 2, 2, 3, 1, 2, 1, 5, 1, 4]
def baseStart_4060860 : Nat := 118140960795 + 4060860 * 2 ^ 59
def prefixEnd_4060860 : Nat := 4983230072969 + 3 ^ 40 * 4060860 * 2
def baseEnd_4060860 : Nat := 695057683539029033424817

theorem tailTrace_4060860 : CollatzResearch.WordTrace tailWord_4060860 prefixEnd_4060860 695057683539029033424817 := by
  unfold tailWord_4060860
  simp only [CollatzResearch.WordTrace]
  refine ⟨74055866034102617258798017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98741154712136823011730689 74055866034102617258798017)
  ·
    refine ⟨55541899525576962944098513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74055866034102617258798017 55541899525576962944098513)
    ·
      refine ⟨41656424644182722208073885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55541899525576962944098513 41656424644182722208073885)
      ·
        refine ⟨15621159241568520828027707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41656424644182722208073885 15621159241568520828027707)
        ·
          refine ⟨23431738862352781242041561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15621159241568520828027707 23431738862352781242041561)
          ·
            refine ⟨17573804146764585931531171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23431738862352781242041561 17573804146764585931531171)
            ·
              refine ⟨26360706220146878897296757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17573804146764585931531171 26360706220146878897296757)
              ·
                refine ⟨2471316208138769896621571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26360706220146878897296757 2471316208138769896621571)
                ·
                  refine ⟨3706974312208154844932357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2471316208138769896621571 3706974312208154844932357)
                  ·
                    refine ⟨695057683539029033424817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3706974312208154844932357 695057683539029033424817)
                    ·
                      rfl

theorem cell23_4060860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_4060860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060860 prefixEnd_4060860 := by exact prefixLift 4060860
  have htrace : WordTrace (prefixWord ++ tailWord_4060860) baseStart_4060860 baseEnd_4060860 := by
    simpa [prefixWord, tailWord_4060860, baseEnd_4060860] using wordTrace_append hprefix tailTrace_4060860
  have hstable : (prefixWord ++ tailWord_4060860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060860).length < 2 ^ (prefixWord ++ tailWord_4060860).sum := by decide
  have hdescent : baseEnd_4060860 < baseStart_4060860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060877 : List Nat := [1, 6, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_4060877 : Nat := 118140960795 + 4060877 * 2 ^ 59
def prefixEnd_4060877 : Nat := 4983230072969 + 3 ^ 40 * 4060877 * 2
def baseEnd_4060877 : Nat := 695060593262737844587291

theorem tailTrace_4060877 : CollatzResearch.WordTrace tailWord_4060877 prefixEnd_4060877 695060593262737844587291 := by
  unfold tailWord_4060877
  simp only [CollatzResearch.WordTrace]
  refine ⟨148112352109143646420964885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98741568072762430947309923 148112352109143646420964885)
  ·
    refine ⟨6942766505116108425982729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 148112352109143646420964885 6942766505116108425982729)
    ·
      refine ⟨5207074878837081319487047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6942766505116108425982729 5207074878837081319487047)
      ·
        refine ⟨7810612318255621979230571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5207074878837081319487047 7810612318255621979230571)
        ·
          refine ⟨11715918477383432968845857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7810612318255621979230571 11715918477383432968845857)
          ·
            refine ⟨8786938858037574726634393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11715918477383432968845857 8786938858037574726634393)
            ·
              refine ⟨6590204143528181044975795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8786938858037574726634393 6590204143528181044975795)
              ·
                refine ⟨9885306215292271567463693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6590204143528181044975795 9885306215292271567463693)
                ·
                  refine ⟨3706989830734601837798885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9885306215292271567463693 3706989830734601837798885)
                  ·
                    refine ⟨695060593262737844587291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3706989830734601837798885 695060593262737844587291)
                    ·
                      rfl

theorem cell23_4060877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_4060877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060877 prefixEnd_4060877 := by exact prefixLift 4060877
  have htrace : WordTrace (prefixWord ++ tailWord_4060877) baseStart_4060877 baseEnd_4060877 := by
    simpa [prefixWord, tailWord_4060877, baseEnd_4060877] using wordTrace_append hprefix tailTrace_4060877
  have hstable : (prefixWord ++ tailWord_4060877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060877).length < 2 ^ (prefixWord ++ tailWord_4060877).sum := by decide
  have hdescent : baseEnd_4060877 < baseStart_4060877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060910 : List Nat := [4, 1, 2, 1, 1, 2, 2, 3, 2, 3, 2]
def baseStart_4060910 : Nat := 118140960795 + 4060910 * 2 ^ 59
def prefixEnd_4060910 : Nat := 4983230072969 + 3 ^ 40 * 4060910 * 2
def baseEnd_4060910 : Nat := 2085198724649811904649221

theorem tailTrace_4060910 : CollatzResearch.WordTrace tailWord_4060910 prefixEnd_4060910 2085198724649811904649221 := by
  unfold tailWord_4060910
  simp only [CollatzResearch.WordTrace]
  refine ⟨18514194464753011632114523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98742370478682728704610789 18514194464753011632114523)
  ·
    refine ⟨27771291697129517448171785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18514194464753011632114523 27771291697129517448171785)
    ·
      refine ⟨20828468772847138086128839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27771291697129517448171785 20828468772847138086128839)
      ·
        refine ⟨31242703159270707129193259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20828468772847138086128839 31242703159270707129193259)
        ·
          refine ⟨46864054738906060693789889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31242703159270707129193259 46864054738906060693789889)
          ·
            refine ⟨35148041054179545520342417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46864054738906060693789889 35148041054179545520342417)
            ·
              refine ⟨26361030790634659140256813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35148041054179545520342417 26361030790634659140256813)
              ·
                refine ⟨9885386546487997177596305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26361030790634659140256813 9885386546487997177596305)
                ·
                  refine ⟨7414039909865997883197229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9885386546487997177596305 7414039909865997883197229)
                  ·
                    refine ⟨2780264966199749206198961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7414039909865997883197229 2780264966199749206198961)
                    ·
                      refine ⟨2085198724649811904649221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2780264966199749206198961 2085198724649811904649221)
                      ·
                        rfl

theorem cell23_4060910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_4060910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060910 prefixEnd_4060910 := by exact prefixLift 4060910
  have htrace : WordTrace (prefixWord ++ tailWord_4060910) baseStart_4060910 baseEnd_4060910 := by
    simpa [prefixWord, tailWord_4060910, baseEnd_4060910] using wordTrace_append hprefix tailTrace_4060910
  have hstable : (prefixWord ++ tailWord_4060910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060910).length < 2 ^ (prefixWord ++ tailWord_4060910).sum := by decide
  have hdescent : baseEnd_4060910 < baseStart_4060910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060936 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_4060936 : Nat := 118140960795 + 4060936 * 2 ^ 59
def prefixEnd_4060936 : Nat := 4983230072969 + 3 ^ 40 * 4060936 * 2
def baseEnd_4060936 : Nat := 2085212075146828802924101

theorem tailTrace_4060936 : CollatzResearch.WordTrace tailWord_4060936 prefixEnd_4060936 2085212075146828802924101 := by
  unfold tailWord_4060936
  simp only [CollatzResearch.WordTrace]
  refine ⟨74057252007964949748681331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98743002677286599664908441 74057252007964949748681331)
  ·
    refine ⟨111085878011947424623021997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74057252007964949748681331 111085878011947424623021997)
    ·
      refine ⟨41657204254480284233633249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111085878011947424623021997 41657204254480284233633249)
      ·
        refine ⟨31242903190860213175224937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41657204254480284233633249 31242903190860213175224937)
        ·
          refine ⟨23432177393145159881418703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31242903190860213175224937 23432177393145159881418703)
          ·
            refine ⟨35148266089717739822128055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23432177393145159881418703 35148266089717739822128055)
            ·
              refine ⟨52722399134576609733192083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35148266089717739822128055 52722399134576609733192083)
              ·
                refine ⟨79083598701864914599788125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52722399134576609733192083 79083598701864914599788125)
                ·
                  refine ⟨29656349513199342974920547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79083598701864914599788125 29656349513199342974920547)
                  ·
                    refine ⟨44484524269799014462380821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29656349513199342974920547 44484524269799014462380821)
                    ·
                      refine ⟨2085212075146828802924101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44484524269799014462380821 2085212075146828802924101)
                      ·
                        rfl

theorem cell23_4060936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_4060936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060936 prefixEnd_4060936 := by exact prefixLift 4060936
  have htrace : WordTrace (prefixWord ++ tailWord_4060936) baseStart_4060936 baseEnd_4060936 := by
    simpa [prefixWord, tailWord_4060936, baseEnd_4060936] using wordTrace_append hprefix tailTrace_4060936
  have hstable : (prefixWord ++ tailWord_4060936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060936).length < 2 ^ (prefixWord ++ tailWord_4060936).sum := by decide
  have hdescent : baseEnd_4060936 < baseStart_4060936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060974 : List Nat := [4, 1, 3, 2, 2, 1, 3, 1, 1, 1, 4]
def baseStart_4060974 : Nat := 118140960795 + 4060974 * 2 ^ 59
def prefixEnd_4060974 : Nat := 4983230072969 + 3 ^ 40 * 4060974 * 2
def baseEnd_4060974 : Nat := 2085231587411699654248927

theorem tailTrace_4060974 : CollatzResearch.WordTrace tailWord_4060974 prefixEnd_4060974 2085231587411699654248927 := by
  unfold tailWord_4060974
  simp only [CollatzResearch.WordTrace]
  refine ⟨18514486248724028998405747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98743926659861487991497317 18514486248724028998405747)
  ·
    refine ⟨27771729373086043497608621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18514486248724028998405747 27771729373086043497608621)
    ·
      refine ⟨10414398514907266311603233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27771729373086043497608621 10414398514907266311603233)
      ·
        refine ⟨7810798886180449733702425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10414398514907266311603233 7810798886180449733702425)
        ·
          refine ⟨5858099164635337300276819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7810798886180449733702425 5858099164635337300276819)
          ·
            refine ⟨8787148746953005950415229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5858099164635337300276819 8787148746953005950415229)
            ·
              refine ⟨3295180780107377231405711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8787148746953005950415229 3295180780107377231405711)
              ·
                refine ⟨4942771170161065847108567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3295180780107377231405711 4942771170161065847108567)
                ·
                  refine ⟨7414156755241598770662851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4942771170161065847108567 7414156755241598770662851)
                  ·
                    refine ⟨11121235132862398155994277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7414156755241598770662851 11121235132862398155994277)
                    ·
                      refine ⟨2085231587411699654248927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11121235132862398155994277 2085231587411699654248927)
                      ·
                        rfl

theorem cell23_4060974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_4060974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060974 prefixEnd_4060974 := by exact prefixLift 4060974
  have htrace : WordTrace (prefixWord ++ tailWord_4060974) baseStart_4060974 baseEnd_4060974 := by
    simpa [prefixWord, tailWord_4060974, baseEnd_4060974] using wordTrace_append hprefix tailTrace_4060974
  have hstable : (prefixWord ++ tailWord_4060974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060974).length < 2 ^ (prefixWord ++ tailWord_4060974).sum := by decide
  have hdescent : baseEnd_4060974 < baseStart_4060974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060977 : List Nat := [1, 2, 2, 3, 2, 3, 3, 1, 1, 2, 3]
def baseStart_4060977 : Nat := 118140960795 + 4060977 * 2 ^ 59
def prefixEnd_4060977 : Nat := 4983230072969 + 3 ^ 40 * 4060977 * 2
def baseEnd_4060977 : Nat := 2085233127853663142511413

theorem tailTrace_4060977 : CollatzResearch.WordTrace tailWord_4060977 prefixEnd_4060977 2085233127853663142511413 := by
  unfold tailWord_4060977
  simp only [CollatzResearch.WordTrace]
  refine ⟨148115999408781363499605185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98743999605854242333070123 148115999408781363499605185)
  ·
    refine ⟨111086999556586022624703889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148115999408781363499605185 111086999556586022624703889)
    ·
      refine ⟨83315249667439516968527917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111086999556586022624703889 83315249667439516968527917)
      ·
        refine ⟨31243218625289818863197969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83315249667439516968527917 31243218625289818863197969)
        ·
          refine ⟨23432413968967364147398477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31243218625289818863197969 23432413968967364147398477)
          ·
            refine ⟨8787155238362761555274429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23432413968967364147398477 8787155238362761555274429)
            ·
              refine ⟨3295183214386035583227911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8787155238362761555274429 3295183214386035583227911)
              ·
                refine ⟨4942774821579053374841867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3295183214386035583227911 4942774821579053374841867)
                ·
                  refine ⟨7414162232368580062262801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4942774821579053374841867 7414162232368580062262801)
                  ·
                    refine ⟨5560621674276435046697101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7414162232368580062262801 5560621674276435046697101)
                    ·
                      refine ⟨2085233127853663142511413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5560621674276435046697101 2085233127853663142511413)
                      ·
                        rfl

theorem cell23_4060977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_4060977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4060977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4060977 prefixEnd_4060977 := by exact prefixLift 4060977
  have htrace : WordTrace (prefixWord ++ tailWord_4060977) baseStart_4060977 baseEnd_4060977 := by
    simpa [prefixWord, tailWord_4060977, baseEnd_4060977] using wordTrace_append hprefix tailTrace_4060977
  have hstable : (prefixWord ++ tailWord_4060977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060977).length < 2 ^ (prefixWord ++ tailWord_4060977).sum := by decide
  have hdescent : baseEnd_4060977 < baseStart_4060977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061000 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 3, 3, 2]
def baseStart_4061000 : Nat := 118140960795 + 4061000 * 2 ^ 59
def prefixEnd_4061000 : Nat := 4983230072969 + 3 ^ 40 * 4061000 * 2
def baseEnd_4061000 : Nat := 2085244937908716552523807

theorem tailTrace_4061000 : CollatzResearch.WordTrace tailWord_4061000 prefixEnd_4061000 2085244937908716552523807 := by
  unfold tailWord_4061000
  simp only [CollatzResearch.WordTrace]
  refine ⟨74058419143849019213846227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98744558858465358951794969 74058419143849019213846227)
  ·
    refine ⟨111087628715773528820769341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74058419143849019213846227 111087628715773528820769341)
    ·
      refine ⟨41657860768415073307788503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111087628715773528820769341 41657860768415073307788503)
      ·
        refine ⟨62486791152622609961682755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41657860768415073307788503 62486791152622609961682755)
        ·
          refine ⟨93730186728933914942524133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62486791152622609961682755 93730186728933914942524133)
          ·
            refine ⟨17574410011675109051723275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93730186728933914942524133 17574410011675109051723275)
            ·
              refine ⟨26361615017512663577584913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17574410011675109051723275 26361615017512663577584913)
              ·
                refine ⟨19771211263134497683188685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26361615017512663577584913 19771211263134497683188685)
                ·
                  refine ⟨7414204223675436631195757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19771211263134497683188685 7414204223675436631195757)
                  ·
                    refine ⟨2780326583878288736698409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7414204223675436631195757 2780326583878288736698409)
                    ·
                      refine ⟨2085244937908716552523807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2780326583878288736698409 2085244937908716552523807)
                      ·
                        rfl

theorem cell23_4061000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_4061000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061000 prefixEnd_4061000 := by exact prefixLift 4061000
  have htrace : WordTrace (prefixWord ++ tailWord_4061000) baseStart_4061000 baseEnd_4061000 := by
    simpa [prefixWord, tailWord_4061000, baseEnd_4061000] using wordTrace_append hprefix tailTrace_4061000
  have hstable : (prefixWord ++ tailWord_4061000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061000).length < 2 ^ (prefixWord ++ tailWord_4061000).sum := by decide
  have hdescent : baseEnd_4061000 < baseStart_4061000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061064 : List Nat := [2, 1, 3, 3, 3, 2, 1, 1, 1, 4, 2]
def baseStart_4061064 : Nat := 118140960795 + 4061064 * 2 ^ 59
def prefixEnd_4061064 : Nat := 4983230072969 + 3 ^ 40 * 4061064 * 2
def baseEnd_4061064 : Nat := 2085277800670604302123513

theorem tailTrace_4061064 : CollatzResearch.WordTrace tailWord_4061064 prefixEnd_4061064 2085277800670604302123513 := by
  unfold tailWord_4061064
  simp only [CollatzResearch.WordTrace]
  refine ⟨74059586279733088679011123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98746115039644118238681497 74059586279733088679011123)
  ·
    refine ⟨111089379419599633018516685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74059586279733088679011123 111089379419599633018516685)
    ·
      refine ⟨41658517282349862381943757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111089379419599633018516685 41658517282349862381943757)
      ·
        refine ⟨15621943980881198393228909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41658517282349862381943757 15621943980881198393228909)
        ·
          refine ⟨5858228992830449397460841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15621943980881198393228909 5858228992830449397460841)
          ·
            refine ⟨4393671744622837048095631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5858228992830449397460841 4393671744622837048095631)
            ·
              refine ⟨6590507616934255572143447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4393671744622837048095631 6590507616934255572143447)
              ·
                refine ⟨9885761425401383358215171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6590507616934255572143447 9885761425401383358215171)
                ·
                  refine ⟨14828642138102075037322757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9885761425401383358215171 14828642138102075037322757)
                  ·
                    refine ⟨2780370400894139069498017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14828642138102075037322757 2780370400894139069498017)
                    ·
                      refine ⟨2085277800670604302123513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2780370400894139069498017 2085277800670604302123513)
                      ·
                        rfl

theorem cell23_4061064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_4061064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061064 prefixEnd_4061064 := by exact prefixLift 4061064
  have htrace : WordTrace (prefixWord ++ tailWord_4061064) baseStart_4061064 baseEnd_4061064 := by
    simpa [prefixWord, tailWord_4061064, baseEnd_4061064] using wordTrace_append hprefix tailTrace_4061064
  have hstable : (prefixWord ++ tailWord_4061064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061064).length < 2 ^ (prefixWord ++ tailWord_4061064).sum := by decide
  have hdescent : baseEnd_4061064 < baseStart_4061064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061120 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 1, 6, 2]
def baseStart_4061120 : Nat := 118140960795 + 4061120 * 2 ^ 59
def prefixEnd_4061120 : Nat := 4983230072969 + 3 ^ 40 * 4061120 * 2
def baseEnd_4061120 : Nat := 2085306555587256083023255

theorem tailTrace_4061120 : CollatzResearch.WordTrace tailWord_4061120 prefixEnd_4061120 2085306555587256083023255 := by
  unfold tailWord_4061120
  simp only [CollatzResearch.WordTrace]
  refine ⟨74060607523631649461030407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98747476698175532614707209 74060607523631649461030407)
  ·
    refine ⟨111090911285447474191545611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74060607523631649461030407 111090911285447474191545611)
    ·
      refine ⟨166636366928171211287318417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111090911285447474191545611 166636366928171211287318417)
      ·
        refine ⟨124977275196128408465488813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166636366928171211287318417 124977275196128408465488813)
        ·
          refine ⟨46866478198548153174558305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124977275196128408465488813 46866478198548153174558305)
          ·
            refine ⟨35149858648911114880918729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46866478198548153174558305 35149858648911114880918729)
            ·
              refine ⟨26362393986683336160689047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35149858648911114880918729 26362393986683336160689047)
              ·
                refine ⟨39543590980025004241033571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26362393986683336160689047 39543590980025004241033571)
                ·
                  refine ⟨59315386470037506361550357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39543590980025004241033571 59315386470037506361550357)
                  ·
                    refine ⟨2780408740783008110697673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59315386470037506361550357 2780408740783008110697673)
                    ·
                      refine ⟨2085306555587256083023255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2780408740783008110697673 2085306555587256083023255)
                      ·
                        rfl

theorem cell23_4061120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 1, 6, 2].length) (baseStart_4061120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061120 prefixEnd_4061120 := by exact prefixLift 4061120
  have htrace : WordTrace (prefixWord ++ tailWord_4061120) baseStart_4061120 baseEnd_4061120 := by
    simpa [prefixWord, tailWord_4061120, baseEnd_4061120] using wordTrace_append hprefix tailTrace_4061120
  have hstable : (prefixWord ++ tailWord_4061120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061120).length < 2 ^ (prefixWord ++ tailWord_4061120).sum := by decide
  have hdescent : baseEnd_4061120 < baseStart_4061120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061130 : List Nat := [3, 1, 2, 1, 2, 1, 2, 4, 3, 4]
def baseStart_4061130 : Nat := 118140960795 + 4061130 * 2 ^ 59
def prefixEnd_4061130 : Nat := 4983230072969 + 3 ^ 40 * 4061130 * 2
def baseEnd_4061130 : Nat := 695103896797933681299403

theorem tailTrace_4061130 : CollatzResearch.WordTrace tailWord_4061130 prefixEnd_4061130 695103896797933681299403 := by
  unfold tailWord_4061130
  simp only [CollatzResearch.WordTrace]
  refine ⟨37030394944306767657481211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98747719851484713753283229 37030394944306767657481211)
  ·
    refine ⟨55545592416460151486221817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37030394944306767657481211 55545592416460151486221817)
    ·
      refine ⟨41659194312345113614666363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55545592416460151486221817 41659194312345113614666363)
      ·
        refine ⟨62488791468517670421999545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41659194312345113614666363 62488791468517670421999545)
        ·
          refine ⟨46866593601388252816499659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62488791468517670421999545 46866593601388252816499659)
          ·
            refine ⟨70299890402082379224749489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46866593601388252816499659 70299890402082379224749489)
            ·
              refine ⟨52724917801561784418562117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70299890402082379224749489 52724917801561784418562117)
              ·
                refine ⟨9885922087792834578480397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52724917801561784418562117 9885922087792834578480397)
                ·
                  refine ⟨3707220782922312966930149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9885922087792834578480397 3707220782922312966930149)
                  ·
                    refine ⟨695103896797933681299403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3707220782922312966930149 695103896797933681299403)
                    ·
                      rfl

theorem cell23_4061130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_4061130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061130 prefixEnd_4061130 := by exact prefixLift 4061130
  have htrace : WordTrace (prefixWord ++ tailWord_4061130) baseStart_4061130 baseEnd_4061130 := by
    simpa [prefixWord, tailWord_4061130, baseEnd_4061130] using wordTrace_append hprefix tailTrace_4061130
  have hstable : (prefixWord ++ tailWord_4061130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061130).length < 2 ^ (prefixWord ++ tailWord_4061130).sum := by decide
  have hdescent : baseEnd_4061130 < baseStart_4061130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061237 : List Nat := [1, 3, 3, 1, 1, 1, 2, 5, 2, 4]
def baseStart_4061237 : Nat := 118140960795 + 4061237 * 2 ^ 59
def prefixEnd_4061237 : Nat := 4983230072969 + 3 ^ 40 * 4061237 * 2
def baseEnd_4061237 : Nat := 695122210941277375086739

theorem tailTrace_4061237 : CollatzResearch.WordTrace tailWord_4061237 prefixEnd_4061237 695122210941277375086739 := by
  unfold tailWord_4061237
  simp only [CollatzResearch.WordTrace]
  refine ⟨148125482387839427904069965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98750321591892951936046643 148125482387839427904069965)
  ·
    refine ⟨55547055895439785464026237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148125482387839427904069965 55547055895439785464026237)
    ·
      refine ⟨20830145960789919549009839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55547055895439785464026237 20830145960789919549009839)
      ·
        refine ⟨31245218941184879323514759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20830145960789919549009839 31245218941184879323514759)
        ·
          refine ⟨46867828411777318985272139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31245218941184879323514759 46867828411777318985272139)
          ·
            refine ⟨70301742617665978477908209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46867828411777318985272139 70301742617665978477908209)
            ·
              refine ⟨52726306963249483858431157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70301742617665978477908209 52726306963249483858431157)
              ·
                refine ⟨4943091277804639111727921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52726306963249483858431157 4943091277804639111727921)
                ·
                  refine ⟨3707318458353479333795941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4943091277804639111727921 3707318458353479333795941)
                  ·
                    refine ⟨695122210941277375086739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3707318458353479333795941 695122210941277375086739)
                    ·
                      rfl

theorem cell23_4061237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_4061237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061237 prefixEnd_4061237 := by exact prefixLift 4061237
  have htrace : WordTrace (prefixWord ++ tailWord_4061237) baseStart_4061237 baseEnd_4061237 := by
    simpa [prefixWord, tailWord_4061237, baseEnd_4061237] using wordTrace_append hprefix tailTrace_4061237
  have hstable : (prefixWord ++ tailWord_4061237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061237).length < 2 ^ (prefixWord ++ tailWord_4061237).sum := by decide
  have hdescent : baseEnd_4061237 < baseStart_4061237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061243 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 7]
def baseStart_4061243 : Nat := 118140960795 + 4061243 * 2 ^ 59
def prefixEnd_4061243 : Nat := 4983230072969 + 3 ^ 40 * 4061243 * 2
def baseEnd_4061243 : Nat := 2085369713707759101785189

theorem tailTrace_4061243 : CollatzResearch.WordTrace tailWord_4061243 prefixEnd_4061243 2085369713707759101785189 := by
  unfold tailWord_4061243
  simp only [CollatzResearch.WordTrace]
  refine ⟨148125701225817690928788383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98750467483878460619192255 148125701225817690928788383)
  ·
    refine ⟨222188551838726536393182575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148125701225817690928788383 222188551838726536393182575)
    ·
      refine ⟨333282827758089804589773863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222188551838726536393182575 333282827758089804589773863)
      ·
        refine ⟨499924241637134706884660795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333282827758089804589773863 499924241637134706884660795)
        ·
          refine ⟨749886362455702060326991193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499924241637134706884660795 749886362455702060326991193)
          ·
            refine ⟨562414771841776545245243395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 749886362455702060326991193 562414771841776545245243395)
            ·
              refine ⟨843622157762664817867865093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562414771841776545245243395 843622157762664817867865093)
              ·
                refine ⟨158179154580499653350224705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 843622157762664817867865093 158179154580499653350224705)
                ·
                  refine ⟨118634365935374740012668529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158179154580499653350224705 118634365935374740012668529)
                  ·
                    refine ⟨88975774451531055009501397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118634365935374740012668529 88975774451531055009501397)
                    ·
                      refine ⟨2085369713707759101785189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88975774451531055009501397 2085369713707759101785189)
                      ·
                        rfl

theorem cell23_4061243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 7].length) (baseStart_4061243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061243 prefixEnd_4061243 := by exact prefixLift 4061243
  have htrace : WordTrace (prefixWord ++ tailWord_4061243) baseStart_4061243 baseEnd_4061243 := by
    simpa [prefixWord, tailWord_4061243, baseEnd_4061243] using wordTrace_append hprefix tailTrace_4061243
  have hstable : (prefixWord ++ tailWord_4061243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061243).length < 2 ^ (prefixWord ++ tailWord_4061243).sum := by decide
  have hdescent : baseEnd_4061243 < baseStart_4061243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061244 : List Nat := [2, 2, 2, 2, 2, 1, 1, 4, 3, 2, 2]
def baseStart_4061244 : Nat := 118140960795 + 4061244 * 2 ^ 59
def prefixEnd_4061244 : Nat := 4983230072969 + 3 ^ 40 * 4061244 * 2
def baseEnd_4061244 : Nat := 2085370227188413597872685

theorem tailTrace_4061244 : CollatzResearch.WordTrace tailWord_4061244 prefixEnd_4061244 2085370227188413597872685 := by
  unfold tailWord_4061244
  simp only [CollatzResearch.WordTrace]
  refine ⟨74062868849407034049787393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98750491799209378733049857 74062868849407034049787393)
  ·
    refine ⟨55547151637055275537340545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74062868849407034049787393 55547151637055275537340545)
    ·
      refine ⟨41660363727791456653005409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55547151637055275537340545 41660363727791456653005409)
      ·
        refine ⟨31245272795843592489754057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41660363727791456653005409 31245272795843592489754057)
        ·
          refine ⟨23433954596882694367315543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31245272795843592489754057 23433954596882694367315543)
          ·
            refine ⟨35150931895324041550973315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23433954596882694367315543 35150931895324041550973315)
            ·
              refine ⟨52726397842986062326459973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35150931895324041550973315 52726397842986062326459973)
              ·
                refine ⟨9886199595559886686211245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52726397842986062326459973 9886199595559886686211245)
                ·
                  refine ⟨3707324848334957507329217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9886199595559886686211245 3707324848334957507329217)
                  ·
                    refine ⟨2780493636251218130496913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3707324848334957507329217 2780493636251218130496913)
                    ·
                      refine ⟨2085370227188413597872685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2780493636251218130496913 2085370227188413597872685)
                      ·
                        rfl

theorem cell23_4061244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_4061244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061244 prefixEnd_4061244 := by exact prefixLift 4061244
  have htrace : WordTrace (prefixWord ++ tailWord_4061244) baseStart_4061244 baseEnd_4061244 := by
    simpa [prefixWord, tailWord_4061244, baseEnd_4061244] using wordTrace_append hprefix tailTrace_4061244
  have hstable : (prefixWord ++ tailWord_4061244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061244).length < 2 ^ (prefixWord ++ tailWord_4061244).sum := by decide
  have hdescent : baseEnd_4061244 < baseStart_4061244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061247 : List Nat := [1, 1, 2, 2, 3, 1, 3, 4, 1, 2, 3]
def baseStart_4061247 : Nat := 118140960795 + 4061247 * 2 ^ 59
def prefixEnd_4061247 : Nat := 4983230072969 + 3 ^ 40 * 4061247 * 2
def baseEnd_4061247 : Nat := 2085371767630377086135171

theorem tailTrace_4061247 : CollatzResearch.WordTrace tailWord_4061247 prefixEnd_4061247 2085371767630377086135171 := by
  unfold tailWord_4061247
  simp only [CollatzResearch.WordTrace]
  refine ⟨148125847117803199611933995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98750564745202133074622663 148125847117803199611933995)
  ·
    refine ⟨222188770676704799417900993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148125847117803199611933995 222188770676704799417900993)
    ·
      refine ⟨166641578007528599563425745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222188770676704799417900993 166641578007528599563425745)
      ·
        refine ⟨124981183505646449672569309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166641578007528599563425745 124981183505646449672569309)
        ·
          refine ⟨46867943814617418627213491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124981183505646449672569309 46867943814617418627213491)
          ·
            refine ⟨70301915721926127940820237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46867943814617418627213491 70301915721926127940820237)
            ·
              refine ⟨26363218395722297977807589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70301915721926127940820237 26363218395722297977807589)
              ·
                refine ⟨4943103449197930870838923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26363218395722297977807589 4943103449197930870838923)
                ·
                  refine ⟨7414655173796896306258385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4943103449197930870838923 7414655173796896306258385)
                  ·
                    refine ⟨5560991380347672229693789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7414655173796896306258385 5560991380347672229693789)
                    ·
                      refine ⟨2085371767630377086135171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5560991380347672229693789 2085371767630377086135171)
                      ·
                        rfl

theorem cell23_4061247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 2, 3].length) (baseStart_4061247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061247 prefixEnd_4061247 := by exact prefixLift 4061247
  have htrace : WordTrace (prefixWord ++ tailWord_4061247) baseStart_4061247 baseEnd_4061247 := by
    simpa [prefixWord, tailWord_4061247, baseEnd_4061247] using wordTrace_append hprefix tailTrace_4061247
  have hstable : (prefixWord ++ tailWord_4061247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061247).length < 2 ^ (prefixWord ++ tailWord_4061247).sum := by decide
  have hdescent : baseEnd_4061247 < baseStart_4061247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061254 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_4061254 : Nat := 118140960795 + 4061254 * 2 ^ 59
def prefixEnd_4061254 : Nat := 4983230072969 + 3 ^ 40 * 4061254 * 2
def baseEnd_4061254 : Nat := 695125120664986186249213

theorem tailTrace_4061254 : CollatzResearch.WordTrace tailWord_4061254 prefixEnd_4061254 695125120664986186249213 := by
  unfold tailWord_4061254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4628940700899307493982463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98750734952518559871625877 4628940700899307493982463)
  ·
    refine ⟨6943411051348961240973695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4628940700899307493982463 6943411051348961240973695)
    ·
      refine ⟨10415116577023441861460543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6943411051348961240973695 10415116577023441861460543)
      ·
        refine ⟨15622674865535162792190815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10415116577023441861460543 15622674865535162792190815)
        ·
          refine ⟨23434012298302744188286223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15622674865535162792190815 23434012298302744188286223)
          ·
            refine ⟨35151018447454116282429335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23434012298302744188286223 35151018447454116282429335)
            ·
              refine ⟨52726527671181174423644003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35151018447454116282429335 52726527671181174423644003)
              ·
                refine ⟨79089791506771761635466005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52726527671181174423644003 79089791506771761635466005)
                ·
                  refine ⟨3707333976879926326662469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79089791506771761635466005 3707333976879926326662469)
                  ·
                    refine ⟨695125120664986186249213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3707333976879926326662469 695125120664986186249213)
                    ·
                      rfl

theorem cell23_4061254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_4061254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061254 prefixEnd_4061254 := by exact prefixLift 4061254
  have htrace : WordTrace (prefixWord ++ tailWord_4061254) baseStart_4061254 baseEnd_4061254 := by
    simpa [prefixWord, tailWord_4061254, baseEnd_4061254] using wordTrace_append hprefix tailTrace_4061254
  have hstable : (prefixWord ++ tailWord_4061254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061254).length < 2 ^ (prefixWord ++ tailWord_4061254).sum := by decide
  have hdescent : baseEnd_4061254 < baseStart_4061254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061321 : List Nat := [1, 2, 1, 1, 4, 2, 5, 1, 1, 3, 2]
def baseStart_4061321 : Nat := 118140960795 + 4061321 * 2 ^ 59
def prefixEnd_4061321 : Nat := 4983230072969 + 3 ^ 40 * 4061321 * 2
def baseEnd_4061321 : Nat := 2085409765198809796609831

theorem tailTrace_4061321 : CollatzResearch.WordTrace tailWord_4061321 prefixEnd_4061321 2085409765198809796609831 := by
  unfold tailWord_4061321
  simp only [CollatzResearch.WordTrace]
  refine ⟨148128546119535110250127817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98752364079690073500085211 148128546119535110250127817)
  ·
    refine ⟨111096409589651332687595863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148128546119535110250127817 111096409589651332687595863)
    ·
      refine ⟨166644614384476999031393795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111096409589651332687595863 166644614384476999031393795)
      ·
        refine ⟨249966921576715498547090693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166644614384476999031393795 249966921576715498547090693)
        ·
          refine ⟨46868797795634155977579505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249966921576715498547090693 46868797795634155977579505)
          ·
            refine ⟨35151598346725616983184629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46868797795634155977579505 35151598346725616983184629)
            ·
              refine ⟨3295462345005526592173559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35151598346725616983184629 3295462345005526592173559)
              ·
                refine ⟨4943193517508289888260339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3295462345005526592173559 4943193517508289888260339)
                ·
                  refine ⟨7414790276262434832390509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4943193517508289888260339 7414790276262434832390509)
                  ·
                    refine ⟨2780546353598413062146441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7414790276262434832390509 2780546353598413062146441)
                    ·
                      refine ⟨2085409765198809796609831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2780546353598413062146441 2085409765198809796609831)
                      ·
                        rfl

theorem cell23_4061321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 1, 3, 2].length) (baseStart_4061321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061321 prefixEnd_4061321 := by exact prefixLift 4061321
  have htrace : WordTrace (prefixWord ++ tailWord_4061321) baseStart_4061321 baseEnd_4061321 := by
    simpa [prefixWord, tailWord_4061321, baseEnd_4061321] using wordTrace_append hprefix tailTrace_4061321
  have hstable : (prefixWord ++ tailWord_4061321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061321).length < 2 ^ (prefixWord ++ tailWord_4061321).sum := by decide
  have hdescent : baseEnd_4061321 < baseStart_4061321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061357 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 9]
def baseStart_4061357 : Nat := 118140960795 + 4061357 * 2 ^ 59
def prefixEnd_4061357 : Nat := 4983230072969 + 3 ^ 40 * 4061357 * 2
def baseEnd_4061357 : Nat := 231714250055819072862185

theorem tailTrace_4061357 : CollatzResearch.WordTrace tailWord_4061357 prefixEnd_4061357 231714250055819072862185 := by
  unfold tailWord_4061357
  simp only [CollatzResearch.WordTrace]
  refine ⟨148129859147404688398438325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98753239431603125598958883 148129859147404688398438325)
  ·
    refine ⟨13887174295069189537353593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148129859147404688398438325 13887174295069189537353593)
    ·
      refine ⟨10415380721301892153015195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13887174295069189537353593 10415380721301892153015195)
      ·
        refine ⟨15623071081952838229522793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10415380721301892153015195 15623071081952838229522793)
        ·
          refine ⟨11717303311464628672142095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15623071081952838229522793 11717303311464628672142095)
          ·
            refine ⟨17575954967196943008213143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11717303311464628672142095 17575954967196943008213143)
            ·
              refine ⟨26363932450795414512319715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17575954967196943008213143 26363932450795414512319715)
              ·
                refine ⟨39545898676193121768479573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26363932450795414512319715 39545898676193121768479573)
                ·
                  refine ⟨231714250055819072862185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39545898676193121768479573 231714250055819072862185)
                  ·
                    rfl

theorem cell23_4061357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_4061357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061357 prefixEnd_4061357 := by exact prefixLift 4061357
  have htrace : WordTrace (prefixWord ++ tailWord_4061357) baseStart_4061357 baseEnd_4061357 := by
    simpa [prefixWord, tailWord_4061357, baseEnd_4061357] using wordTrace_append hprefix tailTrace_4061357
  have hstable : (prefixWord ++ tailWord_4061357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061357).length < 2 ^ (prefixWord ++ tailWord_4061357).sum := by decide
  have hdescent : baseEnd_4061357 < baseStart_4061357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061427 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 3]
def baseStart_4061427 : Nat := 118140960795 + 4061427 * 2 ^ 59
def prefixEnd_4061427 : Nat := 4983230072969 + 3 ^ 40 * 4061427 * 2
def baseEnd_4061427 : Nat := 2085464194148186381884343

theorem tailTrace_4061427 : CollatzResearch.WordTrace tailWord_4061427 prefixEnd_4061427 2085464194148186381884343 := by
  unfold tailWord_4061427
  simp only [CollatzResearch.WordTrace]
  refine ⟨148132412257151090353486535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98754941504767393568991023 148132412257151090353486535)
  ·
    refine ⟨222198618385726635530229803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148132412257151090353486535 222198618385726635530229803)
    ·
      refine ⟨333297927578589953295344705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222198618385726635530229803 333297927578589953295344705)
      ·
        refine ⟨249973445683942464971508529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333297927578589953295344705 249973445683942464971508529)
        ·
          refine ⟨187480084262956848728631397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249973445683942464971508529 187480084262956848728631397)
          ·
            refine ⟨35152515799304409136618387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187480084262956848728631397 35152515799304409136618387)
            ·
              refine ⟨52728773698956613704927581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35152515799304409136618387 52728773698956613704927581)
              ·
                refine ⟨19773290137108730139347843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52728773698956613704927581 19773290137108730139347843)
                ·
                  refine ⟨29659935205663095209021765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19773290137108730139347843 29659935205663095209021765)
                  ·
                    refine ⟨5561237851061830351691581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29659935205663095209021765 5561237851061830351691581)
                    ·
                      refine ⟨2085464194148186381884343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5561237851061830351691581 2085464194148186381884343)
                      ·
                        rfl

theorem cell23_4061427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 3].length) (baseStart_4061427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061427 prefixEnd_4061427 := by exact prefixLift 4061427
  have htrace : WordTrace (prefixWord ++ tailWord_4061427) baseStart_4061427 baseEnd_4061427 := by
    simpa [prefixWord, tailWord_4061427, baseEnd_4061427] using wordTrace_append hprefix tailTrace_4061427
  have hstable : (prefixWord ++ tailWord_4061427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061427).length < 2 ^ (prefixWord ++ tailWord_4061427).sum := by decide
  have hdescent : baseEnd_4061427 < baseStart_4061427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061484 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 1, 5, 2]
def baseStart_4061484 : Nat := 118140960795 + 4061484 * 2 ^ 59
def prefixEnd_4061484 : Nat := 4983230072969 + 3 ^ 40 * 4061484 * 2
def baseEnd_4061484 : Nat := 2085493462545492658871581

theorem tailTrace_4061484 : CollatzResearch.WordTrace tailWord_4061484 prefixEnd_4061484 2085493462545492658871581 := by
  unfold tailWord_4061484
  simp only [CollatzResearch.WordTrace]
  refine ⟨74067245608972294544155753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98756327478629726058874337 74067245608972294544155753)
  ·
    refine ⟨55550434206729220908116815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74067245608972294544155753 55550434206729220908116815)
    ·
      refine ⟨83325651310093831362175223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55550434206729220908116815 83325651310093831362175223)
      ·
        refine ⟨124988476965140747043262835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83325651310093831362175223 124988476965140747043262835)
        ·
          refine ⟨187482715447711120564894253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124988476965140747043262835 187482715447711120564894253)
          ·
            refine ⟨70306018292891670211835345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187482715447711120564894253 70306018292891670211835345)
            ·
              refine ⟨52729513719668752658876509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70306018292891670211835345 52729513719668752658876509)
              ·
                refine ⟨19773567644875782247078691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52729513719668752658876509 19773567644875782247078691)
                ·
                  refine ⟨29660351467313673370618037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19773567644875782247078691 29660351467313673370618037)
                  ·
                    refine ⟨2780657950060656878495441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29660351467313673370618037 2780657950060656878495441)
                    ·
                      refine ⟨2085493462545492658871581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2780657950060656878495441 2085493462545492658871581)
                      ·
                        rfl

theorem cell23_4061484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 5, 2].length) (baseStart_4061484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061484 prefixEnd_4061484 := by exact prefixLift 4061484
  have htrace : WordTrace (prefixWord ++ tailWord_4061484) baseStart_4061484 baseEnd_4061484 := by
    simpa [prefixWord, tailWord_4061484, baseEnd_4061484] using wordTrace_append hprefix tailTrace_4061484
  have hstable : (prefixWord ++ tailWord_4061484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061484).length < 2 ^ (prefixWord ++ tailWord_4061484).sum := by decide
  have hdescent : baseEnd_4061484 < baseStart_4061484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061514 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 4, 6, 2]
def baseStart_4061514 : Nat := 118140960795 + 4061514 * 2 ^ 59
def prefixEnd_4061514 : Nat := 4983230072969 + 3 ^ 40 * 4061514 * 2
def baseEnd_4061514 : Nat := 2085508866965127541496443

theorem tailTrace_4061514 : CollatzResearch.WordTrace tailWord_4061514 prefixEnd_4061514 2085508866965127541496443 := by
  unfold tailWord_4061514
  simp only [CollatzResearch.WordTrace]
  refine ⟨37033896351958976052975899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98757056938557269474602397 37033896351958976052975899)
  ·
    refine ⟨55550844527938464079463849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37033896351958976052975899 55550844527938464079463849)
    ·
      refine ⟨41663133395953848059597887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55550844527938464079463849 41663133395953848059597887)
      ·
        refine ⟨62494700093930772089396831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41663133395953848059597887 62494700093930772089396831)
        ·
          refine ⟨93742050140896158134095247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62494700093930772089396831 93742050140896158134095247)
          ·
            refine ⟨140613075211344237201142871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93742050140896158134095247 140613075211344237201142871)
            ·
              refine ⟨210919612817016355801714307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140613075211344237201142871 210919612817016355801714307)
              ·
                refine ⟨316379419225524533702571461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210919612817016355801714307 316379419225524533702571461)
                ·
                  refine ⟨59321141104785850069232149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316379419225524533702571461 59321141104785850069232149)
                  ·
                    refine ⟨2780678489286836721995257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59321141104785850069232149 2780678489286836721995257)
                    ·
                      refine ⟨2085508866965127541496443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2780678489286836721995257 2085508866965127541496443)
                      ·
                        rfl

theorem cell23_4061514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_4061514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061514 prefixEnd_4061514 := by exact prefixLift 4061514
  have htrace : WordTrace (prefixWord ++ tailWord_4061514) baseStart_4061514 baseEnd_4061514 := by
    simpa [prefixWord, tailWord_4061514, baseEnd_4061514] using wordTrace_append hprefix tailTrace_4061514
  have hstable : (prefixWord ++ tailWord_4061514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061514).length < 2 ^ (prefixWord ++ tailWord_4061514).sum := by decide
  have hdescent : baseEnd_4061514 < baseStart_4061514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061524 : List Nat := [2, 4, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_4061524 : Nat := 118140960795 + 4061524 * 2 ^ 59
def prefixEnd_4061524 : Nat := 4983230072969 + 3 ^ 40 * 4061524 * 2
def baseEnd_4061524 : Nat := 695171333923890834123799

theorem tailTrace_4061524 : CollatzResearch.WordTrace tailWord_4061524 prefixEnd_4061524 695171333923890834123799 := by
  unfold tailWord_4061524
  simp only [CollatzResearch.WordTrace]
  refine ⟨74067975068899837959883813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98757300091866450613178417 74067975068899837959883813)
  ·
    refine ⟨13887745325418719617478215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74067975068899837959883813 13887745325418719617478215)
    ·
      refine ⟨20831617988128079426217323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13887745325418719617478215 20831617988128079426217323)
      ·
        refine ⟨31247426982192119139325985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20831617988128079426217323 31247426982192119139325985)
        ·
          refine ⟨23435570236644089354494489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31247426982192119139325985 23435570236644089354494489)
          ·
            refine ⟨17576677677483067015870867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23435570236644089354494489 17576677677483067015870867)
            ·
              refine ⟨26365016516224600523806301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17576677677483067015870867 26365016516224600523806301)
              ·
                refine ⟨9886881193584225196427363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26365016516224600523806301 9886881193584225196427363)
                ·
                  refine ⟨14830321790376337794641045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9886881193584225196427363 14830321790376337794641045)
                  ·
                    refine ⟨695171333923890834123799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14830321790376337794641045 695171333923890834123799)
                    ·
                      rfl

theorem cell23_4061524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_4061524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061524 prefixEnd_4061524 := by exact prefixLift 4061524
  have htrace : WordTrace (prefixWord ++ tailWord_4061524) baseStart_4061524 baseEnd_4061524 := by
    simpa [prefixWord, tailWord_4061524, baseEnd_4061524] using wordTrace_append hprefix tailTrace_4061524
  have hstable : (prefixWord ++ tailWord_4061524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061524).length < 2 ^ (prefixWord ++ tailWord_4061524).sum := by decide
  have hdescent : baseEnd_4061524 < baseStart_4061524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061565 : List Nat := [1, 4, 1, 1, 2, 3, 2, 4, 1, 2, 2]
def baseStart_4061565 : Nat := 118140960795 + 4061565 * 2 ^ 59
def prefixEnd_4061565 : Nat := 4983230072969 + 3 ^ 40 * 4061565 * 2
def baseEnd_4061565 : Nat := 2085535054478506841958709

theorem tailTrace_4061565 : CollatzResearch.WordTrace tailWord_4061565 prefixEnd_4061565 2085535054478506841958709 := by
  unfold tailWord_4061565
  simp only [CollatzResearch.WordTrace]
  refine ⟨148137445530651139922010149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98758297020434093281340099 148137445530651139922010149)
  ·
    refine ⟨27775771036997088735376903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148137445530651139922010149 27775771036997088735376903)
    ·
      refine ⟨41663656555495633103065355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27775771036997088735376903 41663656555495633103065355)
      ·
        refine ⟨62495484833243449654598033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41663656555495633103065355 62495484833243449654598033)
        ·
          refine ⟨46871613624932587240948525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62495484833243449654598033 46871613624932587240948525)
          ·
            refine ⟨17576855109349720215355697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46871613624932587240948525 17576855109349720215355697)
            ·
              refine ⟨13182641332012290161516773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17576855109349720215355697 13182641332012290161516773)
              ·
                refine ⟨2471745249752304405284395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13182641332012290161516773 2471745249752304405284395)
                ·
                  refine ⟨3707617874628456607926593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2471745249752304405284395 3707617874628456607926593)
                  ·
                    refine ⟨2780713405971342455944945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3707617874628456607926593 2780713405971342455944945)
                    ·
                      refine ⟨2085535054478506841958709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2780713405971342455944945 2085535054478506841958709)
                      ·
                        rfl

theorem cell23_4061565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 1, 2, 2].length) (baseStart_4061565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061565 prefixEnd_4061565 := by exact prefixLift 4061565
  have htrace : WordTrace (prefixWord ++ tailWord_4061565) baseStart_4061565 baseEnd_4061565 := by
    simpa [prefixWord, tailWord_4061565, baseEnd_4061565] using wordTrace_append hprefix tailTrace_4061565
  have hstable : (prefixWord ++ tailWord_4061565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061565).length < 2 ^ (prefixWord ++ tailWord_4061565).sum := by decide
  have hdescent : baseEnd_4061565 < baseStart_4061565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061588 : List Nat := [2, 4, 2, 1, 3, 2, 2, 7]
def baseStart_4061588 : Nat := 118140960795 + 4061588 * 2 ^ 59
def prefixEnd_4061588 : Nat := 4983230072969 + 3 ^ 40 * 4061588 * 2
def baseEnd_4061588 : Nat := 77242476464205935258189

theorem tailTrace_4061588 : CollatzResearch.WordTrace tailWord_4061588 prefixEnd_4061588 77242476464205935258189 := by
  unfold tailWord_4061588
  simp only [CollatzResearch.WordTrace]
  refine ⟨74069142204783907425048709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98758856273045209900064945 74069142204783907425048709)
  ·
    refine ⟨13887964163396982642196633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74069142204783907425048709 13887964163396982642196633)
    ·
      refine ⟨10415973122547736981647475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13887964163396982642196633 10415973122547736981647475)
      ·
        refine ⟨15623959683821605472471213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10415973122547736981647475 15623959683821605472471213)
        ·
          refine ⟨5858984881433102052176705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15623959683821605472471213 5858984881433102052176705)
          ·
            refine ⟨4394238661074826539132529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5858984881433102052176705 4394238661074826539132529)
            ·
              refine ⟨3295678995806119904349397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4394238661074826539132529 3295678995806119904349397)
              ·
                refine ⟨77242476464205935258189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3295678995806119904349397 77242476464205935258189)
                ·
                  rfl

theorem cell23_4061588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 7].length) (baseStart_4061588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061588 prefixEnd_4061588 := by exact prefixLift 4061588
  have htrace : WordTrace (prefixWord ++ tailWord_4061588) baseStart_4061588 baseEnd_4061588 := by
    simpa [prefixWord, tailWord_4061588, baseEnd_4061588] using wordTrace_append hprefix tailTrace_4061588
  have hstable : (prefixWord ++ tailWord_4061588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061588).length < 2 ^ (prefixWord ++ tailWord_4061588).sum := by decide
  have hdescent : baseEnd_4061588 < baseStart_4061588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061591 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 3, 3, 2]
def baseStart_4061591 : Nat := 118140960795 + 4061591 * 2 ^ 59
def prefixEnd_4061591 : Nat := 4983230072969 + 3 ^ 40 * 4061591 * 2
def baseEnd_4061591 : Nat := 2085548404975523740233589

theorem tailTrace_4061591 : CollatzResearch.WordTrace tailWord_4061591 prefixEnd_4061591 2085548404975523740233589 := by
  unfold tailWord_4061591
  simp only [CollatzResearch.WordTrace]
  refine ⟨148138393828556946362456627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98758929219037964241637751 148138393828556946362456627)
  ·
    refine ⟨222207590742835419543684941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148138393828556946362456627 222207590742835419543684941)
    ·
      refine ⟨83327846528563282328881853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222207590742835419543684941 83327846528563282328881853)
      ·
        refine ⟨31247942448211230873330695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83327846528563282328881853 31247942448211230873330695)
        ·
          refine ⟨46871913672316846309996043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31247942448211230873330695 46871913672316846309996043)
          ·
            refine ⟨70307870508475269464994065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46871913672316846309996043 70307870508475269464994065)
            ·
              refine ⟨52730902881356452098745549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70307870508475269464994065 52730902881356452098745549)
              ·
                refine ⟨19774088580508669537029581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52730902881356452098745549 19774088580508669537029581)
                ·
                  refine ⟨7415283217690751076386093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19774088580508669537029581 7415283217690751076386093)
                  ·
                    refine ⟨2780731206634031653644785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7415283217690751076386093 2780731206634031653644785)
                    ·
                      refine ⟨2085548404975523740233589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2780731206634031653644785 2085548404975523740233589)
                      ·
                        rfl

theorem cell23_4061591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_4061591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061591 prefixEnd_4061591 := by exact prefixLift 4061591
  have htrace : WordTrace (prefixWord ++ tailWord_4061591) baseStart_4061591 baseEnd_4061591 := by
    simpa [prefixWord, tailWord_4061591, baseEnd_4061591] using wordTrace_append hprefix tailTrace_4061591
  have hstable : (prefixWord ++ tailWord_4061591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061591).length < 2 ^ (prefixWord ++ tailWord_4061591).sum := by decide
  have hdescent : baseEnd_4061591 < baseStart_4061591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061594 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5]
def baseStart_4061594 : Nat := 118140960795 + 4061594 * 2 ^ 59
def prefixEnd_4061594 : Nat := 4983230072969 + 3 ^ 40 * 4061594 * 2
def baseEnd_4061594 : Nat := 2085549945417487228496075

theorem tailTrace_4061594 : CollatzResearch.WordTrace tailWord_4061594 prefixEnd_4061594 2085549945417487228496075 := by
  unfold tailWord_4061594
  simp only [CollatzResearch.WordTrace]
  refine ⟨37034625811886519468703959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98759002165030718583210557 37034625811886519468703959)
  ·
    refine ⟨55551938717829779203055939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37034625811886519468703959 55551938717829779203055939)
    ·
      refine ⟨83327908076744668804583909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55551938717829779203055939 83327908076744668804583909)
      ·
        refine ⟨15623982764389625400859483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83327908076744668804583909 15623982764389625400859483)
        ·
          refine ⟨23435974146584438101289225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15623982764389625400859483 23435974146584438101289225)
          ·
            refine ⟨17576980609938328575966919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23435974146584438101289225 17576980609938328575966919)
            ·
              refine ⟨26365470914907492863950379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17576980609938328575966919 26365470914907492863950379)
              ·
                refine ⟨39548206372361239295925569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26365470914907492863950379 39548206372361239295925569)
                ·
                  refine ⟨29661154779270929471944177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39548206372361239295925569 29661154779270929471944177)
                  ·
                    refine ⟨22245866084453197103958133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29661154779270929471944177 22245866084453197103958133)
                    ·
                      refine ⟨2085549945417487228496075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22245866084453197103958133 2085549945417487228496075)
                      ·
                        rfl

theorem cell23_4061594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_4061594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061594 prefixEnd_4061594 := by exact prefixLift 4061594
  have htrace : WordTrace (prefixWord ++ tailWord_4061594) baseStart_4061594 baseEnd_4061594 := by
    simpa [prefixWord, tailWord_4061594, baseEnd_4061594] using wordTrace_append hprefix tailTrace_4061594
  have hstable : (prefixWord ++ tailWord_4061594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061594).length < 2 ^ (prefixWord ++ tailWord_4061594).sum := by decide
  have hdescent : baseEnd_4061594 < baseStart_4061594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061624 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 2, 4, 3]
def baseStart_4061624 : Nat := 118140960795 + 4061624 * 2 ^ 59
def prefixEnd_4061624 : Nat := 4983230072969 + 3 ^ 40 * 4061624 * 2
def baseEnd_4061624 : Nat := 2085565349837122111120937

theorem tailTrace_4061624 : CollatzResearch.WordTrace tailWord_4061624 prefixEnd_4061624 2085565349837122111120937 := by
  unfold tailWord_4061624
  simp only [CollatzResearch.WordTrace]
  refine ⟨74069798718718696499203963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98759731624958261998938617 74069798718718696499203963)
  ·
    refine ⟨111104698078078044748805945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74069798718718696499203963 111104698078078044748805945)
    ·
      refine ⟨83328523558558533561604459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111104698078078044748805945 83328523558558533561604459)
      ·
        refine ⟨124992785337837800342406689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83328523558558533561604459 124992785337837800342406689)
        ·
          refine ⟨93744589003378350256805017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124992785337837800342406689 93744589003378350256805017)
          ·
            refine ⟨70308441752533762692603763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93744589003378350256805017 70308441752533762692603763)
            ·
              refine ⟨105462662628800644038905645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70308441752533762692603763 105462662628800644038905645)
              ·
                refine ⟨39548498485800241514589617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105462662628800644038905645 39548498485800241514589617)
                ·
                  refine ⟨29661373864350181135942213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39548498485800241514589617 29661373864350181135942213)
                  ·
                    refine ⟨5561507599565658962989165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29661373864350181135942213 5561507599565658962989165)
                    ·
                      refine ⟨2085565349837122111120937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5561507599565658962989165 2085565349837122111120937)
                      ·
                        rfl

theorem cell23_4061624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 2, 4, 3].length) (baseStart_4061624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061624 prefixEnd_4061624 := by exact prefixLift 4061624
  have htrace : WordTrace (prefixWord ++ tailWord_4061624) baseStart_4061624 baseEnd_4061624 := by
    simpa [prefixWord, tailWord_4061624, baseEnd_4061624] using wordTrace_append hprefix tailTrace_4061624
  have hstable : (prefixWord ++ tailWord_4061624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061624).length < 2 ^ (prefixWord ++ tailWord_4061624).sum := by decide
  have hdescent : baseEnd_4061624 < baseStart_4061624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061627 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 13]
def baseStart_4061627 : Nat := 118140960795 + 4061627 * 2 ^ 59
def prefixEnd_4061627 : Nat := 4983230072969 + 3 ^ 40 * 4061627 * 2
def baseEnd_4061627 : Nat := 231729654475453955487047

theorem tailTrace_4061627 : CollatzResearch.WordTrace tailWord_4061627 prefixEnd_4061627 231729654475453955487047 := by
  unfold tailWord_4061627
  simp only [CollatzResearch.WordTrace]
  refine ⟨148139706856426524510767135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98759804570951016340511423 148139706856426524510767135)
  ·
    refine ⟨222209560284639786766150703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148139706856426524510767135 222209560284639786766150703)
    ·
      refine ⟨333314340426959680149226055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222209560284639786766150703 333314340426959680149226055)
      ·
        refine ⟨499971510640439520223839083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333314340426959680149226055 499971510640439520223839083)
        ·
          refine ⟨749957265960659280335758625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499971510640439520223839083 749957265960659280335758625)
          ·
            refine ⟨562467949470494460251818969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 749957265960659280335758625 562467949470494460251818969)
            ·
              refine ⟨421850962102870845188864227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562467949470494460251818969 421850962102870845188864227)
              ·
                refine ⟨632776443154306267783296341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421850962102870845188864227 632776443154306267783296341)
                ·
                  refine ⟨231729654475453955487047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 632776443154306267783296341 231729654475453955487047)
                  ·
                    rfl

theorem cell23_4061627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 13].length) (baseStart_4061627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061627 prefixEnd_4061627 := by exact prefixLift 4061627
  have htrace : WordTrace (prefixWord ++ tailWord_4061627) baseStart_4061627 baseEnd_4061627 := by
    simpa [prefixWord, tailWord_4061627, baseEnd_4061627] using wordTrace_append hprefix tailTrace_4061627
  have hstable : (prefixWord ++ tailWord_4061627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061627).length < 2 ^ (prefixWord ++ tailWord_4061627).sum := by decide
  have hdescent : baseEnd_4061627 < baseStart_4061627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061671 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 3]
def baseStart_4061671 : Nat := 118140960795 + 4061671 * 2 ^ 59
def prefixEnd_4061671 : Nat := 4983230072969 + 3 ^ 40 * 4061671 * 2
def baseEnd_4061671 : Nat := 2085589483427883427233221

theorem tailTrace_4061671 : CollatzResearch.WordTrace tailWord_4061671 prefixEnd_4061671 2085589483427883427233221 := by
  unfold tailWord_4061671
  simp only [CollatzResearch.WordTrace]
  refine ⟨148141311668267120025368867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98760874445511413350245911 148141311668267120025368867)
  ·
    refine ⟨222211967502400680038053301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148141311668267120025368867 222211967502400680038053301)
    ·
      refine ⟨20832371953350063753567497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222211967502400680038053301 20832371953350063753567497)
      ·
        refine ⟨15624278965012547815175623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20832371953350063753567497 15624278965012547815175623)
        ·
          refine ⟨23436418447518821722763435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15624278965012547815175623 23436418447518821722763435)
          ·
            refine ⟨35154627671278232584145153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23436418447518821722763435 35154627671278232584145153)
            ·
              refine ⟨26365970753458674438108865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35154627671278232584145153 26365970753458674438108865)
              ·
                refine ⟨19774478065094005828581649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26365970753458674438108865 19774478065094005828581649)
                ·
                  refine ⟨14830858548820504371436237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19774478065094005828581649 14830858548820504371436237)
                  ·
                    refine ⟨5561571955807689139288589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14830858548820504371436237 5561571955807689139288589)
                    ·
                      refine ⟨2085589483427883427233221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5561571955807689139288589 2085589483427883427233221)
                      ·
                        rfl

theorem cell23_4061671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_4061671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061671 prefixEnd_4061671 := by exact prefixLift 4061671
  have htrace : WordTrace (prefixWord ++ tailWord_4061671) baseStart_4061671 baseEnd_4061671 := by
    simpa [prefixWord, tailWord_4061671, baseEnd_4061671] using wordTrace_append hprefix tailTrace_4061671
  have hstable : (prefixWord ++ tailWord_4061671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061671).length < 2 ^ (prefixWord ++ tailWord_4061671).sum := by decide
  have hdescent : baseEnd_4061671 < baseStart_4061671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061678 : List Nat := [4, 1, 2, 1, 2, 3, 1, 4, 5]
def baseStart_4061678 : Nat := 118140960795 + 4061678 * 2 ^ 59
def prefixEnd_4061678 : Nat := 4983230072969 + 3 ^ 40 * 4061678 * 2
def baseEnd_4061678 : Nat := 231732564199162766649521

theorem tailTrace_4061678 : CollatzResearch.WordTrace tailWord_4061678 prefixEnd_4061678 231732564199162766649521 := by
  unfold tailWord_4061678
  simp only [CollatzResearch.WordTrace]
  refine ⟨18517695872405220027609211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98761044652827840147249125 18517695872405220027609211)
  ·
    refine ⟨27776543808607830041413817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18517695872405220027609211 27776543808607830041413817)
    ·
      refine ⟨20832407856455872531060363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27776543808607830041413817 20832407856455872531060363)
      ·
        refine ⟨31248611784683808796590545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20832407856455872531060363 31248611784683808796590545)
        ·
          refine ⟨23436458838512856597442909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31248611784683808796590545 23436458838512856597442909)
          ·
            refine ⟨8788672064442321224041091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23436458838512856597442909 8788672064442321224041091)
            ·
              refine ⟨13183008096663481836061637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8788672064442321224041091 13183008096663481836061637)
              ·
                refine ⟨2471814018124402844261557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13183008096663481836061637 2471814018124402844261557)
                ·
                  refine ⟨231732564199162766649521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2471814018124402844261557 231732564199162766649521)
                  ·
                    rfl

theorem cell23_4061678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_4061678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061678 prefixEnd_4061678 := by exact prefixLift 4061678
  have htrace : WordTrace (prefixWord ++ tailWord_4061678) baseStart_4061678 baseEnd_4061678 := by
    simpa [prefixWord, tailWord_4061678, baseEnd_4061678] using wordTrace_append hprefix tailTrace_4061678
  have hstable : (prefixWord ++ tailWord_4061678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061678).length < 2 ^ (prefixWord ++ tailWord_4061678).sum := by decide
  have hdescent : baseEnd_4061678 < baseStart_4061678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061681 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 1, 7, 2]
def baseStart_4061681 : Nat := 118140960795 + 4061681 * 2 ^ 59
def prefixEnd_4061681 : Nat := 4983230072969 + 3 ^ 40 * 4061681 * 2
def baseEnd_4061681 : Nat := 2085594618234428388108175

theorem tailTrace_4061681 : CollatzResearch.WordTrace tailWord_4061681 prefixEnd_4061681 2085594618234428388108175 := by
  unfold tailWord_4061681
  simp only [CollatzResearch.WordTrace]
  refine ⟨148141676398230891733232897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98761117598820594488821931 148141676398230891733232897)
  ·
    refine ⟨111106257298673168799924673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148141676398230891733232897 111106257298673168799924673)
    ·
      refine ⟨83329692974004876599943505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111106257298673168799924673 83329692974004876599943505)
      ·
        refine ⟨62497269730503657449957629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83329692974004876599943505 62497269730503657449957629)
        ·
          refine ⟨23436476148938871543734111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62497269730503657449957629 23436476148938871543734111)
          ·
            refine ⟨35154714223408307315601167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23436476148938871543734111 35154714223408307315601167)
            ·
              refine ⟨52732071335112460973401751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35154714223408307315601167 52732071335112460973401751)
              ·
                refine ⟨79098107002668691460102627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52732071335112460973401751 79098107002668691460102627)
                ·
                  refine ⟨118647160504003037190153941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79098107002668691460102627 118647160504003037190153941)
                  ·
                    refine ⟨2780792824312571184144233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 118647160504003037190153941 2780792824312571184144233)
                    ·
                      refine ⟨2085594618234428388108175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2780792824312571184144233 2085594618234428388108175)
                      ·
                        rfl

theorem cell23_4061681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_4061681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061681 prefixEnd_4061681 := by exact prefixLift 4061681
  have htrace : WordTrace (prefixWord ++ tailWord_4061681) baseStart_4061681 baseEnd_4061681 := by
    simpa [prefixWord, tailWord_4061681, baseEnd_4061681] using wordTrace_append hprefix tailTrace_4061681
  have hstable : (prefixWord ++ tailWord_4061681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061681).length < 2 ^ (prefixWord ++ tailWord_4061681).sum := by decide
  have hdescent : baseEnd_4061681 < baseStart_4061681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061708 : List Nat := [2, 2, 1, 2, 4, 3, 1, 1, 2, 5]
def baseStart_4061708 : Nat := 118140960795 + 4061708 * 2 ^ 59
def prefixEnd_4061708 : Nat := 4983230072969 + 3 ^ 40 * 4061708 * 2
def baseEnd_4061708 : Nat := 695202827404033260823517

theorem tailTrace_4061708 : CollatzResearch.WordTrace tailWord_4061708 prefixEnd_4061708 695202827404033260823517 := by
  unfold tailWord_4061708
  simp only [CollatzResearch.WordTrace]
  refine ⟨74071330584566537672232889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98761774112755383562977185 74071330584566537672232889)
  ·
    refine ⟨55553497938424903254174667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74071330584566537672232889 55553497938424903254174667)
    ·
      refine ⟨83330246907637354881262001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55553497938424903254174667 83330246907637354881262001)
      ·
        refine ⟨62497685180728016160946501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83330246907637354881262001 62497685180728016160946501)
        ·
          refine ⟨11718315971386503030177469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62497685180728016160946501 11718315971386503030177469)
          ·
            refine ⟨4394368489269938636316551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11718315971386503030177469 4394368489269938636316551)
            ·
              refine ⟨6591552733904907954474827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4394368489269938636316551 6591552733904907954474827)
              ·
                refine ⟨9887329100857361931712241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6591552733904907954474827 9887329100857361931712241)
                ·
                  refine ⟨7415496825643021448784181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9887329100857361931712241 7415496825643021448784181)
                  ·
                    refine ⟨695202827404033260823517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7415496825643021448784181 695202827404033260823517)
                    ·
                      rfl

theorem cell23_4061708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 2, 5].length) (baseStart_4061708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061708 prefixEnd_4061708 := by exact prefixLift 4061708
  have htrace : WordTrace (prefixWord ++ tailWord_4061708) baseStart_4061708 baseEnd_4061708 := by
    simpa [prefixWord, tailWord_4061708, baseEnd_4061708] using wordTrace_append hprefix tailTrace_4061708
  have hstable : (prefixWord ++ tailWord_4061708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061708).length < 2 ^ (prefixWord ++ tailWord_4061708).sum := by decide
  have hdescent : baseEnd_4061708 < baseStart_4061708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061711 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 4, 4, 2]
def baseStart_4061711 : Nat := 118140960795 + 4061711 * 2 ^ 59
def prefixEnd_4061711 : Nat := 4983230072969 + 3 ^ 40 * 4061711 * 2
def baseEnd_4061711 : Nat := 2085610022654063270733037

theorem tailTrace_4061711 : CollatzResearch.WordTrace tailWord_4061711 prefixEnd_4061711 2085610022654063270733037 := by
  unfold tailWord_4061711
  simp only [CollatzResearch.WordTrace]
  refine ⟨148142770588122206856824987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98761847058748137904549991 148142770588122206856824987)
  ·
    refine ⟨222214155882183310285237481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148142770588122206856824987 222214155882183310285237481)
    ·
      refine ⟨166660616911637482713928111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222214155882183310285237481 166660616911637482713928111)
      ·
        refine ⟨249990925367456224070892167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166660616911637482713928111 249990925367456224070892167)
        ·
          refine ⟨374986388051184336106338251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249990925367456224070892167 374986388051184336106338251)
          ·
            refine ⟨562479582076776504159507377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374986388051184336106338251 562479582076776504159507377)
            ·
              refine ⟨421859686557582378119630533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562479582076776504159507377 421859686557582378119630533)
              ·
                refine ⟨79098691229546695897430725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 421859686557582378119630533 79098691229546695897430725)
                ·
                  refine ⟨14831004605540005480768261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79098691229546695897430725 14831004605540005480768261)
                  ·
                    refine ⟨2780813363538751027644049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14831004605540005480768261 2780813363538751027644049)
                    ·
                      refine ⟨2085610022654063270733037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2780813363538751027644049 2085610022654063270733037)
                      ·
                        rfl

theorem cell23_4061711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 4, 2].length) (baseStart_4061711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061711 prefixEnd_4061711 := by exact prefixLift 4061711
  have htrace : WordTrace (prefixWord ++ tailWord_4061711) baseStart_4061711 baseEnd_4061711 := by
    simpa [prefixWord, tailWord_4061711, baseEnd_4061711] using wordTrace_append hprefix tailTrace_4061711
  have hstable : (prefixWord ++ tailWord_4061711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061711).length < 2 ^ (prefixWord ++ tailWord_4061711).sum := by decide
  have hdescent : baseEnd_4061711 < baseStart_4061711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061738 : List Nat := [3, 1, 4, 1, 1, 2, 1, 3, 3, 4]
def baseStart_4061738 : Nat := 118140960795 + 4061738 * 2 ^ 59
def prefixEnd_4061738 : Nat := 4983230072969 + 3 ^ 40 * 4061738 * 2
def baseEnd_4061738 : Nat := 695207962210578221698471

theorem tailTrace_4061738 : CollatzResearch.WordTrace tailWord_4061738 prefixEnd_4061738 695207962210578221698471 := by
  unfold tailWord_4061738
  simp only [CollatzResearch.WordTrace]
  refine ⟨37035938839756097617014467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98762503572682926978705245 37035938839756097617014467)
  ·
    refine ⟨55553908259634146425521701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37035938839756097617014467 55553908259634146425521701)
    ·
      refine ⟨10416357798681402454785319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55553908259634146425521701 10416357798681402454785319)
      ·
        refine ⟨15624536698022103682177979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10416357798681402454785319 15624536698022103682177979)
        ·
          refine ⟨23436805047033155523266969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15624536698022103682177979 23436805047033155523266969)
          ·
            refine ⟨17577603785274866642450227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23436805047033155523266969 17577603785274866642450227)
            ·
              refine ⟨26366405677912299963675341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17577603785274866642450227 26366405677912299963675341)
              ·
                refine ⟨9887402129217112486378253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26366405677912299963675341 9887402129217112486378253)
                ·
                  refine ⟨3707775798456417182391845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9887402129217112486378253 3707775798456417182391845)
                  ·
                    refine ⟨695207962210578221698471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3707775798456417182391845 695207962210578221698471)
                    ·
                      rfl

theorem cell23_4061738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_4061738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061738 prefixEnd_4061738 := by exact prefixLift 4061738
  have htrace : WordTrace (prefixWord ++ tailWord_4061738) baseStart_4061738 baseEnd_4061738 := by
    simpa [prefixWord, tailWord_4061738, baseEnd_4061738] using wordTrace_append hprefix tailTrace_4061738
  have hstable : (prefixWord ++ tailWord_4061738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061738).length < 2 ^ (prefixWord ++ tailWord_4061738).sum := by decide
  have hdescent : baseEnd_4061738 < baseStart_4061738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061801 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 3, 1, 4]
def baseStart_4061801 : Nat := 118140960795 + 4061801 * 2 ^ 59
def prefixEnd_4061801 : Nat := 4983230072969 + 3 ^ 40 * 4061801 * 2
def baseEnd_4061801 : Nat := 2085656235912967918607623

theorem tailTrace_4061801 : CollatzResearch.WordTrace tailWord_4061801 prefixEnd_4061801 2085656235912967918607623 := by
  unfold tailWord_4061801
  simp only [CollatzResearch.WordTrace]
  refine ⟨148146053157796152227601257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98764035438530768151734171 148146053157796152227601257)
  ·
    refine ⟨111109539868347114170700943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148146053157796152227601257 111109539868347114170700943)
    ·
      refine ⟨166664309802520671256051415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111109539868347114170700943 166664309802520671256051415)
      ·
        refine ⟨249996464703781006884077123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166664309802520671256051415 249996464703781006884077123)
        ·
          refine ⟨374994697055671510326115685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249996464703781006884077123 374994697055671510326115685)
          ·
            refine ⟨70311505697938408186146691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 374994697055671510326115685 70311505697938408186146691)
            ·
              refine ⟨105467258546907612279220037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70311505697938408186146691 105467258546907612279220037)
              ·
                refine ⟨19775110977545177302353757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105467258546907612279220037 19775110977545177302353757)
                ·
                  refine ⟨7415666616579441488382659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19775110977545177302353757 7415666616579441488382659)
                  ·
                    refine ⟨11123499924869162232573989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7415666616579441488382659 11123499924869162232573989)
                    ·
                      refine ⟨2085656235912967918607623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11123499924869162232573989 2085656235912967918607623)
                      ·
                        rfl

theorem cell23_4061801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 1, 4].length) (baseStart_4061801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061801 prefixEnd_4061801 := by exact prefixLift 4061801
  have htrace : WordTrace (prefixWord ++ tailWord_4061801) baseStart_4061801 baseEnd_4061801 := by
    simpa [prefixWord, tailWord_4061801, baseEnd_4061801] using wordTrace_append hprefix tailTrace_4061801
  have hstable : (prefixWord ++ tailWord_4061801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061801).length < 2 ^ (prefixWord ++ tailWord_4061801).sum := by decide
  have hdescent : baseEnd_4061801 < baseStart_4061801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061811 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 6, 4]
def baseStart_4061811 : Nat := 118140960795 + 4061811 * 2 ^ 59
def prefixEnd_4061811 : Nat := 4983230072969 + 3 ^ 40 * 4061811 * 2
def baseEnd_4061811 : Nat := 695220456906504293160859

theorem tailTrace_4061811 : CollatzResearch.WordTrace tailWord_4061811 prefixEnd_4061811 695220456906504293160859 := by
  unfold tailWord_4061811
  simp only [CollatzResearch.WordTrace]
  refine ⟨148146417887759923935465287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98764278591839949290310191 148146417887759923935465287)
  ·
    refine ⟨222219626831639885903197931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148146417887759923935465287 222219626831639885903197931)
    ·
      refine ⟨333329440247459828854796897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222219626831639885903197931 333329440247459828854796897)
      ·
        refine ⟨249997080185594871641097673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333329440247459828854796897 249997080185594871641097673)
        ·
          refine ⟨187497810139196153730823255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249997080185594871641097673 187497810139196153730823255)
          ·
            refine ⟨281246715208794230596234883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187497810139196153730823255 281246715208794230596234883)
            ·
              refine ⟨421870072813191345894352325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281246715208794230596234883 421870072813191345894352325)
              ·
                refine ⟨79100638652473377355191061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 421870072813191345894352325 79100638652473377355191061)
                ·
                  refine ⟨3707842436834689563524581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79100638652473377355191061 3707842436834689563524581)
                  ·
                    refine ⟨695220456906504293160859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3707842436834689563524581 695220456906504293160859)
                    ·
                      rfl

theorem cell23_4061811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 4].length) (baseStart_4061811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061811 prefixEnd_4061811 := by exact prefixLift 4061811
  have htrace : WordTrace (prefixWord ++ tailWord_4061811) baseStart_4061811 baseEnd_4061811 := by
    simpa [prefixWord, tailWord_4061811, baseEnd_4061811] using wordTrace_append hprefix tailTrace_4061811
  have hstable : (prefixWord ++ tailWord_4061811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061811).length < 2 ^ (prefixWord ++ tailWord_4061811).sum := by decide
  have hdescent : baseEnd_4061811 < baseStart_4061811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061828 : List Nat := [2, 3, 2, 1, 3, 2, 1, 2, 1, 6]
def baseStart_4061828 : Nat := 118140960795 + 4061828 * 2 ^ 59
def prefixEnd_4061828 : Nat := 4983230072969 + 3 ^ 40 * 4061828 * 2
def baseEnd_4061828 : Nat := 695223366630213104323333

theorem tailTrace_4061828 : CollatzResearch.WordTrace tailWord_4061828 prefixEnd_4061828 695223366630213104323333 := by
  unfold tailWord_4061828
  simp only [CollatzResearch.WordTrace]
  refine ⟨74073518964349167919417069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98764691952465557225889425 74073518964349167919417069)
  ·
    refine ⟨27777569611630937969781401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74073518964349167919417069 27777569611630937969781401)
    ·
      refine ⟨20833177208723203477336051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27777569611630937969781401 20833177208723203477336051)
      ·
        refine ⟨31249765813084805216004077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20833177208723203477336051 31249765813084805216004077)
        ·
          refine ⟨11718662179906801956001529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31249765813084805216004077 11718662179906801956001529)
          ·
            refine ⟨8788996634930101467001147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11718662179906801956001529 8788996634930101467001147)
            ·
              refine ⟨13183494952395152200501721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8788996634930101467001147 13183494952395152200501721)
              ·
                refine ⟨9887621214296364150376291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13183494952395152200501721 9887621214296364150376291)
                ·
                  refine ⟨14831431821444546225564437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9887621214296364150376291 14831431821444546225564437)
                  ·
                    refine ⟨695223366630213104323333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14831431821444546225564437 695223366630213104323333)
                    ·
                      rfl

theorem cell23_4061828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_4061828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061828 prefixEnd_4061828 := by exact prefixLift 4061828
  have htrace : WordTrace (prefixWord ++ tailWord_4061828) baseStart_4061828 baseEnd_4061828 := by
    simpa [prefixWord, tailWord_4061828, baseEnd_4061828] using wordTrace_append hprefix tailTrace_4061828
  have hstable : (prefixWord ++ tailWord_4061828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061828).length < 2 ^ (prefixWord ++ tailWord_4061828).sum := by decide
  have hdescent : baseEnd_4061828 < baseStart_4061828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061881 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 2, 2, 5]
def baseStart_4061881 : Nat := 118140960795 + 4061881 * 2 ^ 59
def prefixEnd_4061881 : Nat := 4983230072969 + 3 ^ 40 * 4061881 * 2
def baseEnd_4061881 : Nat := 2085697314365327605607255

theorem tailTrace_4061881 : CollatzResearch.WordTrace tailWord_4061881 prefixEnd_4061881 2085697314365327605607255 := by
  unfold tailWord_4061881
  simp only [CollatzResearch.WordTrace]
  refine ⟨148148970997506325890513497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98765980665004217260342331 148148970997506325890513497)
  ·
    refine ⟨111111728248129744417885123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148148970997506325890513497 111111728248129744417885123)
    ·
      refine ⟨166667592372194616626827685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111111728248129744417885123 166667592372194616626827685)
      ·
        refine ⟨31250173569786490617530191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166667592372194616626827685 31250173569786490617530191)
        ·
          refine ⟨46875260354679735926295287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31250173569786490617530191 46875260354679735926295287)
          ·
            refine ⟨70312890532019603889442931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46875260354679735926295287 70312890532019603889442931)
            ·
              refine ⟨105469335798029405834164397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70312890532019603889442931 105469335798029405834164397)
              ·
                refine ⟨39551000924261027187811649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105469335798029405834164397 39551000924261027187811649)
                ·
                  refine ⟨29663250693195770390858737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39551000924261027187811649 29663250693195770390858737)
                  ·
                    refine ⟨22247438019896827793144053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29663250693195770390858737 22247438019896827793144053)
                    ·
                      refine ⟨2085697314365327605607255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22247438019896827793144053 2085697314365327605607255)
                      ·
                        rfl

theorem cell23_4061881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_4061881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061881 prefixEnd_4061881 := by exact prefixLift 4061881
  have htrace : WordTrace (prefixWord ++ tailWord_4061881) baseStart_4061881 baseEnd_4061881 := by
    simpa [prefixWord, tailWord_4061881, baseEnd_4061881] using wordTrace_append hprefix tailTrace_4061881
  have hstable : (prefixWord ++ tailWord_4061881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061881).length < 2 ^ (prefixWord ++ tailWord_4061881).sum := by decide
  have hdescent : baseEnd_4061881 < baseStart_4061881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061889 : List Nat := [1, 2, 6, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_4061889 : Nat := 118140960795 + 4061889 * 2 ^ 59
def prefixEnd_4061889 : Nat := 4983230072969 + 3 ^ 40 * 4061889 * 2
def baseEnd_4061889 : Nat := 2085701422210563574307219

theorem tailTrace_4061889 : CollatzResearch.WordTrace tailWord_4061889 prefixEnd_4061889 2085701422210563574307219 := by
  unfold tailWord_4061889
  simp only [CollatzResearch.WordTrace]
  refine ⟨148149262781477343256804721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98766175187651562171203147 148149262781477343256804721)
  ·
    refine ⟨111111947086108007442603541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148149262781477343256804721 111111947086108007442603541)
    ·
      refine ⟨5208372519661312848872041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 111111947086108007442603541 5208372519661312848872041)
      ·
        refine ⟨3906279389745984636654031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5208372519661312848872041 3906279389745984636654031)
        ·
          refine ⟨5859419084618976954981047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3906279389745984636654031 5859419084618976954981047)
          ·
            refine ⟨8789128626928465432471571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5859419084618976954981047 8789128626928465432471571)
            ·
              refine ⟨13183692940392698148707357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8789128626928465432471571 13183692940392698148707357)
              ·
                refine ⟨4943884852647261805765259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13183692940392698148707357 4943884852647261805765259)
                ·
                  refine ⟨7415827278970892708647889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4943884852647261805765259 7415827278970892708647889)
                  ·
                    refine ⟨5561870459228169531485917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7415827278970892708647889 5561870459228169531485917)
                    ·
                      refine ⟨2085701422210563574307219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5561870459228169531485917 2085701422210563574307219)
                      ·
                        rfl

theorem cell23_4061889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_4061889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061889 prefixEnd_4061889 := by exact prefixLift 4061889
  have htrace : WordTrace (prefixWord ++ tailWord_4061889) baseStart_4061889 baseEnd_4061889 := by
    simpa [prefixWord, tailWord_4061889, baseEnd_4061889] using wordTrace_append hprefix tailTrace_4061889
  have hstable : (prefixWord ++ tailWord_4061889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061889).length < 2 ^ (prefixWord ++ tailWord_4061889).sum := by decide
  have hdescent : baseEnd_4061889 < baseStart_4061889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061902 : List Nat := [4, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3]
def baseStart_4061902 : Nat := 118140960795 + 4061902 * 2 ^ 59
def prefixEnd_4061902 : Nat := 4983230072969 + 3 ^ 40 * 4061902 * 2
def baseEnd_4061902 : Nat := 2085708097459072023444659

theorem tailTrace_4061902 : CollatzResearch.WordTrace tailWord_4061902 prefixEnd_4061902 2085708097459072023444659 := by
  unfold tailWord_4061902
  simp only [CollatzResearch.WordTrace]
  refine ⟨18518717116303780809628495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98766491286953497651351973 18518717116303780809628495)
  ·
    refine ⟨27778075674455671214442743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18518717116303780809628495 27778075674455671214442743)
    ·
      refine ⟨41667113511683506821664115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27778075674455671214442743 41667113511683506821664115)
      ·
        refine ⟨62500670267525260232496173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41667113511683506821664115 62500670267525260232496173)
        ·
          refine ⟨23437751350321972587186065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62500670267525260232496173 23437751350321972587186065)
          ·
            refine ⟨17578313512741479440389549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23437751350321972587186065 17578313512741479440389549)
            ·
              refine ⟨6591867567278054790146081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17578313512741479440389549 6591867567278054790146081)
              ·
                refine ⟨4943900675458541092609561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6591867567278054790146081 4943900675458541092609561)
                ·
                  refine ⟨3707925506593905819457171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4943900675458541092609561 3707925506593905819457171)
                  ·
                    refine ⟨5561888259890858729185757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3707925506593905819457171 5561888259890858729185757)
                    ·
                      refine ⟨2085708097459072023444659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5561888259890858729185757 2085708097459072023444659)
                      ·
                        rfl

theorem cell23_4061902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_4061902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061902 prefixEnd_4061902 := by exact prefixLift 4061902
  have htrace : WordTrace (prefixWord ++ tailWord_4061902) baseStart_4061902 baseEnd_4061902 := by
    simpa [prefixWord, tailWord_4061902, baseEnd_4061902] using wordTrace_append hprefix tailTrace_4061902
  have hstable : (prefixWord ++ tailWord_4061902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061902).length < 2 ^ (prefixWord ++ tailWord_4061902).sum := by decide
  have hdescent : baseEnd_4061902 < baseStart_4061902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061942 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2]
def baseStart_4061942 : Nat := 118140960795 + 4061942 * 2 ^ 59
def prefixEnd_4061942 : Nat := 4983230072969 + 3 ^ 40 * 4061942 * 2
def baseEnd_4061942 : Nat := 2085728636685251866944475

theorem tailTrace_4061942 : CollatzResearch.WordTrace tailWord_4061942 prefixEnd_4061942 2085728636685251866944475 := by
  unfold tailWord_4061942
  simp only [CollatzResearch.WordTrace]
  refine ⟨9259449740642833331780255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98767463900190222205656053 9259449740642833331780255)
  ·
    refine ⟨13889174610964249997670383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9259449740642833331780255 13889174610964249997670383)
    ·
      refine ⟨20833761916446374996505575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13889174610964249997670383 20833761916446374996505575)
      ·
        refine ⟨31250642874669562494758363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20833761916446374996505575 31250642874669562494758363)
        ·
          refine ⟨46875964312004343742137545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31250642874669562494758363 46875964312004343742137545)
          ·
            refine ⟨35156973234003257806603159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46875964312004343742137545 35156973234003257806603159)
            ·
              refine ⟨52735459851004886709904739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35156973234003257806603159 52735459851004886709904739)
              ·
                refine ⟨79103189776507330064857109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52735459851004886709904739 79103189776507330064857109)
                ·
                  refine ⟨3707962020773781096790177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79103189776507330064857109 3707962020773781096790177)
                  ·
                    refine ⟨2780971515580335822592633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3707962020773781096790177 2780971515580335822592633)
                    ·
                      refine ⟨2085728636685251866944475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2780971515580335822592633 2085728636685251866944475)
                      ·
                        rfl

theorem cell23_4061942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_4061942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061942 prefixEnd_4061942 := by exact prefixLift 4061942
  have htrace : WordTrace (prefixWord ++ tailWord_4061942) baseStart_4061942 baseEnd_4061942 := by
    simpa [prefixWord, tailWord_4061942, baseEnd_4061942] using wordTrace_append hprefix tailTrace_4061942
  have hstable : (prefixWord ++ tailWord_4061942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061942).length < 2 ^ (prefixWord ++ tailWord_4061942).sum := by decide
  have hdescent : baseEnd_4061942 < baseStart_4061942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061978 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 4, 5]
def baseStart_4061978 : Nat := 118140960795 + 4061978 * 2 ^ 59
def prefixEnd_4061978 : Nat := 4983230072969 + 3 ^ 40 * 4061978 * 2
def baseEnd_4061978 : Nat := 695249040662937908698103

theorem tailTrace_4061978 : CollatzResearch.WordTrace tailWord_4061978 prefixEnd_4061978 695249040662937908698103 := by
  unfold tailWord_4061978
  simp only [CollatzResearch.WordTrace]
  refine ⟨37038127219538727864198647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98768339252103274304529725 37038127219538727864198647)
  ·
    refine ⟨55557190829308091796297971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37038127219538727864198647 55557190829308091796297971)
    ·
      refine ⟨83335786243962137694446957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55557190829308091796297971 83335786243962137694446957)
      ·
        refine ⟨31250919841485801635417609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83335786243962137694446957 31250919841485801635417609)
        ·
          refine ⟨23438189881114351226563207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31250919841485801635417609 23438189881114351226563207)
          ·
            refine ⟨35157284821671526839844811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23438189881114351226563207 35157284821671526839844811)
            ·
              refine ⟨52735927232507290259767217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35157284821671526839844811 52735927232507290259767217)
              ·
                refine ⟨39551945424380467694825413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52735927232507290259767217 39551945424380467694825413)
                ·
                  refine ⟨7415989767071337692779765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39551945424380467694825413 7415989767071337692779765)
                  ·
                    refine ⟨695249040662937908698103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7415989767071337692779765 695249040662937908698103)
                    ·
                      rfl

theorem cell23_4061978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_4061978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4061978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4061978 prefixEnd_4061978 := by exact prefixLift 4061978
  have htrace : WordTrace (prefixWord ++ tailWord_4061978) baseStart_4061978 baseEnd_4061978 := by
    simpa [prefixWord, tailWord_4061978, baseEnd_4061978] using wordTrace_append hprefix tailTrace_4061978
  have hstable : (prefixWord ++ tailWord_4061978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061978).length < 2 ^ (prefixWord ++ tailWord_4061978).sum := by decide
  have hdescent : baseEnd_4061978 < baseStart_4061978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062015 : List Nat := [1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 4]
def baseStart_4062015 : Nat := 118140960795 + 4062015 * 2 ^ 59
def prefixEnd_4062015 : Nat := 4983230072969 + 3 ^ 40 * 4062015 * 2
def baseEnd_4062015 : Nat := 2085766120773030081331639

theorem tailTrace_4062015 : CollatzResearch.WordTrace tailWord_4062015 prefixEnd_4062015 2085766120773030081331639 := by
  unfold tailWord_4062015
  simp only [CollatzResearch.WordTrace]
  refine ⟨148153858379020866775891499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98769238919347244517260999 148153858379020866775891499)
  ·
    refine ⟨222230787568531300163837249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148153858379020866775891499 222230787568531300163837249)
    ·
      refine ⟨166673090676398475122877937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222230787568531300163837249 166673090676398475122877937)
      ·
        refine ⟨125004818007298856342158453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166673090676398475122877937 125004818007298856342158453)
        ·
          refine ⟨11719201688184267782077355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125004818007298856342158453 11719201688184267782077355)
          ·
            refine ⟨17578802532276401673116033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11719201688184267782077355 17578802532276401673116033)
            ·
              refine ⟨13184101899207301254837025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17578802532276401673116033 13184101899207301254837025)
              ·
                refine ⟨9888076424405475941127769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13184101899207301254837025 9888076424405475941127769)
                ·
                  refine ⟨7416057318304106955845827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9888076424405475941127769 7416057318304106955845827)
                  ·
                    refine ⟨11124085977456160433768741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7416057318304106955845827 11124085977456160433768741)
                    ·
                      refine ⟨2085766120773030081331639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11124085977456160433768741 2085766120773030081331639)
                      ·
                        rfl

theorem cell23_4062015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_4062015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062015 prefixEnd_4062015 := by exact prefixLift 4062015
  have htrace : WordTrace (prefixWord ++ tailWord_4062015) baseStart_4062015 baseEnd_4062015 := by
    simpa [prefixWord, tailWord_4062015, baseEnd_4062015] using wordTrace_append hprefix tailTrace_4062015
  have hstable : (prefixWord ++ tailWord_4062015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062015).length < 2 ^ (prefixWord ++ tailWord_4062015).sum := by decide
  have hdescent : baseEnd_4062015 < baseStart_4062015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062052 : List Nat := [2, 3, 1, 1, 4, 1, 3, 1, 2, 2, 3]
def baseStart_4062052 : Nat := 118140960795 + 4062052 * 2 ^ 59
def prefixEnd_4062052 : Nat := 4983230072969 + 3 ^ 40 * 4062052 * 2
def baseEnd_4062052 : Nat := 2085785119557246436568969

theorem tailTrace_4062052 : CollatzResearch.WordTrace tailWord_4062052 prefixEnd_4062052 2085785119557246436568969 := by
  unfold tailWord_4062052
  simp only [CollatzResearch.WordTrace]
  refine ⟨74077603939943411047494205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98770138586591214729992273 74077603939943411047494205)
  ·
    refine ⟨27779101477478779142810327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74077603939943411047494205 27779101477478779142810327)
    ·
      refine ⟨41668652216218168714215491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27779101477478779142810327 41668652216218168714215491)
      ·
        refine ⟨62502978324327253071323237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41668652216218168714215491 62502978324327253071323237)
        ·
          refine ⟨11719308435811359950873107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62502978324327253071323237 11719308435811359950873107)
          ·
            refine ⟨17578962653717039926309661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11719308435811359950873107 17578962653717039926309661)
            ·
              refine ⟨6592110995143889972366123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17578962653717039926309661 6592110995143889972366123)
              ·
                refine ⟨9888166492715834958549185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6592110995143889972366123 9888166492715834958549185)
                ·
                  refine ⟨7416124869536876218911889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9888166492715834958549185 7416124869536876218911889)
                  ·
                    refine ⟨5562093652152657164183917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7416124869536876218911889 5562093652152657164183917)
                    ·
                      refine ⟨2085785119557246436568969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5562093652152657164183917 2085785119557246436568969)
                      ·
                        rfl

theorem cell23_4062052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_4062052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062052 prefixEnd_4062052 := by exact prefixLift 4062052
  have htrace : WordTrace (prefixWord ++ tailWord_4062052) baseStart_4062052 baseEnd_4062052 := by
    simpa [prefixWord, tailWord_4062052, baseEnd_4062052] using wordTrace_append hprefix tailTrace_4062052
  have hstable : (prefixWord ++ tailWord_4062052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062052).length < 2 ^ (prefixWord ++ tailWord_4062052).sum := by decide
  have hdescent : baseEnd_4062052 < baseStart_4062052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062105 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 1, 8, 2]
def baseStart_4062105 : Nat := 118140960795 + 4062105 * 2 ^ 59
def prefixEnd_4062105 : Nat := 4983230072969 + 3 ^ 40 * 4062105 * 2
def baseEnd_4062105 : Nat := 2085812334031934729206225

theorem tailTrace_4062105 : CollatzResearch.WordTrace tailWord_4062105 prefixEnd_4062105 2085812334031934729206225 := by
  unfold tailWord_4062105
  simp only [CollatzResearch.WordTrace]
  refine ⟨148157140948694812146667769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98771427299129874764445179 148157140948694812146667769)
  ·
    refine ⟨111117855711521109110000827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148157140948694812146667769 111117855711521109110000827)
    ·
      refine ⟨166676783567281663665001241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111117855711521109110000827 166676783567281663665001241)
      ·
        refine ⟨125007587675461247748750931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166676783567281663665001241 125007587675461247748750931)
        ·
          refine ⟨187511381513191871623126397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125007587675461247748750931 187511381513191871623126397)
          ·
            refine ⟨70316768067446951858672399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187511381513191871623126397 70316768067446951858672399)
            ·
              refine ⟨105475152101170427788008599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70316768067446951858672399 105475152101170427788008599)
              ·
                refine ⟨158212728151755641682012899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105475152101170427788008599 158212728151755641682012899)
                ·
                  refine ⟨237319092227633462523019349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158212728151755641682012899 237319092227633462523019349)
                  ·
                    refine ⟨2781083112042579638941633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 237319092227633462523019349 2781083112042579638941633)
                    ·
                      refine ⟨2085812334031934729206225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2781083112042579638941633 2085812334031934729206225)
                      ·
                        rfl

theorem cell23_4062105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 8, 2].length) (baseStart_4062105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062105 prefixEnd_4062105 := by exact prefixLift 4062105
  have htrace : WordTrace (prefixWord ++ tailWord_4062105) baseStart_4062105 baseEnd_4062105 := by
    simpa [prefixWord, tailWord_4062105, baseEnd_4062105] using wordTrace_append hprefix tailTrace_4062105
  have hstable : (prefixWord ++ tailWord_4062105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062105).length < 2 ^ (prefixWord ++ tailWord_4062105).sum := by decide
  have hdescent : baseEnd_4062105 < baseStart_4062105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062115 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 4, 4]
def baseStart_4062115 : Nat := 118140960795 + 4062115 * 2 ^ 59
def prefixEnd_4062115 : Nat := 4983230072969 + 3 ^ 40 * 4062115 * 2
def baseEnd_4062115 : Nat := 695272489612826563360393

theorem tailTrace_4062115 : CollatzResearch.WordTrace tailWord_4062115 prefixEnd_4062115 695272489612826563360393 := by
  unfold tailWord_4062115
  simp only [CollatzResearch.WordTrace]
  refine ⟨148157505678658583854531799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98771670452439055903021199 148157505678658583854531799)
  ·
    refine ⟨222236258517987875781797699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148157505678658583854531799 222236258517987875781797699)
    ·
      refine ⟨333354387776981813672696549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222236258517987875781797699 333354387776981813672696549)
      ·
        refine ⟨62503947708184090063630603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333354387776981813672696549 62503947708184090063630603)
        ·
          refine ⟨93755921562276135095445905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62503947708184090063630603 93755921562276135095445905)
          ·
            refine ⟨70316941171707101321584429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93755921562276135095445905 70316941171707101321584429)
            ·
              refine ⟨26368852939390162995594161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70316941171707101321584429 26368852939390162995594161)
              ·
                refine ⟨19776639704542622246695621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26368852939390162995594161 19776639704542622246695621)
                ·
                  refine ⟨3708119944601741671255429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19776639704542622246695621 3708119944601741671255429)
                  ·
                    refine ⟨695272489612826563360393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3708119944601741671255429 695272489612826563360393)
                    ·
                      rfl

theorem cell23_4062115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 4].length) (baseStart_4062115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062115 prefixEnd_4062115 := by exact prefixLift 4062115
  have htrace : WordTrace (prefixWord ++ tailWord_4062115) baseStart_4062115 baseEnd_4062115 := by
    simpa [prefixWord, tailWord_4062115, baseEnd_4062115] using wordTrace_append hprefix tailTrace_4062115
  have hstable : (prefixWord ++ tailWord_4062115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062115).length < 2 ^ (prefixWord ++ tailWord_4062115).sum := by decide
  have hdescent : baseEnd_4062115 < baseStart_4062115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062142 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3]
def baseStart_4062142 : Nat := 118140960795 + 4062142 * 2 ^ 59
def prefixEnd_4062142 : Nat := 4983230072969 + 3 ^ 40 * 4062142 * 2
def baseEnd_4062142 : Nat := 2085831332816151084443555

theorem tailTrace_4062142 : CollatzResearch.WordTrace tailWord_4062142 prefixEnd_4062142 2085831332816151084443555 := by
  unfold tailWord_4062142
  simp only [CollatzResearch.WordTrace]
  refine ⟨18519811306195095933220585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98772326966373844977176453 18519811306195095933220585)
  ·
    refine ⟨13889858479646321949915439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18519811306195095933220585 13889858479646321949915439)
    ·
      refine ⟨20834787719469482924873159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13889858479646321949915439 20834787719469482924873159)
      ·
        refine ⟨31252181579204224387309739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20834787719469482924873159 31252181579204224387309739)
        ·
          refine ⟨46878272368806336580964609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31252181579204224387309739 46878272368806336580964609)
          ·
            refine ⟨35158704276604752435723457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46878272368806336580964609 35158704276604752435723457)
            ·
              refine ⟨26369028207453564326792593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35158704276604752435723457 26369028207453564326792593)
              ·
                refine ⟨19776771155590173245094445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26369028207453564326792593 19776771155590173245094445)
                ·
                  refine ⟨7416289183346314966910417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19776771155590173245094445 7416289183346314966910417)
                  ·
                    refine ⟨5562216887509736225182813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7416289183346314966910417 5562216887509736225182813)
                    ·
                      refine ⟨2085831332816151084443555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5562216887509736225182813 2085831332816151084443555)
                      ·
                        rfl

theorem cell23_4062142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_4062142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062142 prefixEnd_4062142 := by exact prefixLift 4062142
  have htrace : WordTrace (prefixWord ++ tailWord_4062142) baseStart_4062142 baseEnd_4062142 := by
    simpa [prefixWord, tailWord_4062142, baseEnd_4062142] using wordTrace_append hprefix tailTrace_4062142
  have hstable : (prefixWord ++ tailWord_4062142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062142).length < 2 ^ (prefixWord ++ tailWord_4062142).sum := by decide
  have hdescent : baseEnd_4062142 < baseStart_4062142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062159 : List Nat := [1, 1, 2, 1, 1, 8, 1, 2, 1, 2, 3]
def baseStart_4062159 : Nat := 118140960795 + 4062159 * 2 ^ 59
def prefixEnd_4062159 : Nat := 4983230072969 + 3 ^ 40 * 4062159 * 2
def baseEnd_4062159 : Nat := 2085840061987277517930977

theorem tailTrace_4062159 : CollatzResearch.WordTrace tailWord_4062159 prefixEnd_4062159 2085840061987277517930977 := by
  unfold tailWord_4062159
  simp only [CollatzResearch.WordTrace]
  refine ⟨148159110490499179369133531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98772740326999452912755687 148159110490499179369133531)
  ·
    refine ⟨222238665735748769053700297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148159110490499179369133531 222238665735748769053700297)
    ·
      refine ⟨166678999301811576790275223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222238665735748769053700297 166678999301811576790275223)
      ·
        refine ⟨250018498952717365185412835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166678999301811576790275223 250018498952717365185412835)
        ·
          refine ⟨375027748429076047778119253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250018498952717365185412835 375027748429076047778119253)
          ·
            refine ⟨4394856426903234934899835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 375027748429076047778119253 4394856426903234934899835)
            ·
              refine ⟨6592284640354852402349753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4394856426903234934899835 6592284640354852402349753)
              ·
                refine ⟨4944213480266139301762315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6592284640354852402349753 4944213480266139301762315)
                ·
                  refine ⟨7416320220399208952643473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4944213480266139301762315 7416320220399208952643473)
                  ·
                    refine ⟨5562240165299406714482605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7416320220399208952643473 5562240165299406714482605)
                    ·
                      refine ⟨2085840061987277517930977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5562240165299406714482605 2085840061987277517930977)
                      ·
                        rfl

theorem cell23_4062159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 2, 3].length) (baseStart_4062159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062159 prefixEnd_4062159 := by exact prefixLift 4062159
  have htrace : WordTrace (prefixWord ++ tailWord_4062159) baseStart_4062159 baseEnd_4062159 := by
    simpa [prefixWord, tailWord_4062159, baseEnd_4062159] using wordTrace_append hprefix tailTrace_4062159
  have hstable : (prefixWord ++ tailWord_4062159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062159).length < 2 ^ (prefixWord ++ tailWord_4062159).sum := by decide
  have hdescent : baseEnd_4062159 < baseStart_4062159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062206 : List Nat := [4, 2, 2, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_4062206 : Nat := 118140960795 + 4062206 * 2 ^ 59
def prefixEnd_4062206 : Nat := 4983230072969 + 3 ^ 40 * 4062206 * 2
def baseEnd_4062206 : Nat := 2085864195578038834043261

theorem tailTrace_4062206 : CollatzResearch.WordTrace tailWord_4062206 prefixEnd_4062206 2085864195578038834043261 := by
  unfold tailWord_4062206
  simp only [CollatzResearch.WordTrace]
  refine ⟨18520103090166113299511809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98773883147552604264062981 18520103090166113299511809)
  ·
    refine ⟨13890077317624584974633857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18520103090166113299511809 13890077317624584974633857)
    ·
      refine ⟨10417557988218438730975393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13890077317624584974633857 10417557988218438730975393)
      ·
        refine ⟨7813168491163829048231545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10417557988218438730975393 7813168491163829048231545)
        ·
          refine ⟨5859876368372871786173659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7813168491163829048231545 5859876368372871786173659)
          ·
            refine ⟨8789814552559307679260489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5859876368372871786173659 8789814552559307679260489)
            ·
              refine ⟨6592360914419480759445367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8789814552559307679260489 6592360914419480759445367)
              ·
                refine ⟨9888541371629221139168051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6592360914419480759445367 9888541371629221139168051)
                ·
                  refine ⟨14832812057443831708752077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9888541371629221139168051 14832812057443831708752077)
                  ·
                    refine ⟨5562304521541436890782029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14832812057443831708752077 5562304521541436890782029)
                    ·
                      refine ⟨2085864195578038834043261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5562304521541436890782029 2085864195578038834043261)
                      ·
                        rfl

theorem cell23_4062206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_4062206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062206 prefixEnd_4062206 := by exact prefixLift 4062206
  have htrace : WordTrace (prefixWord ++ tailWord_4062206) baseStart_4062206 baseEnd_4062206 := by
    simpa [prefixWord, tailWord_4062206, baseEnd_4062206] using wordTrace_append hprefix tailTrace_4062206
  have hstable : (prefixWord ++ tailWord_4062206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062206).length < 2 ^ (prefixWord ++ tailWord_4062206).sum := by decide
  have hdescent : baseEnd_4062206 < baseStart_4062206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062229 : List Nat := [1, 3, 2, 1, 4, 1, 2, 2, 1, 4, 2]
def baseStart_4062229 : Nat := 118140960795 + 4062229 * 2 ^ 59
def prefixEnd_4062229 : Nat := 4983230072969 + 3 ^ 40 * 4062229 * 2
def baseEnd_4062229 : Nat := 2085876005633092244055655

theorem tailTrace_4062229 : CollatzResearch.WordTrace tailWord_4062229 prefixEnd_4062229 2085876005633092244055655 := by
  unfold tailWord_4062229
  simp only [CollatzResearch.WordTrace]
  refine ⟨148161663600245581324181741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98774442400163720882787827 148161663600245581324181741)
  ·
    refine ⟨55560623850092092996568153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148161663600245581324181741 55560623850092092996568153)
    ·
      refine ⟨41670467887569069747426115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55560623850092092996568153 41670467887569069747426115)
      ·
        refine ⟨62505701831353604621139173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41670467887569069747426115 62505701831353604621139173)
        ·
          refine ⟨11719819093378800866463595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62505701831353604621139173 11719819093378800866463595)
          ·
            refine ⟨17579728640068201299695393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11719819093378800866463595 17579728640068201299695393)
            ·
              refine ⟨13184796480051150974771545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17579728640068201299695393 13184796480051150974771545)
              ·
                refine ⟨9888597360038363231078659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13184796480051150974771545 9888597360038363231078659)
                ·
                  refine ⟨14832896040057544846617989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9888597360038363231078659 14832896040057544846617989)
                  ·
                    refine ⟨2781168007510789658740873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14832896040057544846617989 2781168007510789658740873)
                    ·
                      refine ⟨2085876005633092244055655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2781168007510789658740873 2085876005633092244055655)
                      ·
                        rfl

theorem cell23_4062229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_4062229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062229 prefixEnd_4062229 := by exact prefixLift 4062229
  have htrace : WordTrace (prefixWord ++ tailWord_4062229) baseStart_4062229 baseEnd_4062229 := by
    simpa [prefixWord, tailWord_4062229, baseEnd_4062229] using wordTrace_append hprefix tailTrace_4062229
  have hstable : (prefixWord ++ tailWord_4062229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062229).length < 2 ^ (prefixWord ++ tailWord_4062229).sum := by decide
  have hdescent : baseEnd_4062229 < baseStart_4062229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
