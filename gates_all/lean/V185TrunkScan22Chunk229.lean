import V185TrunkScan22Chunk228

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2041613 : List Nat := [1, 7, 2, 1, 2, 1, 1, 1, 6]
def baseStart_2041613 : Nat := 118140960795 + 2041613 * 2 ^ 59
def prefixEnd_2041613 : Nat := 4983230072969 + 3 ^ 40 * 2041613 * 2
def baseEnd_2041613 : Nat := 232961950992850202988511

theorem tailTrace_2041613 : CollatzResearch.WordTrace tailWord_2041613 prefixEnd_2041613 232961950992850202988511 := by
  unfold tailWord_2041613
  simp only [CollatzResearch.WordTrace]
  refine ⟨74463743552592255585697493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49642495701728170390464995 74463743552592255585697493)
  ·
    refine ⟨1745243989513880990289785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 74463743552592255585697493 1745243989513880990289785)
    ·
      refine ⟨1308932992135410742717339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1745243989513880990289785 1308932992135410742717339)
      ·
        refine ⟨1963399488203116114076009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1308932992135410742717339 1963399488203116114076009)
        ·
          refine ⟨1472549616152337085557007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1963399488203116114076009 1472549616152337085557007)
          ·
            refine ⟨2208824424228505628335511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1472549616152337085557007 2208824424228505628335511)
            ·
              refine ⟨3313236636342758442503267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2208824424228505628335511 3313236636342758442503267)
              ·
                refine ⟨4969854954514137663754901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3313236636342758442503267 4969854954514137663754901)
                ·
                  refine ⟨232961950992850202988511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4969854954514137663754901 232961950992850202988511)
                  ·
                    rfl

theorem cell22_2041613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_2041613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041613 prefixEnd_2041613 := by exact prefixLift 2041613
  have htrace : WordTrace (prefixWord ++ tailWord_2041613) baseStart_2041613 baseEnd_2041613 := by
    simpa [prefixWord, tailWord_2041613, baseEnd_2041613] using wordTrace_append hprefix tailTrace_2041613
  have hstable : (prefixWord ++ tailWord_2041613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041613).length < 2 ^ (prefixWord ++ tailWord_2041613).sum := by decide
  have hdescent : baseEnd_2041613 < baseStart_2041613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041635 : List Nat := [1, 1, 1, 4, 2, 1, 6, 1, 5]
def baseStart_2041635 : Nat := 118140960795 + 2041635 * 2 ^ 59
def prefixEnd_2041635 : Nat := 4983230072969 + 3 ^ 40 * 2041635 * 2
def baseEnd_2041635 : Nat := 232964461342716628305155

theorem tailTrace_2041635 : CollatzResearch.WordTrace tailWord_2041635 prefixEnd_2041635 232964461342716628305155 := by
  unfold tailWord_2041635
  simp only [CollatzResearch.WordTrace]
  refine ⟨74464545958512553342998359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49643030639008368895332239 74464545958512553342998359)
  ·
    refine ⟨111696818937768830014497539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74464545958512553342998359 111696818937768830014497539)
    ·
      refine ⟨167545228406653245021746309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111696818937768830014497539 167545228406653245021746309)
      ·
        refine ⟨31414730326247483441577433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167545228406653245021746309 31414730326247483441577433)
        ·
          refine ⟨23561047744685612581183075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31414730326247483441577433 23561047744685612581183075)
          ·
            refine ⟨35341571617028418871774613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23561047744685612581183075 35341571617028418871774613)
            ·
              refine ⟨1656636169548207134614435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35341571617028418871774613 1656636169548207134614435)
              ·
                refine ⟨2484954254322310701921653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656636169548207134614435 2484954254322310701921653)
                ·
                  refine ⟨232964461342716628305155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2484954254322310701921653 232964461342716628305155)
                  ·
                    rfl

theorem cell22_2041635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 5].length) (baseStart_2041635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041635 prefixEnd_2041635 := by exact prefixLift 2041635
  have htrace : WordTrace (prefixWord ++ tailWord_2041635) baseStart_2041635 baseEnd_2041635 := by
    simpa [prefixWord, tailWord_2041635, baseEnd_2041635] using wordTrace_append hprefix tailTrace_2041635
  have hstable : (prefixWord ++ tailWord_2041635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041635).length < 2 ^ (prefixWord ++ tailWord_2041635).sum := by decide
  have hdescent : baseEnd_2041635 < baseStart_2041635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041695 : List Nat := [1, 1, 2, 3, 1, 5, 2, 1, 1, 5]
def baseStart_2041695 : Nat := 118140960795 + 2041695 * 2 ^ 59
def prefixEnd_2041695 : Nat := 4983230072969 + 3 ^ 40 * 2041695 * 2
def baseEnd_2041695 : Nat := 698913923254329728415281

theorem tailTrace_2041695 : CollatzResearch.WordTrace tailWord_2041695 prefixEnd_2041695 698913923254329728415281 := by
  unfold tailWord_2041695
  simp only [CollatzResearch.WordTrace]
  refine ⟨74466734338295183590182539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49644489558863455726788359 74466734338295183590182539)
  ·
    refine ⟨111700101507442775385273809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74466734338295183590182539 111700101507442775385273809)
    ·
      refine ⟨83775076130582081538955357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111700101507442775385273809 83775076130582081538955357)
      ·
        refine ⟨31415653548968280577108259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83775076130582081538955357 31415653548968280577108259)
        ·
          refine ⟨47123480323452420865662389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31415653548968280577108259 47123480323452420865662389)
          ·
            refine ⟨4417826280323664456155849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47123480323452420865662389 4417826280323664456155849)
            ·
              refine ⟨3313369710242748342116887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4417826280323664456155849 3313369710242748342116887)
              ·
                refine ⟨4970054565364122513175331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3313369710242748342116887 4970054565364122513175331)
                ·
                  refine ⟨7455081848046183769762997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4970054565364122513175331 7455081848046183769762997)
                  ·
                    refine ⟨698913923254329728415281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7455081848046183769762997 698913923254329728415281)
                    ·
                      rfl

theorem cell22_2041695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 5].length) (baseStart_2041695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041695 prefixEnd_2041695 := by exact prefixLift 2041695
  have htrace : WordTrace (prefixWord ++ tailWord_2041695) baseStart_2041695 baseEnd_2041695 := by
    simpa [prefixWord, tailWord_2041695, baseEnd_2041695] using wordTrace_append hprefix tailTrace_2041695
  have hstable : (prefixWord ++ tailWord_2041695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041695).length < 2 ^ (prefixWord ++ tailWord_2041695).sum := by decide
  have hdescent : baseEnd_2041695 < baseStart_2041695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041729 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 4, 3]
def baseStart_2041729 : Nat := 118140960795 + 2041729 * 2 ^ 59
def prefixEnd_2041729 : Nat := 4983230072969 + 3 ^ 40 * 2041729 * 2
def baseEnd_2041729 : Nat := 698925562149164973065177

theorem tailTrace_2041729 : CollatzResearch.WordTrace tailWord_2041729 prefixEnd_2041729 698925562149164973065177 := by
  unfold tailWord_2041729
  simp only [CollatzResearch.WordTrace]
  refine ⟨74467974420172007396920241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49645316280114671597946827 74467974420172007396920241)
  ·
    refine ⟨55850980815129005547690181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74467974420172007396920241 55850980815129005547690181)
    ·
      refine ⟨10472058902836688540191909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55850980815129005547690181 10472058902836688540191909)
      ·
        refine ⟨1963511044281879101285983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10472058902836688540191909 1963511044281879101285983)
        ·
          refine ⟨2945266566422818651928975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1963511044281879101285983 2945266566422818651928975)
          ·
            refine ⟨4417899849634227977893463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2945266566422818651928975 4417899849634227977893463)
            ·
              refine ⟨6626849774451341966840195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4417899849634227977893463 6626849774451341966840195)
              ·
                refine ⟨9940274661677012950260293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6626849774451341966840195 9940274661677012950260293)
                ·
                  refine ⟨1863801499064439928173805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9940274661677012950260293 1863801499064439928173805)
                  ·
                    refine ⟨698925562149164973065177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1863801499064439928173805 698925562149164973065177)
                    ·
                      rfl

theorem cell22_2041729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_2041729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041729 prefixEnd_2041729 := by exact prefixLift 2041729
  have htrace : WordTrace (prefixWord ++ tailWord_2041729) baseStart_2041729 baseEnd_2041729 := by
    simpa [prefixWord, tailWord_2041729, baseEnd_2041729] using wordTrace_append hprefix tailTrace_2041729
  have hstable : (prefixWord ++ tailWord_2041729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041729).length < 2 ^ (prefixWord ++ tailWord_2041729).sum := by decide
  have hdescent : baseEnd_2041729 < baseStart_2041729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041746 : List Nat := [3, 2, 3, 2, 1, 2, 3, 1, 2, 3]
def baseStart_2041746 : Nat := 118140960795 + 2041746 * 2 ^ 59
def prefixEnd_2041746 : Nat := 4983230072969 + 3 ^ 40 * 2041746 * 2
def baseEnd_2041746 : Nat := 698931381596582595390125

theorem tailTrace_2041746 : CollatzResearch.WordTrace tailWord_2041746 prefixEnd_2041746 698931381596582595390125 := by
  unfold tailWord_2041746
  simp only [CollatzResearch.WordTrace]
  refine ⟨18617148615277604825072273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49645729640740279533526061 18617148615277604825072273)
  ·
    refine ⟨13962861461458203618804205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18617148615277604825072273 13962861461458203618804205)
    ·
      refine ⟨5236073048046826357051577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13962861461458203618804205 5236073048046826357051577)
      ·
        refine ⟨3927054786035119767788683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5236073048046826357051577 3927054786035119767788683)
        ·
          refine ⟨5890582179052679651683025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3927054786035119767788683 5890582179052679651683025)
          ·
            refine ⟨4417936634289509738762269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5890582179052679651683025 4417936634289509738762269)
            ·
              refine ⟨1656726237858566152035851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4417936634289509738762269 1656726237858566152035851)
              ·
                refine ⟨2485089356787849228053777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656726237858566152035851 2485089356787849228053777)
                ·
                  refine ⟨1863817017590886921040333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2485089356787849228053777 1863817017590886921040333)
                  ·
                    refine ⟨698931381596582595390125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1863817017590886921040333 698931381596582595390125)
                    ·
                      rfl

theorem cell22_2041746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_2041746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041746 prefixEnd_2041746 := by exact prefixLift 2041746
  have htrace : WordTrace (prefixWord ++ tailWord_2041746) baseStart_2041746 baseEnd_2041746 := by
    simpa [prefixWord, tailWord_2041746, baseEnd_2041746] using wordTrace_append hprefix tailTrace_2041746
  have hstable : (prefixWord ++ tailWord_2041746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041746).length < 2 ^ (prefixWord ++ tailWord_2041746).sum := by decide
  have hdescent : baseEnd_2041746 < baseStart_2041746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041757 : List Nat := [1, 4, 2, 1, 2, 2, 2, 2, 3, 3]
def baseStart_2041757 : Nat := 118140960795 + 2041757 * 2 ^ 59
def prefixEnd_2041757 : Nat := 4983230072969 + 3 ^ 40 * 2041757 * 2
def baseEnd_2041757 : Nat := 698935147121382233365091

theorem tailTrace_2041757 : CollatzResearch.WordTrace tailWord_2041757 prefixEnd_2041757 698935147121382233365091 := by
  unfold tailWord_2041757
  simp only [CollatzResearch.WordTrace]
  refine ⟨74468995664070568178939525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49645997109380378785959683 74468995664070568178939525)
  ·
    refine ⟨13962936687013231533551161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74468995664070568178939525 13962936687013231533551161)
    ·
      refine ⟨10472202515259923650163371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13962936687013231533551161 10472202515259923650163371)
      ·
        refine ⟨15708303772889885475245057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10472202515259923650163371 15708303772889885475245057)
        ·
          refine ⟨11781227829667414106433793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15708303772889885475245057 11781227829667414106433793)
          ·
            refine ⟨8835920872250560579825345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11781227829667414106433793 8835920872250560579825345)
            ·
              refine ⟨6626940654187920434869009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8835920872250560579825345 6626940654187920434869009)
              ·
                refine ⟨4970205490640940326151757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6626940654187920434869009 4970205490640940326151757)
                ·
                  refine ⟨1863827058990352622306909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4970205490640940326151757 1863827058990352622306909)
                  ·
                    refine ⟨698935147121382233365091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1863827058990352622306909 698935147121382233365091)
                    ·
                      rfl

theorem cell22_2041757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_2041757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041757 prefixEnd_2041757 := by exact prefixLift 2041757
  have htrace : WordTrace (prefixWord ++ tailWord_2041757) baseStart_2041757 baseEnd_2041757 := by
    simpa [prefixWord, tailWord_2041757, baseEnd_2041757] using wordTrace_append hprefix tailTrace_2041757
  have hstable : (prefixWord ++ tailWord_2041757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041757).length < 2 ^ (prefixWord ++ tailWord_2041757).sum := by decide
  have hdescent : baseEnd_2041757 < baseStart_2041757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041759 : List Nat := [1, 1, 2, 5, 4, 1, 2, 6]
def baseStart_2041759 : Nat := 118140960795 + 2041759 * 2 ^ 59
def prefixEnd_2041759 : Nat := 4983230072969 + 3 ^ 40 * 2041759 * 2
def baseEnd_2041759 : Nat := 77659536862472766090565

theorem tailTrace_2041759 : CollatzResearch.WordTrace tailWord_2041759 prefixEnd_2041759 77659536862472766090565 := by
  unfold tailWord_2041759
  simp only [CollatzResearch.WordTrace]
  refine ⟨74469068610063322520512331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49646045740042215013674887 74469068610063322520512331)
  ·
    refine ⟨111703602915094983780768497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74469068610063322520512331 111703602915094983780768497)
    ·
      refine ⟨83777702186321237835576373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111703602915094983780768497 83777702186321237835576373)
      ·
        refine ⟨7854159579967616047085285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83777702186321237835576373 7854159579967616047085285)
        ·
          refine ⟨1472654921243928008828491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7854159579967616047085285 1472654921243928008828491)
          ·
            refine ⟨2208982381865892013242737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1472654921243928008828491 2208982381865892013242737)
            ·
              refine ⟨1656736786399419009932053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2208982381865892013242737 1656736786399419009932053)
              ·
                refine ⟨77659536862472766090565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1656736786399419009932053 77659536862472766090565)
                ·
                  rfl

theorem cell22_2041759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 6].length) (baseStart_2041759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041759 prefixEnd_2041759 := by exact prefixLift 2041759
  have htrace : WordTrace (prefixWord ++ tailWord_2041759) baseStart_2041759 baseEnd_2041759 := by
    simpa [prefixWord, tailWord_2041759, baseEnd_2041759] using wordTrace_append hprefix tailTrace_2041759
  have hstable : (prefixWord ++ tailWord_2041759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041759).length < 2 ^ (prefixWord ++ tailWord_2041759).sum := by decide
  have hdescent : baseEnd_2041759 < baseStart_2041759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041804 : List Nat := [2, 2, 1, 4, 1, 4, 2, 1, 5]
def baseStart_2041804 : Nat := 118140960795 + 2041804 * 2 ^ 59
def prefixEnd_2041804 : Nat := 4983230072969 + 3 ^ 40 * 2041804 * 2
def baseEnd_2041804 : Nat := 232983745393963259146649

theorem tailTrace_2041804 : CollatzResearch.WordTrace tailWord_2041804 prefixEnd_2041804 232983745393963259146649 := by
  unfold tailWord_2041804
  simp only [CollatzResearch.WordTrace]
  refine ⟨37235354947450147602950233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49647139929933530137266977 37235354947450147602950233)
  ·
    refine ⟨27926516210587610702212675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37235354947450147602950233 27926516210587610702212675)
    ·
      refine ⟨41889774315881416053319013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27926516210587610702212675 41889774315881416053319013)
      ·
        refine ⟨7854332684227765509997315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41889774315881416053319013 7854332684227765509997315)
        ·
          refine ⟨11781499026341648264995973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7854332684227765509997315 11781499026341648264995973)
          ·
            refine ⟨2209031067439059049686745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11781499026341648264995973 2209031067439059049686745)
            ·
              refine ⟨1656773300579294287265059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2209031067439059049686745 1656773300579294287265059)
              ·
                refine ⟨2485159950868941430897589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656773300579294287265059 2485159950868941430897589)
                ·
                  refine ⟨232983745393963259146649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2485159950868941430897589 232983745393963259146649)
                  ·
                    rfl

theorem cell22_2041804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 5].length) (baseStart_2041804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041804 prefixEnd_2041804 := by exact prefixLift 2041804
  have htrace : WordTrace (prefixWord ++ tailWord_2041804) baseStart_2041804 baseEnd_2041804 := by
    simpa [prefixWord, tailWord_2041804, baseEnd_2041804] using wordTrace_append hprefix tailTrace_2041804
  have hstable : (prefixWord ++ tailWord_2041804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041804).length < 2 ^ (prefixWord ++ tailWord_2041804).sum := by decide
  have hdescent : baseEnd_2041804 < baseStart_2041804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041817 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 3, 4]
def baseStart_2041817 : Nat := 118140960795 + 2041817 * 2 ^ 59
def prefixEnd_2041817 : Nat := 4983230072969 + 3 ^ 40 * 2041817 * 2
def baseEnd_2041817 : Nat := 698955686347562076864907

theorem tailTrace_2041817 : CollatzResearch.WordTrace tailWord_2041817 prefixEnd_2041817 698955686347562076864907 := by
  unfold tailWord_2041817
  simp only [CollatzResearch.WordTrace]
  refine ⟨74471184043853198426123705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49647456029235465617415803 74471184043853198426123705)
  ·
    refine ⟨55853388032889898819592779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74471184043853198426123705 55853388032889898819592779)
    ·
      refine ⟨83780082049334848229389169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55853388032889898819592779 83780082049334848229389169)
      ·
        refine ⟨62835061537001136172041877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83780082049334848229389169 62835061537001136172041877)
        ·
          refine ⟨2945393509546928258064463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62835061537001136172041877 2945393509546928258064463)
          ·
            refine ⟨4418090264320392387096695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2945393509546928258064463 4418090264320392387096695)
            ·
              refine ⟨6627135396480588580645043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4418090264320392387096695 6627135396480588580645043)
              ·
                refine ⟨9940703094720882870967565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6627135396480588580645043 9940703094720882870967565)
                ·
                  refine ⟨3727763660520331076612837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9940703094720882870967565 3727763660520331076612837)
                  ·
                    refine ⟨698955686347562076864907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3727763660520331076612837 698955686347562076864907)
                    ·
                      rfl

theorem cell22_2041817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 4].length) (baseStart_2041817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041817 prefixEnd_2041817 := by exact prefixLift 2041817
  have htrace : WordTrace (prefixWord ++ tailWord_2041817) baseStart_2041817 baseEnd_2041817 := by
    simpa [prefixWord, tailWord_2041817, baseEnd_2041817] using wordTrace_append hprefix tailTrace_2041817
  have hstable : (prefixWord ++ tailWord_2041817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041817).length < 2 ^ (prefixWord ++ tailWord_2041817).sum := by decide
  have hdescent : baseEnd_2041817 < baseStart_2041817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041832 : List Nat := [2, 1, 4, 1, 1, 1, 1, 7, 4]
def baseStart_2041832 : Nat := 118140960795 + 2041832 * 2 ^ 59
def prefixEnd_2041832 : Nat := 4983230072969 + 3 ^ 40 * 2041832 * 2
def baseEnd_2041832 : Nat := 232986940384702345913287

theorem tailTrace_2041832 : CollatzResearch.WordTrace tailWord_2041832 prefixEnd_2041832 232986940384702345913287 := by
  unfold tailWord_2041832
  simp only [CollatzResearch.WordTrace]
  refine ⟨37235865569399427993959875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49647820759199237325279833 37235865569399427993959875)
  ·
    refine ⟨55853798354099141990939813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37235865569399427993959875 55853798354099141990939813)
    ·
      refine ⟨10472587191393589123301215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55853798354099141990939813 10472587191393589123301215)
      ·
        refine ⟨15708880787090383684951823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10472587191393589123301215 15708880787090383684951823)
        ·
          refine ⟨23563321180635575527427735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15708880787090383684951823 23563321180635575527427735)
          ·
            refine ⟨35344981770953363291141603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23563321180635575527427735 35344981770953363291141603)
            ·
              refine ⟨53017472656430044936712405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35344981770953363291141603 53017472656430044936712405)
              ·
                refine ⟨1242597015385079178204197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53017472656430044936712405 1242597015385079178204197)
                ·
                  refine ⟨232986940384702345913287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1242597015385079178204197 232986940384702345913287)
                  ·
                    rfl

theorem cell22_2041832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 4].length) (baseStart_2041832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041832 prefixEnd_2041832 := by exact prefixLift 2041832
  have htrace : WordTrace (prefixWord ++ tailWord_2041832) baseStart_2041832 baseEnd_2041832 := by
    simpa [prefixWord, tailWord_2041832, baseEnd_2041832] using wordTrace_append hprefix tailTrace_2041832
  have hstable : (prefixWord ++ tailWord_2041832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041832).length < 2 ^ (prefixWord ++ tailWord_2041832).sum := by decide
  have hdescent : baseEnd_2041832 < baseStart_2041832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041834 : List Nat := [3, 1, 3, 1, 2, 1, 5, 1, 1, 4]
def baseStart_2041834 : Nat := 118140960795 + 2041834 * 2 ^ 59
def prefixEnd_2041834 : Nat := 4983230072969 + 3 ^ 40 * 2041834 * 2
def baseEnd_2041834 : Nat := 698961505794979699189855

theorem tailTrace_2041834 : CollatzResearch.WordTrace tailWord_2041834 prefixEnd_2041834 698961505794979699189855 := by
  unfold tailWord_2041834
  simp only [CollatzResearch.WordTrace]
  refine ⟨18617951021197902582373139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49647869389861073552995037 18617951021197902582373139)
  ·
    refine ⟨27926926531796853873559709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18617951021197902582373139 27926926531796853873559709)
    ·
      refine ⟨10472597449423820202584891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27926926531796853873559709 10472597449423820202584891)
      ·
        refine ⟨15708896174135730303877337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10472597449423820202584891 15708896174135730303877337)
        ·
          refine ⟨11781672130601797727908003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15708896174135730303877337 11781672130601797727908003)
          ·
            refine ⟨17672508195902696591862005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11781672130601797727908003 17672508195902696591862005)
            ·
              refine ⟨1656797643365877805487063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17672508195902696591862005 1656797643365877805487063)
              ·
                refine ⟨2485196465048816708230595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656797643365877805487063 2485196465048816708230595)
                ·
                  refine ⟨3727794697573225062345893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2485196465048816708230595 3727794697573225062345893)
                  ·
                    refine ⟨698961505794979699189855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3727794697573225062345893 698961505794979699189855)
                    ·
                      rfl

theorem cell22_2041834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_2041834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041834 prefixEnd_2041834 := by exact prefixLift 2041834
  have htrace : WordTrace (prefixWord ++ tailWord_2041834) baseStart_2041834 baseEnd_2041834 := by
    simpa [prefixWord, tailWord_2041834, baseEnd_2041834] using wordTrace_append hprefix tailTrace_2041834
  have hstable : (prefixWord ++ tailWord_2041834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041834).length < 2 ^ (prefixWord ++ tailWord_2041834).sum := by decide
  have hdescent : baseEnd_2041834 < baseStart_2041834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041849 : List Nat := [1, 2, 1, 3, 1, 4, 4, 2, 4]
def baseStart_2041849 : Nat := 118140960795 + 2041849 * 2 ^ 59
def prefixEnd_2041849 : Nat := 4983230072969 + 3 ^ 40 * 2041849 * 2
def baseEnd_2041849 : Nat := 232988880200508220021603

theorem tailTrace_2041849 : CollatzResearch.WordTrace tailWord_2041849 prefixEnd_2041849 232988880200508220021603 := by
  unfold tailWord_2041849
  simp only [CollatzResearch.WordTrace]
  refine ⟨74472351179737267891288601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49648234119824845260859067 74472351179737267891288601)
  ·
    refine ⟨55854263384802950918466451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74472351179737267891288601 55854263384802950918466451)
    ·
      refine ⟨83781395077204426377699677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55854263384802950918466451 83781395077204426377699677)
      ·
        refine ⟨31418023153951659891637379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83781395077204426377699677 31418023153951659891637379)
        ·
          refine ⟨47127034730927489837456069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31418023153951659891637379 47127034730927489837456069)
          ·
            refine ⟨8836319012048904344523013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47127034730927489837456069 8836319012048904344523013)
            ·
              refine ⟨1656809814759169564598065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8836319012048904344523013 1656809814759169564598065)
              ·
                refine ⟨1242607361069377173448549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1656809814759169564598065 1242607361069377173448549)
                ·
                  refine ⟨232988880200508220021603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1242607361069377173448549 232988880200508220021603)
                  ·
                    rfl

theorem cell22_2041849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 4].length) (baseStart_2041849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041849 prefixEnd_2041849 := by exact prefixLift 2041849
  have htrace : WordTrace (prefixWord ++ tailWord_2041849) baseStart_2041849 baseEnd_2041849 := by
    simpa [prefixWord, tailWord_2041849, baseEnd_2041849] using wordTrace_append hprefix tailTrace_2041849
  have hstable : (prefixWord ++ tailWord_2041849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041849).length < 2 ^ (prefixWord ++ tailWord_2041849).sum := by decide
  have hdescent : baseEnd_2041849 < baseStart_2041849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041926 : List Nat := [6, 1, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_2041926 : Nat := 118140960795 + 2041926 * 2 ^ 59
def prefixEnd_2041926 : Nat := 4983230072969 + 3 ^ 40 * 2041926 * 2
def baseEnd_2041926 : Nat := 698992999275122125889573

theorem tailTrace_2041926 : CollatzResearch.WordTrace tailWord_2041926 prefixEnd_2041926 698992999275122125889573 := by
  unfold tailWord_2041926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2327348737514322188807551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49650106400305540027894421 2327348737514322188807551)
  ·
    refine ⟨3491023106271483283211327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2327348737514322188807551 3491023106271483283211327)
    ·
      refine ⟨5236534659407224924816991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3491023106271483283211327 5236534659407224924816991)
      ·
        refine ⟨7854801989110837387225487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5236534659407224924816991 7854801989110837387225487)
        ·
          refine ⟨11782202983666256080838231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7854801989110837387225487 11782202983666256080838231)
          ·
            refine ⟨17673304475499384121257347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11782202983666256080838231 17673304475499384121257347)
            ·
              refine ⟨26509956713249076181886021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17673304475499384121257347 26509956713249076181886021)
              ·
                refine ⟨4970616883734201784103629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26509956713249076181886021 4970616883734201784103629)
                ·
                  refine ⟨1863981331400325669038861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4970616883734201784103629 1863981331400325669038861)
                  ·
                    refine ⟨698992999275122125889573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1863981331400325669038861 698992999275122125889573)
                    ·
                      rfl

theorem cell22_2041926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_2041926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041926 prefixEnd_2041926 := by exact prefixLift 2041926
  have htrace : WordTrace (prefixWord ++ tailWord_2041926) baseStart_2041926 baseEnd_2041926 := by
    simpa [prefixWord, tailWord_2041926, baseEnd_2041926] using wordTrace_append hprefix tailTrace_2041926
  have hstable : (prefixWord ++ tailWord_2041926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041926).length < 2 ^ (prefixWord ++ tailWord_2041926).sum := by decide
  have hdescent : baseEnd_2041926 < baseStart_2041926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041967 : List Nat := [1, 1, 2, 1, 3, 4, 3, 1, 6]
def baseStart_2041967 : Nat := 118140960795 + 2041967 * 2 ^ 59
def prefixEnd_2041967 : Nat := 4983230072969 + 3 ^ 40 * 2041967 * 2
def baseEnd_2041967 : Nat := 233002344804337228538149

theorem tailTrace_2041967 : CollatzResearch.WordTrace tailWord_2041967 prefixEnd_2041967 233002344804337228538149 := by
  unfold tailWord_2041967
  simp only [CollatzResearch.WordTrace]
  refine ⟨74476654993309774044084155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49651103328873182696056103 74476654993309774044084155)
  ·
    refine ⟨111714982489964661066126233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74476654993309774044084155 111714982489964661066126233)
    ·
      refine ⟨83786236867473495799594675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111714982489964661066126233 83786236867473495799594675)
      ·
        refine ⟨125679355301210243699392013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83786236867473495799594675 125679355301210243699392013)
        ·
          refine ⟨47129758237953841387272005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125679355301210243699392013 47129758237953841387272005)
          ·
            refine ⟨8836829669616345260113501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47129758237953841387272005 8836829669616345260113501)
            ·
              refine ⟨3313811126106129472542563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8836829669616345260113501 3313811126106129472542563)
              ·
                refine ⟨4970716689159194208813845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3313811126106129472542563 4970716689159194208813845)
                ·
                  refine ⟨233002344804337228538149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4970716689159194208813845 233002344804337228538149)
                  ·
                    rfl

theorem cell22_2041967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 6].length) (baseStart_2041967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2041967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2041967 prefixEnd_2041967 := by exact prefixLift 2041967
  have htrace : WordTrace (prefixWord ++ tailWord_2041967) baseStart_2041967 baseEnd_2041967 := by
    simpa [prefixWord, tailWord_2041967, baseEnd_2041967] using wordTrace_append hprefix tailTrace_2041967
  have hstable : (prefixWord ++ tailWord_2041967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041967).length < 2 ^ (prefixWord ++ tailWord_2041967).sum := by decide
  have hdescent : baseEnd_2041967 < baseStart_2041967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042016 : List Nat := [2, 1, 1, 4, 2, 3, 2, 2, 2, 3]
def baseStart_2042016 : Nat := 118140960795 + 2042016 * 2 ^ 59
def prefixEnd_2042016 : Nat := 4983230072969 + 3 ^ 40 * 2042016 * 2
def baseEnd_2042016 : Nat := 699023808114391891139297

theorem tailTrace_2042016 : CollatzResearch.WordTrace tailWord_2042016 prefixEnd_2042016 699023808114391891139297 := by
  unfold tailWord_2042016
  simp only [CollatzResearch.WordTrace]
  refine ⟨37239221085066127706308951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49652294780088170275078601 37239221085066127706308951)
  ·
    refine ⟨55858831627599191559463427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37239221085066127706308951 55858831627599191559463427)
    ·
      refine ⟨83788247441398787339195141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55858831627599191559463427 83788247441398787339195141)
      ·
        refine ⟨15710296395262272626099089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83788247441398787339195141 15710296395262272626099089)
        ·
          refine ⟨11782722296446704469574317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15710296395262272626099089 11782722296446704469574317)
          ·
            refine ⟨4418520861167514176090369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11782722296446704469574317 4418520861167514176090369)
            ·
              refine ⟨3313890645875635632067777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4418520861167514176090369 3313890645875635632067777)
              ·
                refine ⟨2485417984406726724050833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3313890645875635632067777 2485417984406726724050833)
                ·
                  refine ⟨1864063488305045043038125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2485417984406726724050833 1864063488305045043038125)
                  ·
                    refine ⟨699023808114391891139297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1864063488305045043038125 699023808114391891139297)
                    ·
                      rfl

theorem cell22_2042016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 2, 3].length) (baseStart_2042016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042016 prefixEnd_2042016 := by exact prefixLift 2042016
  have htrace : WordTrace (prefixWord ++ tailWord_2042016) baseStart_2042016 baseEnd_2042016 := by
    simpa [prefixWord, tailWord_2042016, baseEnd_2042016] using wordTrace_append hprefix tailTrace_2042016
  have hstable : (prefixWord ++ tailWord_2042016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042016).length < 2 ^ (prefixWord ++ tailWord_2042016).sum := by decide
  have hdescent : baseEnd_2042016 < baseStart_2042016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042018 : List Nat := [3, 3, 1, 3, 1, 1, 4, 2, 4]
def baseStart_2042018 : Nat := 118140960795 + 2042018 * 2 ^ 59
def prefixEnd_2042018 : Nat := 4983230072969 + 3 ^ 40 * 2042018 * 2
def baseEnd_2042018 : Nat := 233008164251754850863097

theorem tailTrace_2042018 : CollatzResearch.WordTrace tailWord_2042018 prefixEnd_2042018 233008164251754850863097 := by
  unfold tailWord_2042018
  simp only [CollatzResearch.WordTrace]
  refine ⟨18619628779031252438547677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49652343410750006502793805 18619628779031252438547677)
  ·
    refine ⟨6982360792136719664455379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18619628779031252438547677 6982360792136719664455379)
    ·
      refine ⟨10473541188205079496683069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6982360792136719664455379 10473541188205079496683069)
      ·
        refine ⟨3927577945576904811256151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10473541188205079496683069 3927577945576904811256151)
        ·
          refine ⟨5891366918365357216884227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3927577945576904811256151 5891366918365357216884227)
          ·
            refine ⟨8837050377548035825326341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5891366918365357216884227 8837050377548035825326341)
            ·
              refine ⟨1656946945790256717248689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8837050377548035825326341 1656946945790256717248689)
              ·
                refine ⟨1242710209342692537936517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1656946945790256717248689 1242710209342692537936517)
                ·
                  refine ⟨233008164251754850863097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1242710209342692537936517 233008164251754850863097)
                  ·
                    rfl

theorem cell22_2042018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_2042018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042018 prefixEnd_2042018 := by exact prefixLift 2042018
  have htrace : WordTrace (prefixWord ++ tailWord_2042018) baseStart_2042018 baseEnd_2042018 := by
    simpa [prefixWord, tailWord_2042018, baseEnd_2042018] using wordTrace_append hprefix tailTrace_2042018
  have hstable : (prefixWord ++ tailWord_2042018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042018).length < 2 ^ (prefixWord ++ tailWord_2042018).sum := by decide
  have hdescent : baseEnd_2042018 < baseStart_2042018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042029 : List Nat := [1, 5, 2, 1, 2, 1, 3, 7]
def baseStart_2042029 : Nat := 118140960795 + 2042029 * 2 ^ 59
def prefixEnd_2042029 : Nat := 4983230072969 + 3 ^ 40 * 2042029 * 2
def baseEnd_2042029 : Nat := 77669806475562687840473

theorem tailTrace_2042029 : CollatzResearch.WordTrace tailWord_2042029 prefixEnd_2042029 77669806475562687840473 := by
  unfold tailWord_2042029
  simp only [CollatzResearch.WordTrace]
  refine ⟨74478916319085158632841141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49652610879390105755227427 74478916319085158632841141)
  ·
    refine ⟨6982398404914233621828857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74478916319085158632841141 6982398404914233621828857)
    ·
      refine ⟨5236798803685675216371643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6982398404914233621828857 5236798803685675216371643)
      ·
        refine ⟨7855198205528512824557465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5236798803685675216371643 7855198205528512824557465)
        ·
          refine ⟨5891398654146384618418099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7855198205528512824557465 5891398654146384618418099)
          ·
            refine ⟨8837097981219576927627149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5891398654146384618418099 8837097981219576927627149)
            ·
              refine ⟨3313911742957341347860181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8837097981219576927627149 3313911742957341347860181)
              ·
                refine ⟨77669806475562687840473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3313911742957341347860181 77669806475562687840473)
                ·
                  rfl

theorem cell22_2042029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 7].length) (baseStart_2042029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042029 prefixEnd_2042029 := by exact prefixLift 2042029
  have htrace : WordTrace (prefixWord ++ tailWord_2042029) baseStart_2042029 baseEnd_2042029 := by
    simpa [prefixWord, tailWord_2042029, baseEnd_2042029] using wordTrace_append hprefix tailTrace_2042029
  have hstable : (prefixWord ++ tailWord_2042029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042029).length < 2 ^ (prefixWord ++ tailWord_2042029).sum := by decide
  have hdescent : baseEnd_2042029 < baseStart_2042029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042046 : List Nat := [4, 2, 1, 1, 4, 1, 3, 6]
def baseStart_2042046 : Nat := 118140960795 + 2042046 * 2 ^ 59
def prefixEnd_2042046 : Nat := 4983230072969 + 3 ^ 40 * 2042046 * 2
def baseEnd_2042046 : Nat := 77670453080831312543245

theorem tailTrace_2042046 : CollatzResearch.WordTrace tailWord_2042046 prefixEnd_2042046 77670453080831312543245 := by
  unfold tailWord_2042046
  simp only [CollatzResearch.WordTrace]
  refine ⟨9309942045002946317026249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49653024240015713690806661 9309942045002946317026249)
  ·
    refine ⟨6982456533752209737769687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9309942045002946317026249 6982456533752209737769687)
    ·
      refine ⟨10473684800628314606654531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6982456533752209737769687 10473684800628314606654531)
      ·
        refine ⟨15710527200942471909981797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10473684800628314606654531 15710527200942471909981797)
        ·
          refine ⟨2945723850176713483121587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15710527200942471909981797 2945723850176713483121587)
          ·
            refine ⟨4418585775265070224682381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2945723850176713483121587 4418585775265070224682381)
            ·
              refine ⟨1656969665724401334255893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4418585775265070224682381 1656969665724401334255893)
              ·
                refine ⟨77670453080831312543245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1656969665724401334255893 77670453080831312543245)
                ·
                  rfl

theorem cell22_2042046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_2042046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042046 prefixEnd_2042046 := by exact prefixLift 2042046
  have htrace : WordTrace (prefixWord ++ tailWord_2042046) baseStart_2042046 baseEnd_2042046 := by
    simpa [prefixWord, tailWord_2042046, baseEnd_2042046] using wordTrace_append hprefix tailTrace_2042046
  have hstable : (prefixWord ++ tailWord_2042046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042046).length < 2 ^ (prefixWord ++ tailWord_2042046).sum := by decide
  have hdescent : baseEnd_2042046 < baseStart_2042046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042074 : List Nat := [3, 1, 1, 2, 2, 1, 5, 2, 5]
def baseStart_2042074 : Nat := 118140960795 + 2042074 * 2 ^ 59
def prefixEnd_2042074 : Nat := 4983230072969 + 3 ^ 40 * 2042074 * 2
def baseEnd_2042074 : Nat := 233014554233233024396373

theorem tailTrace_2042074 : CollatzResearch.WordTrace tailWord_2042074 prefixEnd_2042074 233014554233233024396373 := by
  unfold tailWord_2042074
  simp only [CollatzResearch.WordTrace]
  refine ⟨18620139400980532829557319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49653705069281420878819517 18620139400980532829557319)
  ·
    refine ⟨27930209101470799244335979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18620139400980532829557319 27930209101470799244335979)
    ·
      refine ⟨41895313652206198866503969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27930209101470799244335979 41895313652206198866503969)
      ·
        refine ⟨31421485239154649149877977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41895313652206198866503969 31421485239154649149877977)
        ·
          refine ⟨23566113929365986862408483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31421485239154649149877977 23566113929365986862408483)
          ·
            refine ⟨35349170894048980293612725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23566113929365986862408483 35349170894048980293612725)
            ·
              refine ⟨3313984771317091902526193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35349170894048980293612725 3313984771317091902526193)
              ·
                refine ⟨2485488578487818926894645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3313984771317091902526193 2485488578487818926894645)
                ·
                  refine ⟨233014554233233024396373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2485488578487818926894645 233014554233233024396373)
                  ·
                    rfl

theorem cell22_2042074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_2042074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042074 prefixEnd_2042074 := by exact prefixLift 2042074
  have htrace : WordTrace (prefixWord ++ tailWord_2042074) baseStart_2042074 baseEnd_2042074 := by
    simpa [prefixWord, tailWord_2042074, baseEnd_2042074] using wordTrace_append hprefix tailTrace_2042074
  have hstable : (prefixWord ++ tailWord_2042074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042074).length < 2 ^ (prefixWord ++ tailWord_2042074).sum := by decide
  have hdescent : baseEnd_2042074 < baseStart_2042074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042194 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_2042194 : Nat := 118140960795 + 2042194 * 2 ^ 59
def prefixEnd_2042194 : Nat := 4983230072969 + 3 ^ 40 * 2042194 * 2
def baseEnd_2042194 : Nat := 699084741152058760188751

theorem tailTrace_2042194 : CollatzResearch.WordTrace tailWord_2042194 prefixEnd_2042194 699084741152058760188751 := by
  unfold tailWord_2042194
  simp only [CollatzResearch.WordTrace]
  refine ⟨18621233590871847953149409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49656622908991594541731757 18621233590871847953149409)
  ·
    refine ⟨13965925193153885964862057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18621233590871847953149409 13965925193153885964862057)
    ·
      refine ⟨10474443894865414473646543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13965925193153885964862057 10474443894865414473646543)
      ·
        refine ⟨15711665842298121710469815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10474443894865414473646543 15711665842298121710469815)
        ·
          refine ⟨23567498763447182565704723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15711665842298121710469815 23567498763447182565704723)
          ·
            refine ⟨35351248145170773848557085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23567498763447182565704723 35351248145170773848557085)
            ·
              refine ⟨13256718054439040193208907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35351248145170773848557085 13256718054439040193208907)
              ·
                refine ⟨19885077081658560289813361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13256718054439040193208907 19885077081658560289813361)
                ·
                  refine ⟨14913807811243920217360021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19885077081658560289813361 14913807811243920217360021)
                  ·
                    refine ⟨699084741152058760188751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14913807811243920217360021 699084741152058760188751)
                    ·
                      rfl

theorem cell22_2042194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_2042194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042194 prefixEnd_2042194 := by exact prefixLift 2042194
  have htrace : WordTrace (prefixWord ++ tailWord_2042194) baseStart_2042194 baseEnd_2042194 := by
    simpa [prefixWord, tailWord_2042194, baseEnd_2042194] using wordTrace_append hprefix tailTrace_2042194
  have hstable : (prefixWord ++ tailWord_2042194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042194).length < 2 ^ (prefixWord ++ tailWord_2042194).sum := by decide
  have hdescent : baseEnd_2042194 < baseStart_2042194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042241 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 2, 5]
def baseStart_2042241 : Nat := 118140960795 + 2042241 * 2 ^ 59
def prefixEnd_2042241 : Nat := 4983230072969 + 3 ^ 40 * 2042241 * 2
def baseEnd_2042241 : Nat := 699100830212566304263607

theorem tailTrace_2042241 : CollatzResearch.WordTrace tailWord_2042241 prefixEnd_2042241 699100830212566304263607 := by
  unfold tailWord_2042241
  simp only [CollatzResearch.WordTrace]
  refine ⟨74486648594317118839558577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49657765729544745893039051 74486648594317118839558577)
  ·
    refine ⟨55864986445737839129668933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74486648594317118839558577 55864986445737839129668933)
    ·
      refine ⟨10474684958575844836812925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55864986445737839129668933 10474684958575844836812925)
      ·
        refine ⟨3928006859465941813804847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10474684958575844836812925 3928006859465941813804847)
        ·
          refine ⟨5892010289198912720707271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3928006859465941813804847 5892010289198912720707271)
          ·
            refine ⟨8838015433798369081060907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5892010289198912720707271 8838015433798369081060907)
            ·
              refine ⟨13257023150697553621591361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8838015433798369081060907 13257023150697553621591361)
              ·
                refine ⟨9942767363023165216193521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13257023150697553621591361 9942767363023165216193521)
                ·
                  refine ⟨7457075522267373912145141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9942767363023165216193521 7457075522267373912145141)
                  ·
                    refine ⟨699100830212566304263607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7457075522267373912145141 699100830212566304263607)
                    ·
                      rfl

theorem cell22_2042241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_2042241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042241 prefixEnd_2042241 := by exact prefixLift 2042241
  have htrace : WordTrace (prefixWord ++ tailWord_2042241) baseStart_2042241 baseEnd_2042241 := by
    simpa [prefixWord, tailWord_2042241, baseEnd_2042241] using wordTrace_append hprefix tailTrace_2042241
  have hstable : (prefixWord ++ tailWord_2042241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042241).length < 2 ^ (prefixWord ++ tailWord_2042241).sum := by decide
  have hdescent : baseEnd_2042241 < baseStart_2042241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042243 : List Nat := [1, 1, 1, 3, 6, 2, 1, 2, 5]
def baseStart_2042243 : Nat := 118140960795 + 2042243 * 2 ^ 59
def prefixEnd_2042243 : Nat := 4983230072969 + 3 ^ 40 * 2042243 * 2
def baseEnd_2042243 : Nat := 233033838284479655237867

theorem tailTrace_2042243 : CollatzResearch.WordTrace tailWord_2042243 prefixEnd_2042243 233033838284479655237867 := by
  unfold tailWord_2042243
  simp only [CollatzResearch.WordTrace]
  refine ⟨74486721540309873181131383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49657814360206582120754255 74486721540309873181131383)
  ·
    refine ⟨111730082310464809771697075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74486721540309873181131383 111730082310464809771697075)
    ·
      refine ⟨167595123465697214657545613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111730082310464809771697075 167595123465697214657545613)
      ·
        refine ⟨62848171299636455496579605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167595123465697214657545613 62848171299636455496579605)
        ·
          refine ⟨2946008029670458851402169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62848171299636455496579605 2946008029670458851402169)
          ·
            refine ⟨2209506022252844138551627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2946008029670458851402169 2209506022252844138551627)
            ·
              refine ⟨3314259033379266207827441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2209506022252844138551627 3314259033379266207827441)
              ·
                refine ⟨2485694275034449655870581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3314259033379266207827441 2485694275034449655870581)
                ·
                  refine ⟨233033838284479655237867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2485694275034449655870581 233033838284479655237867)
                  ·
                    rfl

theorem cell22_2042243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 5].length) (baseStart_2042243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042243 prefixEnd_2042243 := by exact prefixLift 2042243
  have htrace : WordTrace (prefixWord ++ tailWord_2042243) baseStart_2042243 baseEnd_2042243 := by
    simpa [prefixWord, tailWord_2042243, baseEnd_2042243] using wordTrace_append hprefix tailTrace_2042243
  have hstable : (prefixWord ++ tailWord_2042243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042243).length < 2 ^ (prefixWord ++ tailWord_2042243).sum := by decide
  have hdescent : baseEnd_2042243 < baseStart_2042243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042260 : List Nat := [2, 4, 2, 1, 3, 1, 3, 1, 5]
def baseStart_2042260 : Nat := 118140960795 + 2042260 * 2 ^ 59
def prefixEnd_2042260 : Nat := 4983230072969 + 3 ^ 40 * 2042260 * 2
def baseEnd_2042260 : Nat := 233035778100285529346183

theorem tailTrace_2042260 : CollatzResearch.WordTrace tailWord_2042260 prefixEnd_2042260 233035778100285529346183 := by
  unfold tailWord_2042260
  simp only [CollatzResearch.WordTrace]
  refine ⟨37243670790624142542250117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49658227720832190056333489 37243670790624142542250117)
  ·
    refine ⟨6983188273242026726671897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37243670790624142542250117 6983188273242026726671897)
    ·
      refine ⟨5237391204931520045003923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6983188273242026726671897 5237391204931520045003923)
      ·
        refine ⟨7856086807397280067505885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5237391204931520045003923 7856086807397280067505885)
        ·
          refine ⟨2946032552773980025314707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7856086807397280067505885 2946032552773980025314707)
          ·
            refine ⟨4419048829160970037972061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2946032552773980025314707 4419048829160970037972061)
            ·
              refine ⟨1657143310935363764239523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4419048829160970037972061 1657143310935363764239523)
              ·
                refine ⟨2485714966403045646359285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1657143310935363764239523 2485714966403045646359285)
                ·
                  refine ⟨233035778100285529346183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2485714966403045646359285 233035778100285529346183)
                  ·
                    rfl

theorem cell22_2042260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_2042260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042260 prefixEnd_2042260 := by exact prefixLift 2042260
  have htrace : WordTrace (prefixWord ++ tailWord_2042260) baseStart_2042260 baseEnd_2042260 := by
    simpa [prefixWord, tailWord_2042260, baseEnd_2042260] using wordTrace_append hprefix tailTrace_2042260
  have hstable : (prefixWord ++ tailWord_2042260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042260).length < 2 ^ (prefixWord ++ tailWord_2042260).sum := by decide
  have hdescent : baseEnd_2042260 < baseStart_2042260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042301 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 4, 4]
def baseStart_2042301 : Nat := 118140960795 + 2042301 * 2 ^ 59
def prefixEnd_2042301 : Nat := 4983230072969 + 3 ^ 40 * 2042301 * 2
def baseEnd_2042301 : Nat := 699121369438746147763423

theorem tailTrace_2042301 : CollatzResearch.WordTrace tailWord_2042301 prefixEnd_2042301 699121369438746147763423 := by
  unfold tailWord_2042301
  simp only [CollatzResearch.WordTrace]
  refine ⟨74488836974099749086742757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49659224649399832724495171 74488836974099749086742757)
  ·
    refine ⟨13966656932643702953764267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74488836974099749086742757 13966656932643702953764267)
    ·
      refine ⟨20949985398965554430646401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13966656932643702953764267 20949985398965554430646401)
      ·
        refine ⟨15712489049224165822984801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20949985398965554430646401 15712489049224165822984801)
        ·
          refine ⟨11784366786918124367238601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15712489049224165822984801 11784366786918124367238601)
          ·
            refine ⟨8838275090188593275428951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11784366786918124367238601 8838275090188593275428951)
            ·
              refine ⟨13257412635282889913143427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8838275090188593275428951 13257412635282889913143427)
              ·
                refine ⟨19886118952924334869715141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13257412635282889913143427 19886118952924334869715141)
                ·
                  refine ⟨3728647303673312788071589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19886118952924334869715141 3728647303673312788071589)
                  ·
                    refine ⟨699121369438746147763423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3728647303673312788071589 699121369438746147763423)
                    ·
                      rfl

theorem cell22_2042301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_2042301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042301 prefixEnd_2042301 := by exact prefixLift 2042301
  have htrace : WordTrace (prefixWord ++ tailWord_2042301) baseStart_2042301 baseEnd_2042301 := by
    simpa [prefixWord, tailWord_2042301, baseEnd_2042301] using wordTrace_append hprefix tailTrace_2042301
  have hstable : (prefixWord ++ tailWord_2042301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042301).length < 2 ^ (prefixWord ++ tailWord_2042301).sum := by decide
  have hdescent : baseEnd_2042301 < baseStart_2042301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042361 : List Nat := [1, 2, 1, 3, 1, 2, 3, 4, 5]
def baseStart_2042361 : Nat := 118140960795 + 2042361 * 2 ^ 59
def prefixEnd_2042361 : Nat := 4983230072969 + 3 ^ 40 * 2042361 * 2
def baseEnd_2042361 : Nat := 233047302888308663754413

theorem tailTrace_2042361 : CollatzResearch.WordTrace tailWord_2042361 prefixEnd_2042361 233047302888308663754413 := by
  unfold tailWord_2042361
  simp only [CollatzResearch.WordTrace]
  refine ⟨74491025353882379333926937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49660683569254919555951291 74491025353882379333926937)
  ·
    refine ⟨55868269015411784500445203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74491025353882379333926937 55868269015411784500445203)
    ·
      refine ⟨83802403523117676750667805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55868269015411784500445203 83802403523117676750667805)
      ·
        refine ⟨31425901321169128781500427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83802403523117676750667805 31425901321169128781500427)
        ·
          refine ⟨47138851981753693172250641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31425901321169128781500427 47138851981753693172250641)
          ·
            refine ⟨35354138986315269879187981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47138851981753693172250641 35354138986315269879187981)
            ·
              refine ⟨13257802119868226204695493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35354138986315269879187981 13257802119868226204695493)
              ·
                refine ⟨2485837897475292413380405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13257802119868226204695493 2485837897475292413380405)
                ·
                  refine ⟨233047302888308663754413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2485837897475292413380405 233047302888308663754413)
                  ·
                    rfl

theorem cell22_2042361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 5].length) (baseStart_2042361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042361 prefixEnd_2042361 := by exact prefixLift 2042361
  have htrace : WordTrace (prefixWord ++ tailWord_2042361) baseStart_2042361 baseEnd_2042361 := by
    simpa [prefixWord, tailWord_2042361, baseEnd_2042361] using wordTrace_append hprefix tailTrace_2042361
  have hstable : (prefixWord ++ tailWord_2042361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042361).length < 2 ^ (prefixWord ++ tailWord_2042361).sum := by decide
  have hdescent : baseEnd_2042361 < baseStart_2042361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042365 : List Nat := [1, 4, 1, 1, 1, 3, 3, 4, 1, 3]
def baseStart_2042365 : Nat := 118140960795 + 2042365 * 2 ^ 59
def prefixEnd_2042365 : Nat := 4983230072969 + 3 ^ 40 * 2042365 * 2
def baseEnd_2042365 : Nat := 699143277946671314163227

theorem tailTrace_2042365 : CollatzResearch.WordTrace tailWord_2042365 prefixEnd_2042365 699143277946671314163227 := by
  unfold tailWord_2042365
  simp only [CollatzResearch.WordTrace]
  refine ⟨74491171245867888017072549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49660780830578592011381699 74491171245867888017072549)
  ·
    refine ⟨13967094608600229003201103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74491171245867888017072549 13967094608600229003201103)
    ·
      refine ⟨20950641912900343504801655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13967094608600229003201103 20950641912900343504801655)
      ·
        refine ⟨31425962869350515257202483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20950641912900343504801655 31425962869350515257202483)
        ·
          refine ⟨47138944304025772885803725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31425962869350515257202483 47138944304025772885803725)
          ·
            refine ⟨17677104114009664832176397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47138944304025772885803725 17677104114009664832176397)
            ·
              refine ⟨6628914042753624312066149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17677104114009664832176397 6628914042753624312066149)
              ·
                refine ⟨1242921383016304558512403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6628914042753624312066149 1242921383016304558512403)
                ·
                  refine ⟨1864382074524456837768605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1242921383016304558512403 1864382074524456837768605)
                  ·
                    refine ⟨699143277946671314163227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1864382074524456837768605 699143277946671314163227)
                    ·
                      rfl

theorem cell22_2042365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_2042365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042365 prefixEnd_2042365 := by exact prefixLift 2042365
  have htrace : WordTrace (prefixWord ++ tailWord_2042365) baseStart_2042365 baseEnd_2042365 := by
    simpa [prefixWord, tailWord_2042365, baseEnd_2042365] using wordTrace_append hprefix tailTrace_2042365
  have hstable : (prefixWord ++ tailWord_2042365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042365).length < 2 ^ (prefixWord ++ tailWord_2042365).sum := by decide
  have hdescent : baseEnd_2042365 < baseStart_2042365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042423 : List Nat := [1, 1, 3, 1, 2, 3, 1, 6, 4]
def baseStart_2042423 : Nat := 118140960795 + 2042423 * 2 ^ 59
def prefixEnd_2042423 : Nat := 4983230072969 + 3 ^ 40 * 2042423 * 2
def baseEnd_2042423 : Nat := 233054377510659498737683

theorem tailTrace_2042423 : CollatzResearch.WordTrace tailWord_2042423 prefixEnd_2042423 233054377510659498737683 := by
  unfold tailWord_2042423
  simp only [CollatzResearch.WordTrace]
  refine ⟨74493286679657763922683923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49662191119771842615122615 74493286679657763922683923)
  ·
    refine ⟨111739930019486645884025885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74493286679657763922683923 111739930019486645884025885)
    ·
      refine ⟨41902473757307492206509707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111739930019486645884025885 41902473757307492206509707)
      ·
        refine ⟨62853710635961238309764561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41902473757307492206509707 62853710635961238309764561)
        ·
          refine ⟨47140282976970928732323421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62853710635961238309764561 47140282976970928732323421)
          ·
            refine ⟨17677606116364098274621283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47140282976970928732323421 17677606116364098274621283)
            ·
              refine ⟨26516409174546147411931925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17677606116364098274621283 26516409174546147411931925)
              ·
                refine ⟨1242956680056850659934309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26516409174546147411931925 1242956680056850659934309)
                ·
                  refine ⟨233054377510659498737683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1242956680056850659934309 233054377510659498737683)
                  ·
                    rfl

theorem cell22_2042423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 4].length) (baseStart_2042423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042423 prefixEnd_2042423 := by exact prefixLift 2042423
  have htrace : WordTrace (prefixWord ++ tailWord_2042423) baseStart_2042423 baseEnd_2042423 := by
    simpa [prefixWord, tailWord_2042423, baseEnd_2042423] using wordTrace_append hprefix tailTrace_2042423
  have hstable : (prefixWord ++ tailWord_2042423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042423).length < 2 ^ (prefixWord ++ tailWord_2042423).sum := by decide
  have hdescent : baseEnd_2042423 < baseStart_2042423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042483 : List Nat := [1, 1, 1, 2, 2, 1, 1, 7, 3, 3]
def baseStart_2042483 : Nat := 118140960795 + 2042483 * 2 ^ 59
def prefixEnd_2042483 : Nat := 4983230072969 + 3 ^ 40 * 2042483 * 2
def baseEnd_2042483 : Nat := 699183671758158339712865

theorem tailTrace_2042483 : CollatzResearch.WordTrace tailWord_2042483 prefixEnd_2042483 699183671758158339712865 := by
  unfold tailWord_2042483
  simp only [CollatzResearch.WordTrace]
  refine ⟨74495475059440394169868103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49663650039626929446578735 74495475059440394169868103)
  ·
    refine ⟨111743212589160591254802155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74495475059440394169868103 111743212589160591254802155)
    ·
      refine ⟨167614818883740886882203233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111743212589160591254802155 167614818883740886882203233)
      ·
        refine ⟨125711114162805665161652425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167614818883740886882203233 125711114162805665161652425)
        ·
          refine ⟨94283335622104248871239319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125711114162805665161652425 94283335622104248871239319)
          ·
            refine ⟨141425003433156373306858979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94283335622104248871239319 141425003433156373306858979)
            ·
              refine ⟨212137505149734559960288469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141425003433156373306858979 212137505149734559960288469)
              ·
                refine ⟨4971972776946903749069261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 212137505149734559960288469 4971972776946903749069261)
                ·
                  refine ⟨1864489791355088905900973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4971972776946903749069261 1864489791355088905900973)
                  ·
                    refine ⟨699183671758158339712865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1864489791355088905900973 699183671758158339712865)
                    ·
                      rfl

theorem cell22_2042483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 3].length) (baseStart_2042483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042483 prefixEnd_2042483 := by exact prefixLift 2042483
  have htrace : WordTrace (prefixWord ++ tailWord_2042483) baseStart_2042483 baseEnd_2042483 := by
    simpa [prefixWord, tailWord_2042483, baseEnd_2042483] using wordTrace_append hprefix tailTrace_2042483
  have hstable : (prefixWord ++ tailWord_2042483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042483).length < 2 ^ (prefixWord ++ tailWord_2042483).sum := by decide
  have hdescent : baseEnd_2042483 < baseStart_2042483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042485 : List Nat := [1, 3, 4, 2, 2, 1, 2, 7]
def baseStart_2042485 : Nat := 118140960795 + 2042485 * 2 ^ 59
def prefixEnd_2042485 : Nat := 4983230072969 + 3 ^ 40 * 2042485 * 2
def baseEnd_2042485 : Nat := 77687150711003444573651

theorem tailTrace_2042485 : CollatzResearch.WordTrace tailWord_2042485 prefixEnd_2042485 77687150711003444573651 := by
  unfold tailWord_2042485
  simp only [CollatzResearch.WordTrace]
  refine ⟨74495548005433148511440909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49663698670288765674293939 74495548005433148511440909)
  ·
    refine ⟨27935830502037430691790341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74495548005433148511440909 27935830502037430691790341)
    ·
      refine ⟨5237968219132018254710689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27935830502037430691790341 5237968219132018254710689)
      ·
        refine ⟨3928476164349013691033017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5237968219132018254710689 3928476164349013691033017)
        ·
          refine ⟨2946357123261760268274763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3928476164349013691033017 2946357123261760268274763)
          ·
            refine ⟨4419535684892640402412145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2946357123261760268274763 4419535684892640402412145)
            ·
              refine ⟨3314651763669480301809109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4419535684892640402412145 3314651763669480301809109)
              ·
                refine ⟨77687150711003444573651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3314651763669480301809109 77687150711003444573651)
                ·
                  rfl

theorem cell22_2042485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 7].length) (baseStart_2042485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042485 prefixEnd_2042485 := by exact prefixLift 2042485
  have htrace : WordTrace (prefixWord ++ tailWord_2042485) baseStart_2042485 baseEnd_2042485 := by
    simpa [prefixWord, tailWord_2042485, baseEnd_2042485] using wordTrace_append hprefix tailTrace_2042485
  have hstable : (prefixWord ++ tailWord_2042485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042485).length < 2 ^ (prefixWord ++ tailWord_2042485).sum := by decide
  have hdescent : baseEnd_2042485 < baseStart_2042485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042511 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 1, 7]
def baseStart_2042511 : Nat := 118140960795 + 2042511 * 2 ^ 59
def prefixEnd_2042511 : Nat := 4983230072969 + 3 ^ 40 * 2042511 * 2
def baseEnd_2042511 : Nat := 699193256730375600012779

theorem tailTrace_2042511 : CollatzResearch.WordTrace tailWord_2042511 prefixEnd_2042511 699193256730375600012779 := by
  unfold tailWord_2042511
  simp only [CollatzResearch.WordTrace]
  refine ⟨74496496303338954951887387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49664330868892636634591591 74496496303338954951887387)
  ·
    refine ⟨111744744455008432427831081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74496496303338954951887387 111744744455008432427831081)
    ·
      refine ⟨83808558341256324320873311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111744744455008432427831081 83808558341256324320873311)
      ·
        refine ⟨125712837511884486481309967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83808558341256324320873311 125712837511884486481309967)
        ·
          refine ⟨188569256267826729721964951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125712837511884486481309967 188569256267826729721964951)
          ·
            refine ⟨282853884401740094582947427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188569256267826729721964951 282853884401740094582947427)
            ·
              refine ⟨424280826602610141874421141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282853884401740094582947427 424280826602610141874421141)
              ·
                refine ⟨19888163746997350400363491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 424280826602610141874421141 19888163746997350400363491)
                ·
                  refine ⟨29832245620496025600545237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19888163746997350400363491 29832245620496025600545237)
                  ·
                    refine ⟨699193256730375600012779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29832245620496025600545237 699193256730375600012779)
                    ·
                      rfl

theorem cell22_2042511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_2042511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042511 prefixEnd_2042511 := by exact prefixLift 2042511
  have htrace : WordTrace (prefixWord ++ tailWord_2042511) baseStart_2042511 baseEnd_2042511 := by
    simpa [prefixWord, tailWord_2042511, baseEnd_2042511] using wordTrace_append hprefix tailTrace_2042511
  have hstable : (prefixWord ++ tailWord_2042511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042511).length < 2 ^ (prefixWord ++ tailWord_2042511).sum := by decide
  have hdescent : baseEnd_2042511 < baseStart_2042511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042543 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 3, 4]
def baseStart_2042543 : Nat := 118140960795 + 2042543 * 2 ^ 59
def prefixEnd_2042543 : Nat := 4983230072969 + 3 ^ 40 * 2042543 * 2
def baseEnd_2042543 : Nat := 699204210984338183212681

theorem tailTrace_2042543 : CollatzResearch.WordTrace tailWord_2042543 prefixEnd_2042543 699204210984338183212681 := by
  unfold tailWord_2042543
  simp only [CollatzResearch.WordTrace]
  refine ⟨74497663439223024417052283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49665108959482016278034855 74497663439223024417052283)
  ·
    refine ⟨111746495158834536625578425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74497663439223024417052283 111746495158834536625578425)
    ·
      refine ⟨83809871369125902469183819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111746495158834536625578425 83809871369125902469183819)
      ·
        refine ⟨125714807053688853703775729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83809871369125902469183819 125714807053688853703775729)
        ·
          refine ⟨94286105290266640277831797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125714807053688853703775729 94286105290266640277831797)
          ·
            refine ⟨8839322370962497526046731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94286105290266640277831797 8839322370962497526046731)
            ·
              refine ⟨13258983556443746289070097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8839322370962497526046731 13258983556443746289070097)
              ·
                refine ⟨9944237667332809716802573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13258983556443746289070097 9944237667332809716802573)
                ·
                  refine ⟨3729089125249803643800965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9944237667332809716802573 3729089125249803643800965)
                  ·
                    refine ⟨699204210984338183212681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3729089125249803643800965 699204210984338183212681)
                    ·
                      rfl

theorem cell22_2042543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 4].length) (baseStart_2042543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042543 prefixEnd_2042543 := by exact prefixLift 2042543
  have htrace : WordTrace (prefixWord ++ tailWord_2042543) baseStart_2042543 baseEnd_2042543 := by
    simpa [prefixWord, tailWord_2042543, baseEnd_2042543] using wordTrace_append hprefix tailTrace_2042543
  have hstable : (prefixWord ++ tailWord_2042543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042543).length < 2 ^ (prefixWord ++ tailWord_2042543).sum := by decide
  have hdescent : baseEnd_2042543 < baseStart_2042543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042620 : List Nat := [2, 2, 2, 1, 3, 2, 4, 6]
def baseStart_2042620 : Nat := 118140960795 + 2042620 * 2 ^ 59
def prefixEnd_2042620 : Nat := 4983230072969 + 3 ^ 40 * 2042620 * 2
def baseEnd_2042620 : Nat := 77692285517548405448605

theorem tailTrace_2042620 : CollatzResearch.WordTrace tailWord_2042620 prefixEnd_2042620 77692285517548405448605 := by
  unfold tailWord_2042620
  simp only [CollatzResearch.WordTrace]
  refine ⟨37250235929972033283802657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49666981239962711045070209 37250235929972033283802657)
  ·
    refine ⟨27937676947479024962851993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37250235929972033283802657 27937676947479024962851993)
    ·
      refine ⟨20953257710609268722138995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27937676947479024962851993 20953257710609268722138995)
      ·
        refine ⟨31429886565913903083208493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20953257710609268722138995 31429886565913903083208493)
        ·
          refine ⟨11786207462217713656203185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31429886565913903083208493 11786207462217713656203185)
          ·
            refine ⟨8839655596663285242152389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11786207462217713656203185 8839655596663285242152389)
            ·
              refine ⟨1657435424374365982903573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8839655596663285242152389 1657435424374365982903573)
              ·
                refine ⟨77692285517548405448605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1657435424374365982903573 77692285517548405448605)
                ·
                  rfl

theorem cell22_2042620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 6].length) (baseStart_2042620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042620 prefixEnd_2042620 := by exact prefixLift 2042620
  have htrace : WordTrace (prefixWord ++ tailWord_2042620) baseStart_2042620 baseEnd_2042620 := by
    simpa [prefixWord, tailWord_2042620, baseEnd_2042620] using wordTrace_append hprefix tailTrace_2042620
  have hstable : (prefixWord ++ tailWord_2042620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042620).length < 2 ^ (prefixWord ++ tailWord_2042620).sum := by decide
  have hdescent : baseEnd_2042620 < baseStart_2042620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042652 : List Nat := [2, 2, 3, 1, 1, 3, 3, 1, 3, 3]
def baseStart_2042652 : Nat := 118140960795 + 2042652 * 2 ^ 59
def prefixEnd_2042652 : Nat := 4983230072969 + 3 ^ 40 * 2042652 * 2
def baseEnd_2042652 : Nat := 699241523911898232237347

theorem tailTrace_2042652 : CollatzResearch.WordTrace tailWord_2042652 prefixEnd_2042652 699241523911898232237347 := by
  unfold tailWord_2042652
  simp only [CollatzResearch.WordTrace]
  refine ⟨37250819497914068016385105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49667759330552090688513473 37250819497914068016385105)
  ·
    refine ⟨27938114623435551012288829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37250819497914068016385105 27938114623435551012288829)
    ·
      refine ⟨10476792983788331629608311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27938114623435551012288829 10476792983788331629608311)
      ·
        refine ⟨15715189475682497444412467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10476792983788331629608311 15715189475682497444412467)
        ·
          refine ⟨23572784213523746166618701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15715189475682497444412467 23572784213523746166618701)
          ·
            refine ⟨8839794080071404812482013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23572784213523746166618701 8839794080071404812482013)
            ·
              refine ⟨3314922780026776804680755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8839794080071404812482013 3314922780026776804680755)
              ·
                refine ⟨4972384170040165207021133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3314922780026776804680755 4972384170040165207021133)
                ·
                  refine ⟨1864644063765061952632925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4972384170040165207021133 1864644063765061952632925)
                  ·
                    refine ⟨699241523911898232237347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1864644063765061952632925 699241523911898232237347)
                    ·
                      rfl

theorem cell22_2042652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_2042652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042652 prefixEnd_2042652 := by exact prefixLift 2042652
  have htrace : WordTrace (prefixWord ++ tailWord_2042652) baseStart_2042652 baseEnd_2042652 := by
    simpa [prefixWord, tailWord_2042652, baseEnd_2042652] using wordTrace_append hprefix tailTrace_2042652
  have hstable : (prefixWord ++ tailWord_2042652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042652).length < 2 ^ (prefixWord ++ tailWord_2042652).sum := by decide
  have hdescent : baseEnd_2042652 < baseStart_2042652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042693 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 10]
def baseStart_2042693 : Nat := 118140960795 + 2042693 * 2 ^ 59
def prefixEnd_2042693 : Nat := 4983230072969 + 3 ^ 40 * 2042693 * 2
def baseEnd_2042693 : Nat := 233085186349929263987407

theorem tailTrace_2042693 : CollatzResearch.WordTrace tailWord_2042693 prefixEnd_2042693 233085186349929263987407 := by
  unfold tailWord_2042693
  simp only [CollatzResearch.WordTrace]
  refine ⟨74503134388679600035012733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49668756259119733356675155 74503134388679600035012733)
  ·
    refine ⟨27938675395754850013129775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74503134388679600035012733 27938675395754850013129775)
    ·
      refine ⟨41908013093632275019694663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27938675395754850013129775 41908013093632275019694663)
      ·
        refine ⟨62862019640448412529541995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41908013093632275019694663 62862019640448412529541995)
        ·
          refine ⟨94293029460672618794312993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62862019640448412529541995 94293029460672618794312993)
          ·
            refine ⟨70719772095504464095734745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94293029460672618794312993 70719772095504464095734745)
            ·
              refine ⟨53039829071628348071801059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70719772095504464095734745 53039829071628348071801059)
              ·
                refine ⟨79559743607442522107701589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53039829071628348071801059 79559743607442522107701589)
                ·
                  refine ⟨233085186349929263987407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 79559743607442522107701589 233085186349929263987407)
                  ·
                    rfl

theorem cell22_2042693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_2042693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042693 prefixEnd_2042693 := by exact prefixLift 2042693
  have htrace : WordTrace (prefixWord ++ tailWord_2042693) baseStart_2042693 baseEnd_2042693 := by
    simpa [prefixWord, tailWord_2042693, baseEnd_2042693] using wordTrace_append hprefix tailTrace_2042693
  have hstable : (prefixWord ++ tailWord_2042693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042693).length < 2 ^ (prefixWord ++ tailWord_2042693).sum := by decide
  have hdescent : baseEnd_2042693 < baseStart_2042693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042725 : List Nat := [1, 3, 1, 3, 1, 1, 3, 3, 1, 5]
def baseStart_2042725 : Nat := 118140960795 + 2042725 * 2 ^ 59
def prefixEnd_2042725 : Nat := 4983230072969 + 3 ^ 40 * 2042725 * 2
def baseEnd_2042725 : Nat := 699266513303750375162123

theorem tailTrace_2042725 : CollatzResearch.WordTrace tailWord_2042725 prefixEnd_2042725 699266513303750375162123 := by
  unfold tailWord_2042725
  simp only [CollatzResearch.WordTrace]
  refine ⟨74504301524563669500177629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49669534349709113000118419 74504301524563669500177629)
  ·
    refine ⟨27939113071711376062566611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74504301524563669500177629 27939113071711376062566611)
    ·
      refine ⟨41908669607567064093849917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27939113071711376062566611 41908669607567064093849917)
      ·
        refine ⟨15715751102837649035193719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41908669607567064093849917 15715751102837649035193719)
        ·
          refine ⟨23573626654256473552790579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15715751102837649035193719 23573626654256473552790579)
          ·
            refine ⟨35360439981384710329185869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23573626654256473552790579 35360439981384710329185869)
            ·
              refine ⟨13260164993019266373444701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35360439981384710329185869 13260164993019266373444701)
              ·
                refine ⟨4972561872382224890041763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13260164993019266373444701 4972561872382224890041763)
                ·
                  refine ⟨7458842808573337335062645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4972561872382224890041763 7458842808573337335062645)
                  ·
                    refine ⟨699266513303750375162123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7458842808573337335062645 699266513303750375162123)
                    ·
                      rfl

theorem cell22_2042725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_2042725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042725 prefixEnd_2042725 := by exact prefixLift 2042725
  have htrace : WordTrace (prefixWord ++ tailWord_2042725) baseStart_2042725 baseEnd_2042725 := by
    simpa [prefixWord, tailWord_2042725, baseEnd_2042725] using wordTrace_append hprefix tailTrace_2042725
  have hstable : (prefixWord ++ tailWord_2042725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042725).length < 2 ^ (prefixWord ++ tailWord_2042725).sum := by decide
  have hdescent : baseEnd_2042725 < baseStart_2042725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042759 : List Nat := [1, 1, 4, 2, 3, 1, 3, 2, 2, 3]
def baseStart_2042759 : Nat := 118140960795 + 2042759 * 2 ^ 59
def prefixEnd_2042759 : Nat := 4983230072969 + 3 ^ 40 * 2042759 * 2
def baseEnd_2042759 : Nat := 699278152198585619812019

theorem tailTrace_2042759 : CollatzResearch.WordTrace tailWord_2042759 prefixEnd_2042759 699278152198585619812019 := by
  unfold tailWord_2042759
  simp only [CollatzResearch.WordTrace]
  refine ⟨74505541606440493306915331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49670361070960328871276887 74505541606440493306915331)
  ·
    refine ⟨111758312409660739960372997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74505541606440493306915331 111758312409660739960372997)
    ·
      refine ⟨20954683576811388742569937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111758312409660739960372997 20954683576811388742569937)
      ·
        refine ⟨15716012682608541556927453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20954683576811388742569937 15716012682608541556927453)
        ·
          refine ⟨5893504755978203083847795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15716012682608541556927453 5893504755978203083847795)
          ·
            refine ⟨8840257133967304625771693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5893504755978203083847795 8840257133967304625771693)
            ·
              refine ⟨3315096425237739234664385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8840257133967304625771693 3315096425237739234664385)
              ·
                refine ⟨2486322318928304425998289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3315096425237739234664385 2486322318928304425998289)
                ·
                  refine ⟨1864741739196228319498717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2486322318928304425998289 1864741739196228319498717)
                  ·
                    refine ⟨699278152198585619812019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1864741739196228319498717 699278152198585619812019)
                    ·
                      rfl

theorem cell22_2042759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_2042759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042759 prefixEnd_2042759 := by exact prefixLift 2042759
  have htrace : WordTrace (prefixWord ++ tailWord_2042759) baseStart_2042759 baseEnd_2042759 := by
    simpa [prefixWord, tailWord_2042759, baseEnd_2042759] using wordTrace_append hprefix tailTrace_2042759
  have hstable : (prefixWord ++ tailWord_2042759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042759).length < 2 ^ (prefixWord ++ tailWord_2042759).sum := by decide
  have hdescent : baseEnd_2042759 < baseStart_2042759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042787 : List Nat := [1, 1, 1, 4, 1, 2, 4, 2, 3, 3]
def baseStart_2042787 : Nat := 118140960795 + 2042787 * 2 ^ 59
def prefixEnd_2042787 : Nat := 4983230072969 + 3 ^ 40 * 2042787 * 2
def baseEnd_2042787 : Nat := 699287737170802880111933

theorem tailTrace_2042787 : CollatzResearch.WordTrace tailWord_2042787 prefixEnd_2042787 699287737170802880111933 := by
  unfold tailWord_2042787
  simp only [CollatzResearch.WordTrace]
  refine ⟨74506562850339054088934615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49671041900226036059289743 74506562850339054088934615)
  ·
    refine ⟨111759844275508581133401923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74506562850339054088934615 111759844275508581133401923)
    ·
      refine ⟨167639766413262871700102885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111759844275508581133401923 167639766413262871700102885)
      ·
        refine ⟨31432456202486788443769291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167639766413262871700102885 31432456202486788443769291)
        ·
          refine ⟨47148684303730182665653937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31432456202486788443769291 47148684303730182665653937)
          ·
            refine ⟨35361513227797636999240453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47148684303730182665653937 35361513227797636999240453)
            ·
              refine ⟨6630283730212056937357585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35361513227797636999240453 6630283730212056937357585)
              ·
                refine ⟨4972712797659042703018189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6630283730212056937357585 4972712797659042703018189)
                ·
                  refine ⟨1864767299122141013631821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4972712797659042703018189 1864767299122141013631821)
                  ·
                    refine ⟨699287737170802880111933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1864767299122141013631821 699287737170802880111933)
                    ·
                      rfl

theorem cell22_2042787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 3].length) (baseStart_2042787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042787 prefixEnd_2042787 := by exact prefixLift 2042787
  have htrace : WordTrace (prefixWord ++ tailWord_2042787) baseStart_2042787 baseEnd_2042787 := by
    simpa [prefixWord, tailWord_2042787, baseEnd_2042787] using wordTrace_append hprefix tailTrace_2042787
  have hstable : (prefixWord ++ tailWord_2042787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042787).length < 2 ^ (prefixWord ++ tailWord_2042787).sum := by decide
  have hdescent : baseEnd_2042787 < baseStart_2042787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042815 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 2, 5]
def baseStart_2042815 : Nat := 118140960795 + 2042815 * 2 ^ 59
def prefixEnd_2042815 : Nat := 4983230072969 + 3 ^ 40 * 2042815 * 2
def baseEnd_2042815 : Nat := 699297322143020140411847

theorem tailTrace_2042815 : CollatzResearch.WordTrace tailWord_2042815 prefixEnd_2042815 699297322143020140411847 := by
  unfold tailWord_2042815
  simp only [CollatzResearch.WordTrace]
  refine ⟨74507584094237614870953899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49671722729491743247302599 74507584094237614870953899)
  ·
    refine ⟨111761376141356422306430849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74507584094237614870953899 111761376141356422306430849)
    ·
      refine ⟨83821032106017316729823137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111761376141356422306430849 83821032106017316729823137)
      ·
        refine ⟨62865774079512987547367353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83821032106017316729823137 62865774079512987547367353)
        ·
          refine ⟨47149330559634740660525515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62865774079512987547367353 47149330559634740660525515)
          ·
            refine ⟨70723995839452110990788273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47149330559634740660525515 70723995839452110990788273)
            ·
              refine ⟨53042996879589083243091205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70723995839452110990788273 53042996879589083243091205)
              ·
                refine ⟨9945561914922953108079601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53042996879589083243091205 9945561914922953108079601)
                ·
                  refine ⟨7459171436192214831059701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9945561914922953108079601 7459171436192214831059701)
                  ·
                    refine ⟨699297322143020140411847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7459171436192214831059701 699297322143020140411847)
                    ·
                      rfl

theorem cell22_2042815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_2042815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042815 prefixEnd_2042815 := by exact prefixLift 2042815
  have htrace : WordTrace (prefixWord ++ tailWord_2042815) baseStart_2042815 baseEnd_2042815 := by
    simpa [prefixWord, tailWord_2042815, baseEnd_2042815] using wordTrace_append hprefix tailTrace_2042815
  have hstable : (prefixWord ++ tailWord_2042815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042815).length < 2 ^ (prefixWord ++ tailWord_2042815).sum := by decide
  have hdescent : baseEnd_2042815 < baseStart_2042815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042834 : List Nat := [3, 2, 2, 3, 1, 2, 1, 3, 5]
def baseStart_2042834 : Nat := 118140960795 + 2042834 * 2 ^ 59
def prefixEnd_2042834 : Nat := 4983230072969 + 3 ^ 40 * 2042834 * 2
def baseEnd_2042834 : Nat := 233101275410436808062263

theorem tailTrace_2042834 : CollatzResearch.WordTrace tailWord_2042834 prefixEnd_2042834 233101275410436808062263 := by
  unfold tailWord_2042834
  simp only [CollatzResearch.WordTrace]
  refine ⟨18627069270292195278973889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49672184720779187410597037 18627069270292195278973889)
  ·
    refine ⟨13970301952719146459230417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18627069270292195278973889 13970301952719146459230417)
    ·
      refine ⟨10477726464539359844422813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13970301952719146459230417 10477726464539359844422813)
      ·
        refine ⟨3929147424202259941658555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10477726464539359844422813 3929147424202259941658555)
        ·
          refine ⟨5893721136303389912487833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3929147424202259941658555 5893721136303389912487833)
          ·
            refine ⟨4420290852227542434365875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5893721136303389912487833 4420290852227542434365875)
            ·
              refine ⟨6630436278341313651548813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4420290852227542434365875 6630436278341313651548813)
              ·
                refine ⟨2486413604377992619330805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6630436278341313651548813 2486413604377992619330805)
                ·
                  refine ⟨233101275410436808062263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2486413604377992619330805 233101275410436808062263)
                  ·
                    rfl

theorem cell22_2042834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_2042834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042834 prefixEnd_2042834 := by exact prefixLift 2042834
  have htrace : WordTrace (prefixWord ++ tailWord_2042834) baseStart_2042834 baseEnd_2042834 := by
    simpa [prefixWord, tailWord_2042834, baseEnd_2042834] using wordTrace_append hprefix tailTrace_2042834
  have hstable : (prefixWord ++ tailWord_2042834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042834).length < 2 ^ (prefixWord ++ tailWord_2042834).sum := by decide
  have hdescent : baseEnd_2042834 < baseStart_2042834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042875 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 3, 6]
def baseStart_2042875 : Nat := 118140960795 + 2042875 * 2 ^ 59
def prefixEnd_2042875 : Nat := 4983230072969 + 3 ^ 40 * 2042875 * 2
def baseEnd_2042875 : Nat := 699317861369199983911663

theorem tailTrace_2042875 : CollatzResearch.WordTrace tailWord_2042875 prefixEnd_2042875 699317861369199983911663 := by
  unfold tailWord_2042875
  simp only [CollatzResearch.WordTrace]
  refine ⟨74509772474020245118138079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49673181649346830078758719 74509772474020245118138079)
  ·
    refine ⟨111764658711030367677207119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74509772474020245118138079 111764658711030367677207119)
    ·
      refine ⟨167646988066545551515810679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111764658711030367677207119 167646988066545551515810679)
      ·
        refine ⟨251470482099818327273716019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167646988066545551515810679 251470482099818327273716019)
        ·
          refine ⟨377205723149727490910574029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251470482099818327273716019 377205723149727490910574029)
          ·
            refine ⟨141452146181147809091465261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377205723149727490910574029 141452146181147809091465261)
            ·
              refine ⟨53044554817930428409299473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141452146181147809091465261 53044554817930428409299473)
              ·
                refine ⟨39783416113447821306974605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53044554817930428409299473 39783416113447821306974605)
                ·
                  refine ⟨14918781042542932990115477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39783416113447821306974605 14918781042542932990115477)
                  ·
                    refine ⟨699317861369199983911663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14918781042542932990115477 699317861369199983911663)
                    ·
                      rfl

theorem cell22_2042875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 6].length) (baseStart_2042875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042875 prefixEnd_2042875 := by exact prefixLift 2042875
  have htrace : WordTrace (prefixWord ++ tailWord_2042875) baseStart_2042875 baseEnd_2042875 := by
    simpa [prefixWord, tailWord_2042875, baseEnd_2042875] using wordTrace_append hprefix tailTrace_2042875
  have hstable : (prefixWord ++ tailWord_2042875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042875).length < 2 ^ (prefixWord ++ tailWord_2042875).sum := by decide
  have hdescent : baseEnd_2042875 < baseStart_2042875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042894 : List Nat := [4, 1, 1, 2, 2, 3, 2, 1, 1, 5]
def baseStart_2042894 : Nat := 118140960795 + 2042894 * 2 ^ 59
def prefixEnd_2042894 : Nat := 4983230072969 + 3 ^ 40 * 2042894 * 2
def baseEnd_2042894 : Nat := 699324365457490267686605

theorem tailTrace_2042894 : CollatzResearch.WordTrace tailWord_2042894 prefixEnd_2042894 699324365457490267686605 := by
  unfold tailWord_2042894
  simp only [CollatzResearch.WordTrace]
  refine ⟨9313808182618926420384967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49673643640634274242053157 9313808182618926420384967)
  ·
    refine ⟨13970712273928389630577451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9313808182618926420384967 13970712273928389630577451)
    ·
      refine ⟨20956068410892584445866177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13970712273928389630577451 20956068410892584445866177)
      ·
        refine ⟨15717051308169438334399633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20956068410892584445866177 15717051308169438334399633)
        ·
          refine ⟨11787788481127078750799725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15717051308169438334399633 11787788481127078750799725)
          ·
            refine ⟨4420420680422654531549897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11787788481127078750799725 4420420680422654531549897)
            ·
              refine ⟨3315315510316990898662423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4420420680422654531549897 3315315510316990898662423)
              ·
                refine ⟨4972973265475486347993635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3315315510316990898662423 4972973265475486347993635)
                ·
                  refine ⟨7459459898213229521990453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4972973265475486347993635 7459459898213229521990453)
                  ·
                    refine ⟨699324365457490267686605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7459459898213229521990453 699324365457490267686605)
                    ·
                      rfl

theorem cell22_2042894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_2042894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042894 prefixEnd_2042894 := by exact prefixLift 2042894
  have htrace : WordTrace (prefixWord ++ tailWord_2042894) baseStart_2042894 baseEnd_2042894 := by
    simpa [prefixWord, tailWord_2042894, baseEnd_2042894] using wordTrace_append hprefix tailTrace_2042894
  have hstable : (prefixWord ++ tailWord_2042894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042894).length < 2 ^ (prefixWord ++ tailWord_2042894).sum := by decide
  have hdescent : baseEnd_2042894 < baseStart_2042894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042909 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 1, 6]
def baseStart_2042909 : Nat := 118140960795 + 2042909 * 2 ^ 59
def prefixEnd_2042909 : Nat := 4983230072969 + 3 ^ 40 * 2042909 * 2
def baseEnd_2042909 : Nat := 699329500264035228561559

theorem tailTrace_2042909 : CollatzResearch.WordTrace tailWord_2042909 prefixEnd_2042909 699329500264035228561559 := by
  unfold tailWord_2042909
  simp only [CollatzResearch.WordTrace]
  refine ⟨74511012555897068924875781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49674008370598045949917187 74511012555897068924875781)
  ·
    refine ⟨13970814854230700423414209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74511012555897068924875781 13970814854230700423414209)
    ·
      refine ⟨10478111140673025317560657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13970814854230700423414209 10478111140673025317560657)
      ·
        refine ⟨7858583355504768988170493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10478111140673025317560657 7858583355504768988170493)
        ·
          refine ⟨2946968758314288370563935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7858583355504768988170493 2946968758314288370563935)
          ·
            refine ⟨4420453137471432555845903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2946968758314288370563935 4420453137471432555845903)
            ·
              refine ⟨6630679706207148833768855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4420453137471432555845903 6630679706207148833768855)
              ·
                refine ⟨9946019559310723250653283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6630679706207148833768855 9946019559310723250653283)
                ·
                  refine ⟨14919029338966084875979925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9946019559310723250653283 14919029338966084875979925)
                  ·
                    refine ⟨699329500264035228561559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14919029338966084875979925 699329500264035228561559)
                    ·
                      rfl

theorem cell22_2042909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_2042909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042909 prefixEnd_2042909 := by exact prefixLift 2042909
  have htrace : WordTrace (prefixWord ++ tailWord_2042909) baseStart_2042909 baseEnd_2042909 := by
    simpa [prefixWord, tailWord_2042909, baseEnd_2042909] using wordTrace_append hprefix tailTrace_2042909
  have hstable : (prefixWord ++ tailWord_2042909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042909).length < 2 ^ (prefixWord ++ tailWord_2042909).sum := by decide
  have hdescent : baseEnd_2042909 < baseStart_2042909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042990 : List Nat := [4, 1, 2, 2, 1, 3, 3, 2, 1, 3]
def baseStart_2042990 : Nat := 118140960795 + 2042990 * 2 ^ 59
def prefixEnd_2042990 : Nat := 4983230072969 + 3 ^ 40 * 2042990 * 2
def baseEnd_2042990 : Nat := 699357228219378017286311

theorem tailTrace_2042990 : CollatzResearch.WordTrace tailWord_2042990 prefixEnd_2042990 699357228219378017286311 := by
  unfold tailWord_2042990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9314245858575452469821803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49675977912402413172382949 9314245858575452469821803)
  ·
    refine ⟨13971368787863178704732705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9314245858575452469821803 13971368787863178704732705)
    ·
      refine ⟨10478526590897384028549529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13971368787863178704732705 10478526590897384028549529)
      ·
        refine ⟨7858894943173038021412147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10478526590897384028549529 7858894943173038021412147)
        ·
          refine ⟨11788342414759557032118221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7858894943173038021412147 11788342414759557032118221)
          ·
            refine ⟨4420628405534833887044333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11788342414759557032118221 4420628405534833887044333)
            ·
              refine ⟨1657735652075562707641625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4420628405534833887044333 1657735652075562707641625)
              ·
                refine ⟨1243301739056672030731219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1657735652075562707641625 1243301739056672030731219)
                ·
                  refine ⟨1864952608585008046096829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243301739056672030731219 1864952608585008046096829)
                  ·
                    refine ⟨699357228219378017286311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1864952608585008046096829 699357228219378017286311)
                    ·
                      rfl

theorem cell22_2042990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_2042990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2042990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2042990 prefixEnd_2042990 := by exact prefixLift 2042990
  have htrace : WordTrace (prefixWord ++ tailWord_2042990) baseStart_2042990 baseEnd_2042990 := by
    simpa [prefixWord, tailWord_2042990, baseEnd_2042990] using wordTrace_append hprefix tailTrace_2042990
  have hstable : (prefixWord ++ tailWord_2042990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042990).length < 2 ^ (prefixWord ++ tailWord_2042990).sum := by decide
  have hdescent : baseEnd_2042990 < baseStart_2042990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043016 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 3, 4]
def baseStart_2043016 : Nat := 118140960795 + 2043016 * 2 ^ 59
def prefixEnd_2043016 : Nat := 4983230072969 + 3 ^ 40 * 2043016 * 2
def baseEnd_2043016 : Nat := 699366128550722616136231

theorem tailTrace_2043016 : CollatzResearch.WordTrace tailWord_2043016 prefixEnd_2043016 699366128550722616136231 := by
  unfold tailWord_2043016
  simp only [CollatzResearch.WordTrace]
  refine ⟨37257457583254713099510451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49676610111006284132680601 37257457583254713099510451)
  ·
    refine ⟨55886186374882069649265677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37257457583254713099510451 55886186374882069649265677)
    ·
      refine ⟨20957319890580776118474629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55886186374882069649265677 20957319890580776118474629)
      ·
        refine ⟨3929497479483895522213993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20957319890580776118474629 3929497479483895522213993)
        ·
          refine ⟨2947123109612921641660495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3929497479483895522213993 2947123109612921641660495)
          ·
            refine ⟨4420684664419382462490743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2947123109612921641660495 4420684664419382462490743)
            ·
              refine ⟨6631026996629073693736115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4420684664419382462490743 6631026996629073693736115)
              ·
                refine ⟨9946540494943610540604173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6631026996629073693736115 9946540494943610540604173)
                ·
                  refine ⟨3729952685603853952726565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9946540494943610540604173 3729952685603853952726565)
                  ·
                    refine ⟨699366128550722616136231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3729952685603853952726565 699366128550722616136231)
                    ·
                      rfl

theorem cell22_2043016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_2043016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043016 prefixEnd_2043016 := by exact prefixLift 2043016
  have htrace : WordTrace (prefixWord ++ tailWord_2043016) baseStart_2043016 baseEnd_2043016 := by
    simpa [prefixWord, tailWord_2043016, baseEnd_2043016] using wordTrace_append hprefix tailTrace_2043016
  have hstable : (prefixWord ++ tailWord_2043016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043016).length < 2 ^ (prefixWord ++ tailWord_2043016).sum := by decide
  have hdescent : baseEnd_2043016 < baseStart_2043016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043027 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 1, 6]
def baseStart_2043027 : Nat := 118140960795 + 2043027 * 2 ^ 59
def prefixEnd_2043027 : Nat := 4983230072969 + 3 ^ 40 * 2043027 * 2
def baseEnd_2043027 : Nat := 699369894075522254111197

theorem tailTrace_2043027 : CollatzResearch.WordTrace tailWord_2043027 prefixEnd_2043027 699369894075522254111197 := by
  unfold tailWord_2043027
  simp only [CollatzResearch.WordTrace]
  refine ⟨74515316369469575077671335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49676877579646383385114223 74515316369469575077671335)
  ·
    refine ⟨111772974554204362616507003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74515316369469575077671335 111772974554204362616507003)
    ·
      refine ⟨167659461831306543924760505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111772974554204362616507003 167659461831306543924760505)
      ·
        refine ⟨125744596373479907943570379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167659461831306543924760505 125744596373479907943570379)
        ·
          refine ⟨188616894560219861915355569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125744596373479907943570379 188616894560219861915355569)
          ·
            refine ⟨141462670920164896436516677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188616894560219861915355569 141462670920164896436516677)
            ·
              refine ⟨26524250797530918081846877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141462670920164896436516677 26524250797530918081846877)
              ·
                refine ⟨9946594049074094280692579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26524250797530918081846877 9946594049074094280692579)
                ·
                  refine ⟨14919891073611141421038869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9946594049074094280692579 14919891073611141421038869)
                  ·
                    refine ⟨699369894075522254111197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14919891073611141421038869 699369894075522254111197)
                    ·
                      rfl

theorem cell22_2043027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 6].length) (baseStart_2043027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043027 prefixEnd_2043027 := by exact prefixLift 2043027
  have htrace : WordTrace (prefixWord ++ tailWord_2043027) baseStart_2043027 baseEnd_2043027 := by
    simpa [prefixWord, tailWord_2043027, baseEnd_2043027] using wordTrace_append hprefix tailTrace_2043027
  have hstable : (prefixWord ++ tailWord_2043027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043027).length < 2 ^ (prefixWord ++ tailWord_2043027).sum := by decide
  have hdescent : baseEnd_2043027 < baseStart_2043027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043029 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 4, 3]
def baseStart_2043029 : Nat := 118140960795 + 2043029 * 2 ^ 59
def prefixEnd_2043029 : Nat := 4983230072969 + 3 ^ 40 * 2043029 * 2
def baseEnd_2043029 : Nat := 699370578716394915561191

theorem tailTrace_2043029 : CollatzResearch.WordTrace tailWord_2043029 prefixEnd_2043029 699370578716394915561191 := by
  unfold tailWord_2043029
  simp only [CollatzResearch.WordTrace]
  refine ⟨74515389315462329419244141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49676926210308219612829427 74515389315462329419244141)
  ·
    refine ⟨27943270993298373532216553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74515389315462329419244141 27943270993298373532216553)
    ·
      refine ⟨20957453244973780149162415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27943270993298373532216553 20957453244973780149162415)
      ·
        refine ⟨31436179867460670223743623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20957453244973780149162415 31436179867460670223743623)
        ·
          refine ⟨47154269801191005335615435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31436179867460670223743623 47154269801191005335615435)
          ·
            refine ⟨70731404701786508003423153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47154269801191005335615435 70731404701786508003423153)
            ·
              refine ⟨53048553526339881002567365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70731404701786508003423153 53048553526339881002567365)
              ·
                refine ⟨9946603786188727687981381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53048553526339881002567365 9946603786188727687981381)
                ·
                  refine ⟨1864988209910386441496509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9946603786188727687981381 1864988209910386441496509)
                  ·
                    refine ⟨699370578716394915561191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1864988209910386441496509 699370578716394915561191)
                    ·
                      rfl

theorem cell22_2043029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_2043029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043029 prefixEnd_2043029 := by exact prefixLift 2043029
  have htrace : WordTrace (prefixWord ++ tailWord_2043029) baseStart_2043029 baseEnd_2043029 := by
    simpa [prefixWord, tailWord_2043029, baseEnd_2043029] using wordTrace_append hprefix tailTrace_2043029
  have hstable : (prefixWord ++ tailWord_2043029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043029).length < 2 ^ (prefixWord ++ tailWord_2043029).sum := by decide
  have hdescent : baseEnd_2043029 < baseStart_2043029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043104 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 7]
def baseStart_2043104 : Nat := 118140960795 + 2043104 * 2 ^ 59
def prefixEnd_2043104 : Nat := 4983230072969 + 3 ^ 40 * 2043104 * 2
def baseEnd_2043104 : Nat := 233132084249706573311987

theorem tailTrace_2043104 : CollatzResearch.WordTrace tailWord_2043104 prefixEnd_2043104 233132084249706573311987 := by
  unfold tailWord_2043104
  simp only [CollatzResearch.WordTrace]
  refine ⟨37259062395095308614112183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49678749860127078152149577 37259062395095308614112183)
  ·
    refine ⟨55888593592642962921168275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37259062395095308614112183 55888593592642962921168275)
    ·
      refine ⟨83832890388964444381752413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55888593592642962921168275 83832890388964444381752413)
      ·
        refine ⟨31437333895861666643157155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83832890388964444381752413 31437333895861666643157155)
        ·
          refine ⟨47156000843792499964735733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31437333895861666643157155 47156000843792499964735733)
          ·
            refine ⟨4420875079105546871693975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47156000843792499964735733 4420875079105546871693975)
            ·
              refine ⟨6631312618658320307540963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4420875079105546871693975 6631312618658320307540963)
              ·
                refine ⟨9946968927987480461311445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6631312618658320307540963 9946968927987480461311445)
                ·
                  refine ⟨233132084249706573311987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9946968927987480461311445 233132084249706573311987)
                  ·
                    rfl

theorem cell22_2043104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 7].length) (baseStart_2043104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043104 prefixEnd_2043104 := by exact prefixLift 2043104
  have htrace : WordTrace (prefixWord ++ tailWord_2043104) baseStart_2043104 baseEnd_2043104 := by
    simpa [prefixWord, tailWord_2043104, baseEnd_2043104] using wordTrace_append hprefix tailTrace_2043104
  have hstable : (prefixWord ++ tailWord_2043104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043104).length < 2 ^ (prefixWord ++ tailWord_2043104).sum := by decide
  have hdescent : baseEnd_2043104 < baseStart_2043104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043108 : List Nat := [2, 3, 1, 1, 1, 2, 4, 4, 1, 3]
def baseStart_2043108 : Nat := 118140960795 + 2043108 * 2 ^ 59
def prefixEnd_2043108 : Nat := 4983230072969 + 3 ^ 40 * 2043108 * 2
def baseEnd_2043108 : Nat := 699397622030865042835949

theorem tailTrace_2043108 : CollatzResearch.WordTrace tailWord_2043108 prefixEnd_2043108 699397622030865042835949 := by
  unfold tailWord_2043108
  simp only [CollatzResearch.WordTrace]
  refine ⟨37259135341088062955684989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49678847121450750607579985 37259135341088062955684989)
  ·
    refine ⟨13972175752908023608381871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37259135341088062955684989 13972175752908023608381871)
    ·
      refine ⟨20958263629362035412572807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13972175752908023608381871 20958263629362035412572807)
      ·
        refine ⟨31437395444043053118859211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20958263629362035412572807 31437395444043053118859211)
        ·
          refine ⟨47156093166064579678288817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31437395444043053118859211 47156093166064579678288817)
          ·
            refine ⟨35367069874548434758716613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47156093166064579678288817 35367069874548434758716613)
            ·
              refine ⟨6631325601477831517259365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35367069874548434758716613 6631325601477831517259365)
              ·
                refine ⟨1243373550277093409486131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6631325601477831517259365 1243373550277093409486131)
                ·
                  refine ⟨1865060325415640114229197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243373550277093409486131 1865060325415640114229197)
                  ·
                    refine ⟨699397622030865042835949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1865060325415640114229197 699397622030865042835949)
                    ·
                      rfl

theorem cell22_2043108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_2043108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043108 prefixEnd_2043108 := by exact prefixLift 2043108
  have htrace : WordTrace (prefixWord ++ tailWord_2043108) baseStart_2043108 baseEnd_2043108 := by
    simpa [prefixWord, tailWord_2043108, baseEnd_2043108] using wordTrace_append hprefix tailTrace_2043108
  have hstable : (prefixWord ++ tailWord_2043108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043108).length < 2 ^ (prefixWord ++ tailWord_2043108).sum := by decide
  have hdescent : baseEnd_2043108 < baseStart_2043108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043194 : List Nat := [3, 1, 1, 1, 4, 1, 1, 10]
def baseStart_2043194 : Nat := 118140960795 + 2043194 * 2 ^ 59
def prefixEnd_2043194 : Nat := 4983230072969 + 3 ^ 40 * 2043194 * 2
def baseEnd_2043194 : Nat := 77714117954265498353965

theorem tailTrace_2043194 : CollatzResearch.WordTrace tailWord_2043194 prefixEnd_2043194 77714117954265498353965 := by
  unfold tailWord_2043194
  simp only [CollatzResearch.WordTrace]
  refine ⟨18630351839966140649750159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49680938239909708399333757 18630351839966140649750159)
  ·
    refine ⟨27945527759949210974625239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18630351839966140649750159 27945527759949210974625239)
    ·
      refine ⟨41918291639923816461937859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27945527759949210974625239 41918291639923816461937859)
      ·
        refine ⟨62877437459885724692906789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41918291639923816461937859 62877437459885724692906789)
        ·
          refine ⟨11789519523728573379920023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62877437459885724692906789 11789519523728573379920023)
          ·
            refine ⟨17684279285592860069880035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11789519523728573379920023 17684279285592860069880035)
            ·
              refine ⟨26526418928389290104820053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17684279285592860069880035 26526418928389290104820053)
              ·
                refine ⟨77714117954265498353965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26526418928389290104820053 77714117954265498353965)
                ·
                  rfl

theorem cell22_2043194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 10].length) (baseStart_2043194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043194 prefixEnd_2043194 := by exact prefixLift 2043194
  have htrace : WordTrace (prefixWord ++ tailWord_2043194) baseStart_2043194 baseEnd_2043194 := by
    simpa [prefixWord, tailWord_2043194, baseEnd_2043194] using wordTrace_append hprefix tailTrace_2043194
  have hstable : (prefixWord ++ tailWord_2043194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043194).length < 2 ^ (prefixWord ++ tailWord_2043194).sum := by decide
  have hdescent : baseEnd_2043194 < baseStart_2043194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043196 : List Nat := [2, 2, 2, 2, 1, 3, 1, 3, 2, 4]
def baseStart_2043196 : Nat := 118140960795 + 2043196 * 2 ^ 59
def prefixEnd_2043196 : Nat := 4983230072969 + 3 ^ 40 * 2043196 * 2
def baseEnd_2043196 : Nat := 699427746229262146635679

theorem tailTrace_2043196 : CollatzResearch.WordTrace tailWord_2043196 prefixEnd_2043196 699427746229262146635679 := by
  unfold tailWord_2043196
  simp only [CollatzResearch.WordTrace]
  refine ⟨37260740152928658470286721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49680986870571544627048961 37260740152928658470286721)
  ·
    refine ⟨27945555114696493852715041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37260740152928658470286721 27945555114696493852715041)
    ·
      refine ⟨20959166336022370389536281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27945555114696493852715041 20959166336022370389536281)
      ·
        refine ⟨15719374752016777792152211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20959166336022370389536281 15719374752016777792152211)
        ·
          refine ⟨23579062128025166688228317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15719374752016777792152211 23579062128025166688228317)
          ·
            refine ⟨8842148298009437508085619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23579062128025166688228317 8842148298009437508085619)
            ·
              refine ⟨13263222447014156262128429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8842148298009437508085619 13263222447014156262128429)
              ·
                refine ⟨4973708417630308598298161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13263222447014156262128429 4973708417630308598298161)
                ·
                  refine ⟨3730281313222731448723621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4973708417630308598298161 3730281313222731448723621)
                  ·
                    refine ⟨699427746229262146635679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3730281313222731448723621 699427746229262146635679)
                    ·
                      rfl

theorem cell22_2043196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_2043196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043196 prefixEnd_2043196 := by exact prefixLift 2043196
  have htrace : WordTrace (prefixWord ++ tailWord_2043196) baseStart_2043196 baseEnd_2043196 := by
    simpa [prefixWord, tailWord_2043196, baseEnd_2043196] using wordTrace_append hprefix tailTrace_2043196
  have hstable : (prefixWord ++ tailWord_2043196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043196).length < 2 ^ (prefixWord ++ tailWord_2043196).sum := by decide
  have hdescent : baseEnd_2043196 < baseStart_2043196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043224 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 1, 8]
def baseStart_2043224 : Nat := 118140960795 + 2043224 * 2 ^ 59
def prefixEnd_2043224 : Nat := 4983230072969 + 3 ^ 40 * 2043224 * 2
def baseEnd_2043224 : Nat := 699437331201479406935593

theorem tailTrace_2043224 : CollatzResearch.WordTrace tailWord_2043224 prefixEnd_2043224 699437331201479406935593 := by
  unfold tailWord_2043224
  simp only [CollatzResearch.WordTrace]
  refine ⟨37261250774877938861296363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49681667699837251815061817 37261250774877938861296363)
  ·
    refine ⟨55891876162316908291944545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37261250774877938861296363 55891876162316908291944545)
    ·
      refine ⟨41918907121737681218958409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55891876162316908291944545 41918907121737681218958409)
      ·
        refine ⟨31439180341303260914218807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41918907121737681218958409 31439180341303260914218807)
        ·
          refine ⟨47158770511954891371328211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31439180341303260914218807 47158770511954891371328211)
          ·
            refine ⟨70738155767932337056992317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47158770511954891371328211 70738155767932337056992317)
            ·
              refine ⟨26526808412974626396372119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70738155767932337056992317 26526808412974626396372119)
              ·
                refine ⟨39790212619461939594558179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26526808412974626396372119 39790212619461939594558179)
                ·
                  refine ⟨59685318929192909391837269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39790212619461939594558179 59685318929192909391837269)
                  ·
                    refine ⟨699437331201479406935593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59685318929192909391837269 699437331201479406935593)
                    ·
                      rfl

theorem cell22_2043224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_2043224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043224 prefixEnd_2043224 := by exact prefixLift 2043224
  have htrace : WordTrace (prefixWord ++ tailWord_2043224) baseStart_2043224 baseEnd_2043224 := by
    simpa [prefixWord, tailWord_2043224, baseEnd_2043224] using wordTrace_append hprefix tailTrace_2043224
  have hstable : (prefixWord ++ tailWord_2043224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043224).length < 2 ^ (prefixWord ++ tailWord_2043224).sum := by decide
  have hdescent : baseEnd_2043224 < baseStart_2043224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043260 : List Nat := [2, 2, 2, 1, 1, 1, 6, 3, 1, 3]
def baseStart_2043260 : Nat := 118140960795 + 2043260 * 2 ^ 59
def prefixEnd_2043260 : Nat := 4983230072969 + 3 ^ 40 * 2043260 * 2
def baseEnd_2043260 : Nat := 699449654737187313035483

theorem tailTrace_2043260 : CollatzResearch.WordTrace tailWord_2043260 prefixEnd_2043260 699449654737187313035483 := by
  unfold tailWord_2043260
  simp only [CollatzResearch.WordTrace]
  refine ⟨37261907288812727935451617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49682543051750303913935489 37261907288812727935451617)
  ·
    refine ⟨27946430466609545951588713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37261907288812727935451617 27946430466609545951588713)
    ·
      refine ⟨20959822849957159463691535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27946430466609545951588713 20959822849957159463691535)
      ·
        refine ⟨31439734274935739195537303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20959822849957159463691535 31439734274935739195537303)
        ·
          refine ⟨47159601412403608793305955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31439734274935739195537303 47159601412403608793305955)
          ·
            refine ⟨70739402118605413189958933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47159601412403608793305955 70739402118605413189958933)
            ·
              refine ⟨3315909474309628743279325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70739402118605413189958933 3315909474309628743279325)
              ·
                refine ⟨1243466052866110778729747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3315909474309628743279325 1243466052866110778729747)
                ·
                  refine ⟨1865199079299166168094621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243466052866110778729747 1865199079299166168094621)
                  ·
                    refine ⟨699449654737187313035483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1865199079299166168094621 699449654737187313035483)
                    ·
                      rfl

theorem cell22_2043260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_2043260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043260 prefixEnd_2043260 := by exact prefixLift 2043260
  have htrace : WordTrace (prefixWord ++ tailWord_2043260) baseStart_2043260 baseEnd_2043260 := by
    simpa [prefixWord, tailWord_2043260, baseEnd_2043260] using wordTrace_append hprefix tailTrace_2043260
  have hstable : (prefixWord ++ tailWord_2043260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043260).length < 2 ^ (prefixWord ++ tailWord_2043260).sum := by decide
  have hdescent : baseEnd_2043260 < baseStart_2043260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043271 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 2, 5]
def baseStart_2043271 : Nat := 118140960795 + 2043271 * 2 ^ 59
def prefixEnd_2043271 : Nat := 4983230072969 + 3 ^ 40 * 2043271 * 2
def baseEnd_2043271 : Nat := 699453420261986951010449

theorem tailTrace_2043271 : CollatzResearch.WordTrace tailWord_2043271 prefixEnd_2043271 699453420261986951010449 := by
  unfold tailWord_2043271
  simp only [CollatzResearch.WordTrace]
  refine ⟨74524215780585604749553667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49682810520390403166369111 74524215780585604749553667)
  ·
    refine ⟨111786323670878407124330501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74524215780585604749553667 111786323670878407124330501)
    ·
      refine ⟨20959935688289701335811969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111786323670878407124330501 20959935688289701335811969)
      ·
        refine ⟨15719951766217276001858977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20959935688289701335811969 15719951766217276001858977)
        ·
          refine ⟨11789963824662957001394233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15719951766217276001858977 11789963824662957001394233)
          ·
            refine ⟨8842472868497217751045675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11789963824662957001394233 8842472868497217751045675)
            ·
              refine ⟨13263709302745826626568513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8842472868497217751045675 13263709302745826626568513)
              ·
                refine ⟨9947781977059369969926385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13263709302745826626568513 9947781977059369969926385)
                ·
                  refine ⟨7460836482794527477444789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9947781977059369969926385 7460836482794527477444789)
                  ·
                    refine ⟨699453420261986951010449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7460836482794527477444789 699453420261986951010449)
                    ·
                      rfl

theorem cell22_2043271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_2043271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043271 prefixEnd_2043271 := by exact prefixLift 2043271
  have htrace : WordTrace (prefixWord ++ tailWord_2043271) baseStart_2043271 baseEnd_2043271 := by
    simpa [prefixWord, tailWord_2043271, baseEnd_2043271] using wordTrace_append hprefix tailTrace_2043271
  have hstable : (prefixWord ++ tailWord_2043271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043271).length < 2 ^ (prefixWord ++ tailWord_2043271).sum := by decide
  have hdescent : baseEnd_2043271 < baseStart_2043271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043331 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 4, 4]
def baseStart_2043331 : Nat := 118140960795 + 2043331 * 2 ^ 59
def prefixEnd_2043331 : Nat := 4983230072969 + 3 ^ 40 * 2043331 * 2
def baseEnd_2043331 : Nat := 699473959488166794510265

theorem tailTrace_2043331 : CollatzResearch.WordTrace tailWord_2043331 prefixEnd_2043331 699473959488166794510265 := by
  unfold tailWord_2043331
  simp only [CollatzResearch.WordTrace]
  refine ⟨74526404160368234996737847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49684269440245489997825231 74526404160368234996737847)
  ·
    refine ⟨111789606240552352495106771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74526404160368234996737847 111789606240552352495106771)
    ·
      refine ⟨167684409360828528742660157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111789606240552352495106771 167684409360828528742660157)
      ·
        refine ⟨62881653510310698278497559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167684409360828528742660157 62881653510310698278497559)
        ·
          refine ⟨94322480265466047417746339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62881653510310698278497559 94322480265466047417746339)
          ·
            refine ⟨141483720398199071126619509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94322480265466047417746339 141483720398199071126619509)
            ·
              refine ⟨13264098787331162918120579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141483720398199071126619509 13264098787331162918120579)
              ·
                refine ⟨19896148180996744377180869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13264098787331162918120579 19896148180996744377180869)
                ·
                  refine ⟨3730527783936889570721413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19896148180996744377180869 3730527783936889570721413)
                  ·
                    refine ⟨699473959488166794510265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3730527783936889570721413 699473959488166794510265)
                    ·
                      rfl

theorem cell22_2043331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 4].length) (baseStart_2043331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043331 prefixEnd_2043331 := by exact prefixLift 2043331
  have htrace : WordTrace (prefixWord ++ tailWord_2043331) baseStart_2043331 baseEnd_2043331 := by
    simpa [prefixWord, tailWord_2043331, baseEnd_2043331] using wordTrace_append hprefix tailTrace_2043331
  have hstable : (prefixWord ++ tailWord_2043331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043331).length < 2 ^ (prefixWord ++ tailWord_2043331).sum := by decide
  have hdescent : baseEnd_2043331 < baseStart_2043331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043335 : List Nat := [1, 1, 4, 1, 1, 3, 5, 2, 4]
def baseStart_2043335 : Nat := 118140960795 + 2043335 * 2 ^ 59
def prefixEnd_2043335 : Nat := 4983230072969 + 3 ^ 40 * 2043335 * 2
def baseEnd_2043335 : Nat := 233158442923304039136751

theorem tailTrace_2043335 : CollatzResearch.WordTrace tailWord_2043335 prefixEnd_2043335 233158442923304039136751 := by
  unfold tailWord_2043335
  simp only [CollatzResearch.WordTrace]
  refine ⟨74526550052353743679883459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49684366701569162453255639 74526550052353743679883459)
  ·
    refine ⟨111789825078530615519825189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74526550052353743679883459 111789825078530615519825189)
    ·
      refine ⟨20960592202224490409967223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111789825078530615519825189 20960592202224490409967223)
      ·
        refine ⟨31440888303336735614950835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20960592202224490409967223 31440888303336735614950835)
        ·
          refine ⟨47161332455005103422426253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31440888303336735614950835 47161332455005103422426253)
          ·
            refine ⟨17685499670626913783409845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47161332455005103422426253 17685499670626913783409845)
            ·
              refine ⟨1658015594121273167194673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17685499670626913783409845 1658015594121273167194673)
              ·
                refine ⟨1243511695590954875396005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1658015594121273167194673 1243511695590954875396005)
                ·
                  refine ⟨233158442923304039136751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1243511695590954875396005 233158442923304039136751)
                  ·
                    rfl

theorem cell22_2043335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 4].length) (baseStart_2043335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043335 prefixEnd_2043335 := by exact prefixLift 2043335
  have htrace : WordTrace (prefixWord ++ tailWord_2043335) baseStart_2043335 baseEnd_2043335 := by
    simpa [prefixWord, tailWord_2043335, baseEnd_2043335] using wordTrace_append hprefix tailTrace_2043335
  have hstable : (prefixWord ++ tailWord_2043335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043335).length < 2 ^ (prefixWord ++ tailWord_2043335).sum := by decide
  have hdescent : baseEnd_2043335 < baseStart_2043335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043365 : List Nat := [1, 3, 1, 5, 1, 2, 2, 1, 2, 4]
def baseStart_2043365 : Nat := 118140960795 + 2043365 * 2 ^ 59
def prefixEnd_2043365 : Nat := 4983230072969 + 3 ^ 40 * 2043365 * 2
def baseEnd_2043365 : Nat := 699485598383002039160161

theorem tailTrace_2043365 : CollatzResearch.WordTrace tailWord_2043365 prefixEnd_2043365 699485598383002039160161 := by
  unfold tailWord_2043365
  simp only [CollatzResearch.WordTrace]
  refine ⟨74527644242245058803475549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49685096161496705868983699 74527644242245058803475549)
  ·
    refine ⟨27947866590841897051303331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74527644242245058803475549 27947866590841897051303331)
    ·
      refine ⟨41921799886262845576954997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27947866590841897051303331 41921799886262845576954997)
      ·
        refine ⟨3930168739337141772839531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41921799886262845576954997 3930168739337141772839531)
        ·
          refine ⟨5895253109005712659259297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3930168739337141772839531 5895253109005712659259297)
          ·
            refine ⟨4421439831754284494444473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5895253109005712659259297 4421439831754284494444473)
            ·
              refine ⟨3316079873815713370833355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4421439831754284494444473 3316079873815713370833355)
              ·
                refine ⟨4974119810723570056250033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3316079873815713370833355 4974119810723570056250033)
                ·
                  refine ⟨3730589858042677542187525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4974119810723570056250033 3730589858042677542187525)
                  ·
                    refine ⟨699485598383002039160161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3730589858042677542187525 699485598383002039160161)
                    ·
                      rfl

theorem cell22_2043365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_2043365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043365 prefixEnd_2043365 := by exact prefixLift 2043365
  have htrace : WordTrace (prefixWord ++ tailWord_2043365) baseStart_2043365 baseEnd_2043365 := by
    simpa [prefixWord, tailWord_2043365, baseEnd_2043365] using wordTrace_append hprefix tailTrace_2043365
  have hstable : (prefixWord ++ tailWord_2043365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043365).length < 2 ^ (prefixWord ++ tailWord_2043365).sum := by decide
  have hdescent : baseEnd_2043365 < baseStart_2043365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043498 : List Nat := [3, 1, 3, 2, 1, 2, 10]
def baseStart_2043498 : Nat := 118140960795 + 2043498 * 2 ^ 59
def prefixEnd_2043498 : Nat := 4983230072969 + 3 ^ 40 * 2043498 * 2
def baseEnd_2043498 : Nat := 25908560259297556503139

theorem tailTrace_2043498 : CollatzResearch.WordTrace tailWord_2043498 prefixEnd_2043498 25908560259297556503139 := by
  unfold tailWord_2043498
  simp only [CollatzResearch.WordTrace]
  refine ⟨18633123787690805629516787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49688330100508815012044765 18633123787690805629516787)
  ·
    refine ⟨27949685681536208444275181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18633123787690805629516787 27949685681536208444275181)
    ·
      refine ⟨10481132130576078166603193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27949685681536208444275181 10481132130576078166603193)
      ·
        refine ⟨7860849097932058624952395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10481132130576078166603193 7860849097932058624952395)
        ·
          refine ⟨11791273646898087937428593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7860849097932058624952395 11791273646898087937428593)
          ·
            refine ⟨8843455235173565953071445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11791273646898087937428593 8843455235173565953071445)
            ·
              refine ⟨25908560259297556503139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8843455235173565953071445 25908560259297556503139)
              ·
                rfl

theorem cell22_2043498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 10].length) (baseStart_2043498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043498 prefixEnd_2043498 := by exact prefixLift 2043498
  have htrace : WordTrace (prefixWord ++ tailWord_2043498) baseStart_2043498 baseEnd_2043498 := by
    simpa [prefixWord, tailWord_2043498, baseEnd_2043498] using wordTrace_append hprefix tailTrace_2043498
  have hstable : (prefixWord ++ tailWord_2043498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043498).length < 2 ^ (prefixWord ++ tailWord_2043498).sum := by decide
  have hdescent : baseEnd_2043498 < baseStart_2043498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043575 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 2, 5]
def baseStart_2043575 : Nat := 118140960795 + 2043575 * 2 ^ 59
def prefixEnd_2043575 : Nat := 4983230072969 + 3 ^ 40 * 2043575 * 2
def baseEnd_2043575 : Nat := 699557485674631491409517

theorem tailTrace_2043575 : CollatzResearch.WordTrace tailWord_2043575 prefixEnd_2043575 699557485674631491409517 := by
  unfold tailWord_2043575
  simp only [CollatzResearch.WordTrace]
  refine ⟨74535303571484264668620179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49690202380989509779080119 74535303571484264668620179)
  ·
    refine ⟨111802955357226397002930269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74535303571484264668620179 111802955357226397002930269)
    ·
      refine ⟨41926108258959898876098851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111802955357226397002930269 41926108258959898876098851)
      ·
        refine ⟨62889162388439848314148277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41926108258959898876098851 62889162388439848314148277)
        ·
          refine ⟨5895858973916235779451401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62889162388439848314148277 5895858973916235779451401)
          ·
            refine ⟨4421894230437176834588551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5895858973916235779451401 4421894230437176834588551)
            ·
              refine ⟨6632841345655765251882827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4421894230437176834588551 6632841345655765251882827)
              ·
                refine ⟨9949262018483647877824241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6632841345655765251882827 9949262018483647877824241)
                ·
                  refine ⟨7461946513862735908368181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9949262018483647877824241 7461946513862735908368181)
                  ·
                    refine ⟨699557485674631491409517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7461946513862735908368181 699557485674631491409517)
                    ·
                      rfl

theorem cell22_2043575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_2043575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043575 prefixEnd_2043575 := by exact prefixLift 2043575
  have htrace : WordTrace (prefixWord ++ tailWord_2043575) baseStart_2043575 baseEnd_2043575 := by
    simpa [prefixWord, tailWord_2043575, baseEnd_2043575] using wordTrace_append hprefix tailTrace_2043575
  have hstable : (prefixWord ++ tailWord_2043575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043575).length < 2 ^ (prefixWord ++ tailWord_2043575).sum := by decide
  have hdescent : baseEnd_2043575 < baseStart_2043575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043603 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 7, 5]
def baseStart_2043603 : Nat := 118140960795 + 2043603 * 2 ^ 59
def prefixEnd_2043603 : Nat := 4983230072969 + 3 ^ 40 * 2043603 * 2
def baseEnd_2043603 : Nat := 699567070646848751709431

theorem tailTrace_2043603 : CollatzResearch.WordTrace tailWord_2043603 prefixEnd_2043603 699567070646848751709431 := by
  unfold tailWord_2043603
  simp only [CollatzResearch.WordTrace]
  refine ⟨74536324815382825450639463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49690883210255216967092975 74536324815382825450639463)
  ·
    refine ⟨111804487223074238175959195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74536324815382825450639463 111804487223074238175959195)
    ·
      refine ⟨167706730834611357263938793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111804487223074238175959195 167706730834611357263938793)
      ·
        refine ⟨125780048125958517947954095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167706730834611357263938793 125780048125958517947954095)
        ·
          refine ⟨188670072188937776921931143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125780048125958517947954095 188670072188937776921931143)
          ·
            refine ⟨283005108283406665382896715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188670072188937776921931143 283005108283406665382896715)
            ·
              refine ⟨424507662425109998074345073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283005108283406665382896715 424507662425109998074345073)
              ·
                refine ⟨318380746818832498555758805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424507662425109998074345073 318380746818832498555758805)
                ·
                  refine ⟨7462048753566386684900597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 318380746818832498555758805 7462048753566386684900597)
                  ·
                    refine ⟨699567070646848751709431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7462048753566386684900597 699567070646848751709431)
                    ·
                      rfl

theorem cell22_2043603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 5].length) (baseStart_2043603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043603 prefixEnd_2043603 := by exact prefixLift 2043603
  have htrace : WordTrace (prefixWord ++ tailWord_2043603) baseStart_2043603 baseEnd_2043603 := by
    simpa [prefixWord, tailWord_2043603, baseEnd_2043603] using wordTrace_append hprefix tailTrace_2043603
  have hstable : (prefixWord ++ tailWord_2043603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043603).length < 2 ^ (prefixWord ++ tailWord_2043603).sum := by decide
  have hdescent : baseEnd_2043603 < baseStart_2043603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043680 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 2, 6]
def baseStart_2043680 : Nat := 118140960795 + 2043680 * 2 ^ 59
def prefixEnd_2043680 : Nat := 4983230072969 + 3 ^ 40 * 2043680 * 2
def baseEnd_2043680 : Nat := 699593429320446217534195

theorem tailTrace_2043680 : CollatzResearch.WordTrace tailWord_2043680 prefixEnd_2043680 699593429320446217534195 := by
  unfold tailWord_2043680
  simp only [CollatzResearch.WordTrace]
  refine ⟨37269566618051933800596247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49692755490735911734128329 37269566618051933800596247)
  ·
    refine ⟨55904349927077900700894371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37269566618051933800596247 55904349927077900700894371)
    ·
      refine ⟨83856524890616851051341557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55904349927077900700894371 83856524890616851051341557)
      ·
        refine ⟨7861549208495329786063271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83856524890616851051341557 7861549208495329786063271)
        ·
          refine ⟨11792323812742994679094907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7861549208495329786063271 11792323812742994679094907)
          ·
            refine ⟨17688485719114492018642361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11792323812742994679094907 17688485719114492018642361)
            ·
              refine ⟨13266364289335869013981771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17688485719114492018642361 13266364289335869013981771)
              ·
                refine ⟨19899546434003803520972657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13266364289335869013981771 19899546434003803520972657)
                ·
                  refine ⟨14924659825502852640729493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19899546434003803520972657 14924659825502852640729493)
                  ·
                    refine ⟨699593429320446217534195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14924659825502852640729493 699593429320446217534195)
                    ·
                      rfl

theorem cell22_2043680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_2043680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043680 prefixEnd_2043680 := by exact prefixLift 2043680
  have htrace : WordTrace (prefixWord ++ tailWord_2043680) baseStart_2043680 baseEnd_2043680 := by
    simpa [prefixWord, tailWord_2043680, baseEnd_2043680] using wordTrace_append hprefix tailTrace_2043680
  have hstable : (prefixWord ++ tailWord_2043680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043680).length < 2 ^ (prefixWord ++ tailWord_2043680).sum := by decide
  have hdescent : baseEnd_2043680 < baseStart_2043680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043695 : List Nat := [1, 1, 2, 1, 2, 1, 2, 7, 5]
def baseStart_2043695 : Nat := 118140960795 + 2043695 * 2 ^ 59
def prefixEnd_2043695 : Nat := 4983230072969 + 3 ^ 40 * 2043695 * 2
def baseEnd_2043695 : Nat := 233199521375663726136383

theorem tailTrace_2043695 : CollatzResearch.WordTrace tailWord_2043695 prefixEnd_2043695 233199521375663726136383 := by
  unfold tailWord_2043695
  simp only [CollatzResearch.WordTrace]
  refine ⟨74539680331049525162988539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49693120220699683441992359 74539680331049525162988539)
  ·
    refine ⟨111809520496574287744482809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74539680331049525162988539 111809520496574287744482809)
    ·
      refine ⟨83857140372430715808362107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111809520496574287744482809 83857140372430715808362107)
      ·
        refine ⟨125785710558646073712543161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83857140372430715808362107 125785710558646073712543161)
        ·
          refine ⟨94339282918984555284407371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125785710558646073712543161 94339282918984555284407371)
          ·
            refine ⟨141508924378476832926611057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94339282918984555284407371 141508924378476832926611057)
            ·
              refine ⟨106131693283857624694958293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141508924378476832926611057 106131693283857624694958293)
              ·
                refine ⟨2487461561340413078788085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 106131693283857624694958293 2487461561340413078788085)
                ·
                  refine ⟨233199521375663726136383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2487461561340413078788085 233199521375663726136383)
                  ·
                    rfl

theorem cell22_2043695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 5].length) (baseStart_2043695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043695 prefixEnd_2043695 := by exact prefixLift 2043695
  have htrace : WordTrace (prefixWord ++ tailWord_2043695) baseStart_2043695 baseEnd_2043695 := by
    simpa [prefixWord, tailWord_2043695, baseEnd_2043695] using wordTrace_append hprefix tailTrace_2043695
  have hstable : (prefixWord ++ tailWord_2043695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043695).length < 2 ^ (prefixWord ++ tailWord_2043695).sum := by decide
  have hdescent : baseEnd_2043695 < baseStart_2043695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043733 : List Nat := [1, 3, 2, 2, 2, 4, 2, 2, 1, 3]
def baseStart_2043733 : Nat := 118140960795 + 2043733 * 2 ^ 59
def prefixEnd_2043733 : Nat := 4983230072969 + 3 ^ 40 * 2043733 * 2
def baseEnd_2043733 : Nat := 699611572303571745959033

theorem tailTrace_2043733 : CollatzResearch.WordTrace tailWord_2043733 prefixEnd_2043733 699611572303571745959033 := by
  unfold tailWord_2043733
  simp only [CollatzResearch.WordTrace]
  refine ⟨74541066304911857652871853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49694044203274571768581235 74541066304911857652871853)
  ·
    refine ⟨27952899864341946619826945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74541066304911857652871853 27952899864341946619826945)
    ·
      refine ⟨20964674898256459964870209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27952899864341946619826945 20964674898256459964870209)
      ·
        refine ⟨15723506173692344973652657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20964674898256459964870209 15723506173692344973652657)
        ·
          refine ⟨11792629630269258730239493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15723506173692344973652657 11792629630269258730239493)
          ·
            refine ⟨2211118055675486011919905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11792629630269258730239493 2211118055675486011919905)
            ·
              refine ⟨1658338541756614508939929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2211118055675486011919905 1658338541756614508939929)
              ·
                refine ⟨1243753906317460881704947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1658338541756614508939929 1243753906317460881704947)
                ·
                  refine ⟨1865630859476191322557421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243753906317460881704947 1865630859476191322557421)
                  ·
                    refine ⟨699611572303571745959033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1865630859476191322557421 699611572303571745959033)
                    ·
                      rfl

theorem cell22_2043733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_2043733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043733 prefixEnd_2043733 := by exact prefixLift 2043733
  have htrace : WordTrace (prefixWord ++ tailWord_2043733) baseStart_2043733 baseEnd_2043733 := by
    simpa [prefixWord, tailWord_2043733, baseEnd_2043733] using wordTrace_append hprefix tailTrace_2043733
  have hstable : (prefixWord ++ tailWord_2043733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043733).length < 2 ^ (prefixWord ++ tailWord_2043733).sum := by decide
  have hdescent : baseEnd_2043733 < baseStart_2043733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043785 : List Nat := [1, 2, 1, 1, 5, 1, 11]
def baseStart_2043785 : Nat := 118140960795 + 2043785 * 2 ^ 59
def prefixEnd_2043785 : Nat := 4983230072969 + 3 ^ 40 * 2043785 * 2
def baseEnd_2043785 : Nat := 25912198998750405320699

theorem tailTrace_2043785 : CollatzResearch.WordTrace tailWord_2043785 prefixEnd_2043785 25912198998750405320699 := by
  unfold tailWord_2043785
  simp only [CollatzResearch.WordTrace]
  refine ⟨74542962900723470533764809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49695308600482313689176539 74542962900723470533764809)
  ·
    refine ⟨55907222175542602900323607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74542962900723470533764809 55907222175542602900323607)
    ·
      refine ⟨83860833263313904350485411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55907222175542602900323607 83860833263313904350485411)
      ·
        refine ⟨125791249894970856525728117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83860833263313904350485411 125791249894970856525728117)
        ·
          refine ⟨11792929677653517799287011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125791249894970856525728117 11792929677653517799287011)
          ·
            refine ⟨17689394516480276698930517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11792929677653517799287011 17689394516480276698930517)
            ·
              refine ⟨25912198998750405320699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17689394516480276698930517 25912198998750405320699)
              ·
                rfl

theorem cell22_2043785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 11].length) (baseStart_2043785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043785 prefixEnd_2043785 := by exact prefixLift 2043785
  have htrace : WordTrace (prefixWord ++ tailWord_2043785) baseStart_2043785 baseEnd_2043785 := by
    simpa [prefixWord, tailWord_2043785, baseEnd_2043785] using wordTrace_append hprefix tailTrace_2043785
  have hstable : (prefixWord ++ tailWord_2043785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043785).length < 2 ^ (prefixWord ++ tailWord_2043785).sum := by decide
  have hdescent : baseEnd_2043785 < baseStart_2043785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043817 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 5, 3]
def baseStart_2043817 : Nat := 118140960795 + 2043817 * 2 ^ 59
def prefixEnd_2043817 : Nat := 4983230072969 + 3 ^ 40 * 2043817 * 2
def baseEnd_2043817 : Nat := 699640327220223526858775

theorem tailTrace_2043817 : CollatzResearch.WordTrace tailWord_2043817 prefixEnd_2043817 699640327220223526858775 := by
  unfold tailWord_2043817
  simp only [CollatzResearch.WordTrace]
  refine ⟨74544130036607539998929705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49696086691071693332619803 74544130036607539998929705)
  ·
    refine ⟨55908097527455654999197279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74544130036607539998929705 55908097527455654999197279)
    ·
      refine ⟨83862146291183482498795919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55908097527455654999197279 83862146291183482498795919)
      ·
        refine ⟨125793219436775223748193879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83862146291183482498795919 125793219436775223748193879)
        ·
          refine ⟨188689829155162835622290819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125793219436775223748193879 188689829155162835622290819)
          ·
            refine ⟨283034743732744253433436229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188689829155162835622290819 283034743732744253433436229)
            ·
              refine ⟨53069014449889547518769293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 283034743732744253433436229 53069014449889547518769293)
              ·
                refine ⟨19900880418708580319538485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53069014449889547518769293 19900880418708580319538485)
                ·
                  refine ⟨1865707539253929404956733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19900880418708580319538485 1865707539253929404956733)
                  ·
                    refine ⟨699640327220223526858775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1865707539253929404956733 699640327220223526858775)
                    ·
                      rfl

theorem cell22_2043817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 3].length) (baseStart_2043817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043817 prefixEnd_2043817 := by exact prefixLift 2043817
  have htrace : WordTrace (prefixWord ++ tailWord_2043817) baseStart_2043817 baseEnd_2043817 := by
    simpa [prefixWord, tailWord_2043817, baseEnd_2043817] using wordTrace_append hprefix tailTrace_2043817
  have hstable : (prefixWord ++ tailWord_2043817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043817).length < 2 ^ (prefixWord ++ tailWord_2043817).sum := by decide
  have hdescent : baseEnd_2043817 < baseStart_2043817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043836 : List Nat := [2, 2, 2, 5, 2, 1, 8]
def baseStart_2043836 : Nat := 118140960795 + 2043836 * 2 ^ 59
def prefixEnd_2043836 : Nat := 4983230072969 + 3 ^ 40 * 2043836 * 2
def baseEnd_2043836 : Nat := 25912845604019030023471

theorem tailTrace_2043836 : CollatzResearch.WordTrace tailWord_2043836 prefixEnd_2043836 25912845604019030023471 := by
  unfold tailWord_2043836
  simp only [CollatzResearch.WordTrace]
  refine ⟨37272411511769353121935681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49696548682359137495914241 37272411511769353121935681)
  ·
    refine ⟨27954308633827014841451761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37272411511769353121935681 27954308633827014841451761)
    ·
      refine ⟨20965731475370261131088821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27954308633827014841451761 20965731475370261131088821)
      ·
        refine ⟨1965537325815961981039577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20965731475370261131088821 1965537325815961981039577)
        ·
          refine ⟨1474152994361971485779683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1965537325815961981039577 1474152994361971485779683)
          ·
            refine ⟨2211229491542957228669525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474152994361971485779683 2211229491542957228669525)
            ·
              refine ⟨25912845604019030023471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2211229491542957228669525 25912845604019030023471)
              ·
                rfl

theorem cell22_2043836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 8].length) (baseStart_2043836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043836 prefixEnd_2043836 := by exact prefixLift 2043836
  have htrace : WordTrace (prefixWord ++ tailWord_2043836) baseStart_2043836 baseEnd_2043836 := by
    simpa [prefixWord, tailWord_2043836, baseEnd_2043836] using wordTrace_append hprefix tailTrace_2043836
  have hstable : (prefixWord ++ tailWord_2043836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043836).length < 2 ^ (prefixWord ++ tailWord_2043836).sum := by decide
  have hdescent : baseEnd_2043836 < baseStart_2043836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043847 : List Nat := [1, 1, 4, 1, 1, 2, 1, 6, 5]
def baseStart_2043847 : Nat := 118140960795 + 2043847 * 2 ^ 59
def prefixEnd_2043847 : Nat := 4983230072969 + 3 ^ 40 * 2043847 * 2
def baseEnd_2043847 : Nat := 233216865611104482869561

theorem tailTrace_2043847 : CollatzResearch.WordTrace tailWord_2043847 prefixEnd_2043847 233216865611104482869561 := by
  unfold tailWord_2043847
  simp only [CollatzResearch.WordTrace]
  refine ⟨74545224226498855122521795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49696816150999236748347863 74545224226498855122521795)
  ·
    refine ⟨111817836339748282683782693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74545224226498855122521795 111817836339748282683782693)
    ·
      refine ⟨20965844313702803003209255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111817836339748282683782693 20965844313702803003209255)
      ·
        refine ⟨31448766470554204504813883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20965844313702803003209255 31448766470554204504813883)
        ·
          refine ⟨47173149705831306757220825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31448766470554204504813883 47173149705831306757220825)
          ·
            refine ⟨35379862279373480067915619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47173149705831306757220825 35379862279373480067915619)
            ·
              refine ⟨53069793419060220101873429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35379862279373480067915619 53069793419060220101873429)
              ·
                refine ⟨2487646566518447817275317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53069793419060220101873429 2487646566518447817275317)
                ·
                  refine ⟨233216865611104482869561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2487646566518447817275317 233216865611104482869561)
                  ·
                    rfl

theorem cell22_2043847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 5].length) (baseStart_2043847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043847 prefixEnd_2043847 := by exact prefixLift 2043847
  have htrace : WordTrace (prefixWord ++ tailWord_2043847) baseStart_2043847 baseEnd_2043847 := by
    simpa [prefixWord, tailWord_2043847, baseEnd_2043847] using wordTrace_append hprefix tailTrace_2043847
  have hstable : (prefixWord ++ tailWord_2043847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043847).length < 2 ^ (prefixWord ++ tailWord_2043847).sum := by decide
  have hdescent : baseEnd_2043847 < baseStart_2043847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043902 : List Nat := [4, 2, 2, 2, 1, 3, 2, 2, 1, 3]
def baseStart_2043902 : Nat := 118140960795 + 2043902 * 2 ^ 59
def prefixEnd_2043902 : Nat := 4983230072969 + 3 ^ 40 * 2043902 * 2
def baseEnd_2043902 : Nat := 699669424457311638483515

theorem tailTrace_2043902 : CollatzResearch.WordTrace tailWord_2043902 prefixEnd_2043902 699669424457311638483515 := by
  unfold tailWord_2043902
  simp only [CollatzResearch.WordTrace]
  refine ⟨9318403780162449939471745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49698153494199733010515973 9318403780162449939471745)
  ·
    refine ⟨6988802835121837454603809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9318403780162449939471745 6988802835121837454603809)
    ·
      refine ⟨5241602126341378090952857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6988802835121837454603809 5241602126341378090952857)
      ·
        refine ⟨3931201594756033568214643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5241602126341378090952857 3931201594756033568214643)
        ·
          refine ⟨5896802392134050352321965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3931201594756033568214643 5896802392134050352321965)
          ·
            refine ⟨2211300897050268882120737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5896802392134050352321965 2211300897050268882120737)
            ·
              refine ⟨1658475672787701661590553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2211300897050268882120737 1658475672787701661590553)
              ·
                refine ⟨1243856754590776246192915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1658475672787701661590553 1243856754590776246192915)
                ·
                  refine ⟨1865785131886164369289373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243856754590776246192915 1865785131886164369289373)
                  ·
                    refine ⟨699669424457311638483515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1865785131886164369289373 699669424457311638483515)
                    ·
                      rfl

theorem cell22_2043902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_2043902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043902 prefixEnd_2043902 := by exact prefixLift 2043902
  have htrace : WordTrace (prefixWord ++ tailWord_2043902) baseStart_2043902 baseEnd_2043902 := by
    simpa [prefixWord, tailWord_2043902, baseEnd_2043902] using wordTrace_append hprefix tailTrace_2043902
  have hstable : (prefixWord ++ tailWord_2043902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043902).length < 2 ^ (prefixWord ++ tailWord_2043902).sum := by decide
  have hdescent : baseEnd_2043902 < baseStart_2043902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043967 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 1, 8]
def baseStart_2043967 : Nat := 118140960795 + 2043967 * 2 ^ 59
def prefixEnd_2043967 : Nat := 4983230072969 + 3 ^ 40 * 2043967 * 2
def baseEnd_2043967 : Nat := 699691675285673135608315

theorem tailTrace_2043967 : CollatzResearch.WordTrace tailWord_2043967 prefixEnd_2043967 699691675285673135608315 := by
  unfold tailWord_2043967
  simp only [CollatzResearch.WordTrace]
  refine ⟨74549600986064115616890155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49699733990709410411260103 74549600986064115616890155)
  ·
    refine ⟨111824401479096173425335233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74549600986064115616890155 111824401479096173425335233)
    ·
      refine ⟨83868301109322130069001425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111824401479096173425335233 83868301109322130069001425)
      ·
        refine ⟨62901225831991597551751069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83868301109322130069001425 62901225831991597551751069)
        ·
          refine ⟨23587959686996849081906651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62901225831991597551751069 23587959686996849081906651)
          ·
            refine ⟨35381939530495273622859977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23587959686996849081906651 35381939530495273622859977)
            ·
              refine ⟨26536454647871455217144983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35381939530495273622859977 26536454647871455217144983)
              ·
                refine ⟨39804681971807182825717475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26536454647871455217144983 39804681971807182825717475)
                ·
                  refine ⟨59707022957710774238576213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39804681971807182825717475 59707022957710774238576213)
                  ·
                    refine ⟨699691675285673135608315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59707022957710774238576213 699691675285673135608315)
                    ·
                      rfl

theorem cell22_2043967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_2043967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2043967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2043967 prefixEnd_2043967 := by exact prefixLift 2043967
  have htrace : WordTrace (prefixWord ++ tailWord_2043967) baseStart_2043967 baseEnd_2043967 := by
    simpa [prefixWord, tailWord_2043967, baseEnd_2043967] using wordTrace_append hprefix tailTrace_2043967
  have hstable : (prefixWord ++ tailWord_2043967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043967).length < 2 ^ (prefixWord ++ tailWord_2043967).sum := by decide
  have hdescent : baseEnd_2043967 < baseStart_2043967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044003 : List Nat := [1, 1, 1, 5, 1, 1, 5, 3, 1, 3]
def baseStart_2044003 : Nat := 118140960795 + 2044003 * 2 ^ 59
def prefixEnd_2044003 : Nat := 4983230072969 + 3 ^ 40 * 2044003 * 2
def baseEnd_2044003 : Nat := 699703998821381041708205

theorem tailTrace_2044003 : CollatzResearch.WordTrace tailWord_2044003 prefixEnd_2044003 699703998821381041708205 := by
  unfold tailWord_2044003
  simp only [CollatzResearch.WordTrace]
  refine ⟨74550914013933693765200663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49700609342622462510133775 74550914013933693765200663)
  ·
    refine ⟨111826371020900540647800995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74550914013933693765200663 111826371020900540647800995)
    ·
      refine ⟨167739556531350810971701493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111826371020900540647800995 167739556531350810971701493)
      ·
        refine ⟨15725583424814138528597015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167739556531350810971701493 15725583424814138528597015)
        ·
          refine ⟨23588375137221207792895523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15725583424814138528597015 23588375137221207792895523)
          ·
            refine ⟨35382562705831811689343285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23588375137221207792895523 35382562705831811689343285)
            ·
              refine ⟨3317115253671732345875933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35382562705831811689343285 3317115253671732345875933)
              ·
                refine ⟨1243918220126899629703475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3317115253671732345875933 1243918220126899629703475)
                ·
                  refine ⟨1865877330190349444555213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243918220126899629703475 1865877330190349444555213)
                  ·
                    refine ⟨699703998821381041708205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1865877330190349444555213 699703998821381041708205)
                    ·
                      rfl

theorem cell22_2044003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 1, 3].length) (baseStart_2044003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044003 prefixEnd_2044003 := by exact prefixLift 2044003
  have htrace : WordTrace (prefixWord ++ tailWord_2044003) baseStart_2044003 baseEnd_2044003 := by
    simpa [prefixWord, tailWord_2044003, baseEnd_2044003] using wordTrace_append hprefix tailTrace_2044003
  have hstable : (prefixWord ++ tailWord_2044003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044003).length < 2 ^ (prefixWord ++ tailWord_2044003).sum := by decide
  have hdescent : baseEnd_2044003 < baseStart_2044003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044106 : List Nat := [3, 1, 2, 1, 3, 1, 5, 6]
def baseStart_2044106 : Nat := 118140960795 + 2044106 * 2 ^ 59
def prefixEnd_2044106 : Nat := 4983230072969 + 3 ^ 40 * 2044106 * 2
def baseEnd_2044106 : Nat := 77748806425147011820321

theorem tailTrace_2044106 : CollatzResearch.WordTrace tailWord_2044106 prefixEnd_2044106 77748806425147011820321 := by
  unfold tailWord_2044106
  simp only [CollatzResearch.WordTrace]
  refine ⟨18638667683140135589050043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49703113821707028237466781 18638667683140135589050043)
  ·
    refine ⟨27958001524710203383575065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18638667683140135589050043 27958001524710203383575065)
    ·
      refine ⟨20968501143532652537681299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27958001524710203383575065 20968501143532652537681299)
      ·
        refine ⟨31452751715298978806521949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20968501143532652537681299 31452751715298978806521949)
        ·
          refine ⟨11794781893237117052445731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31452751715298978806521949 11794781893237117052445731)
          ·
            refine ⟨17692172839855675578668597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11794781893237117052445731 17692172839855675578668597)
            ·
              refine ⟨1658641203736469585500181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17692172839855675578668597 1658641203736469585500181)
              ·
                refine ⟨77748806425147011820321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1658641203736469585500181 77748806425147011820321)
                ·
                  rfl

theorem cell22_2044106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 6].length) (baseStart_2044106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044106 prefixEnd_2044106 := by exact prefixLift 2044106
  have htrace : WordTrace (prefixWord ++ tailWord_2044106) baseStart_2044106 baseEnd_2044106 := by
    simpa [prefixWord, tailWord_2044106, baseEnd_2044106] using wordTrace_append hprefix tailTrace_2044106
  have hstable : (prefixWord ++ tailWord_2044106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044106).length < 2 ^ (prefixWord ++ tailWord_2044106).sum := by decide
  have hdescent : baseEnd_2044106 < baseStart_2044106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044108 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 1, 6]
def baseStart_2044108 : Nat := 118140960795 + 2044108 * 2 ^ 59
def prefixEnd_2044108 : Nat := 4983230072969 + 3 ^ 40 * 2044108 * 2
def baseEnd_2044108 : Nat := 699739942467195767832883

theorem tailTrace_2044108 : CollatzResearch.WordTrace tailWord_2044108 prefixEnd_2044108 699739942467195767832883 := by
  unfold tailWord_2044108
  simp only [CollatzResearch.WordTrace]
  refine ⟨37277371839276648348886489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49703162452368864465181985 37277371839276648348886489)
  ·
    refine ⟨27958028879457486261664867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37277371839276648348886489 27958028879457486261664867)
    ·
      refine ⟨41937043319186229392497301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27958028879457486261664867 41937043319186229392497301)
      ·
        refine ⟨1965798905586854502773311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41937043319186229392497301 1965798905586854502773311)
        ·
          refine ⟨2948698358380281754159967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1965798905586854502773311 2948698358380281754159967)
          ·
            refine ⟨4423047537570422631239951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2948698358380281754159967 4423047537570422631239951)
            ·
              refine ⟨6634571306355633946859927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4423047537570422631239951 6634571306355633946859927)
              ·
                refine ⟨9951856959533450920289891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6634571306355633946859927 9951856959533450920289891)
                ·
                  refine ⟨14927785439300176380434837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9951856959533450920289891 14927785439300176380434837)
                  ·
                    refine ⟨699739942467195767832883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14927785439300176380434837 699739942467195767832883)
                    ·
                      rfl

theorem cell22_2044108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 1, 6].length) (baseStart_2044108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044108 prefixEnd_2044108 := by exact prefixLift 2044108
  have htrace : WordTrace (prefixWord ++ tailWord_2044108) baseStart_2044108 baseEnd_2044108 := by
    simpa [prefixWord, tailWord_2044108, baseEnd_2044108] using wordTrace_append hprefix tailTrace_2044108
  have hstable : (prefixWord ++ tailWord_2044108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044108).length < 2 ^ (prefixWord ++ tailWord_2044108).sum := by decide
  have hdescent : baseEnd_2044108 < baseStart_2044108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044138 : List Nat := [3, 1, 3, 1, 1, 2, 4, 1, 3, 3]
def baseStart_2044138 : Nat := 118140960795 + 2044138 * 2 ^ 59
def prefixEnd_2044138 : Nat := 4983230072969 + 3 ^ 40 * 2044138 * 2
def baseEnd_2044138 : Nat := 699750212080285689582791

theorem tailTrace_2044138 : CollatzResearch.WordTrace tailWord_2044138 prefixEnd_2044138 699750212080285689582791 := by
  unfold tailWord_2044138
  simp only [CollatzResearch.WordTrace]
  refine ⟨18638959467111152955341267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49703891912296407880910045 18638959467111152955341267)
  ·
    refine ⟨27958439200666729433011901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18638959467111152955341267 27958439200666729433011901)
    ·
      refine ⟨10484414700250023537379463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27958439200666729433011901 10484414700250023537379463)
      ·
        refine ⟨15726622050375035306069195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10484414700250023537379463 15726622050375035306069195)
        ·
          refine ⟨23589933075562552959103793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15726622050375035306069195 23589933075562552959103793)
          ·
            refine ⟨17692449806671914719327845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23589933075562552959103793 17692449806671914719327845)
            ·
              refine ⟨3317334338750984009873971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17692449806671914719327845 3317334338750984009873971)
              ·
                refine ⟨4976001508126476014810957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3317334338750984009873971 4976001508126476014810957)
                ·
                  refine ⟨1866000565547428505554109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4976001508126476014810957 1866000565547428505554109)
                  ·
                    refine ⟨699750212080285689582791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1866000565547428505554109 699750212080285689582791)
                    ·
                      rfl

theorem cell22_2044138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_2044138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044138 prefixEnd_2044138 := by exact prefixLift 2044138
  have htrace : WordTrace (prefixWord ++ tailWord_2044138) baseStart_2044138 baseEnd_2044138 := by
    simpa [prefixWord, tailWord_2044138, baseEnd_2044138] using wordTrace_append hprefix tailTrace_2044138
  have hstable : (prefixWord ++ tailWord_2044138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044138).length < 2 ^ (prefixWord ++ tailWord_2044138).sum := by decide
  have hdescent : baseEnd_2044138 < baseStart_2044138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044179 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 8]
def baseStart_2044179 : Nat := 118140960795 + 2044179 * 2 ^ 59
def prefixEnd_2044179 : Nat := 4983230072969 + 3 ^ 40 * 2044179 * 2
def baseEnd_2044179 : Nat := 233254749072725083102555

theorem tailTrace_2044179 : CollatzResearch.WordTrace tailWord_2044179 prefixEnd_2044179 233254749072725083102555 := by
  unfold tailWord_2044179
  simp only [CollatzResearch.WordTrace]
  refine ⟨74557333261296075823607591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49704888840864050549071727 74557333261296075823607591)
  ·
    refine ⟨111835999891944113735411387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74557333261296075823607591 111835999891944113735411387)
    ·
      refine ⟨167753999837916170603117081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111835999891944113735411387 167753999837916170603117081)
      ·
        refine ⟨125815499878437127952337811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167753999837916170603117081 125815499878437127952337811)
        ·
          refine ⟨188723249817655691928506717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125815499878437127952337811 188723249817655691928506717)
          ·
            refine ⟨70771218681620884473190019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188723249817655691928506717 70771218681620884473190019)
            ·
              refine ⟨106156828022431326709785029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70771218681620884473190019 106156828022431326709785029)
              ·
                refine ⟨19904405254205873758084693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106156828022431326709785029 19904405254205873758084693)
                ·
                  refine ⟨233254749072725083102555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19904405254205873758084693 233254749072725083102555)
                  ·
                    rfl

theorem cell22_2044179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 8].length) (baseStart_2044179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044179 prefixEnd_2044179 := by exact prefixLift 2044179
  have htrace : WordTrace (prefixWord ++ tailWord_2044179) baseStart_2044179 baseEnd_2044179 := by
    simpa [prefixWord, tailWord_2044179, baseEnd_2044179] using wordTrace_append hprefix tailTrace_2044179
  have hstable : (prefixWord ++ tailWord_2044179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044179).length < 2 ^ (prefixWord ++ tailWord_2044179).sum := by decide
  have hdescent : baseEnd_2044179 < baseStart_2044179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044189 : List Nat := [1, 4, 2, 3, 2, 1, 3, 2, 1, 3]
def baseStart_2044189 : Nat := 118140960795 + 2044189 * 2 ^ 59
def prefixEnd_2044189 : Nat := 4983230072969 + 3 ^ 40 * 2044189 * 2
def baseEnd_2044189 : Nat := 699767670422538556557635

theorem tailTrace_2044189 : CollatzResearch.WordTrace tailWord_2044189 prefixEnd_2044189 699767670422538556557635 := by
  unfold tailWord_2044189
  simp only [CollatzResearch.WordTrace]
  refine ⟨74557697991259847531471621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49705131994173231687647747 74557697991259847531471621)
  ·
    refine ⟨13979568373361221412150929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74557697991259847531471621 13979568373361221412150929)
    ·
      refine ⟨10484676280020916059113197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13979568373361221412150929 10484676280020916059113197)
      ·
        refine ⟨3931753605007843522167449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10484676280020916059113197 3931753605007843522167449)
        ·
          refine ⟨2948815203755882641625587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3931753605007843522167449 2948815203755882641625587)
          ·
            refine ⟨4423222805633823962438381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2948815203755882641625587 4423222805633823962438381)
            ·
              refine ⟨1658708552112683985914393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4423222805633823962438381 1658708552112683985914393)
              ·
                refine ⟨1244031414084512989435795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1658708552112683985914393 1244031414084512989435795)
                ·
                  refine ⟨1866047121126769484153693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1244031414084512989435795 1866047121126769484153693)
                  ·
                    refine ⟨699767670422538556557635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1866047121126769484153693 699767670422538556557635)
                    ·
                      rfl

theorem cell22_2044189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_2044189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044189 prefixEnd_2044189 := by exact prefixLift 2044189
  have htrace : WordTrace (prefixWord ++ tailWord_2044189) baseStart_2044189 baseEnd_2044189 := by
    simpa [prefixWord, tailWord_2044189, baseEnd_2044189] using wordTrace_append hprefix tailTrace_2044189
  have hstable : (prefixWord ++ tailWord_2044189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044189).length < 2 ^ (prefixWord ++ tailWord_2044189).sum := by decide
  have hdescent : baseEnd_2044189 < baseStart_2044189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044202 : List Nat := [3, 1, 4, 2, 2, 2, 2, 1, 5]
def baseStart_2044202 : Nat := 118140960795 + 2044202 * 2 ^ 59
def prefixEnd_2044202 : Nat := 4983230072969 + 3 ^ 40 * 2044202 * 2
def baseEnd_2044202 : Nat := 233257373529403618660865

theorem tailTrace_2044202 : CollatzResearch.WordTrace tailWord_2044202 prefixEnd_2044202 233257373529403618660865 := by
  unfold tailWord_2044202
  simp only [CollatzResearch.WordTrace]
  refine ⟨18639543035053187687923715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49705448093475167167796573 18639543035053187687923715)
  ·
    refine ⟨27959314552579781531885573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18639543035053187687923715 27959314552579781531885573)
    ·
      refine ⟨5242371478608709037228545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27959314552579781531885573 5242371478608709037228545)
      ·
        refine ⟨3931778608956531777921409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5242371478608709037228545 3931778608956531777921409)
        ·
          refine ⟨2948833956717398833441057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3931778608956531777921409 2948833956717398833441057)
          ·
            refine ⟨2211625467538049125080793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2948833956717398833441057 2211625467538049125080793)
            ·
              refine ⟨1658719100653536843810595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2211625467538049125080793 1658719100653536843810595)
              ·
                refine ⟨2488078650980305265715893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1658719100653536843810595 2488078650980305265715893)
                ·
                  refine ⟨233257373529403618660865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2488078650980305265715893 233257373529403618660865)
                  ·
                    rfl

theorem cell22_2044202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 5].length) (baseStart_2044202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044202 prefixEnd_2044202 := by exact prefixLift 2044202
  have htrace : WordTrace (prefixWord ++ tailWord_2044202) baseStart_2044202 baseEnd_2044202 := by
    simpa [prefixWord, tailWord_2044202, baseEnd_2044202] using wordTrace_append hprefix tailTrace_2044202
  have hstable : (prefixWord ++ tailWord_2044202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044202).length < 2 ^ (prefixWord ++ tailWord_2044202).sum := by decide
  have hdescent : baseEnd_2044202 < baseStart_2044202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044211 : List Nat := [1, 1, 1, 2, 5, 1, 2, 3, 1, 5]
def baseStart_2044211 : Nat := 118140960795 + 2044211 * 2 ^ 59
def prefixEnd_2044211 : Nat := 4983230072969 + 3 ^ 40 * 2044211 * 2
def baseEnd_2044211 : Nat := 699775201472137832507567

theorem tailTrace_2044211 : CollatzResearch.WordTrace tailWord_2044211 prefixEnd_2044211 699775201472137832507567 := by
  unfold tailWord_2044211
  simp only [CollatzResearch.WordTrace]
  refine ⟨74558500397180145288772487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49705666931453430192514991 74558500397180145288772487)
  ·
    refine ⟨111837750595770217933158731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74558500397180145288772487 111837750595770217933158731)
    ·
      refine ⟨167756625893655326899738097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111837750595770217933158731 167756625893655326899738097)
      ·
        refine ⟨125817469420241495174803573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167756625893655326899738097 125817469420241495174803573)
        ·
          refine ⟨11795387758147640172637835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125817469420241495174803573 11795387758147640172637835)
          ·
            refine ⟨17693081637221460258956753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11795387758147640172637835 17693081637221460258956753)
            ·
              refine ⟨13269811227916095194217565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17693081637221460258956753 13269811227916095194217565)
              ·
                refine ⟨4976179210468535697831587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13269811227916095194217565 4976179210468535697831587)
                ·
                  refine ⟨7464268815702803546747381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4976179210468535697831587 7464268815702803546747381)
                  ·
                    refine ⟨699775201472137832507567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7464268815702803546747381 699775201472137832507567)
                    ·
                      rfl

theorem cell22_2044211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 5].length) (baseStart_2044211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044211 prefixEnd_2044211 := by exact prefixLift 2044211
  have htrace : WordTrace (prefixWord ++ tailWord_2044211) baseStart_2044211 baseEnd_2044211 := by
    simpa [prefixWord, tailWord_2044211, baseEnd_2044211] using wordTrace_append hprefix tailTrace_2044211
  have hstable : (prefixWord ++ tailWord_2044211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044211).length < 2 ^ (prefixWord ++ tailWord_2044211).sum := by decide
  have hdescent : baseEnd_2044211 < baseStart_2044211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044258 : List Nat := [3, 3, 2, 1, 1, 2, 3, 7]
def baseStart_2044258 : Nat := 118140960795 + 2044258 * 2 ^ 59
def prefixEnd_2044258 : Nat := 4983230072969 + 3 ^ 40 * 2044258 * 2
def baseEnd_2044258 : Nat := 77754587836960597398047

theorem tailTrace_2044258 : CollatzResearch.WordTrace tailWord_2044258 prefixEnd_2044258 77754587836960597398047 := by
  unfold tailWord_2044258
  simp only [CollatzResearch.WordTrace]
  refine ⟨18640053657002468078933357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49706809752006581543822285 18640053657002468078933357)
  ·
    refine ⟨6990020121375925529600009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18640053657002468078933357 6990020121375925529600009)
    ·
      refine ⟨5242515091031944147200007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6990020121375925529600009 5242515091031944147200007)
      ·
        refine ⟨7863772636547916220800011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5242515091031944147200007 7863772636547916220800011)
        ·
          refine ⟨11795658954821874331200017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7863772636547916220800011 11795658954821874331200017)
          ·
            refine ⟨8846744216116405748400013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11795658954821874331200017 8846744216116405748400013)
            ·
              refine ⟨3317529081043652155650005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8846744216116405748400013 3317529081043652155650005)
              ·
                refine ⟨77754587836960597398047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3317529081043652155650005 77754587836960597398047)
                ·
                  rfl

theorem cell22_2044258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 7].length) (baseStart_2044258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044258 prefixEnd_2044258 := by exact prefixLift 2044258
  have htrace : WordTrace (prefixWord ++ tailWord_2044258) baseStart_2044258 baseEnd_2044258 := by
    simpa [prefixWord, tailWord_2044258, baseEnd_2044258] using wordTrace_append hprefix tailTrace_2044258
  have hstable : (prefixWord ++ tailWord_2044258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044258).length < 2 ^ (prefixWord ++ tailWord_2044258).sum := by decide
  have hdescent : baseEnd_2044258 < baseStart_2044258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044320 : List Nat := [2, 1, 1, 4, 1, 4, 3, 1, 5]
def baseStart_2044320 : Nat := 118140960795 + 2044320 * 2 ^ 59
def prefixEnd_2044320 : Nat := 4983230072969 + 3 ^ 40 * 2044320 * 2
def baseEnd_2044320 : Nat := 233270838133232627177411

theorem tailTrace_2044320 : CollatzResearch.WordTrace tailWord_2044320 prefixEnd_2044320 233270838133232627177411 := by
  unfold tailWord_2044320
  simp only [CollatzResearch.WordTrace]
  refine ⟨37281237976892628452245207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49708317302523504602993609 37281237976892628452245207)
  ·
    refine ⟨55921856965338942678367811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37281237976892628452245207 55921856965338942678367811)
    ·
      refine ⟨83882785448008414017551717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55921856965338942678367811 83882785448008414017551717)
      ·
        refine ⟨15728022271501577628290947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83882785448008414017551717 15728022271501577628290947)
        ·
          refine ⟨23592033407252366442436421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15728022271501577628290947 23592033407252366442436421)
          ·
            refine ⟨4423506263859818707956829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23592033407252366442436421 4423506263859818707956829)
            ·
              refine ⟨1658814848947432015483811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4423506263859818707956829 1658814848947432015483811)
              ·
                refine ⟨2488222273421148023225717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1658814848947432015483811 2488222273421148023225717)
                ·
                  refine ⟨233270838133232627177411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2488222273421148023225717 233270838133232627177411)
                  ·
                    rfl

theorem cell22_2044320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 5].length) (baseStart_2044320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044320 prefixEnd_2044320 := by exact prefixLift 2044320
  have htrace : WordTrace (prefixWord ++ tailWord_2044320) baseStart_2044320 baseEnd_2044320 := by
    simpa [prefixWord, tailWord_2044320, baseEnd_2044320] using wordTrace_append hprefix tailTrace_2044320
  have hstable : (prefixWord ++ tailWord_2044320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044320).length < 2 ^ (prefixWord ++ tailWord_2044320).sum := by decide
  have hdescent : baseEnd_2044320 < baseStart_2044320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044341 : List Nat := [1, 3, 3, 2, 4, 1, 1, 3, 1, 3]
def baseStart_2044341 : Nat := 118140960795 + 2044341 * 2 ^ 59
def prefixEnd_2044341 : Nat := 4983230072969 + 3 ^ 40 * 2044341 * 2
def baseEnd_2044341 : Nat := 699819703128860826757169

theorem tailTrace_2044341 : CollatzResearch.WordTrace tailWord_2044341 prefixEnd_2044341 699819703128860826757169 := by
  unfold tailWord_2044341
  simp only [CollatzResearch.WordTrace]
  refine ⟨74563241886709177491004877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49708827924472784994003251 74563241886709177491004877)
  ·
    refine ⟨27961215707515941559126829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74563241886709177491004877 27961215707515941559126829)
    ·
      refine ⟨10485455890318478084672561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27961215707515941559126829 10485455890318478084672561)
      ·
        refine ⟨7864091917738858563504421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10485455890318478084672561 7864091917738858563504421)
        ·
          refine ⟨1474517234576035980657079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7864091917738858563504421 1474517234576035980657079)
          ·
            refine ⟨2211775851864053970985619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474517234576035980657079 2211775851864053970985619)
            ·
              refine ⟨3317663777796080956478429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2211775851864053970985619 3317663777796080956478429)
              ·
                refine ⟨1244123916673530358679411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3317663777796080956478429 1244123916673530358679411)
                ·
                  refine ⟨1866185875010295538019117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1244123916673530358679411 1866185875010295538019117)
                  ·
                    refine ⟨699819703128860826757169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1866185875010295538019117 699819703128860826757169)
                    ·
                      rfl

theorem cell22_2044341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_2044341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044341 prefixEnd_2044341 := by exact prefixLift 2044341
  have htrace : WordTrace (prefixWord ++ tailWord_2044341) baseStart_2044341 baseEnd_2044341 := by
    simpa [prefixWord, tailWord_2044341, baseEnd_2044341] using wordTrace_append hprefix tailTrace_2044341
  have hstable : (prefixWord ++ tailWord_2044341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044341).length < 2 ^ (prefixWord ++ tailWord_2044341).sum := by decide
  have hdescent : baseEnd_2044341 < baseStart_2044341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044350 : List Nat := [4, 2, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_2044350 : Nat := 118140960795 + 2044350 * 2 ^ 59
def prefixEnd_2044350 : Nat := 4983230072969 + 3 ^ 40 * 2044350 * 2
def baseEnd_2044350 : Nat := 699822784012787803282141

theorem tailTrace_2044350 : CollatzResearch.WordTrace tailWord_2044350 prefixEnd_2044350 699822784012787803282141 := by
  unfold tailWord_2044350
  simp only [CollatzResearch.WordTrace]
  refine ⟨9320446267959571503510313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49709046762451048018721669 9320446267959571503510313)
  ·
    refine ⟨6990334700969678627632735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9320446267959571503510313 6990334700969678627632735)
    ·
      refine ⟨10485502051454517941449103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6990334700969678627632735 10485502051454517941449103)
      ·
        refine ⟨15728253077181776912173655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10485502051454517941449103 15728253077181776912173655)
        ·
          refine ⟨23592379615772665368260483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15728253077181776912173655 23592379615772665368260483)
          ·
            refine ⟨35388569423658998052390725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23592379615772665368260483 35388569423658998052390725)
            ·
              refine ⟨6635356766936062134823261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35388569423658998052390725 6635356766936062134823261)
              ·
                refine ⟨2488258787601023300558723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6635356766936062134823261 2488258787601023300558723)
                ·
                  refine ⟨3732388181401534950838085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2488258787601023300558723 3732388181401534950838085)
                  ·
                    refine ⟨699822784012787803282141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3732388181401534950838085 699822784012787803282141)
                    ·
                      rfl

theorem cell22_2044350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_2044350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044350 prefixEnd_2044350 := by exact prefixLift 2044350
  have htrace : WordTrace (prefixWord ++ tailWord_2044350) baseStart_2044350 baseEnd_2044350 := by
    simpa [prefixWord, tailWord_2044350, baseEnd_2044350] using wordTrace_append hprefix tailTrace_2044350
  have hstable : (prefixWord ++ tailWord_2044350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044350).length < 2 ^ (prefixWord ++ tailWord_2044350).sum := by decide
  have hdescent : baseEnd_2044350 < baseStart_2044350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044378 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 4, 4]
def baseStart_2044378 : Nat := 118140960795 + 2044378 * 2 ^ 59
def prefixEnd_2044378 : Nat := 4983230072969 + 3 ^ 40 * 2044378 * 2
def baseEnd_2044378 : Nat := 699832368985005063582055

theorem tailTrace_2044378 : CollatzResearch.WordTrace tailWord_2044378 prefixEnd_2044378 699832368985005063582055 := by
  unfold tailWord_2044378
  simp only [CollatzResearch.WordTrace]
  refine ⟨18641147846893783202525447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49709727591716755206734525 18641147846893783202525447)
  ·
    refine ⟨27961721770340674803788171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18641147846893783202525447 27961721770340674803788171)
    ·
      refine ⟨41942582655511012205682257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27961721770340674803788171 41942582655511012205682257)
      ·
        refine ⟨31456936991633259154261693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41942582655511012205682257 31456936991633259154261693)
        ·
          refine ⟨11796351371862472182848135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31456936991633259154261693 11796351371862472182848135)
          ·
            refine ⟨17694527057793708274272203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11796351371862472182848135 17694527057793708274272203)
            ·
              refine ⟨26541790586690562411408305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17694527057793708274272203 26541790586690562411408305)
              ·
                refine ⟨19906342940017921808556229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26541790586690562411408305 19906342940017921808556229)
                ·
                  refine ⟨3732439301253360339104293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19906342940017921808556229 3732439301253360339104293)
                  ·
                    refine ⟨699832368985005063582055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3732439301253360339104293 699832368985005063582055)
                    ·
                      rfl

theorem cell22_2044378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_2044378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044378 prefixEnd_2044378 := by exact prefixLift 2044378
  have htrace : WordTrace (prefixWord ++ tailWord_2044378) baseStart_2044378 baseEnd_2044378 := by
    simpa [prefixWord, tailWord_2044378, baseEnd_2044378] using wordTrace_append hprefix tailTrace_2044378
  have hstable : (prefixWord ++ tailWord_2044378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044378).length < 2 ^ (prefixWord ++ tailWord_2044378).sum := by decide
  have hdescent : baseEnd_2044378 < baseStart_2044378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044500 : List Nat := [2, 4, 1, 1, 1, 3, 2, 2, 6]
def baseStart_2044500 : Nat := 118140960795 + 2044500 * 2 ^ 59
def prefixEnd_2044500 : Nat := 4983230072969 + 3 ^ 40 * 2044500 * 2
def baseEnd_2044500 : Nat := 233291377359412470677227

theorem tailTrace_2044500 : CollatzResearch.WordTrace tailWord_2044500 prefixEnd_2044500 233291377359412470677227 := by
  unfold tailWord_2044500
  simp only [CollatzResearch.WordTrace]
  refine ⟨37284520546566573823021477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49712694062088765097361969 37284520546566573823021477)
  ·
    refine ⟨6990847602481232591816527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37284520546566573823021477 6990847602481232591816527)
    ·
      refine ⟨10486271403721848887724791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6990847602481232591816527 10486271403721848887724791)
      ·
        refine ⟨15729407105582773331587187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10486271403721848887724791 15729407105582773331587187)
        ·
          refine ⟨23594110658374159997380781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15729407105582773331587187 23594110658374159997380781)
          ·
            refine ⟨8847791496890309999017793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23594110658374159997380781 8847791496890309999017793)
            ·
              refine ⟨6635843622667732499263345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8847791496890309999017793 6635843622667732499263345)
              ·
                refine ⟨4976882717000799374447509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6635843622667732499263345 4976882717000799374447509)
                ·
                  refine ⟨233291377359412470677227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4976882717000799374447509 233291377359412470677227)
                  ·
                    rfl

theorem cell22_2044500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_2044500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044500 prefixEnd_2044500 := by exact prefixLift 2044500
  have htrace : WordTrace (prefixWord ++ tailWord_2044500) baseStart_2044500 baseEnd_2044500 := by
    simpa [prefixWord, tailWord_2044500, baseEnd_2044500] using wordTrace_append hprefix tailTrace_2044500
  have hstable : (prefixWord ++ tailWord_2044500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044500).length < 2 ^ (prefixWord ++ tailWord_2044500).sum := by decide
  have hdescent : baseEnd_2044500 < baseStart_2044500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044515 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 6, 3]
def baseStart_2044515 : Nat := 118140960795 + 2044515 * 2 ^ 59
def prefixEnd_2044515 : Nat := 4983230072969 + 3 ^ 40 * 2044515 * 2
def baseEnd_2044515 : Nat := 699879266884782372906635

theorem tailTrace_2044515 : CollatzResearch.WordTrace tailWord_2044515 prefixEnd_2044515 699879266884782372906635 := by
  unfold tailWord_2044515
  simp only [CollatzResearch.WordTrace]
  refine ⟨74569588188078805207838999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49713058792052536805225999 74569588188078805207838999)
  ·
    refine ⟨111854382282118207811758499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74569588188078805207838999 111854382282118207811758499)
    ·
      refine ⟨167781573423177311717637749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111854382282118207811758499 167781573423177311717637749)
      ·
        refine ⟨15729522508422872973528539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167781573423177311717637749 15729522508422872973528539)
        ·
          refine ⟨23594283762634309460292809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15729522508422872973528539 23594283762634309460292809)
          ·
            refine ⟨17695712821975732095219607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23594283762634309460292809 17695712821975732095219607)
            ·
              refine ⟨26543569232963598142829411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17695712821975732095219607 26543569232963598142829411)
              ·
                refine ⟨39815353849445397214244117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26543569232963598142829411 39815353849445397214244117)
                ·
                  refine ⟨1866344711692752994417693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39815353849445397214244117 1866344711692752994417693)
                  ·
                    refine ⟨699879266884782372906635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1866344711692752994417693 699879266884782372906635)
                    ·
                      rfl

theorem cell22_2044515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 3].length) (baseStart_2044515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044515 prefixEnd_2044515 := by exact prefixLift 2044515
  have htrace : WordTrace (prefixWord ++ tailWord_2044515) baseStart_2044515 baseEnd_2044515 := by
    simpa [prefixWord, tailWord_2044515, baseEnd_2044515] using wordTrace_append hprefix tailTrace_2044515
  have hstable : (prefixWord ++ tailWord_2044515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044515).length < 2 ^ (prefixWord ++ tailWord_2044515).sum := by decide
  have hdescent : baseEnd_2044515 < baseStart_2044515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044534 : List Nat := [5, 1, 1, 2, 3, 2, 1, 1, 6]
def baseStart_2044534 : Nat := 118140960795 + 2044534 * 2 ^ 59
def prefixEnd_2044534 : Nat := 4983230072969 + 3 ^ 40 * 2044534 * 2
def baseEnd_2044534 : Nat := 233295256991024218893859

theorem tailTrace_2044534 : CollatzResearch.WordTrace tailWord_2044534 prefixEnd_2044534 233295256991024218893859 := by
  unfold tailWord_2044534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4660642573438123215798791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49713520783339980968520437 4660642573438123215798791)
  ·
    refine ⟨6990963860157184823698187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4660642573438123215798791 6990963860157184823698187)
    ·
      refine ⟨10486445790235777235547281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6990963860157184823698187 10486445790235777235547281)
      ·
        refine ⟨7864834342676832926660461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10486445790235777235547281 7864834342676832926660461)
        ·
          refine ⟨2949312878503812347497673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7864834342676832926660461 2949312878503812347497673)
          ·
            refine ⟨2211984658877859260623255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2949312878503812347497673 2211984658877859260623255)
            ·
              refine ⟨3317976988316788890934883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2211984658877859260623255 3317976988316788890934883)
              ·
                refine ⟨4976965482475183336402325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3317976988316788890934883 4976965482475183336402325)
                ·
                  refine ⟨233295256991024218893859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4976965482475183336402325 233295256991024218893859)
                  ·
                    rfl

theorem cell22_2044534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_2044534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044534 prefixEnd_2044534 := by exact prefixLift 2044534
  have htrace : WordTrace (prefixWord ++ tailWord_2044534) baseStart_2044534 baseEnd_2044534 := by
    simpa [prefixWord, tailWord_2044534, baseEnd_2044534] using wordTrace_append hprefix tailTrace_2044534
  have hstable : (prefixWord ++ tailWord_2044534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044534).length < 2 ^ (prefixWord ++ tailWord_2044534).sum := by decide
  have hdescent : baseEnd_2044534 < baseStart_2044534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044543 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 2, 7]
def baseStart_2044543 : Nat := 118140960795 + 2044543 * 2 ^ 59
def prefixEnd_2044543 : Nat := 4983230072969 + 3 ^ 40 * 2044543 * 2
def baseEnd_2044543 : Nat := 699888851856999633206549

theorem tailTrace_2044543 : CollatzResearch.WordTrace tailWord_2044543 prefixEnd_2044543 699888851856999633206549 := by
  unfold tailWord_2044543
  simp only [CollatzResearch.WordTrace]
  refine ⟨74570609431977365989858283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49713739621318243993238855 74570609431977365989858283)
  ·
    refine ⟨111855914147966048984787425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74570609431977365989858283 111855914147966048984787425)
    ·
      refine ⟨83891935610974536738590569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111855914147966048984787425 83891935610974536738590569)
      ·
        refine ⟨62918951708230902553942927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83891935610974536738590569 62918951708230902553942927)
        ·
          refine ⟨94378427562346353830914391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62918951708230902553942927 94378427562346353830914391)
          ·
            refine ⟨141567641343519530746371587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94378427562346353830914391 141567641343519530746371587)
            ·
              refine ⟨212351462015279296119557381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141567641343519530746371587 212351462015279296119557381)
              ·
                refine ⟨39815899127864868022417009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212351462015279296119557381 39815899127864868022417009)
                ·
                  refine ⟨29861924345898651016812757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39815899127864868022417009 29861924345898651016812757)
                  ·
                    refine ⟨699888851856999633206549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29861924345898651016812757 699888851856999633206549)
                    ·
                      rfl

theorem cell22_2044543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_2044543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044543 prefixEnd_2044543 := by exact prefixLift 2044543
  have htrace : WordTrace (prefixWord ++ tailWord_2044543) baseStart_2044543 baseEnd_2044543 := by
    simpa [prefixWord, tailWord_2044543, baseEnd_2044543] using wordTrace_append hprefix tailTrace_2044543
  have hstable : (prefixWord ++ tailWord_2044543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044543).length < 2 ^ (prefixWord ++ tailWord_2044543).sum := by decide
  have hdescent : baseEnd_2044543 < baseStart_2044543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044545 : List Nat := [1, 2, 4, 2, 1, 1, 4, 7]
def baseStart_2044545 : Nat := 118140960795 + 2044545 * 2 ^ 59
def prefixEnd_2044545 : Nat := 4983230072969 + 3 ^ 40 * 2044545 * 2
def baseEnd_2044545 : Nat := 77765504055319143850727

theorem tailTrace_2044545 : CollatzResearch.WordTrace tailWord_2044545 prefixEnd_2044545 77765504055319143850727 := by
  unfold tailWord_2044545
  simp only [CollatzResearch.WordTrace]
  refine ⟨74570682377970120331431089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49713788251980080220954059 74570682377970120331431089)
  ·
    refine ⟨55928011783477590248573317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74570682377970120331431089 55928011783477590248573317)
    ·
      refine ⟨10486502209402048171607497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55928011783477590248573317 10486502209402048171607497)
      ·
        refine ⟨7864876657051536128705623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10486502209402048171607497 7864876657051536128705623)
        ·
          refine ⟨11797314985577304193058435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7864876657051536128705623 11797314985577304193058435)
          ·
            refine ⟨17695972478365956289587653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11797314985577304193058435 17695972478365956289587653)
            ·
              refine ⟨3317994839693616804297685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17695972478365956289587653 3317994839693616804297685)
              ·
                refine ⟨77765504055319143850727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3317994839693616804297685 77765504055319143850727)
                ·
                  rfl

theorem cell22_2044545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 7].length) (baseStart_2044545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044545 prefixEnd_2044545 := by exact prefixLift 2044545
  have htrace : WordTrace (prefixWord ++ tailWord_2044545) baseStart_2044545 baseEnd_2044545 := by
    simpa [prefixWord, tailWord_2044545, baseEnd_2044545] using wordTrace_append hprefix tailTrace_2044545
  have hstable : (prefixWord ++ tailWord_2044545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044545).length < 2 ^ (prefixWord ++ tailWord_2044545).sum := by decide
  have hdescent : baseEnd_2044545 < baseStart_2044545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044549 : List Nat := [1, 3, 1, 1, 4, 2, 4, 1, 2, 3]
def baseStart_2044549 : Nat := 118140960795 + 2044549 * 2 ^ 59
def prefixEnd_2044549 : Nat := 4983230072969 + 3 ^ 40 * 2044549 * 2
def baseEnd_2044549 : Nat := 699890905779617617556531

theorem tailTrace_2044549 : CollatzResearch.WordTrace tailWord_2044549 prefixEnd_2044549 699890905779617617556531 := by
  unfold tailWord_2044549
  simp only [CollatzResearch.WordTrace]
  refine ⟨74570828269955629014576701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49713885513303752676384467 74570828269955629014576701)
  ·
    refine ⟨27964060601233360880466263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74570828269955629014576701 27964060601233360880466263)
    ·
      refine ⟨41946090901850041320699395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27964060601233360880466263 41946090901850041320699395)
      ·
        refine ⟨62919136352775061981049093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41946090901850041320699395 62919136352775061981049093)
        ·
          refine ⟨11797338066145324121446705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62919136352775061981049093 11797338066145324121446705)
          ·
            refine ⟨8848003549608993091085029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11797338066145324121446705 8848003549608993091085029)
            ·
              refine ⟨1659000665551686204578443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8848003549608993091085029 1659000665551686204578443)
              ·
                refine ⟨2488500998327529306867665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1659000665551686204578443 2488500998327529306867665)
                ·
                  refine ⟨1866375748745646980150749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2488500998327529306867665 1866375748745646980150749)
                  ·
                    refine ⟨699890905779617617556531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1866375748745646980150749 699890905779617617556531)
                    ·
                      rfl

theorem cell22_2044549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 2, 3].length) (baseStart_2044549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044549 prefixEnd_2044549 := by exact prefixLift 2044549
  have htrace : WordTrace (prefixWord ++ tailWord_2044549) baseStart_2044549 baseEnd_2044549 := by
    simpa [prefixWord, tailWord_2044549, baseEnd_2044549] using wordTrace_append hprefix tailTrace_2044549
  have hstable : (prefixWord ++ tailWord_2044549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044549).length < 2 ^ (prefixWord ++ tailWord_2044549).sum := by decide
  have hdescent : baseEnd_2044549 < baseStart_2044549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044564 : List Nat := [2, 4, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_2044564 : Nat := 118140960795 + 2044564 * 2 ^ 59
def prefixEnd_2044564 : Nat := 4983230072969 + 3 ^ 40 * 2044564 * 2
def baseEnd_2044564 : Nat := 699896040586162578431485

theorem tailTrace_2044564 : CollatzResearch.WordTrace tailWord_2044564 prefixEnd_2044564 699896040586162578431485 := by
  unfold tailWord_2044564
  simp only [CollatzResearch.WordTrace]
  refine ⟨37285687682450643288186373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49714250243267524384248497 37285687682450643288186373)
  ·
    refine ⟨6991066440459495616534945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37285687682450643288186373 6991066440459495616534945)
    ·
      refine ⟨5243299830344621712401209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6991066440459495616534945 5243299830344621712401209)
      ·
        refine ⟨3932474872758466284300907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5243299830344621712401209 3932474872758466284300907)
        ·
          refine ⟨5898712309137699426451361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3932474872758466284300907 5898712309137699426451361)
          ·
            refine ⟨4424034231853274569838521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5898712309137699426451361 4424034231853274569838521)
            ·
              refine ⟨3318025673889955927378891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4424034231853274569838521 3318025673889955927378891)
              ·
                refine ⟨4977038510834933891068337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3318025673889955927378891 4977038510834933891068337)
                ·
                  refine ⟨3732778883126200418301253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4977038510834933891068337 3732778883126200418301253)
                  ·
                    refine ⟨699896040586162578431485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3732778883126200418301253 699896040586162578431485)
                    ·
                      rfl

theorem cell22_2044564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_2044564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044564 prefixEnd_2044564 := by exact prefixLift 2044564
  have htrace : WordTrace (prefixWord ++ tailWord_2044564) baseStart_2044564 baseEnd_2044564 := by
    simpa [prefixWord, tailWord_2044564, baseEnd_2044564] using wordTrace_append hprefix tailTrace_2044564
  have hstable : (prefixWord ++ tailWord_2044564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044564).length < 2 ^ (prefixWord ++ tailWord_2044564).sum := by decide
  have hdescent : baseEnd_2044564 < baseStart_2044564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044605 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_2044605 : Nat := 118140960795 + 2044605 * 2 ^ 59
def prefixEnd_2044605 : Nat := 4983230072969 + 3 ^ 40 * 2044605 * 2
def baseEnd_2044605 : Nat := 699910075724052138156359

theorem tailTrace_2044605 : CollatzResearch.WordTrace tailWord_2044605 prefixEnd_2044605 699910075724052138156359 := by
  unfold tailWord_2044605
  simp only [CollatzResearch.WordTrace]
  refine ⟨74572870757752750578615269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49715247171835167052410179 74572870757752750578615269)
  ·
    refine ⟨13982413267078640733490363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74572870757752750578615269 13982413267078640733490363)
    ·
      refine ⟨20973619900617961100235545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13982413267078640733490363 20973619900617961100235545)
      ·
        refine ⟨15730214925463470825176659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20973619900617961100235545 15730214925463470825176659)
        ·
          refine ⟨23595322388195206237764989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15730214925463470825176659 23595322388195206237764989)
          ·
            refine ⟨8848245895573202339161871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23595322388195206237764989 8848245895573202339161871)
            ·
              refine ⟨13272368843359803508742807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8848245895573202339161871 13272368843359803508742807)
              ·
                refine ⟨19908553265039705263114211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13272368843359803508742807 19908553265039705263114211)
                ·
                  refine ⟨29862829897559557894671317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19908553265039705263114211 29862829897559557894671317)
                  ·
                    refine ⟨699910075724052138156359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29862829897559557894671317 699910075724052138156359)
                    ·
                      rfl

theorem cell22_2044605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_2044605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044605 prefixEnd_2044605 := by exact prefixLift 2044605
  have htrace : WordTrace (prefixWord ++ tailWord_2044605) baseStart_2044605 baseEnd_2044605 := by
    simpa [prefixWord, tailWord_2044605, baseEnd_2044605] using wordTrace_append hprefix tailTrace_2044605
  have hstable : (prefixWord ++ tailWord_2044605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044605).length < 2 ^ (prefixWord ++ tailWord_2044605).sum := by decide
  have hdescent : baseEnd_2044605 < baseStart_2044605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044628 : List Nat := [2, 4, 1, 3, 2, 1, 2, 3, 1, 3]
def baseStart_2044628 : Nat := 118140960795 + 2044628 * 2 ^ 59
def prefixEnd_2044628 : Nat := 4983230072969 + 3 ^ 40 * 2044628 * 2
def baseEnd_2044628 : Nat := 699917949094087744831289

theorem tailTrace_2044628 : CollatzResearch.WordTrace tailWord_2044628 prefixEnd_2044628 699917949094087744831289 := by
  unfold tailWord_2044628
  simp only [CollatzResearch.WordTrace]
  refine ⟨37286854818334712753351269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49715806424446283671135025 37286854818334712753351269)
  ·
    refine ⟨6991285278437758641253363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37286854818334712753351269 6991285278437758641253363)
    ·
      refine ⟨10486927917656637961880045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6991285278437758641253363 10486927917656637961880045)
      ·
        refine ⟨3932597969121239235705017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10486927917656637961880045 3932597969121239235705017)
        ·
          refine ⟨2949448476840929426778763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3932597969121239235705017 2949448476840929426778763)
          ·
            refine ⟨4424172715261394140168145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2949448476840929426778763 4424172715261394140168145)
            ·
              refine ⟨3318129536446045605126109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4424172715261394140168145 3318129536446045605126109)
              ·
                refine ⟨1244298576167267101922291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3318129536446045605126109 1244298576167267101922291)
                ·
                  refine ⟨1866447864250900652883437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1244298576167267101922291 1866447864250900652883437)
                  ·
                    refine ⟨699917949094087744831289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1866447864250900652883437 699917949094087744831289)
                    ·
                      rfl

theorem cell22_2044628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_2044628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044628 prefixEnd_2044628 := by exact prefixLift 2044628
  have htrace : WordTrace (prefixWord ++ tailWord_2044628) baseStart_2044628 baseEnd_2044628 := by
    simpa [prefixWord, tailWord_2044628, baseEnd_2044628] using wordTrace_append hprefix tailTrace_2044628
  have hstable : (prefixWord ++ tailWord_2044628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044628).length < 2 ^ (prefixWord ++ tailWord_2044628).sum := by decide
  have hdescent : baseEnd_2044628 < baseStart_2044628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044682 : List Nat := [3, 1, 2, 2, 1, 2, 2, 3, 2, 4]
def baseStart_2044682 : Nat := 118140960795 + 2044682 * 2 ^ 59
def prefixEnd_2044682 : Nat := 4983230072969 + 3 ^ 40 * 2044682 * 2
def baseEnd_2044682 : Nat := 699936434397649603981123

theorem tailTrace_2044682 : CollatzResearch.WordTrace tailWord_2044682 prefixEnd_2044682 699936434397649603981123 := by
  unfold tailWord_2044682
  simp only [CollatzResearch.WordTrace]
  refine ⟨18643919794618448182292075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49717119452315861819445533 18643919794618448182292075)
  ·
    refine ⟨27965879691927672273438113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18643919794618448182292075 27965879691927672273438113)
    ·
      refine ⟨20974409768945754205078585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27965879691927672273438113 20974409768945754205078585)
      ·
        refine ⟨15730807326709315653808939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20974409768945754205078585 15730807326709315653808939)
        ·
          refine ⟨23596210990063973480713409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15730807326709315653808939 23596210990063973480713409)
          ·
            refine ⟨17697158242547980110535057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23596210990063973480713409 17697158242547980110535057)
            ·
              refine ⟨13272868681910985082901293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17697158242547980110535057 13272868681910985082901293)
              ·
                refine ⟨4977325755716619406087985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13272868681910985082901293 4977325755716619406087985)
                ·
                  refine ⟨3732994316787464554565989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4977325755716619406087985 3732994316787464554565989)
                  ·
                    refine ⟨699936434397649603981123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3732994316787464554565989 699936434397649603981123)
                    ·
                      rfl

theorem cell22_2044682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_2044682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044682 prefixEnd_2044682 := by exact prefixLift 2044682
  have htrace : WordTrace (prefixWord ++ tailWord_2044682) baseStart_2044682 baseEnd_2044682 := by
    simpa [prefixWord, tailWord_2044682, baseEnd_2044682] using wordTrace_append hprefix tailTrace_2044682
  have hstable : (prefixWord ++ tailWord_2044682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044682).length < 2 ^ (prefixWord ++ tailWord_2044682).sum := by decide
  have hdescent : baseEnd_2044682 < baseStart_2044682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044718 : List Nat := [4, 1, 3, 2, 1, 1, 4, 1, 2, 3]
def baseStart_2044718 : Nat := 118140960795 + 2044718 * 2 ^ 59
def prefixEnd_2044718 : Nat := 4983230072969 + 3 ^ 40 * 2044718 * 2
def baseEnd_2044718 : Nat := 699948757933357510081013

theorem tailTrace_2044718 : CollatzResearch.WordTrace tailWord_2044718 prefixEnd_2044718 699948757933357510081013 := by
  unfold tailWord_2044718
  simp only [CollatzResearch.WordTrace]
  refine ⟨9322124025792921359684851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49717994804228913918319205 9322124025792921359684851)
  ·
    refine ⟨13983186038689382039527277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9322124025792921359684851 13983186038689382039527277)
    ·
      refine ⟨5243694764508518264822729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13983186038689382039527277 5243694764508518264822729)
      ·
        refine ⟨3932771073381388698617047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5243694764508518264822729 3932771073381388698617047)
        ·
          refine ⟨5899156610072083047925571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3932771073381388698617047 5899156610072083047925571)
          ·
            refine ⟨8848734915108124571888357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5899156610072083047925571 8848734915108124571888357)
            ·
              refine ⟨1659137796582773357229067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8848734915108124571888357 1659137796582773357229067)
              ·
                refine ⟨2488706694874160035843601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1659137796582773357229067 2488706694874160035843601)
                ·
                  refine ⟨1866530021155620026882701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2488706694874160035843601 1866530021155620026882701)
                  ·
                    refine ⟨699948757933357510081013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1866530021155620026882701 699948757933357510081013)
                    ·
                      rfl

theorem cell22_2044718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_2044718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044718 prefixEnd_2044718 := by exact prefixLift 2044718
  have htrace : WordTrace (prefixWord ++ tailWord_2044718) baseStart_2044718 baseEnd_2044718 := by
    simpa [prefixWord, tailWord_2044718, baseEnd_2044718] using wordTrace_append hprefix tailTrace_2044718
  have hstable : (prefixWord ++ tailWord_2044718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044718).length < 2 ^ (prefixWord ++ tailWord_2044718).sum := by decide
  have hdescent : baseEnd_2044718 < baseStart_2044718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044757 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 2, 5]
def baseStart_2044757 : Nat := 118140960795 + 2044757 * 2 ^ 59
def prefixEnd_2044757 : Nat := 4983230072969 + 3 ^ 40 * 2044757 * 2
def baseEnd_2044757 : Nat := 699962108430374408355893

theorem tailTrace_2044757 : CollatzResearch.WordTrace tailWord_2044757 prefixEnd_2044757 699962108430374408355893 := by
  unfold tailWord_2044757
  simp only [CollatzResearch.WordTrace]
  refine ⟨74578414653202080538148525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49718943102134720358765683 74578414653202080538148525)
  ·
    refine ⟨27966905494950780201805697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74578414653202080538148525 27966905494950780201805697)
    ·
      refine ⟨20975179121213085151354273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27966905494950780201805697 20975179121213085151354273)
      ·
        refine ⟨15731384340909813863515705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20975179121213085151354273 15731384340909813863515705)
        ·
          refine ⟨11798538255682360397636779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15731384340909813863515705 11798538255682360397636779)
          ·
            refine ⟨17697807383523540596455169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11798538255682360397636779 17697807383523540596455169)
            ·
              refine ⟨13273355537642655447341377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17697807383523540596455169 13273355537642655447341377)
              ·
                refine ⟨9955016653231991585506033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13273355537642655447341377 9955016653231991585506033)
                ·
                  refine ⟨7466262489923993689129525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9955016653231991585506033 7466262489923993689129525)
                  ·
                    refine ⟨699962108430374408355893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7466262489923993689129525 699962108430374408355893)
                    ·
                      rfl

theorem cell22_2044757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_2044757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044757 prefixEnd_2044757 := by exact prefixLift 2044757
  have htrace : WordTrace (prefixWord ++ tailWord_2044757) baseStart_2044757 baseEnd_2044757 := by
    simpa [prefixWord, tailWord_2044757, baseEnd_2044757] using wordTrace_append hprefix tailTrace_2044757
  have hstable : (prefixWord ++ tailWord_2044757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044757).length < 2 ^ (prefixWord ++ tailWord_2044757).sum := by decide
  have hdescent : baseEnd_2044757 < baseStart_2044757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044759 : List Nat := [1, 1, 3, 2, 4, 2, 2, 2, 5]
def baseStart_2044759 : Nat := 118140960795 + 2044759 * 2 ^ 59
def prefixEnd_2044759 : Nat := 4983230072969 + 3 ^ 40 * 2044759 * 2
def baseEnd_2044759 : Nat := 233320931023749023268629

theorem tailTrace_2044759 : CollatzResearch.WordTrace tailWord_2044759 prefixEnd_2044759 233320931023749023268629 := by
  unfold tailWord_2044759
  simp only [CollatzResearch.WordTrace]
  refine ⟨74578487599194834879721331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49718991732796556586480887 74578487599194834879721331)
  ·
    refine ⟨111867731398792252319581997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74578487599194834879721331 111867731398792252319581997)
    ·
      refine ⟨41950399274547094619843249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111867731398792252319581997 41950399274547094619843249)
      ·
        refine ⟨31462799455910320964882437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41950399274547094619843249 31462799455910320964882437)
        ·
          refine ⟨5899274897983185180915457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31462799455910320964882437 5899274897983185180915457)
          ·
            refine ⟨4424456173487388885686593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5899274897983185180915457 4424456173487388885686593)
            ·
              refine ⟨3318342130115541664264945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4424456173487388885686593 3318342130115541664264945)
              ·
                refine ⟨2488756597586656248198709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3318342130115541664264945 2488756597586656248198709)
                ·
                  refine ⟨233320931023749023268629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2488756597586656248198709 233320931023749023268629)
                  ·
                    rfl

theorem cell22_2044759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 5].length) (baseStart_2044759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044759 prefixEnd_2044759 := by exact prefixLift 2044759
  have htrace : WordTrace (prefixWord ++ tailWord_2044759) baseStart_2044759 baseEnd_2044759 := by
    simpa [prefixWord, tailWord_2044759, baseEnd_2044759] using wordTrace_append hprefix tailTrace_2044759
  have hstable : (prefixWord ++ tailWord_2044759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044759).length < 2 ^ (prefixWord ++ tailWord_2044759).sum := by decide
  have hdescent : baseEnd_2044759 < baseStart_2044759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044789 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 3, 4]
def baseStart_2044789 : Nat := 118140960795 + 2044789 * 2 ^ 59
def prefixEnd_2044789 : Nat := 4983230072969 + 3 ^ 40 * 2044789 * 2
def baseEnd_2044789 : Nat := 699973062684336991555795

theorem tailTrace_2044789 : CollatzResearch.WordTrace tailWord_2044789 prefixEnd_2044789 699973062684336991555795 := by
  unfold tailWord_2044789
  simp only [CollatzResearch.WordTrace]
  refine ⟨74579581789086150003313421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49719721192724100002208947 74579581789086150003313421)
  ·
    refine ⟨27967343170907306251242533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74579581789086150003313421 27967343170907306251242533)
    ·
      refine ⟨5243876844545119922107975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27967343170907306251242533 5243876844545119922107975)
      ·
        refine ⟨7865815266817679883161963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5243876844545119922107975 7865815266817679883161963)
        ·
          refine ⟨11798722900226519824742945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7865815266817679883161963 11798722900226519824742945)
          ·
            refine ⟨8849042175169889868557209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11798722900226519824742945 8849042175169889868557209)
            ·
              refine ⟨6636781631377417401417907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8849042175169889868557209 6636781631377417401417907)
              ·
                refine ⟨9955172447066126102126861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6636781631377417401417907 9955172447066126102126861)
                ·
                  refine ⟨3733189667649797288297573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9955172447066126102126861 3733189667649797288297573)
                  ·
                    refine ⟨699973062684336991555795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3733189667649797288297573 699973062684336991555795)
                    ·
                      rfl

theorem cell22_2044789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_2044789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044789 prefixEnd_2044789 := by exact prefixLift 2044789
  have htrace : WordTrace (prefixWord ++ tailWord_2044789) baseStart_2044789 baseEnd_2044789 := by
    simpa [prefixWord, tailWord_2044789, baseEnd_2044789] using wordTrace_append hprefix tailTrace_2044789
  have hstable : (prefixWord ++ tailWord_2044789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044789).length < 2 ^ (prefixWord ++ tailWord_2044789).sum := by decide
  have hdescent : baseEnd_2044789 < baseStart_2044789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044817 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 4, 4]
def baseStart_2044817 : Nat := 118140960795 + 2044817 * 2 ^ 59
def prefixEnd_2044817 : Nat := 4983230072969 + 3 ^ 40 * 2044817 * 2
def baseEnd_2044817 : Nat := 699982647656554251855709

theorem tailTrace_2044817 : CollatzResearch.WordTrace tailWord_2044817 prefixEnd_2044817 699982647656554251855709 := by
  unfold tailWord_2044817
  simp only [CollatzResearch.WordTrace]
  refine ⟨74580603032984710785332705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49720402021989807190221803 74580603032984710785332705)
  ·
    refine ⟨55935452274738533088999529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74580603032984710785332705 55935452274738533088999529)
    ·
      refine ⟨41951589206053899816749647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55935452274738533088999529 41951589206053899816749647)
      ·
        refine ⟨62927383809080849725124471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41951589206053899816749647 62927383809080849725124471)
        ·
          refine ⟨94391075713621274587686707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62927383809080849725124471 94391075713621274587686707)
          ·
            refine ⟨141586613570431911881530061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94391075713621274587686707 141586613570431911881530061)
            ·
              refine ⟨53094980088911966955573773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141586613570431911881530061 53094980088911966955573773)
              ·
                refine ⟨19910617533341987608340165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53094980088911966955573773 19910617533341987608340165)
                ·
                  refine ⟨3733240787501622676563781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19910617533341987608340165 3733240787501622676563781)
                  ·
                    refine ⟨699982647656554251855709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3733240787501622676563781 699982647656554251855709)
                    ·
                      rfl

theorem cell22_2044817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_2044817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044817 prefixEnd_2044817 := by exact prefixLift 2044817
  have htrace : WordTrace (prefixWord ++ tailWord_2044817) baseStart_2044817 baseEnd_2044817 := by
    simpa [prefixWord, tailWord_2044817, baseEnd_2044817] using wordTrace_append hprefix tailTrace_2044817
  have hstable : (prefixWord ++ tailWord_2044817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044817).length < 2 ^ (prefixWord ++ tailWord_2044817).sum := by decide
  have hdescent : baseEnd_2044817 < baseStart_2044817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044819 : List Nat := [1, 1, 1, 2, 1, 2, 1, 8, 2, 3]
def baseStart_2044819 : Nat := 118140960795 + 2044819 * 2 ^ 59
def prefixEnd_2044819 : Nat := 4983230072969 + 3 ^ 40 * 2044819 * 2
def baseEnd_2044819 : Nat := 699983332297426913305703

theorem tailTrace_2044819 : CollatzResearch.WordTrace tailWord_2044819 prefixEnd_2044819 699983332297426913305703 := by
  unfold tailWord_2044819
  simp only [CollatzResearch.WordTrace]
  refine ⟨74580675978977465126905511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49720450652651643417937007 74580675978977465126905511)
  ·
    refine ⟨111871013968466197690358267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74580675978977465126905511 111871013968466197690358267)
    ·
      refine ⟨167806520952699296535537401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111871013968466197690358267 167806520952699296535537401)
      ·
        refine ⟨125854890714524472401653051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167806520952699296535537401 125854890714524472401653051)
        ·
          refine ⟨188782336071786708602479577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125854890714524472401653051 188782336071786708602479577)
          ·
            refine ⟨141586752053840031451859683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188782336071786708602479577 141586752053840031451859683)
            ·
              refine ⟨212380128080760047177789525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141586752053840031451859683 212380128080760047177789525)
              ·
                refine ⟨2488829625946406802864721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 212380128080760047177789525 2488829625946406802864721)
                ·
                  refine ⟨1866622219459805102148541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2488829625946406802864721 1866622219459805102148541)
                  ·
                    refine ⟨699983332297426913305703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1866622219459805102148541 699983332297426913305703)
                    ·
                      rfl

theorem cell22_2044819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 3].length) (baseStart_2044819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044819 prefixEnd_2044819 := by exact prefixLift 2044819
  have htrace : WordTrace (prefixWord ++ tailWord_2044819) baseStart_2044819 baseEnd_2044819 := by
    simpa [prefixWord, tailWord_2044819, baseEnd_2044819] using wordTrace_append hprefix tailTrace_2044819
  have hstable : (prefixWord ++ tailWord_2044819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044819).length < 2 ^ (prefixWord ++ tailWord_2044819).sum := by decide
  have hdescent : baseEnd_2044819 < baseStart_2044819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044834 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_2044834 : Nat := 118140960795 + 2044834 * 2 ^ 59
def prefixEnd_2044834 : Nat := 4983230072969 + 3 ^ 40 * 2044834 * 2
def baseEnd_2044834 : Nat := 699988467103971874180657

theorem tailTrace_2044834 : CollatzResearch.WordTrace tailWord_2044834 prefixEnd_2044834 699988467103971874180657 := by
  unfold tailWord_2044834
  simp only [CollatzResearch.WordTrace]
  refine ⟨18645305768480780672175389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49720815382615415125801037 18645305768480780672175389)
  ·
    refine ⟨6991989663180292752065771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18645305768480780672175389 6991989663180292752065771)
    ·
      refine ⟨10487984494770439128098657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6991989663180292752065771 10487984494770439128098657)
      ·
        refine ⟨7865988371077829346073993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10487984494770439128098657 7865988371077829346073993)
        ·
          refine ⟨5899491278308372009555495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7865988371077829346073993 5899491278308372009555495)
          ·
            refine ⟨8849236917462558014333243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5899491278308372009555495 8849236917462558014333243)
            ·
              refine ⟨13273855376193837021499865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8849236917462558014333243 13273855376193837021499865)
              ·
                refine ⟨9955391532145377766124899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13273855376193837021499865 9955391532145377766124899)
                ·
                  refine ⟨14933087298218066649187349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9955391532145377766124899 14933087298218066649187349)
                  ·
                    refine ⟨699988467103971874180657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14933087298218066649187349 699988467103971874180657)
                    ·
                      rfl

theorem cell22_2044834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_2044834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044834 prefixEnd_2044834 := by exact prefixLift 2044834
  have htrace : WordTrace (prefixWord ++ tailWord_2044834) baseStart_2044834 baseEnd_2044834 := by
    simpa [prefixWord, tailWord_2044834, baseEnd_2044834] using wordTrace_append hprefix tailTrace_2044834
  have hstable : (prefixWord ++ tailWord_2044834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044834).length < 2 ^ (prefixWord ++ tailWord_2044834).sum := by decide
  have hdescent : baseEnd_2044834 < baseStart_2044834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044849 : List Nat := [1, 2, 2, 4, 3, 1, 1, 8]
def baseStart_2044849 : Nat := 118140960795 + 2044849 * 2 ^ 59
def prefixEnd_2044849 : Nat := 4983230072969 + 3 ^ 40 * 2044849 * 2
def baseEnd_2044849 : Nat := 77777066878946315006179

theorem tailTrace_2044849 : CollatzResearch.WordTrace tailWord_2044849 prefixEnd_2044849 77777066878946315006179 := by
  unfold tailWord_2044849
  simp only [CollatzResearch.WordTrace]
  refine ⟨74581770168868780250497601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49721180112579186833665067 74581770168868780250497601)
  ·
    refine ⟨55936327626651585187873201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74581770168868780250497601 55936327626651585187873201)
    ·
      refine ⟨41952245719988688890904901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55936327626651585187873201 41952245719988688890904901)
      ·
        refine ⟨7866046072497879167044669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41952245719988688890904901 7866046072497879167044669)
        ·
          refine ⟨2949767277186704687641751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7866046072497879167044669 2949767277186704687641751)
          ·
            refine ⟨4424650915780057031462627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2949767277186704687641751 4424650915780057031462627)
            ·
              refine ⟨6636976373670085547193941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4424650915780057031462627 6636976373670085547193941)
              ·
                refine ⟨77777066878946315006179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6636976373670085547193941 77777066878946315006179)
                ·
                  rfl

theorem cell22_2044849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 8].length) (baseStart_2044849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044849 prefixEnd_2044849 := by exact prefixLift 2044849
  have htrace : WordTrace (prefixWord ++ tailWord_2044849) baseStart_2044849 baseEnd_2044849 := by
    simpa [prefixWord, tailWord_2044849, baseEnd_2044849] using wordTrace_append hprefix tailTrace_2044849
  have hstable : (prefixWord ++ tailWord_2044849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044849).length < 2 ^ (prefixWord ++ tailWord_2044849).sum := by decide
  have hdescent : baseEnd_2044849 < baseStart_2044849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044868 : List Nat := [2, 3, 3, 3, 1, 1, 1, 2, 2, 4]
def baseStart_2044868 : Nat := 118140960795 + 2044868 * 2 ^ 59
def prefixEnd_2044868 : Nat := 4983230072969 + 3 ^ 40 * 2044868 * 2
def baseEnd_2044868 : Nat := 700000105998807118830553

theorem tailTrace_2044868 : CollatzResearch.WordTrace tailWord_2044868 prefixEnd_2044868 700000105998807118830553 := by
  unfold tailWord_2044868
  simp only [CollatzResearch.WordTrace]
  refine ⟨37291231577899973247719629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49721642103866630996959505 37291231577899973247719629)
  ·
    refine ⟨13984211841712489967894861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37291231577899973247719629 13984211841712489967894861)
    ·
      refine ⟨5244079440642183737960573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13984211841712489967894861 5244079440642183737960573)
      ·
        refine ⟨1966529790240818901735215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5244079440642183737960573 1966529790240818901735215)
        ·
          refine ⟨2949794685361228352602823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1966529790240818901735215 2949794685361228352602823)
          ·
            refine ⟨4424692028041842528904235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2949794685361228352602823 4424692028041842528904235)
            ·
              refine ⟨6637038042062763793356353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4424692028041842528904235 6637038042062763793356353)
              ·
                refine ⟨4977778531547072845017265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6637038042062763793356353 4977778531547072845017265)
                ·
                  refine ⟨3733333898660304633762949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4977778531547072845017265 3733333898660304633762949)
                  ·
                    refine ⟨700000105998807118830553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3733333898660304633762949 700000105998807118830553)
                    ·
                      rfl

theorem cell22_2044868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_2044868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044868 prefixEnd_2044868 := by exact prefixLift 2044868
  have htrace : WordTrace (prefixWord ++ tailWord_2044868) baseStart_2044868 baseEnd_2044868 := by
    simpa [prefixWord, tailWord_2044868, baseEnd_2044868] using wordTrace_append hprefix tailTrace_2044868
  have hstable : (prefixWord ++ tailWord_2044868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044868).length < 2 ^ (prefixWord ++ tailWord_2044868).sum := by decide
  have hdescent : baseEnd_2044868 < baseStart_2044868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044956 : List Nat := [2, 2, 3, 1, 4, 1, 1, 2, 6]
def baseStart_2044956 : Nat := 118140960795 + 2044956 * 2 ^ 59
def prefixEnd_2044956 : Nat := 4983230072969 + 3 ^ 40 * 2044956 * 2
def baseEnd_2044956 : Nat := 233343410065734740876761

theorem tailTrace_2044956 : CollatzResearch.WordTrace tailWord_2044956 prefixEnd_2044956 233343410065734740876761 := by
  unfold tailWord_2044956
  simp only [CollatzResearch.WordTrace]
  refine ⟨37292836389740568762321361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49723781852987425016428481 37292836389740568762321361)
  ·
    refine ⟨27969627292305426571741021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37292836389740568762321361 27969627292305426571741021)
    ·
      refine ⟨10488610234614534964402883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27969627292305426571741021 10488610234614534964402883)
      ·
        refine ⟨15732915351921802446604325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10488610234614534964402883 15732915351921802446604325)
        ·
          refine ⟨2949921628485337958738311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15732915351921802446604325 2949921628485337958738311)
          ·
            refine ⟨4424882442728006938107467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2949921628485337958738311 4424882442728006938107467)
            ·
              refine ⟨6637323664092010407161201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4424882442728006938107467 6637323664092010407161201)
              ·
                refine ⟨4977992748069007805370901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6637323664092010407161201 4977992748069007805370901)
                ·
                  refine ⟨233343410065734740876761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4977992748069007805370901 233343410065734740876761)
                  ·
                    rfl

theorem cell22_2044956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_2044956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044956 prefixEnd_2044956 := by exact prefixLift 2044956
  have htrace : WordTrace (prefixWord ++ tailWord_2044956) baseStart_2044956 baseEnd_2044956 := by
    simpa [prefixWord, tailWord_2044956, baseEnd_2044956] using wordTrace_append hprefix tailTrace_2044956
  have hstable : (prefixWord ++ tailWord_2044956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044956).length < 2 ^ (prefixWord ++ tailWord_2044956).sum := by decide
  have hdescent : baseEnd_2044956 < baseStart_2044956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044984 : List Nat := [2, 1, 2, 1, 5, 2, 9]
def baseStart_2044984 : Nat := 118140960795 + 2044984 * 2 ^ 59
def prefixEnd_2044984 : Nat := 4983230072969 + 3 ^ 40 * 2044984 * 2
def baseEnd_2044984 : Nat := 25927400561830425293711

theorem tailTrace_2044984 : CollatzResearch.WordTrace tailWord_2044984 prefixEnd_2044984 25927400561830425293711 := by
  unfold tailWord_2044984
  simp only [CollatzResearch.WordTrace]
  refine ⟨37293347011689849153331003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49724462682253132204441337 37293347011689849153331003)
  ·
    refine ⟨55940020517534773729996505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37293347011689849153331003 55940020517534773729996505)
    ·
      refine ⟨41955015388151080297497379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55940020517534773729996505 41955015388151080297497379)
      ·
        refine ⟨62932523082226620446246069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41955015388151080297497379 62932523082226620446246069)
        ·
          refine ⟨5899924038958745666835569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62932523082226620446246069 5899924038958745666835569)
          ·
            refine ⟨4424943029219059250126677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5899924038958745666835569 4424943029219059250126677)
            ·
              refine ⟨25927400561830425293711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4424943029219059250126677 25927400561830425293711)
              ·
                rfl

theorem cell22_2044984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 9].length) (baseStart_2044984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044984 prefixEnd_2044984 := by exact prefixLift 2044984
  have htrace : WordTrace (prefixWord ++ tailWord_2044984) baseStart_2044984 baseEnd_2044984 := by
    simpa [prefixWord, tailWord_2044984, baseEnd_2044984] using wordTrace_append hprefix tailTrace_2044984
  have hstable : (prefixWord ++ tailWord_2044984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044984).length < 2 ^ (prefixWord ++ tailWord_2044984).sum := by decide
  have hdescent : baseEnd_2044984 < baseStart_2044984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044988 : List Nat := [2, 2, 2, 2, 2, 2, 3, 2, 2, 3]
def baseStart_2044988 : Nat := 118140960795 + 2044988 * 2 ^ 59
def prefixEnd_2044988 : Nat := 4983230072969 + 3 ^ 40 * 2044988 * 2
def baseEnd_2044988 : Nat := 700041184451166805830185

theorem tailTrace_2044988 : CollatzResearch.WordTrace tailWord_2044988 prefixEnd_2044988 700041184451166805830185 := by
  unfold tailWord_2044988
  simp only [CollatzResearch.WordTrace]
  refine ⟨37293419957682603494903809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49724559943576804659871745 37293419957682603494903809)
  ·
    refine ⟨27970064968261952621177857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37293419957682603494903809 27970064968261952621177857)
    ·
      refine ⟨20977548726196464465883393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27970064968261952621177857 20977548726196464465883393)
      ·
        refine ⟨15733161544647348349412545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20977548726196464465883393 15733161544647348349412545)
        ·
          refine ⟨11799871158485511262059409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15733161544647348349412545 11799871158485511262059409)
          ·
            refine ⟨8849903368864133446544557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11799871158485511262059409 8849903368864133446544557)
            ·
              refine ⟨3318713763324050042454209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8849903368864133446544557 3318713763324050042454209)
              ·
                refine ⟨2489035322493037531840657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3318713763324050042454209 2489035322493037531840657)
                ·
                  refine ⟨1866776491869778148880493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2489035322493037531840657 1866776491869778148880493)
                  ·
                    refine ⟨700041184451166805830185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1866776491869778148880493 700041184451166805830185)
                    ·
                      rfl

theorem cell22_2044988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_2044988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2044988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2044988 prefixEnd_2044988 := by exact prefixLift 2044988
  have htrace : WordTrace (prefixWord ++ tailWord_2044988) baseStart_2044988 baseEnd_2044988 := by
    simpa [prefixWord, tailWord_2044988, baseEnd_2044988] using wordTrace_append hprefix tailTrace_2044988
  have hstable : (prefixWord ++ tailWord_2044988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044988).length < 2 ^ (prefixWord ++ tailWord_2044988).sum := by decide
  have hdescent : baseEnd_2044988 < baseStart_2044988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045016 : List Nat := [2, 1, 2, 2, 1, 3, 1, 4, 3, 3]
def baseStart_2045016 : Nat := 118140960795 + 2045016 * 2 ^ 59
def prefixEnd_2045016 : Nat := 4983230072969 + 3 ^ 40 * 2045016 * 2
def baseEnd_2045016 : Nat := 700050769423384066130099

theorem tailTrace_2045016 : CollatzResearch.WordTrace tailWord_2045016 prefixEnd_2045016 700050769423384066130099 := by
  unfold tailWord_2045016
  simp only [CollatzResearch.WordTrace]
  refine ⟨37293930579631883885913451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49725240772842511847884601 37293930579631883885913451)
  ·
    refine ⟨55940895869447825828870177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37293930579631883885913451 55940895869447825828870177)
    ·
      refine ⟨41955671902085869371652633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55940895869447825828870177 41955671902085869371652633)
      ·
        refine ⟨31466753926564402028739475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41955671902085869371652633 31466753926564402028739475)
        ·
          refine ⟨47200130889846603043109213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31466753926564402028739475 47200130889846603043109213)
          ·
            refine ⟨17700049083692476141165955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47200130889846603043109213 17700049083692476141165955)
            ·
              refine ⟨26550073625538714211748933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17700049083692476141165955 26550073625538714211748933)
              ·
                refine ⟨4978138804788508914702925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26550073625538714211748933 4978138804788508914702925)
                ·
                  refine ⟨1866802051795690843013597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4978138804788508914702925 1866802051795690843013597)
                  ·
                    refine ⟨700050769423384066130099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1866802051795690843013597 700050769423384066130099)
                    ·
                      rfl

theorem cell22_2045016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 3, 3].length) (baseStart_2045016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045016 prefixEnd_2045016 := by exact prefixLift 2045016
  have htrace : WordTrace (prefixWord ++ tailWord_2045016) baseStart_2045016 baseEnd_2045016 := by
    simpa [prefixWord, tailWord_2045016, baseEnd_2045016] using wordTrace_append hprefix tailTrace_2045016
  have hstable : (prefixWord ++ tailWord_2045016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045016).length < 2 ^ (prefixWord ++ tailWord_2045016).sum := by decide
  have hdescent : baseEnd_2045016 < baseStart_2045016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045029 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 9]
def baseStart_2045029 : Nat := 118140960795 + 2045029 * 2 ^ 59
def prefixEnd_2045029 : Nat := 4983230072969 + 3 ^ 40 * 2045029 * 2
def baseEnd_2045029 : Nat := 233351739863018788518353

theorem tailTrace_2045029 : CollatzResearch.WordTrace tailWord_2045029 prefixEnd_2045029 233351739863018788518353 := by
  unfold tailWord_2045029
  simp only [CollatzResearch.WordTrace]
  refine ⟨74588335308216670992050141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49725556872144447328033427 74588335308216670992050141)
  ·
    refine ⟨27970625740581251622018803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74588335308216670992050141 27970625740581251622018803)
    ·
      refine ⟨41955938610871877433028205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27970625740581251622018803 41955938610871877433028205)
      ·
        refine ⟨15733476979076954037385577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41955938610871877433028205 15733476979076954037385577)
        ·
          refine ⟨11800107734307715528039183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15733476979076954037385577 11800107734307715528039183)
          ·
            refine ⟨17700161601461573292058775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11800107734307715528039183 17700161601461573292058775)
            ·
              refine ⟨26550242402192359938088163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17700161601461573292058775 26550242402192359938088163)
              ·
                refine ⟨39825363603288539907132245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26550242402192359938088163 39825363603288539907132245)
                ·
                  refine ⟨233351739863018788518353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39825363603288539907132245 233351739863018788518353)
                  ·
                    rfl

theorem cell22_2045029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_2045029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045029 prefixEnd_2045029 := by exact prefixLift 2045029
  have htrace : WordTrace (prefixWord ++ tailWord_2045029) baseStart_2045029 baseEnd_2045029 := by
    simpa [prefixWord, tailWord_2045029, baseEnd_2045029] using wordTrace_append hprefix tailTrace_2045029
  have hstable : (prefixWord ++ tailWord_2045029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045029).length < 2 ^ (prefixWord ++ tailWord_2045029).sum := by decide
  have hdescent : baseEnd_2045029 < baseStart_2045029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045046 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_2045046 : Nat := 118140960795 + 2045046 * 2 ^ 59
def prefixEnd_2045046 : Nat := 4983230072969 + 3 ^ 40 * 2045046 * 2
def baseEnd_2045046 : Nat := 233353679678824662626669

theorem tailTrace_2045046 : CollatzResearch.WordTrace tailWord_2045046 prefixEnd_2045046 233353679678824662626669 := by
  unfold tailWord_2045046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4661809709322192680963687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49725970232770055263612661 4661809709322192680963687)
  ·
    refine ⟨6992714563983289021445531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4661809709322192680963687 6992714563983289021445531)
    ·
      refine ⟨10489071845974933532168297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6992714563983289021445531 10489071845974933532168297)
      ·
        refine ⟨7866803884481200149126223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10489071845974933532168297 7866803884481200149126223)
        ·
          refine ⟨11800205826721800223689335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7866803884481200149126223 11800205826721800223689335)
          ·
            refine ⟨17700308740082700335534003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11800205826721800223689335 17700308740082700335534003)
            ·
              refine ⟨26550463110124050503301005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17700308740082700335534003 26550463110124050503301005)
              ·
                refine ⟨9956423666296518938737877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26550463110124050503301005 9956423666296518938737877)
                ·
                  refine ⟨233353679678824662626669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9956423666296518938737877 233353679678824662626669)
                  ·
                    rfl

theorem cell22_2045046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_2045046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045046 prefixEnd_2045046 := by exact prefixLift 2045046
  have htrace : WordTrace (prefixWord ++ tailWord_2045046) baseStart_2045046 baseEnd_2045046 := by
    simpa [prefixWord, tailWord_2045046, baseEnd_2045046] using wordTrace_append hprefix tailTrace_2045046
  have hstable : (prefixWord ++ tailWord_2045046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045046).length < 2 ^ (prefixWord ++ tailWord_2045046).sum := by decide
  have hdescent : baseEnd_2045046 < baseStart_2045046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045101 : List Nat := [1, 5, 2, 1, 4, 1, 2, 2, 1, 3]
def baseStart_2045101 : Nat := 118140960795 + 2045101 * 2 ^ 59
def prefixEnd_2045101 : Nat := 4983230072969 + 3 ^ 40 * 2045101 * 2
def baseEnd_2045101 : Nat := 700079866660472177754839

theorem tailTrace_2045101 : CollatzResearch.WordTrace tailWord_2045101 prefixEnd_2045101 700079866660472177754839 := by
  unfold tailWord_2045101
  simp only [CollatzResearch.WordTrace]
  refine ⟨74590961363955827288671157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49727307575970551525780771 74590961363955827288671157)
  ·
    refine ⟨6992902627870858808312921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74590961363955827288671157 6992902627870858808312921)
    ·
      refine ⟨5244676970903144106234691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6992902627870858808312921 5244676970903144106234691)
      ·
        refine ⟨7867015456354716159352037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5244676970903144106234691 7867015456354716159352037)
        ·
          refine ⟨1475065398066509279878507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7867015456354716159352037 1475065398066509279878507)
          ·
            refine ⟨2212598097099763919817761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475065398066509279878507 2212598097099763919817761)
            ·
              refine ⟨1659448572824822939863321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2212598097099763919817761 1659448572824822939863321)
              ·
                refine ⟨1244586429618617204897491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1659448572824822939863321 1244586429618617204897491)
                ·
                  refine ⟨1866879644427925807346237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1244586429618617204897491 1866879644427925807346237)
                  ·
                    refine ⟨700079866660472177754839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1866879644427925807346237 700079866660472177754839)
                    ·
                      rfl

theorem cell22_2045101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_2045101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045101 prefixEnd_2045101 := by exact prefixLift 2045101
  have htrace : WordTrace (prefixWord ++ tailWord_2045101) baseStart_2045101 baseEnd_2045101 := by
    simpa [prefixWord, tailWord_2045101, baseEnd_2045101] using wordTrace_append hprefix tailTrace_2045101
  have hstable : (prefixWord ++ tailWord_2045101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045101).length < 2 ^ (prefixWord ++ tailWord_2045101).sum := by decide
  have hdescent : baseEnd_2045101 < baseStart_2045101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045157 : List Nat := [1, 3, 1, 4, 3, 2, 1, 2, 2, 3]
def baseStart_2045157 : Nat := 118140960795 + 2045157 * 2 ^ 59
def prefixEnd_2045157 : Nat := 4983230072969 + 3 ^ 40 * 2045157 * 2
def baseEnd_2045157 : Nat := 700099036604906698354667

theorem tailTrace_2045157 : CollatzResearch.WordTrace tailWord_2045157 prefixEnd_2045157 700099036604906698354667 := by
  unfold tailWord_2045157
  simp only [CollatzResearch.WordTrace]
  refine ⟨74593003851752948852709725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49728669234501965901806483 74593003851752948852709725)
  ·
    refine ⟨27972376444407355819766147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74593003851752948852709725 27972376444407355819766147)
    ·
      refine ⟨41958564666611033729649221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27972376444407355819766147 41958564666611033729649221)
      ·
        refine ⟨7867230874989568824309229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41958564666611033729649221 7867230874989568824309229)
        ·
          refine ⟨2950211578121088309115961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7867230874989568824309229 2950211578121088309115961)
          ·
            refine ⟨2212658683590816231836971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2950211578121088309115961 2212658683590816231836971)
            ·
              refine ⟨3318988025386224347755457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2212658683590816231836971 3318988025386224347755457)
              ·
                refine ⟨2489241019039668260816593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3318988025386224347755457 2489241019039668260816593)
                ·
                  refine ⟨1866930764279751195612445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2489241019039668260816593 1866930764279751195612445)
                  ·
                    refine ⟨700099036604906698354667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1866930764279751195612445 700099036604906698354667)
                    ·
                      rfl

theorem cell22_2045157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 3].length) (baseStart_2045157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045157 prefixEnd_2045157 := by exact prefixLift 2045157
  have htrace : WordTrace (prefixWord ++ tailWord_2045157) baseStart_2045157 baseEnd_2045157 := by
    simpa [prefixWord, tailWord_2045157, baseEnd_2045157] using wordTrace_append hprefix tailTrace_2045157
  have hstable : (prefixWord ++ tailWord_2045157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045157).length < 2 ^ (prefixWord ++ tailWord_2045157).sum := by decide
  have hdescent : baseEnd_2045157 < baseStart_2045157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045166 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_2045166 : Nat := 118140960795 + 2045166 * 2 ^ 59
def prefixEnd_2045166 : Nat := 4983230072969 + 3 ^ 40 * 2045166 * 2
def baseEnd_2045166 : Nat := 700102117488833674879639

theorem tailTrace_2045166 : CollatzResearch.WordTrace tailWord_2045166 prefixEnd_2045166 700102117488833674879639 := by
  unfold tailWord_2045166
  simp only [CollatzResearch.WordTrace]
  refine ⟨9324166513590042923723419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49728888072480228926524901 9324166513590042923723419)
  ·
    refine ⟨13986249770385064385585129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9324166513590042923723419 13986249770385064385585129)
    ·
      refine ⟨10489687327788798289188847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13986249770385064385585129 10489687327788798289188847)
      ·
        refine ⟨15734530991683197433783271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10489687327788798289188847 15734530991683197433783271)
        ·
          refine ⟨23601796487524796150674907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15734530991683197433783271 23601796487524796150674907)
          ·
            refine ⟨35402694731287194226012361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23601796487524796150674907 35402694731287194226012361)
            ·
              refine ⟨26552021048465395669509271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35402694731287194226012361 26552021048465395669509271)
              ·
                refine ⟨39828031572698093504263907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26552021048465395669509271 39828031572698093504263907)
                ·
                  refine ⟨59742047359047140256395861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39828031572698093504263907 59742047359047140256395861)
                  ·
                    refine ⟨700102117488833674879639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59742047359047140256395861 700102117488833674879639)
                    ·
                      rfl

theorem cell22_2045166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_2045166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045166 prefixEnd_2045166 := by exact prefixLift 2045166
  have htrace : WordTrace (prefixWord ++ tailWord_2045166) baseStart_2045166 baseEnd_2045166 := by
    simpa [prefixWord, tailWord_2045166, baseEnd_2045166] using wordTrace_append hprefix tailTrace_2045166
  have hstable : (prefixWord ++ tailWord_2045166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045166).length < 2 ^ (prefixWord ++ tailWord_2045166).sum := by decide
  have hdescent : baseEnd_2045166 < baseStart_2045166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045211 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 5, 4]
def baseStart_2045211 : Nat := 118140960795 + 2045211 * 2 ^ 59
def prefixEnd_2045211 : Nat := 4983230072969 + 3 ^ 40 * 2045211 * 2
def baseEnd_2045211 : Nat := 700117521908468557504501

theorem tailTrace_2045211 : CollatzResearch.WordTrace tailWord_2045211 prefixEnd_2045211 700117521908468557504501 := by
  unfold tailWord_2045211
  simp only [CollatzResearch.WordTrace]
  refine ⟨74594973393557316075175487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49729982262371544050116991 74594973393557316075175487)
  ·
    refine ⟨111892460090335974112763231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74594973393557316075175487 111892460090335974112763231)
    ·
      refine ⟨167838690135503961169144847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111892460090335974112763231 167838690135503961169144847)
      ·
        refine ⟨251758035203255941753717271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167838690135503961169144847 251758035203255941753717271)
        ·
          refine ⟨377637052804883912630575907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251758035203255941753717271 377637052804883912630575907)
          ·
            refine ⟨566455579207325868945863861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377637052804883912630575907 566455579207325868945863861)
            ·
              refine ⟨53105210550686800213674737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 566455579207325868945863861 53105210550686800213674737)
              ·
                refine ⟨39828907913015100160256053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53105210550686800213674737 39828907913015100160256053)
                ·
                  refine ⟨3733960116845165640024005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39828907913015100160256053 3733960116845165640024005)
                  ·
                    refine ⟨700117521908468557504501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3733960116845165640024005 700117521908468557504501)
                    ·
                      rfl

theorem cell22_2045211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 4].length) (baseStart_2045211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045211 prefixEnd_2045211 := by exact prefixLift 2045211
  have htrace : WordTrace (prefixWord ++ tailWord_2045211) baseStart_2045211 baseEnd_2045211 := by
    simpa [prefixWord, tailWord_2045211, baseEnd_2045211] using wordTrace_append hprefix tailTrace_2045211
  have hstable : (prefixWord ++ tailWord_2045211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045211).length < 2 ^ (prefixWord ++ tailWord_2045211).sum := by decide
  have hdescent : baseEnd_2045211 < baseStart_2045211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045258 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 6, 3]
def baseStart_2045258 : Nat := 118140960795 + 2045258 * 2 ^ 59
def prefixEnd_2045258 : Nat := 4983230072969 + 3 ^ 40 * 2045258 * 2
def baseEnd_2045258 : Nat := 700133610968976101579357

theorem tailTrace_2045258 : CollatzResearch.WordTrace tailWord_2045258 prefixEnd_2045258 700133610968976101579357 := by
  unfold tailWord_2045258
  simp only [CollatzResearch.WordTrace]
  refine ⟨18649171906096760775534107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49731125082924695401424285 18649171906096760775534107)
  ·
    refine ⟨27973757859145141163301161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18649171906096760775534107 27973757859145141163301161)
    ·
      refine ⟨20980318394358855872475871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27973757859145141163301161 20980318394358855872475871)
      ·
        refine ⟨31470477591538283808713807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20980318394358855872475871 31470477591538283808713807)
        ·
          refine ⟨47205716387307425713070711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31470477591538283808713807 47205716387307425713070711)
          ·
            refine ⟨70808574580961138569606067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47205716387307425713070711 70808574580961138569606067)
            ·
              refine ⟨106212861871441707854409101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70808574580961138569606067 106212861871441707854409101)
              ·
                refine ⟨39829823201790640445403413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106212861871441707854409101 39829823201790640445403413)
                ·
                  refine ⟨1867022962583936270878285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39829823201790640445403413 1867022962583936270878285)
                  ·
                    refine ⟨700133610968976101579357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1867022962583936270878285 700133610968976101579357)
                    ·
                      rfl

theorem cell22_2045258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_2045258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045258 prefixEnd_2045258 := by exact prefixLift 2045258
  have htrace : WordTrace (prefixWord ++ tailWord_2045258) baseStart_2045258 baseEnd_2045258 := by
    simpa [prefixWord, tailWord_2045258, baseEnd_2045258] using wordTrace_append hprefix tailTrace_2045258
  have hstable : (prefixWord ++ tailWord_2045258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045258).length < 2 ^ (prefixWord ++ tailWord_2045258).sum := by decide
  have hdescent : baseEnd_2045258 < baseStart_2045258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045271 : List Nat := [1, 1, 3, 2, 3, 12]
def baseStart_2045271 : Nat := 118140960795 + 2045271 * 2 ^ 59
def prefixEnd_2045271 : Nat := 4983230072969 + 3 ^ 40 * 2045271 * 2
def baseEnd_2045271 : Nat := 8643679767094424703757

theorem tailTrace_2045271 : CollatzResearch.WordTrace tailWord_2045271 prefixEnd_2045271 8643679767094424703757 := by
  unfold tailWord_2045271
  simp only [CollatzResearch.WordTrace]
  refine ⟨74597161773339946322359667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49731441182226630881573111 74597161773339946322359667)
  ·
    refine ⟨111895742660009919483539501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74597161773339946322359667 111895742660009919483539501)
    ·
      refine ⟨41960903497503719806327313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111895742660009919483539501 41960903497503719806327313)
      ·
        refine ⟨31470677623127789854745485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41960903497503719806327313 31470677623127789854745485)
        ·
          refine ⟨11801504108672921195529557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31470677623127789854745485 11801504108672921195529557)
          ·
            refine ⟨8643679767094424703757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 11801504108672921195529557 8643679767094424703757)
            ·
              rfl

theorem cell22_2045271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 12].length) (baseStart_2045271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045271 prefixEnd_2045271 := by exact prefixLift 2045271
  have htrace : WordTrace (prefixWord ++ tailWord_2045271) baseStart_2045271 baseEnd_2045271 := by
    simpa [prefixWord, tailWord_2045271, baseEnd_2045271] using wordTrace_append hprefix tailTrace_2045271
  have hstable : (prefixWord ++ tailWord_2045271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045271).length < 2 ^ (prefixWord ++ tailWord_2045271).sum := by decide
  have hdescent : baseEnd_2045271 < baseStart_2045271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045273 : List Nat := [1, 2, 1, 2, 2, 2, 4, 2, 2, 4]
def baseStart_2045273 : Nat := 118140960795 + 2045273 * 2 ^ 59
def prefixEnd_2045273 : Nat := 4983230072969 + 3 ^ 40 * 2045273 * 2
def baseEnd_2045273 : Nat := 700138745775521062454311

theorem tailTrace_2045273 : CollatzResearch.WordTrace tailWord_2045273 prefixEnd_2045273 700138745775521062454311 := by
  unfold tailWord_2045273
  simp only [CollatzResearch.WordTrace]
  refine ⟨74597234719332700663932473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49731489812888467109288315 74597234719332700663932473)
  ·
    refine ⟨55947926039499525497949355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74597234719332700663932473 55947926039499525497949355)
    ·
      refine ⟨83921889059249288246924033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55947926039499525497949355 83921889059249288246924033)
      ·
        refine ⟨62941416794436966185193025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83921889059249288246924033 62941416794436966185193025)
        ·
          refine ⟨47206062595827724638894769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62941416794436966185193025 47206062595827724638894769)
          ·
            refine ⟨35404546946870793479171077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47206062595827724638894769 35404546946870793479171077)
            ·
              refine ⟨6638352552538273777344577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35404546946870793479171077 6638352552538273777344577)
              ·
                refine ⟨4978764414403705333008433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6638352552538273777344577 4978764414403705333008433)
                ·
                  refine ⟨3734073310802778999756325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4978764414403705333008433 3734073310802778999756325)
                  ·
                    refine ⟨700138745775521062454311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3734073310802778999756325 700138745775521062454311)
                    ·
                      rfl

theorem cell22_2045273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 4].length) (baseStart_2045273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045273 prefixEnd_2045273 := by exact prefixLift 2045273
  have htrace : WordTrace (prefixWord ++ tailWord_2045273) baseStart_2045273 baseEnd_2045273 := by
    simpa [prefixWord, tailWord_2045273, baseEnd_2045273] using wordTrace_append hprefix tailTrace_2045273
  have hstable : (prefixWord ++ tailWord_2045273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045273).length < 2 ^ (prefixWord ++ tailWord_2045273).sum := by decide
  have hdescent : baseEnd_2045273 < baseStart_2045273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045326 : List Nat := [4, 1, 1, 4, 3, 1, 1, 2, 2, 3]
def baseStart_2045326 : Nat := 118140960795 + 2045326 * 2 ^ 59
def prefixEnd_2045326 : Nat := 4983230072969 + 3 ^ 40 * 2045326 * 2
def baseEnd_2045326 : Nat := 700156888758646590879149

theorem tailTrace_2045326 : CollatzResearch.WordTrace tailWord_2045326 prefixEnd_2045326 700156888758646590879149 := by
  unfold tailWord_2045326
  simp only [CollatzResearch.WordTrace]
  refine ⟨9324895973517586339451479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49732778525427127143741221 9324895973517586339451479)
  ·
    refine ⟨13987343960276379509177219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9324895973517586339451479 13987343960276379509177219)
    ·
      refine ⟨20981015940414569263765829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13987343960276379509177219 20981015940414569263765829)
      ·
        refine ⟨3933940488827731736956093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20981015940414569263765829 3933940488827731736956093)
        ·
          refine ⟨1475227683310399401358535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3933940488827731736956093 1475227683310399401358535)
          ·
            refine ⟨2212841524965599102037803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475227683310399401358535 2212841524965599102037803)
            ·
              refine ⟨3319262287448398653056705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2212841524965599102037803 3319262287448398653056705)
              ·
                refine ⟨2489446715586298989792529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3319262287448398653056705 2489446715586298989792529)
                ·
                  refine ⟨1867085036689724242344397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2489446715586298989792529 1867085036689724242344397)
                  ·
                    refine ⟨700156888758646590879149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1867085036689724242344397 700156888758646590879149)
                    ·
                      rfl

theorem cell22_2045326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_2045326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045326 prefixEnd_2045326 := by exact prefixLift 2045326
  have htrace : WordTrace (prefixWord ++ tailWord_2045326) baseStart_2045326 baseEnd_2045326 := by
    simpa [prefixWord, tailWord_2045326, baseEnd_2045326] using wordTrace_append hprefix tailTrace_2045326
  have hstable : (prefixWord ++ tailWord_2045326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045326).length < 2 ^ (prefixWord ++ tailWord_2045326).sum := by decide
  have hdescent : baseEnd_2045326 < baseStart_2045326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045337 : List Nat := [1, 2, 1, 2, 1, 5, 2, 4, 1, 3]
def baseStart_2045337 : Nat := 118140960795 + 2045337 * 2 ^ 59
def prefixEnd_2045337 : Nat := 4983230072969 + 3 ^ 40 * 2045337 * 2
def baseEnd_2045337 : Nat := 700160654283446228854115

theorem tailTrace_2045337 : CollatzResearch.WordTrace tailWord_2045337 prefixEnd_2045337 700160654283446228854115 := by
  unfold tailWord_2045337
  simp only [CollatzResearch.WordTrace]
  refine ⟨74599568991100839594262265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49733045994067226396174843 74599568991100839594262265)
  ·
    refine ⟨55949676743325629695696699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74599568991100839594262265 55949676743325629695696699)
    ·
      refine ⟨83924515114988444543545049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55949676743325629695696699 83924515114988444543545049)
      ·
        refine ⟨62943386336241333407658787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83924515114988444543545049 62943386336241333407658787)
        ·
          refine ⟨94415079504362000111488181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62943386336241333407658787 94415079504362000111488181)
          ·
            refine ⟨8851413703533937510452017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94415079504362000111488181 8851413703533937510452017)
            ·
              refine ⟨6638560277650453132839013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8851413703533937510452017 6638560277650453132839013)
              ·
                refine ⟨1244730052059459962407315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6638560277650453132839013 1244730052059459962407315)
                ·
                  refine ⟨1867095078089189943610973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1244730052059459962407315 1867095078089189943610973)
                  ·
                    refine ⟨700160654283446228854115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1867095078089189943610973 700160654283446228854115)
                    ·
                      rfl

theorem cell22_2045337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 1, 3].length) (baseStart_2045337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045337 prefixEnd_2045337 := by exact prefixLift 2045337
  have htrace : WordTrace (prefixWord ++ tailWord_2045337) baseStart_2045337 baseEnd_2045337 := by
    simpa [prefixWord, tailWord_2045337, baseEnd_2045337] using wordTrace_append hprefix tailTrace_2045337
  have hstable : (prefixWord ++ tailWord_2045337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045337).length < 2 ^ (prefixWord ++ tailWord_2045337).sum := by decide
  have hdescent : baseEnd_2045337 < baseStart_2045337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045363 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 3, 4]
def baseStart_2045363 : Nat := 118140960795 + 2045363 * 2 ^ 59
def prefixEnd_2045363 : Nat := 4983230072969 + 3 ^ 40 * 2045363 * 2
def baseEnd_2045363 : Nat := 700169554614790827704035

theorem tailTrace_2045363 : CollatzResearch.WordTrace tailWord_2045363 prefixEnd_2045363 700169554614790827704035 := by
  unfold tailWord_2045363
  simp only [CollatzResearch.WordTrace]
  refine ⟨74600517289006646034708743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49733678192671097356472495 74600517289006646034708743)
  ·
    refine ⟨111900775933509969052063115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74600517289006646034708743 111900775933509969052063115)
    ·
      refine ⟨167851163900264953578094673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111900775933509969052063115 167851163900264953578094673)
      ·
        refine ⟨125888372925198715183571005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167851163900264953578094673 125888372925198715183571005)
        ·
          refine ⟨47208139846949518193839127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125888372925198715183571005 47208139846949518193839127)
          ·
            refine ⟨70812209770424277290758691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47208139846949518193839127 70812209770424277290758691)
            ·
              refine ⟨106218314655636415936138037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70812209770424277290758691 106218314655636415936138037)
              ·
                refine ⟨9957966998965913994012941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106218314655636415936138037 9957966998965913994012941)
                ·
                  refine ⟨3734237624612217747754853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9957966998965913994012941 3734237624612217747754853)
                  ·
                    refine ⟨700169554614790827704035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3734237624612217747754853 700169554614790827704035)
                    ·
                      rfl

theorem cell22_2045363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 4].length) (baseStart_2045363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045363 prefixEnd_2045363 := by exact prefixLift 2045363
  have htrace : WordTrace (prefixWord ++ tailWord_2045363) baseStart_2045363 baseEnd_2045363 := by
    simpa [prefixWord, tailWord_2045363, baseEnd_2045363] using wordTrace_append hprefix tailTrace_2045363
  have hstable : (prefixWord ++ tailWord_2045363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045363).length < 2 ^ (prefixWord ++ tailWord_2045363).sum := by decide
  have hdescent : baseEnd_2045363 < baseStart_2045363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045408 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 1, 6]
def baseStart_2045408 : Nat := 118140960795 + 2045408 * 2 ^ 59
def prefixEnd_2045408 : Nat := 4983230072969 + 3 ^ 40 * 2045408 * 2
def baseEnd_2045408 : Nat := 700184959034425710328897

theorem tailTrace_2045408 : CollatzResearch.WordTrace tailWord_2045408 prefixEnd_2045408 700184959034425710328897 := by
  unfold tailWord_2045408
  simp only [CollatzResearch.WordTrace]
  refine ⟨37301079286921809360048439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49734772382562412480064585 37301079286921809360048439)
  ·
    refine ⟨55951618930382714040072659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37301079286921809360048439 55951618930382714040072659)
    ·
      refine ⟨83927428395574071060108989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55951618930382714040072659 83927428395574071060108989)
      ·
        refine ⟨31472785648340276647540871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83927428395574071060108989 31472785648340276647540871)
        ·
          refine ⟨47209178472510414971311307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31472785648340276647540871 47209178472510414971311307)
          ·
            refine ⟨70813767708765622456966961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47209178472510414971311307 70813767708765622456966961)
            ·
              refine ⟨53110325781574216842725221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70813767708765622456966961 53110325781574216842725221)
              ·
                refine ⟨9958186084045165658010979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53110325781574216842725221 9958186084045165658010979)
                ·
                  refine ⟨14937279126067748487016469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9958186084045165658010979 14937279126067748487016469)
                  ·
                    refine ⟨700184959034425710328897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14937279126067748487016469 700184959034425710328897)
                    ·
                      rfl

theorem cell22_2045408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_2045408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045408 prefixEnd_2045408 := by exact prefixLift 2045408
  have htrace : WordTrace (prefixWord ++ tailWord_2045408) baseStart_2045408 baseEnd_2045408 := by
    simpa [prefixWord, tailWord_2045408, baseEnd_2045408] using wordTrace_append hprefix tailTrace_2045408
  have hstable : (prefixWord ++ tailWord_2045408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045408).length < 2 ^ (prefixWord ++ tailWord_2045408).sum := by decide
  have hdescent : baseEnd_2045408 < baseStart_2045408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045423 : List Nat := [1, 1, 2, 1, 4, 1, 4, 8]
def baseStart_2045423 : Nat := 118140960795 + 2045423 * 2 ^ 59
def prefixEnd_2045423 : Nat := 4983230072969 + 3 ^ 40 * 2045423 * 2
def baseEnd_2045423 : Nat := 77798899315663407911539

theorem tailTrace_2045423 : CollatzResearch.WordTrace tailWord_2045423 prefixEnd_2045423 77798899315663407911539 := by
  unfold tailWord_2045423
  simp only [CollatzResearch.WordTrace]
  refine ⟨74602705668789276281892923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49735137112526184187928615 74602705668789276281892923)
  ·
    refine ⟨111904058503183914422839385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74602705668789276281892923 111904058503183914422839385)
    ·
      refine ⟨83928043877387935817129539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111904058503183914422839385 83928043877387935817129539)
      ·
        refine ⟨125892065816081903725694309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83928043877387935817129539 125892065816081903725694309)
        ·
          refine ⟨23604762340515356948567683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125892065816081903725694309 23604762340515356948567683)
          ·
            refine ⟨35407143510773035422851525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23604762340515356948567683 35407143510773035422851525)
            ·
              refine ⟨6638839408269944141784661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35407143510773035422851525 6638839408269944141784661)
              ·
                refine ⟨77798899315663407911539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6638839408269944141784661 77798899315663407911539)
                ·
                  rfl

theorem cell22_2045423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 8].length) (baseStart_2045423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045423 prefixEnd_2045423 := by exact prefixLift 2045423
  have htrace : WordTrace (prefixWord ++ tailWord_2045423) baseStart_2045423 baseEnd_2045423 := by
    simpa [prefixWord, tailWord_2045423, baseEnd_2045423] using wordTrace_append hprefix tailTrace_2045423
  have hstable : (prefixWord ++ tailWord_2045423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045423).length < 2 ^ (prefixWord ++ tailWord_2045423).sum := by decide
  have hdescent : baseEnd_2045423 < baseStart_2045423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045425 : List Nat := [1, 2, 2, 2, 3, 2, 1, 3, 2, 4]
def baseStart_2045425 : Nat := 118140960795 + 2045425 * 2 ^ 59
def prefixEnd_2045425 : Nat := 4983230072969 + 3 ^ 40 * 2045425 * 2
def baseEnd_2045425 : Nat := 700190778481843332653845

theorem tailTrace_2045425 : CollatzResearch.WordTrace tailWord_2045425 prefixEnd_2045425 700190778481843332653845 := by
  unfold tailWord_2045425
  simp only [CollatzResearch.WordTrace]
  refine ⟨74602778614782030623465729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49735185743188020415643819 74602778614782030623465729)
  ·
    refine ⟨55952083961086522967599297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74602778614782030623465729 55952083961086522967599297)
    ·
      refine ⟨41964062970814892225699473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55952083961086522967599297 41964062970814892225699473)
      ·
        refine ⟨31473047228111169169274605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41964062970814892225699473 31473047228111169169274605)
        ·
          refine ⟨11802392710541688438477977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31473047228111169169274605 11802392710541688438477977)
          ·
            refine ⟨8851794532906266328858483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11802392710541688438477977 8851794532906266328858483)
            ·
              refine ⟨13277691799359399493287725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8851794532906266328858483 13277691799359399493287725)
              ·
                refine ⟨4979134424759774809982897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13277691799359399493287725 4979134424759774809982897)
                ·
                  refine ⟨3734350818569831107487173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4979134424759774809982897 3734350818569831107487173)
                  ·
                    refine ⟨700190778481843332653845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3734350818569831107487173 700190778481843332653845)
                    ·
                      rfl

theorem cell22_2045425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_2045425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045425 prefixEnd_2045425 := by exact prefixLift 2045425
  have htrace : WordTrace (prefixWord ++ tailWord_2045425) baseStart_2045425 baseEnd_2045425 := by
    simpa [prefixWord, tailWord_2045425, baseEnd_2045425] using wordTrace_append hprefix tailTrace_2045425
  have hstable : (prefixWord ++ tailWord_2045425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045425).length < 2 ^ (prefixWord ++ tailWord_2045425).sum := by decide
  have hdescent : baseEnd_2045425 < baseStart_2045425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045472 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 5, 3]
def baseStart_2045472 : Nat := 118140960795 + 2045472 * 2 ^ 59
def prefixEnd_2045472 : Nat := 4983230072969 + 3 ^ 40 * 2045472 * 2
def baseEnd_2045472 : Nat := 700206867542350876728701

theorem tailTrace_2045472 : CollatzResearch.WordTrace tailWord_2045472 prefixEnd_2045472 700206867542350876728701 := by
  unfold tailWord_2045472
  simp only [CollatzResearch.WordTrace]
  refine ⟨37302246422805878825213335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49736328563741171766951113 37302246422805878825213335)
  ·
    refine ⟨55953369634208818237820003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37302246422805878825213335 55953369634208818237820003)
    ·
      refine ⟨83930054451313227356730005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55953369634208818237820003 83930054451313227356730005)
      ·
        refine ⟨3934221302405307532346719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83930054451313227356730005 3934221302405307532346719)
        ·
          refine ⟨5901331953607961298520079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3934221302405307532346719 5901331953607961298520079)
          ·
            refine ⟨8851997930411941947780119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5901331953607961298520079 8851997930411941947780119)
            ·
              refine ⟨13277996895617912921670179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8851997930411941947780119 13277996895617912921670179)
              ·
                refine ⟨19916995343426869382505269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13277996895617912921670179 19916995343426869382505269)
                ·
                  refine ⟨1867218313446269004609869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19916995343426869382505269 1867218313446269004609869)
                  ·
                    refine ⟨700206867542350876728701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1867218313446269004609869 700206867542350876728701)
                    ·
                      rfl

theorem cell22_2045472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 5, 3].length) (baseStart_2045472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045472 prefixEnd_2045472 := by exact prefixLift 2045472
  have htrace : WordTrace (prefixWord ++ tailWord_2045472) baseStart_2045472 baseEnd_2045472 := by
    simpa [prefixWord, tailWord_2045472, baseEnd_2045472] using wordTrace_append hprefix tailTrace_2045472
  have hstable : (prefixWord ++ tailWord_2045472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045472).length < 2 ^ (prefixWord ++ tailWord_2045472).sum := by decide
  have hdescent : baseEnd_2045472 < baseStart_2045472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045545 : List Nat := [1, 2, 1, 1, 1, 4, 2, 4, 1, 5]
def baseStart_2045545 : Nat := 118140960795 + 2045545 * 2 ^ 59
def prefixEnd_2045545 : Nat := 4983230072969 + 3 ^ 40 * 2045545 * 2
def baseEnd_2045545 : Nat := 700231856934203019653477

theorem tailTrace_2045545 : CollatzResearch.WordTrace tailWord_2045545 prefixEnd_2045545 700231856934203019653477 := by
  unfold tailWord_2045545
  simp only [CollatzResearch.WordTrace]
  refine ⟨74607155374347291117834089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49738103582898194078556059 74607155374347291117834089)
  ·
    refine ⟨55955366530760468338375567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74607155374347291117834089 55955366530760468338375567)
    ·
      refine ⟨83933049796140702507563351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55955366530760468338375567 83933049796140702507563351)
      ·
        refine ⟨125899574694211053761345027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83933049796140702507563351 125899574694211053761345027)
        ·
          refine ⟨188849362041316580642017541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125899574694211053761345027 188849362041316580642017541)
          ·
            refine ⟨35409255382746858870378289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188849362041316580642017541 35409255382746858870378289)
            ·
              refine ⟨26556941537060144152783717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35409255382746858870378289 26556941537060144152783717)
              ·
                refine ⟨4979426538198777028646947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26556941537060144152783717 4979426538198777028646947)
                ·
                  refine ⟨7469139807298165542970421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4979426538198777028646947 7469139807298165542970421)
                  ·
                    refine ⟨700231856934203019653477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7469139807298165542970421 700231856934203019653477)
                    ·
                      rfl

theorem cell22_2045545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 5].length) (baseStart_2045545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045545 prefixEnd_2045545 := by exact prefixLift 2045545
  have htrace : WordTrace (prefixWord ++ tailWord_2045545) baseStart_2045545 baseEnd_2045545 := by
    simpa [prefixWord, tailWord_2045545, baseEnd_2045545] using wordTrace_append hprefix tailTrace_2045545
  have hstable : (prefixWord ++ tailWord_2045545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045545).length < 2 ^ (prefixWord ++ tailWord_2045545).sum := by decide
  have hdescent : baseEnd_2045545 < baseStart_2045545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045575 : List Nat := [1, 1, 4, 2, 1, 3, 1, 9]
def baseStart_2045575 : Nat := 118140960795 + 2045575 * 2 ^ 59
def prefixEnd_2045575 : Nat := 4983230072969 + 3 ^ 40 * 2045575 * 2
def baseEnd_2045575 : Nat := 77804680727476993489265

theorem tailTrace_2045575 : CollatzResearch.WordTrace tailWord_2045575 prefixEnd_2045575 77804680727476993489265 := by
  unfold tailWord_2045575
  simp only [CollatzResearch.WordTrace]
  refine ⟨74608249564238606241426179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49738833042825737494284119 74608249564238606241426179)
  ·
    refine ⟨111912374346357909362139269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74608249564238606241426179 111912374346357909362139269)
    ·
      refine ⟨20983570189942108005401113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111912374346357909362139269 20983570189942108005401113)
      ·
        refine ⟨15737677642456581004050835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20983570189942108005401113 15737677642456581004050835)
        ·
          refine ⟨23606516463684871506076253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15737677642456581004050835 23606516463684871506076253)
          ·
            refine ⟨8852443673881826814778595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23606516463684871506076253 8852443673881826814778595)
            ·
              refine ⟨13278665510822740222167893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8852443673881826814778595 13278665510822740222167893)
              ·
                refine ⟨77804680727476993489265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13278665510822740222167893 77804680727476993489265)
                ·
                  rfl

theorem cell22_2045575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 9].length) (baseStart_2045575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045575 prefixEnd_2045575 := by exact prefixLift 2045575
  have htrace : WordTrace (prefixWord ++ tailWord_2045575) baseStart_2045575 baseEnd_2045575 := by
    simpa [prefixWord, tailWord_2045575, baseEnd_2045575] using wordTrace_append hprefix tailTrace_2045575
  have hstable : (prefixWord ++ tailWord_2045575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045575).length < 2 ^ (prefixWord ++ tailWord_2045575).sum := by decide
  have hdescent : baseEnd_2045575 < baseStart_2045575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045729 : List Nat := [1, 2, 3, 2, 1, 4, 1, 2, 2, 4]
def baseStart_2045729 : Nat := 118140960795 + 2045729 * 2 ^ 59
def prefixEnd_2045729 : Nat := 4983230072969 + 3 ^ 40 * 2045729 * 2
def baseEnd_2045729 : Nat := 700294843894487873052913

theorem tailTrace_2045729 : CollatzResearch.WordTrace tailWord_2045729 prefixEnd_2045729 700294843894487873052913 := by
  unfold tailWord_2045729
  simp only [CollatzResearch.WordTrace]
  refine ⟨74613866405680690542532241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49742577603787127028354827 74613866405680690542532241)
  ·
    refine ⟨55960399804260517906899181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74613866405680690542532241 55960399804260517906899181)
    ·
      refine ⟨20985149926597694215087193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55960399804260517906899181 20985149926597694215087193)
      ·
        refine ⟨15738862444948270661315395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20985149926597694215087193 15738862444948270661315395)
        ·
          refine ⟨23608293667422405991973093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15738862444948270661315395 23608293667422405991973093)
          ·
            refine ⟨4426555062641701123494955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23608293667422405991973093 4426555062641701123494955)
            ·
              refine ⟨6639832593962551685242433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4426555062641701123494955 6639832593962551685242433)
              ·
                refine ⟨4979874445471913763931825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6639832593962551685242433 4979874445471913763931825)
                ·
                  refine ⟨3734905834103935322948869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4979874445471913763931825 3734905834103935322948869)
                  ·
                    refine ⟨700294843894487873052913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3734905834103935322948869 700294843894487873052913)
                    ·
                      rfl

theorem cell22_2045729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_2045729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045729 prefixEnd_2045729 := by exact prefixLift 2045729
  have htrace : WordTrace (prefixWord ++ tailWord_2045729) baseStart_2045729 baseEnd_2045729 := by
    simpa [prefixWord, tailWord_2045729, baseEnd_2045729] using wordTrace_append hprefix tailTrace_2045729
  have hstable : (prefixWord ++ tailWord_2045729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045729).length < 2 ^ (prefixWord ++ tailWord_2045729).sum := by decide
  have hdescent : baseEnd_2045729 < baseStart_2045729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045748 : List Nat := [2, 5, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_2045748 : Nat := 118140960795 + 2045748 * 2 ^ 59
def prefixEnd_2045748 : Nat := 4983230072969 + 3 ^ 40 * 2045748 * 2
def baseEnd_2045748 : Nat := 700301347982778156827855

theorem tailTrace_2045748 : CollatzResearch.WordTrace tailWord_2045748 prefixEnd_2045748 700301347982778156827855 := by
  unfold tailWord_2045748
  simp only [CollatzResearch.WordTrace]
  refine ⟨37307279696305928393736949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49743039595074571191649265 37307279696305928393736949)
  ·
    refine ⟨3497557471528680786912839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37307279696305928393736949 3497557471528680786912839)
    ·
      refine ⟨5246336207293021180369259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3497557471528680786912839 5246336207293021180369259)
      ·
        refine ⟨7869504310939531770553889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5246336207293021180369259 7869504310939531770553889)
        ·
          refine ⟨5902128233204648827915417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7869504310939531770553889 5902128233204648827915417)
          ·
            refine ⟨4426596174903486620936563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5902128233204648827915417 4426596174903486620936563)
            ·
              refine ⟨6639894262355229931404845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4426596174903486620936563 6639894262355229931404845)
              ·
                refine ⟨2489960348383211224276817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6639894262355229931404845 2489960348383211224276817)
                ·
                  refine ⟨1867470261287408418207613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2489960348383211224276817 1867470261287408418207613)
                  ·
                    refine ⟨700301347982778156827855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1867470261287408418207613 700301347982778156827855)
                    ·
                      rfl

theorem cell22_2045748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_2045748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045748 prefixEnd_2045748 := by exact prefixLift 2045748
  have htrace : WordTrace (prefixWord ++ tailWord_2045748) baseStart_2045748 baseEnd_2045748 := by
    simpa [prefixWord, tailWord_2045748, baseEnd_2045748] using wordTrace_append hprefix tailTrace_2045748
  have hstable : (prefixWord ++ tailWord_2045748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045748).length < 2 ^ (prefixWord ++ tailWord_2045748).sum := by decide
  have hdescent : baseEnd_2045748 < baseStart_2045748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045776 : List Nat := [2, 1, 1, 1, 1, 4, 1, 7, 1, 3]
def baseStart_2045776 : Nat := 118140960795 + 2045776 * 2 ^ 59
def prefixEnd_2045776 : Nat := 4983230072969 + 3 ^ 40 * 2045776 * 2
def baseEnd_2045776 : Nat := 700310932954995417127769

theorem tailTrace_2045776 : CollatzResearch.WordTrace tailWord_2045776 prefixEnd_2045776 700310932954995417127769 := by
  unfold tailWord_2045776
  simp only [CollatzResearch.WordTrace]
  refine ⟨37307790318255208784746591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49743720424340278379662121 37307790318255208784746591)
  ·
    refine ⟨55961685477382813177119887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37307790318255208784746591 55961685477382813177119887)
    ·
      refine ⟨83942528216074219765679831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55961685477382813177119887 83942528216074219765679831)
      ·
        refine ⟨125913792324111329648519747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83942528216074219765679831 125913792324111329648519747)
        ·
          refine ⟨188870688486166994472779621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125913792324111329648519747 188870688486166994472779621)
          ·
            refine ⟨35413254091156311463646179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188870688486166994472779621 35413254091156311463646179)
            ·
              refine ⟨53119881136734467195469269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35413254091156311463646179 53119881136734467195469269)
              ·
                refine ⟨1244997214142214074893811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53119881136734467195469269 1244997214142214074893811)
                ·
                  refine ⟨1867495821213321112340717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1244997214142214074893811 1867495821213321112340717)
                  ·
                    refine ⟨700310932954995417127769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1867495821213321112340717 700310932954995417127769)
                    ·
                      rfl

theorem cell22_2045776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 1, 3].length) (baseStart_2045776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045776 prefixEnd_2045776 := by exact prefixLift 2045776
  have htrace : WordTrace (prefixWord ++ tailWord_2045776) baseStart_2045776 baseEnd_2045776 := by
    simpa [prefixWord, tailWord_2045776, baseEnd_2045776] using wordTrace_append hprefix tailTrace_2045776
  have hstable : (prefixWord ++ tailWord_2045776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045776).length < 2 ^ (prefixWord ++ tailWord_2045776).sum := by decide
  have hdescent : baseEnd_2045776 < baseStart_2045776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045804 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 2, 5]
def baseStart_2045804 : Nat := 118140960795 + 2045804 * 2 ^ 59
def prefixEnd_2045804 : Nat := 4983230072969 + 3 ^ 40 * 2045804 * 2
def baseEnd_2045804 : Nat := 700320517927212677427683

theorem tailTrace_2045804 : CollatzResearch.WordTrace tailWord_2045804 prefixEnd_2045804 700320517927212677427683 := by
  unfold tailWord_2045804
  simp only [CollatzResearch.WordTrace]
  refine ⟨37308300940204489175756233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49744401253605985567674977 37308300940204489175756233)
  ·
    refine ⟨27981225705153366881817175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37308300940204489175756233 27981225705153366881817175)
    ·
      refine ⟨41971838557730050322725763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27981225705153366881817175 41971838557730050322725763)
      ·
        refine ⟨62957757836595075484088645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41971838557730050322725763 62957757836595075484088645)
        ·
          refine ⟨11804579594361576653266621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62957757836595075484088645 11804579594361576653266621)
          ·
            refine ⟨4426717347885591244974983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11804579594361576653266621 4426717347885591244974983)
            ·
              refine ⟨6640076021828386867462475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4426717347885591244974983 6640076021828386867462475)
              ·
                refine ⟨9960114032742580301193713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6640076021828386867462475 9960114032742580301193713)
                ·
                  refine ⟨7470085524556935225895285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9960114032742580301193713 7470085524556935225895285)
                  ·
                    refine ⟨700320517927212677427683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7470085524556935225895285 700320517927212677427683)
                    ·
                      rfl

theorem cell22_2045804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_2045804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045804 prefixEnd_2045804 := by exact prefixLift 2045804
  have htrace : WordTrace (prefixWord ++ tailWord_2045804) baseStart_2045804 baseEnd_2045804 := by
    simpa [prefixWord, tailWord_2045804, baseEnd_2045804] using wordTrace_append hprefix tailTrace_2045804
  have hstable : (prefixWord ++ tailWord_2045804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045804).length < 2 ^ (prefixWord ++ tailWord_2045804).sum := by decide
  have hdescent : baseEnd_2045804 < baseStart_2045804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045806 : List Nat := [4, 1, 2, 3, 1, 1, 2, 3, 5]
def baseStart_2045806 : Nat := 118140960795 + 2045806 * 2 ^ 59
def prefixEnd_2045806 : Nat := 4983230072969 + 3 ^ 40 * 2045806 * 2
def baseEnd_2045806 : Nat := 233440400856028446292559

theorem tailTrace_2045806 : CollatzResearch.WordTrace tailWord_2045806 prefixEnd_2045806 233440400856028446292559 := by
  unfold tailWord_2045806
  simp only [CollatzResearch.WordTrace]
  refine ⟨9327084353300216586635659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49744449884267821795390181 9327084353300216586635659)
  ·
    refine ⟨13990626529950324879953489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9327084353300216586635659 13990626529950324879953489)
    ·
      refine ⟨10492969897462743659965117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13990626529950324879953489 10492969897462743659965117)
      ·
        refine ⟨3934863711548528872486919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10492969897462743659965117 3934863711548528872486919)
        ·
          refine ⟨5902295567322793308730379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3934863711548528872486919 5902295567322793308730379)
          ·
            refine ⟨8853443350984189963095569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5902295567322793308730379 8853443350984189963095569)
            ·
              refine ⟨6640082513238142472321677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8853443350984189963095569 6640082513238142472321677)
              ·
                refine ⟨2490030942464303427120629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6640082513238142472321677 2490030942464303427120629)
                ·
                  refine ⟨233440400856028446292559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2490030942464303427120629 233440400856028446292559)
                  ·
                    rfl

theorem cell22_2045806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_2045806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045806 prefixEnd_2045806 := by exact prefixLift 2045806
  have htrace : WordTrace (prefixWord ++ tailWord_2045806) baseStart_2045806 baseEnd_2045806 := by
    simpa [prefixWord, tailWord_2045806, baseEnd_2045806] using wordTrace_append hprefix tailTrace_2045806
  have hstable : (prefixWord ++ tailWord_2045806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045806).length < 2 ^ (prefixWord ++ tailWord_2045806).sum := by decide
  have hdescent : baseEnd_2045806 < baseStart_2045806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045819 : List Nat := [1, 1, 1, 1, 1, 5, 1, 6, 1, 4]
def baseStart_2045819 : Nat := 118140960795 + 2045819 * 2 ^ 59
def prefixEnd_2045819 : Nat := 4983230072969 + 3 ^ 40 * 2045819 * 2
def baseEnd_2045819 : Nat := 700325652733757638302637

theorem tailTrace_2045819 : CollatzResearch.WordTrace tailWord_2045819 prefixEnd_2045819 700325652733757638302637 := by
  unfold tailWord_2045819
  simp only [CollatzResearch.WordTrace]
  refine ⟨74617148975354635913308511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49744765983569757275539007 74617148975354635913308511)
  ·
    refine ⟨111925723463031953869962767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74617148975354635913308511 111925723463031953869962767)
    ·
      refine ⟨167888585194547930804944151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111925723463031953869962767 167888585194547930804944151)
      ·
        refine ⟨251832877791821896207416227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167888585194547930804944151 251832877791821896207416227)
        ·
          refine ⟨377749316687732844311124341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251832877791821896207416227 377749316687732844311124341)
          ·
            refine ⟨35413998439474954154167907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 377749316687732844311124341 35413998439474954154167907)
            ·
              refine ⟨53120997659212431231251861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35413998439474954154167907 53120997659212431231251861)
              ·
                refine ⟨2490046765275582713964931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53120997659212431231251861 2490046765275582713964931)
                ·
                  refine ⟨3735070147913374070947397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2490046765275582713964931 3735070147913374070947397)
                  ·
                    refine ⟨700325652733757638302637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3735070147913374070947397 700325652733757638302637)
                    ·
                      rfl

theorem cell22_2045819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 4].length) (baseStart_2045819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045819 prefixEnd_2045819 := by exact prefixLift 2045819
  have htrace : WordTrace (prefixWord ++ tailWord_2045819) baseStart_2045819 baseEnd_2045819 := by
    simpa [prefixWord, tailWord_2045819, baseEnd_2045819] using wordTrace_append hprefix tailTrace_2045819
  have hstable : (prefixWord ++ tailWord_2045819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045819).length < 2 ^ (prefixWord ++ tailWord_2045819).sum := by decide
  have hdescent : baseEnd_2045819 < baseStart_2045819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045917 : List Nat := [1, 4, 3, 1, 3, 2, 2, 1, 2, 3]
def baseStart_2045917 : Nat := 118140960795 + 2045917 * 2 ^ 59
def prefixEnd_2045917 : Nat := 4983230072969 + 3 ^ 40 * 2045917 * 2
def baseEnd_2045917 : Nat := 700359200136518049352337

theorem tailTrace_2045917 : CollatzResearch.WordTrace tailWord_2045917 prefixEnd_2045917 700359200136518049352337 := by
  unfold tailWord_2045917
  simp only [CollatzResearch.WordTrace]
  refine ⟨74620723328999598650376005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49747148885999732433584003 74620723328999598650376005)
  ·
    refine ⟨13991385624187424746945501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74620723328999598650376005 13991385624187424746945501)
    ·
      refine ⟨5246769609070284280104563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13991385624187424746945501 5246769609070284280104563)
      ·
        refine ⟨7870154413605426420156845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5246769609070284280104563 7870154413605426420156845)
        ·
          refine ⟨2951307905102034907558817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7870154413605426420156845 2951307905102034907558817)
          ·
            refine ⟨2213480928826526180669113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2951307905102034907558817 2213480928826526180669113)
            ·
              refine ⟨1660110696619894635501835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2213480928826526180669113 1660110696619894635501835)
              ·
                refine ⟨2490166044929841953252753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1660110696619894635501835 2490166044929841953252753)
                ·
                  refine ⟨1867624533697381464939565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2490166044929841953252753 1867624533697381464939565)
                  ·
                    refine ⟨700359200136518049352337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1867624533697381464939565 700359200136518049352337)
                    ·
                      rfl

theorem cell22_2045917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_2045917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045917 prefixEnd_2045917 := by exact prefixLift 2045917
  have htrace : WordTrace (prefixWord ++ tailWord_2045917) baseStart_2045917 baseEnd_2045917 := by
    simpa [prefixWord, tailWord_2045917, baseEnd_2045917] using wordTrace_append hprefix tailTrace_2045917
  have hstable : (prefixWord ++ tailWord_2045917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045917).length < 2 ^ (prefixWord ++ tailWord_2045917).sum := by decide
  have hdescent : baseEnd_2045917 < baseStart_2045917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045986 : List Nat := [3, 3, 1, 1, 1, 2, 3, 2, 6]
def baseStart_2045986 : Nat := 118140960795 + 2045986 * 2 ^ 59
def prefixEnd_2045986 : Nat := 4983230072969 + 3 ^ 40 * 2045986 * 2
def baseEnd_2045986 : Nat := 233460940082208289792375

theorem tailTrace_2045986 : CollatzResearch.WordTrace tailWord_2045986 prefixEnd_2045986 233460940082208289792375 := by
  unfold tailWord_2045986
  simp only [CollatzResearch.WordTrace]
  refine ⟨18655809991437405858659453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49748826643833082289758541 18655809991437405858659453)
  ·
    refine ⟨6995928746789027196997295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18655809991437405858659453 6995928746789027196997295)
    ·
      refine ⟨10493893120183540795495943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6995928746789027196997295 10493893120183540795495943)
      ·
        refine ⟨15740839680275311193243915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10493893120183540795495943 15740839680275311193243915)
        ·
          refine ⟨23611259520412966789865873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15740839680275311193243915 23611259520412966789865873)
          ·
            refine ⟨17708444640309725092399405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23611259520412966789865873 17708444640309725092399405)
            ·
              refine ⟨6640666740116146909649777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17708444640309725092399405 6640666740116146909649777)
              ·
                refine ⟨4980500055087110182237333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6640666740116146909649777 4980500055087110182237333)
                ·
                  refine ⟨233460940082208289792375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4980500055087110182237333 233460940082208289792375)
                  ·
                    rfl

theorem cell22_2045986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_2045986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2045986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2045986 prefixEnd_2045986 := by exact prefixLift 2045986
  have htrace : WordTrace (prefixWord ++ tailWord_2045986) baseStart_2045986 baseEnd_2045986 := by
    simpa [prefixWord, tailWord_2045986, baseEnd_2045986] using wordTrace_append hprefix tailTrace_2045986
  have hstable : (prefixWord ++ tailWord_2045986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045986).length < 2 ^ (prefixWord ++ tailWord_2045986).sum := by decide
  have hdescent : baseEnd_2045986 < baseStart_2045986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046001 : List Nat := [1, 2, 2, 3, 1, 3, 2, 2, 1, 5]
def baseStart_2046001 : Nat := 118140960795 + 2046001 * 2 ^ 59
def prefixEnd_2046001 : Nat := 4983230072969 + 3 ^ 40 * 2046001 * 2
def baseEnd_2046001 : Nat := 700387955053169830252079

theorem tailTrace_2046001 : CollatzResearch.WordTrace tailWord_2046001 prefixEnd_2046001 700387955053169830252079 := by
  unfold tailWord_2046001
  simp only [CollatzResearch.WordTrace]
  refine ⟨74623787060695280996433857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49749191373796853997622571 74623787060695280996433857)
  ·
    refine ⟨55967840295521460747325393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74623787060695280996433857 55967840295521460747325393)
    ·
      refine ⟨41975880221641095560494045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55967840295521460747325393 41975880221641095560494045)
      ·
        refine ⟨15740955083115410835185267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41975880221641095560494045 15740955083115410835185267)
        ·
          refine ⟨23611432624673116252777901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15740955083115410835185267 23611432624673116252777901)
          ·
            refine ⟨8854287234252418594791713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23611432624673116252777901 8854287234252418594791713)
            ·
              refine ⟨6640715425689313946093785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8854287234252418594791713 6640715425689313946093785)
              ·
                refine ⟨4980536569266985459570339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6640715425689313946093785 4980536569266985459570339)
                ·
                  refine ⟨7470804853900478189355509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4980536569266985459570339 7470804853900478189355509)
                  ·
                    refine ⟨700387955053169830252079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7470804853900478189355509 700387955053169830252079)
                    ·
                      rfl

theorem cell22_2046001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_2046001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046001 prefixEnd_2046001 := by exact prefixLift 2046001
  have htrace : WordTrace (prefixWord ++ tailWord_2046001) baseStart_2046001 baseEnd_2046001 := by
    simpa [prefixWord, tailWord_2046001, baseEnd_2046001] using wordTrace_append hprefix tailTrace_2046001
  have hstable : (prefixWord ++ tailWord_2046001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046001).length < 2 ^ (prefixWord ++ tailWord_2046001).sum := by decide
  have hdescent : baseEnd_2046001 < baseStart_2046001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046048 : List Nat := [2, 1, 1, 3, 2, 5, 2, 6]
def baseStart_2046048 : Nat := 118140960795 + 2046048 * 2 ^ 59
def prefixEnd_2046048 : Nat := 4983230072969 + 3 ^ 40 * 2046048 * 2
def baseEnd_2046048 : Nat := 77822671568186374925215

theorem tailTrace_2046048 : CollatzResearch.WordTrace tailWord_2046048 prefixEnd_2046048 77822671568186374925215 := by
  unfold tailWord_2046048
  simp only [CollatzResearch.WordTrace]
  refine ⟨37312750645762504011697399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49750334194350005348929865 37312750645762504011697399)
  ·
    refine ⟨55969125968643756017546099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37312750645762504011697399 55969125968643756017546099)
    ·
      refine ⟨83953688952965634026319149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55969125968643756017546099 83953688952965634026319149)
      ·
        refine ⟨31482633357362112759869681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83953688952965634026319149 31482633357362112759869681)
        ·
          refine ⟨23611975018021584569902261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31482633357362112759869681 23611975018021584569902261)
          ·
            refine ⟨2213622657939523553428337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23611975018021584569902261 2213622657939523553428337)
            ·
              refine ⟨1660216993454642665071253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2213622657939523553428337 1660216993454642665071253)
              ·
                refine ⟨77822671568186374925215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1660216993454642665071253 77822671568186374925215)
                ·
                  rfl

theorem cell22_2046048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 6].length) (baseStart_2046048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046048 prefixEnd_2046048 := by exact prefixLift 2046048
  have htrace : WordTrace (prefixWord ++ tailWord_2046048) baseStart_2046048 baseEnd_2046048 := by
    simpa [prefixWord, tailWord_2046048, baseEnd_2046048] using wordTrace_append hprefix tailTrace_2046048
  have hstable : (prefixWord ++ tailWord_2046048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046048).length < 2 ^ (prefixWord ++ tailWord_2046048).sum := by decide
  have hdescent : baseEnd_2046048 < baseStart_2046048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046076 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 7]
def baseStart_2046076 : Nat := 118140960795 + 2046076 * 2 ^ 59
def prefixEnd_2046076 : Nat := 4983230072969 + 3 ^ 40 * 2046076 * 2
def baseEnd_2046076 : Nat := 233471209695298211542283

theorem tailTrace_2046076 : CollatzResearch.WordTrace tailWord_2046076 prefixEnd_2046076 233471209695298211542283 := by
  unfold tailWord_2046076
  simp only [CollatzResearch.WordTrace]
  refine ⟨37313261267711784402707041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49751015023615712536942721 37313261267711784402707041)
  ·
    refine ⟨27984945950783838302030281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37313261267711784402707041 27984945950783838302030281)
    ·
      refine ⟨20988709463087878726522711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27984945950783838302030281 20988709463087878726522711)
      ·
        refine ⟨31483064194631818089784067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20988709463087878726522711 31483064194631818089784067)
        ·
          refine ⟨47224596291947727134676101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31483064194631818089784067 47224596291947727134676101)
          ·
            refine ⟨8854611804740198837751769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47224596291947727134676101 8854611804740198837751769)
            ·
              refine ⟨6640958853555149128313827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8854611804740198837751769 6640958853555149128313827)
              ·
                refine ⟨9961438280332723692470741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6640958853555149128313827 9961438280332723692470741)
                ·
                  refine ⟨233471209695298211542283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9961438280332723692470741 233471209695298211542283)
                  ·
                    rfl

theorem cell22_2046076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_2046076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046076 prefixEnd_2046076 := by exact prefixLift 2046076
  have htrace : WordTrace (prefixWord ++ tailWord_2046076) baseStart_2046076 baseEnd_2046076 := by
    simpa [prefixWord, tailWord_2046076, baseEnd_2046076] using wordTrace_append hprefix tailTrace_2046076
  have hstable : (prefixWord ++ tailWord_2046076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046076).length < 2 ^ (prefixWord ++ tailWord_2046076).sum := by decide
  have hdescent : baseEnd_2046076 < baseStart_2046076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046136 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 3, 5]
def baseStart_2046136 : Nat := 118140960795 + 2046136 * 2 ^ 59
def prefixEnd_2046136 : Nat := 4983230072969 + 3 ^ 40 * 2046136 * 2
def baseEnd_2046136 : Nat := 700434168312074478126665

theorem tailTrace_2046136 : CollatzResearch.WordTrace tailWord_2046136 prefixEnd_2046136 700434168312074478126665 := by
  unfold tailWord_2046136
  simp only [CollatzResearch.WordTrace]
  refine ⟨37314355457603099526299131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49752473943470799368398841 37314355457603099526299131)
  ·
    refine ⟨55971533186404649289448697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37314355457603099526299131 55971533186404649289448697)
    ·
      refine ⟨41978649889803486967086523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55971533186404649289448697 41978649889803486967086523)
      ·
        refine ⟨62967974834705230450629785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41978649889803486967086523 62967974834705230450629785)
        ·
          refine ⟨47225981126028922837972339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62967974834705230450629785 47225981126028922837972339)
          ·
            refine ⟨70838971689043384256958509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47225981126028922837972339 70838971689043384256958509)
            ·
              refine ⟨26564614383391269096359441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70838971689043384256958509 26564614383391269096359441)
              ·
                refine ⟨19923460787543451822269581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26564614383391269096359441 19923460787543451822269581)
                ·
                  refine ⟨7471297795328794433351093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19923460787543451822269581 7471297795328794433351093)
                  ·
                    refine ⟨700434168312074478126665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7471297795328794433351093 700434168312074478126665)
                    ·
                      rfl

theorem cell22_2046136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_2046136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046136 prefixEnd_2046136 := by exact prefixLift 2046136
  have htrace : WordTrace (prefixWord ++ tailWord_2046136) baseStart_2046136 baseEnd_2046136 := by
    simpa [prefixWord, tailWord_2046136, baseEnd_2046136] using wordTrace_append hprefix tailTrace_2046136
  have hstable : (prefixWord ++ tailWord_2046136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046136).length < 2 ^ (prefixWord ++ tailWord_2046136).sum := by decide
  have hdescent : baseEnd_2046136 < baseStart_2046136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046168 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 1, 6]
def baseStart_2046168 : Nat := 118140960795 + 2046168 * 2 ^ 59
def prefixEnd_2046168 : Nat := 4983230072969 + 3 ^ 40 * 2046168 * 2
def baseEnd_2046168 : Nat := 700445122566037061326567

theorem tailTrace_2046168 : CollatzResearch.WordTrace tailWord_2046168 prefixEnd_2046168 700445122566037061326567 := by
  unfold tailWord_2046168
  simp only [CollatzResearch.WordTrace]
  refine ⟨37314939025545134258881579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49753252034060179011842105 37314939025545134258881579)
  ·
    refine ⟨55972408538317701388322369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37314939025545134258881579 55972408538317701388322369)
    ·
      refine ⟨41979306403738276041241777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55972408538317701388322369 41979306403738276041241777)
      ·
        refine ⟨31484479802803707030931333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41979306403738276041241777 31484479802803707030931333)
        ·
          refine ⟨5903339963025695068299625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31484479802803707030931333 5903339963025695068299625)
          ·
            refine ⟨4427504972269271301224719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5903339963025695068299625 4427504972269271301224719)
            ·
              refine ⟨6641257458403906951837079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4427504972269271301224719 6641257458403906951837079)
              ·
                refine ⟨9961886187605860427755619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6641257458403906951837079 9961886187605860427755619)
                ·
                  refine ⟨14942829281408790641633429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9961886187605860427755619 14942829281408790641633429)
                  ·
                    refine ⟨700445122566037061326567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14942829281408790641633429 700445122566037061326567)
                    ·
                      rfl

theorem cell22_2046168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_2046168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046168 prefixEnd_2046168 := by exact prefixLift 2046168
  have htrace : WordTrace (prefixWord ++ tailWord_2046168) baseStart_2046168 baseEnd_2046168 := by
    simpa [prefixWord, tailWord_2046168, baseEnd_2046168] using wordTrace_append hprefix tailTrace_2046168
  have hstable : (prefixWord ++ tailWord_2046168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046168).length < 2 ^ (prefixWord ++ tailWord_2046168).sum := by decide
  have hdescent : baseEnd_2046168 < baseStart_2046168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046183 : List Nat := [1, 1, 5, 3, 1, 2, 9]
def baseStart_2046183 : Nat := 118140960795 + 2046183 * 2 ^ 59
def prefixEnd_2046183 : Nat := 4983230072969 + 3 ^ 40 * 2046183 * 2
def baseEnd_2046183 : Nat := 25942602124910445266723

theorem tailTrace_2046183 : CollatzResearch.WordTrace tailWord_2046183 prefixEnd_2046183 25942602124910445266723 := by
  unfold tailWord_2046183
  simp only [CollatzResearch.WordTrace]
  refine ⟨74630425146035926079559203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49753616764023950719706135 74630425146035926079559203)
  ·
    refine ⟨111945637719053889119338805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74630425146035926079559203 111945637719053889119338805)
    ·
      refine ⟨10494903536161302104938013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111945637719053889119338805 10494903536161302104938013)
      ·
        refine ⟨3935588826060488289351755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10494903536161302104938013 3935588826060488289351755)
        ·
          refine ⟨5903383239090732434027633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3935588826060488289351755 5903383239090732434027633)
          ·
            refine ⟨4427537429318049325520725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5903383239090732434027633 4427537429318049325520725)
            ·
              refine ⟨25942602124910445266723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4427537429318049325520725 25942602124910445266723)
              ·
                rfl

theorem cell22_2046183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 9].length) (baseStart_2046183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046183 prefixEnd_2046183 := by exact prefixLift 2046183
  have htrace : WordTrace (prefixWord ++ tailWord_2046183) baseStart_2046183 baseEnd_2046183 := by
    simpa [prefixWord, tailWord_2046183, baseEnd_2046183] using wordTrace_append hprefix tailTrace_2046183
  have hstable : (prefixWord ++ tailWord_2046183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046183).length < 2 ^ (prefixWord ++ tailWord_2046183).sum := by decide
  have hdescent : baseEnd_2046183 < baseStart_2046183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046275 : List Nat := [1, 1, 1, 3, 1, 3, 5, 2, 1, 4]
def baseStart_2046275 : Nat := 118140960795 + 2046275 * 2 ^ 59
def prefixEnd_2046275 : Nat := 4983230072969 + 3 ^ 40 * 2046275 * 2
def baseEnd_2046275 : Nat := 700481750852724448901239

theorem tailTrace_2046275 : CollatzResearch.WordTrace tailWord_2046275 prefixEnd_2046275 700481750852724448901239 := by
  unfold tailWord_2046275
  simp only [CollatzResearch.WordTrace]
  refine ⟨74633780661702625791908279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49755853774468417194605519 74633780661702625791908279)
  ·
    refine ⟨111950670992553938687862419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74633780661702625791908279 111950670992553938687862419)
    ·
      refine ⟨167926006488830908031793629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111950670992553938687862419 167926006488830908031793629)
      ·
        refine ⟨62972252433311590511922611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167926006488830908031793629 62972252433311590511922611)
        ·
          refine ⟨94458378649967385767883917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62972252433311590511922611 94458378649967385767883917)
          ·
            refine ⟨35421891993737769662956469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94458378649967385767883917 35421891993737769662956469)
            ·
              refine ⟨3320802374412915905902169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35421891993737769662956469 3320802374412915905902169)
              ·
                refine ⟨2490601780809686929426627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3320802374412915905902169 2490601780809686929426627)
                ·
                  refine ⟨3735902671214530394139941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2490601780809686929426627 3735902671214530394139941)
                  ·
                    refine ⟨700481750852724448901239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3735902671214530394139941 700481750852724448901239)
                    ·
                      rfl

theorem cell22_2046275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 4].length) (baseStart_2046275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046275 prefixEnd_2046275 := by exact prefixLift 2046275
  have htrace : WordTrace (prefixWord ++ tailWord_2046275) baseStart_2046275 baseEnd_2046275 := by
    simpa [prefixWord, tailWord_2046275, baseEnd_2046275] using wordTrace_append hprefix tailTrace_2046275
  have hstable : (prefixWord ++ tailWord_2046275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046275).length < 2 ^ (prefixWord ++ tailWord_2046275).sum := by decide
  have hdescent : baseEnd_2046275 < baseStart_2046275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046288 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 3, 5]
def baseStart_2046288 : Nat := 118140960795 + 2046288 * 2 ^ 59
def prefixEnd_2046288 : Nat := 4983230072969 + 3 ^ 40 * 2046288 * 2
def baseEnd_2046288 : Nat := 700486201018396748326199

theorem tailTrace_2046288 : CollatzResearch.WordTrace tailWord_2046288 prefixEnd_2046288 700486201018396748326199 := by
  unfold tailWord_2046288
  simp only [CollatzResearch.WordTrace]
  refine ⟨37317127405327764506065759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49756169873770352674754345 37317127405327764506065759)
  ·
    refine ⟨55975691107991646759098639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37317127405327764506065759 55975691107991646759098639)
    ·
      refine ⟨83963536661987470138647959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55975691107991646759098639 83963536661987470138647959)
      ·
        refine ⟨125945304992981205207971939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83963536661987470138647959 125945304992981205207971939)
        ·
          refine ⟨188917957489471807811957909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125945304992981205207971939 188917957489471807811957909)
          ·
            refine ⟨8855529257318990991185527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 188917957489471807811957909 8855529257318990991185527)
            ·
              refine ⟨13283293885978486486778291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8855529257318990991185527 13283293885978486486778291)
              ·
                refine ⟨19924940828967729730167437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13283293885978486486778291 19924940828967729730167437)
                ·
                  refine ⟨7471852810862898648812789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19924940828967729730167437 7471852810862898648812789)
                  ·
                    refine ⟨700486201018396748326199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7471852810862898648812789 700486201018396748326199)
                    ·
                      rfl

theorem cell22_2046288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_2046288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046288 prefixEnd_2046288 := by exact prefixLift 2046288
  have htrace : WordTrace (prefixWord ++ tailWord_2046288) baseStart_2046288 baseEnd_2046288 := by
    simpa [prefixWord, tailWord_2046288, baseEnd_2046288] using wordTrace_append hprefix tailTrace_2046288
  have hstable : (prefixWord ++ tailWord_2046288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046288).length < 2 ^ (prefixWord ++ tailWord_2046288).sum := by decide
  have hdescent : baseEnd_2046288 < baseStart_2046288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046300 : List Nat := [2, 2, 4, 3, 2, 1, 2, 2, 1, 3]
def baseStart_2046300 : Nat := 118140960795 + 2046300 * 2 ^ 59
def prefixEnd_2046300 : Nat := 4983230072969 + 3 ^ 40 * 2046300 * 2
def baseEnd_2046300 : Nat := 700490308863632717026163

theorem tailTrace_2046300 : CollatzResearch.WordTrace tailWord_2046300 prefixEnd_2046300 700490308863632717026163 := by
  unfold tailWord_2046300
  simp only [CollatzResearch.WordTrace]
  refine ⟨37317346243306027530784177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49756461657741370041045569 37317346243306027530784177)
  ·
    refine ⟨27988009682479520648088133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37317346243306027530784177 27988009682479520648088133)
    ·
      refine ⟨5247751815464910121516525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27988009682479520648088133 5247751815464910121516525)
      ·
        refine ⟨1967906930799341295568697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5247751815464910121516525 1967906930799341295568697)
        ·
          refine ⟨1475930198099505971676523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1967906930799341295568697 1475930198099505971676523)
          ·
            refine ⟨2213895297149258957514785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475930198099505971676523 2213895297149258957514785)
            ·
              refine ⟨1660421472861944218136089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2213895297149258957514785 1660421472861944218136089)
              ·
                refine ⟨1245316104646458163602067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1660421472861944218136089 1245316104646458163602067)
                ·
                  refine ⟨1867974156969687245403101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1245316104646458163602067 1867974156969687245403101)
                  ·
                    refine ⟨700490308863632717026163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1867974156969687245403101 700490308863632717026163)
                    ·
                      rfl

theorem cell22_2046300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_2046300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046300 prefixEnd_2046300 := by exact prefixLift 2046300
  have htrace : WordTrace (prefixWord ++ tailWord_2046300) baseStart_2046300 baseEnd_2046300 := by
    simpa [prefixWord, tailWord_2046300, baseEnd_2046300] using wordTrace_append hprefix tailTrace_2046300
  have hstable : (prefixWord ++ tailWord_2046300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046300).length < 2 ^ (prefixWord ++ tailWord_2046300).sum := by decide
  have hdescent : baseEnd_2046300 < baseStart_2046300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046322 : List Nat := [3, 2, 1, 2, 1, 3, 2, 3, 2, 3]
def baseStart_2046322 : Nat := 118140960795 + 2046322 * 2 ^ 59
def prefixEnd_2046322 : Nat := 4983230072969 + 3 ^ 40 * 2046322 * 2
def baseEnd_2046322 : Nat := 700497839913231992976095

theorem tailTrace_2046322 : CollatzResearch.WordTrace tailWord_2046322 prefixEnd_2046322 700497839913231992976095 := by
  unfold tailWord_2046322
  simp only [CollatzResearch.WordTrace]
  refine ⟨18658873723133088204717305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49756996595021568545912813 18658873723133088204717305)
  ·
    refine ⟨13994155292349816153537979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18658873723133088204717305 13994155292349816153537979)
    ·
      refine ⟨20991232938524724230306969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13994155292349816153537979 20991232938524724230306969)
      ·
        refine ⟨15743424703893543172730227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20991232938524724230306969 15743424703893543172730227)
        ·
          refine ⟨23615137055840314759095341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15743424703893543172730227 23615137055840314759095341)
          ·
            refine ⟨8855676395940118034660753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23615137055840314759095341 8855676395940118034660753)
            ·
              refine ⟨6641757296955088525995565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8855676395940118034660753 6641757296955088525995565)
              ·
                refine ⟨2490658986358158197248337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6641757296955088525995565 2490658986358158197248337)
                ·
                  refine ⟨1867994239768618647936253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2490658986358158197248337 1867994239768618647936253)
                  ·
                    refine ⟨700497839913231992976095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1867994239768618647936253 700497839913231992976095)
                    ·
                      rfl

theorem cell22_2046322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_2046322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046322 prefixEnd_2046322 := by exact prefixLift 2046322
  have htrace : WordTrace (prefixWord ++ tailWord_2046322) baseStart_2046322 baseEnd_2046322 := by
    simpa [prefixWord, tailWord_2046322, baseEnd_2046322] using wordTrace_append hprefix tailTrace_2046322
  have hstable : (prefixWord ++ tailWord_2046322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046322).length < 2 ^ (prefixWord ++ tailWord_2046322).sum := by decide
  have hdescent : baseEnd_2046322 < baseStart_2046322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046337 : List Nat := [1, 2, 4, 3, 1, 1, 3, 1, 2, 4]
def baseStart_2046337 : Nat := 118140960795 + 2046337 * 2 ^ 59
def prefixEnd_2046337 : Nat := 4983230072969 + 3 ^ 40 * 2046337 * 2
def baseEnd_2046337 : Nat := 700502974719776953851049

theorem tailTrace_2046337 : CollatzResearch.WordTrace tailWord_2046337 prefixEnd_2046337 700502974719776953851049 := by
  unfold tailWord_2046337
  simp only [CollatzResearch.WordTrace]
  refine ⟨74636041987478010380665265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49757361324985340253776843 74636041987478010380665265)
  ·
    refine ⟨55977031490608507785498949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74636041987478010380665265 55977031490608507785498949)
    ·
      refine ⟨10495693404489095209781053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55977031490608507785498949 10495693404489095209781053)
      ·
        refine ⟨3935885026683410703667895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10495693404489095209781053 3935885026683410703667895)
        ·
          refine ⟨5903827540025116055501843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3935885026683410703667895 5903827540025116055501843)
          ·
            refine ⟨8855741310037674083252765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5903827540025116055501843 8855741310037674083252765)
            ·
              refine ⟨3320902991264127781219787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8855741310037674083252765 3320902991264127781219787)
              ·
                refine ⟨4981354486896191671829681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3320902991264127781219787 4981354486896191671829681)
                ·
                  refine ⟨3736015865172143753872261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4981354486896191671829681 3736015865172143753872261)
                  ·
                    refine ⟨700502974719776953851049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3736015865172143753872261 700502974719776953851049)
                    ·
                      rfl

theorem cell22_2046337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_2046337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046337 prefixEnd_2046337 := by exact prefixLift 2046337
  have htrace : WordTrace (prefixWord ++ tailWord_2046337) baseStart_2046337 baseEnd_2046337 := by
    simpa [prefixWord, tailWord_2046337, baseEnd_2046337] using wordTrace_append hprefix tailTrace_2046337
  have hstable : (prefixWord ++ tailWord_2046337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046337).length < 2 ^ (prefixWord ++ tailWord_2046337).sum := by decide
  have hdescent : baseEnd_2046337 < baseStart_2046337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046356 : List Nat := [2, 4, 2, 1, 3, 2, 1, 2, 2, 3]
def baseStart_2046356 : Nat := 118140960795 + 2046356 * 2 ^ 59
def prefixEnd_2046356 : Nat := 4983230072969 + 3 ^ 40 * 2046356 * 2
def baseEnd_2046356 : Nat := 700509478808067237625991

theorem tailTrace_2046356 : CollatzResearch.WordTrace tailWord_2046356 prefixEnd_2046356 700509478808067237625991 := by
  unfold tailWord_2046356
  simp only [CollatzResearch.WordTrace]
  refine ⟨37318367487204588312803461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49757823316272784417071281 37318367487204588312803461)
  ·
    refine ⟨6997193903850860308650649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37318367487204588312803461 6997193903850860308650649)
    ·
      refine ⟨5247895427888145231487987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6997193903850860308650649 5247895427888145231487987)
      ·
        refine ⟨7871843141832217847231981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5247895427888145231487987 7871843141832217847231981)
        ·
          refine ⟨2951941178187081692711993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7871843141832217847231981 2951941178187081692711993)
          ·
            refine ⟨2213955883640311269533995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2951941178187081692711993 2213955883640311269533995)
            ·
              refine ⟨3320933825460466904300993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2213955883640311269533995 3320933825460466904300993)
              ·
                refine ⟨2490700369095350178225745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3320933825460466904300993 2490700369095350178225745)
                ·
                  refine ⟨1868025276821512633669309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2490700369095350178225745 1868025276821512633669309)
                  ·
                    refine ⟨700509478808067237625991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1868025276821512633669309 700509478808067237625991)
                    ·
                      rfl

theorem cell22_2046356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_2046356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046356 prefixEnd_2046356 := by exact prefixLift 2046356
  have htrace : WordTrace (prefixWord ++ tailWord_2046356) baseStart_2046356 baseEnd_2046356 := by
    simpa [prefixWord, tailWord_2046356, baseEnd_2046356] using wordTrace_append hprefix tailTrace_2046356
  have hstable : (prefixWord ++ tailWord_2046356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046356).length < 2 ^ (prefixWord ++ tailWord_2046356).sum := by decide
  have hdescent : baseEnd_2046356 < baseStart_2046356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046367 : List Nat := [1, 1, 2, 5, 1, 1, 4, 1, 3, 3]
def baseStart_2046367 : Nat := 118140960795 + 2046367 * 2 ^ 59
def prefixEnd_2046367 : Nat := 4983230072969 + 3 ^ 40 * 2046367 * 2
def baseEnd_2046367 : Nat := 700513244332866875600957

theorem tailTrace_2046367 : CollatzResearch.WordTrace tailWord_2046367 prefixEnd_2046367 700513244332866875600957 := by
  unfold tailWord_2046367
  simp only [CollatzResearch.WordTrace]
  refine ⟨74637136177369325504257355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49758090784912883669504903 74637136177369325504257355)
  ·
    refine ⟨111955704266053988256386033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74637136177369325504257355 111955704266053988256386033)
    ·
      refine ⟨83966778199540491192289525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111955704266053988256386033 83966778199540491192289525)
      ·
        refine ⟨7871885456206921049277143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83966778199540491192289525 7871885456206921049277143)
        ·
          refine ⟨11807828184310381573915715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7871885456206921049277143 11807828184310381573915715)
          ·
            refine ⟨17711742276465572360873573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11807828184310381573915715 17711742276465572360873573)
            ·
              refine ⟨3320951676837294817663795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17711742276465572360873573 3320951676837294817663795)
              ·
                refine ⟨4981427515255942226495693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3320951676837294817663795 4981427515255942226495693)
                ·
                  refine ⟨1868035318220978334935885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4981427515255942226495693 1868035318220978334935885)
                  ·
                    refine ⟨700513244332866875600957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1868035318220978334935885 700513244332866875600957)
                    ·
                      rfl

theorem cell22_2046367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 3].length) (baseStart_2046367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046367 prefixEnd_2046367 := by exact prefixLift 2046367
  have htrace : WordTrace (prefixWord ++ tailWord_2046367) baseStart_2046367 baseEnd_2046367 := by
    simpa [prefixWord, tailWord_2046367, baseEnd_2046367] using wordTrace_append hprefix tailTrace_2046367
  have hstable : (prefixWord ++ tailWord_2046367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046367).length < 2 ^ (prefixWord ++ tailWord_2046367).sum := by decide
  have hdescent : baseEnd_2046367 < baseStart_2046367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046418 : List Nat := [3, 2, 2, 4, 2, 1, 1, 1, 3, 3]
def baseStart_2046418 : Nat := 118140960795 + 2046418 * 2 ^ 59
def prefixEnd_2046418 : Nat := 4983230072969 + 3 ^ 40 * 2046418 * 2
def baseEnd_2046418 : Nat := 700530702675119742575801

theorem tailTrace_2046418 : CollatzResearch.WordTrace tailWord_2046418 prefixEnd_2046418 700530702675119742575801 := by
  unfold tailWord_2046418
  simp only [CollatzResearch.WordTrace]
  refine ⟨18659749075046140303590977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49759330866789707476242605 18659749075046140303590977)
  ·
    refine ⟨13994811806284605227693233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18659749075046140303590977 13994811806284605227693233)
    ·
      refine ⟨10496108854713453920769925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13994811806284605227693233 10496108854713453920769925)
      ·
        refine ⟨1968020410258772610144361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10496108854713453920769925 1968020410258772610144361)
        ·
          refine ⟨1476015307694079457608271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1968020410258772610144361 1476015307694079457608271)
          ·
            refine ⟨2214022961541119186412407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1476015307694079457608271 2214022961541119186412407)
            ·
              refine ⟨3321034442311678779618611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2214022961541119186412407 3321034442311678779618611)
              ·
                refine ⟨4981551663467518169427917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3321034442311678779618611 4981551663467518169427917)
                ·
                  refine ⟨1868081873800319313535469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4981551663467518169427917 1868081873800319313535469)
                  ·
                    refine ⟨700530702675119742575801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1868081873800319313535469 700530702675119742575801)
                    ·
                      rfl

theorem cell22_2046418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_2046418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046418 prefixEnd_2046418 := by exact prefixLift 2046418
  have htrace : WordTrace (prefixWord ++ tailWord_2046418) baseStart_2046418 baseEnd_2046418 := by
    simpa [prefixWord, tailWord_2046418, baseEnd_2046418] using wordTrace_append hprefix tailTrace_2046418
  have hstable : (prefixWord ++ tailWord_2046418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046418).length < 2 ^ (prefixWord ++ tailWord_2046418).sum := by decide
  have hdescent : baseEnd_2046418 < baseStart_2046418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046474 : List Nat := [3, 1, 2, 2, 2, 1, 4, 2, 2, 3]
def baseStart_2046474 : Nat := 118140960795 + 2046474 * 2 ^ 59
def prefixEnd_2046474 : Nat := 4983230072969 + 3 ^ 40 * 2046474 * 2
def baseEnd_2046474 : Nat := 700549872619554263175629

theorem tailTrace_2046474 : CollatzResearch.WordTrace tailWord_2046474 prefixEnd_2046474 700549872619554263175629 := by
  unfold tailWord_2046474
  simp only [CollatzResearch.WordTrace]
  refine ⟨18660259696995420694600619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49760692525321121852268317 18660259696995420694600619)
  ·
    refine ⟨27990389545493131041900929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18660259696995420694600619 27990389545493131041900929)
    ·
      refine ⟨20992792159119848281425697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27990389545493131041900929 20992792159119848281425697)
      ·
        refine ⟨15744594119339886211069273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20992792159119848281425697 15744594119339886211069273)
        ·
          refine ⟨11808445589504914658301955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15744594119339886211069273 11808445589504914658301955)
          ·
            refine ⟨17712668384257371987452933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11808445589504914658301955 17712668384257371987452933)
            ·
              refine ⟨3321125322048257247647425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17712668384257371987452933 3321125322048257247647425)
              ·
                refine ⟨2490843991536192935735569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3321125322048257247647425 2490843991536192935735569)
                ·
                  refine ⟨1868132993652144701801677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2490843991536192935735569 1868132993652144701801677)
                  ·
                    refine ⟨700549872619554263175629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1868132993652144701801677 700549872619554263175629)
                    ·
                      rfl

theorem cell22_2046474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_2046474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046474 prefixEnd_2046474 := by exact prefixLift 2046474
  have htrace : WordTrace (prefixWord ++ tailWord_2046474) baseStart_2046474 baseEnd_2046474 := by
    simpa [prefixWord, tailWord_2046474, baseEnd_2046474] using wordTrace_append hprefix tailTrace_2046474
  have hstable : (prefixWord ++ tailWord_2046474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046474).length < 2 ^ (prefixWord ++ tailWord_2046474).sum := by decide
  have hdescent : baseEnd_2046474 < baseStart_2046474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046476 : List Nat := [2, 2, 1, 2, 4, 3, 2, 2, 4]
def baseStart_2046476 : Nat := 118140960795 + 2046476 * 2 ^ 59
def prefixEnd_2046476 : Nat := 4983230072969 + 3 ^ 40 * 2046476 * 2
def baseEnd_2046476 : Nat := 233516852420142308208541

theorem tailTrace_2046476 : CollatzResearch.WordTrace tailWord_2046476 prefixEnd_2046476 233516852420142308208541 := by
  unfold tailWord_2046476
  simp only [CollatzResearch.WordTrace]
  refine ⟨37320555866987218559987641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49760741155982958079983521 37320555866987218559987641)
  ·
    refine ⟨27990416900240413919990731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37320555866987218559987641 27990416900240413919990731)
    ·
      refine ⟨41985625350360620879986097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27990416900240413919990731 41985625350360620879986097)
      ·
        refine ⟨31489219012770465659989573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41985625350360620879986097 31489219012770465659989573)
        ·
          refine ⟨5904228564894462311248045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31489219012770465659989573 5904228564894462311248045)
          ·
            refine ⟨2214085711835423366718017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5904228564894462311248045 2214085711835423366718017)
            ·
              refine ⟨1660564283876567525038513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2214085711835423366718017 1660564283876567525038513)
              ·
                refine ⟨1245423212907425643778885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1660564283876567525038513 1245423212907425643778885)
                ·
                  refine ⟨233516852420142308208541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1245423212907425643778885 233516852420142308208541)
                  ·
                    rfl

theorem cell22_2046476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 4].length) (baseStart_2046476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046476 prefixEnd_2046476 := by exact prefixLift 2046476
  have htrace : WordTrace (prefixWord ++ tailWord_2046476) baseStart_2046476 baseEnd_2046476 := by
    simpa [prefixWord, tailWord_2046476, baseEnd_2046476] using wordTrace_append hprefix tailTrace_2046476
  have hstable : (prefixWord ++ tailWord_2046476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046476).length < 2 ^ (prefixWord ++ tailWord_2046476).sum := by decide
  have hdescent : baseEnd_2046476 < baseStart_2046476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046504 : List Nat := [2, 1, 5, 2, 1, 2, 3, 6]
def baseStart_2046504 : Nat := 118140960795 + 2046504 * 2 ^ 59
def prefixEnd_2046504 : Nat := 4983230072969 + 3 ^ 40 * 2046504 * 2
def baseEnd_2046504 : Nat := 77840015803627131658393

theorem tailTrace_2046504 : CollatzResearch.WordTrace tailWord_2046504 prefixEnd_2046504 77840015803627131658393 := by
  unfold tailWord_2046504
  simp only [CollatzResearch.WordTrace]
  refine ⟨37321066488936498950997283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49761421985248665267996377 37321066488936498950997283)
  ·
    refine ⟨55981599733404748426495925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37321066488936498950997283 55981599733404748426495925)
    ·
      refine ⟨5248274975006695164983993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55981599733404748426495925 5248274975006695164983993)
      ·
        refine ⟨3936206231255021373737995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5248274975006695164983993 3936206231255021373737995)
        ·
          refine ⟨5904309346882532060606993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3936206231255021373737995 5904309346882532060606993)
          ·
            refine ⟨4428232010161899045455245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5904309346882532060606993 4428232010161899045455245)
            ·
              refine ⟨1660587003810712142045717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4428232010161899045455245 1660587003810712142045717)
              ·
                refine ⟨77840015803627131658393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1660587003810712142045717 77840015803627131658393)
                ·
                  rfl

theorem cell22_2046504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 6].length) (baseStart_2046504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046504 prefixEnd_2046504 := by exact prefixLift 2046504
  have htrace : WordTrace (prefixWord ++ tailWord_2046504) baseStart_2046504 baseEnd_2046504 := by
    simpa [prefixWord, tailWord_2046504, baseEnd_2046504] using wordTrace_append hprefix tailTrace_2046504
  have hstable : (prefixWord ++ tailWord_2046504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046504).length < 2 ^ (prefixWord ++ tailWord_2046504).sum := by decide
  have hdescent : baseEnd_2046504 < baseStart_2046504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046515 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 7]
def baseStart_2046515 : Nat := 118140960795 + 2046515 * 2 ^ 59
def prefixEnd_2046515 : Nat := 4983230072969 + 3 ^ 40 * 2046515 * 2
def baseEnd_2046515 : Nat := 233521302585814607633501

theorem tailTrace_2046515 : CollatzResearch.WordTrace tailWord_2046515 prefixEnd_2046515 233521302585814607633501 := by
  unfold tailWord_2046515
  simp only [CollatzResearch.WordTrace]
  refine ⟨74642534180833146780644999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49761689453888764520429999 74642534180833146780644999)
  ·
    refine ⟨111963801271249720170967499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74642534180833146780644999 111963801271249720170967499)
    ·
      refine ⟨167945701906874580256451249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111963801271249720170967499 167945701906874580256451249)
      ·
        refine ⟨125959276430155935192338437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167945701906874580256451249 125959276430155935192338437)
        ·
          refine ⟨23617364330654237848563457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125959276430155935192338437 23617364330654237848563457)
          ·
            refine ⟨17713023247990678386422593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23617364330654237848563457 17713023247990678386422593)
            ·
              refine ⟨13284767435993008789816945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17713023247990678386422593 13284767435993008789816945)
              ·
                refine ⟨9963575576994756592362709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13284767435993008789816945 9963575576994756592362709)
                ·
                  refine ⟨233521302585814607633501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9963575576994756592362709 233521302585814607633501)
                  ·
                    rfl

theorem cell22_2046515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 7].length) (baseStart_2046515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046515 prefixEnd_2046515 := by exact prefixLift 2046515
  have htrace : WordTrace (prefixWord ++ tailWord_2046515) baseStart_2046515 baseEnd_2046515 := by
    simpa [prefixWord, tailWord_2046515, baseEnd_2046515] using wordTrace_append hprefix tailTrace_2046515
  have hstable : (prefixWord ++ tailWord_2046515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046515).length < 2 ^ (prefixWord ++ tailWord_2046515).sum := by decide
  have hdescent : baseEnd_2046515 < baseStart_2046515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046652 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 1, 8]
def baseStart_2046652 : Nat := 118140960795 + 2046652 * 2 ^ 59
def prefixEnd_2046652 : Nat := 4983230072969 + 3 ^ 40 * 2046652 * 2
def baseEnd_2046652 : Nat := 700610805657221132225083

theorem tailTrace_2046652 : CollatzResearch.WordTrace tailWord_2046652 prefixEnd_2046652 700610805657221132225083 := by
  unfold tailWord_2046652
  simp only [CollatzResearch.WordTrace]
  refine ⟨37323765490668409589191105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49765020654224546118921473 37323765490668409589191105)
  ·
    refine ⟨27992824118001307191893329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37323765490668409589191105 27992824118001307191893329)
    ·
      refine ⟨20994618088500980393919997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27992824118001307191893329 20994618088500980393919997)
      ·
        refine ⟨7872981783187867647719999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20994618088500980393919997 7872981783187867647719999)
        ·
          refine ⟨11809472674781801471579999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7872981783187867647719999 11809472674781801471579999)
          ·
            refine ⟨17714209012172702207369999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11809472674781801471579999 17714209012172702207369999)
            ·
              refine ⟨26571313518259053311054999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17714209012172702207369999 26571313518259053311054999)
              ·
                refine ⟨39856970277388579966582499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26571313518259053311054999 39856970277388579966582499)
                ·
                  refine ⟨59785455416082869949873749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39856970277388579966582499 59785455416082869949873749)
                  ·
                    refine ⟨700610805657221132225083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59785455416082869949873749 700610805657221132225083)
                    ·
                      rfl

theorem cell22_2046652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_2046652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046652 prefixEnd_2046652 := by exact prefixLift 2046652
  have htrace : WordTrace (prefixWord ++ tailWord_2046652) baseStart_2046652 baseEnd_2046652 := by
    simpa [prefixWord, tailWord_2046652, baseEnd_2046652] using wordTrace_append hprefix tailTrace_2046652
  have hstable : (prefixWord ++ tailWord_2046652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046652).length < 2 ^ (prefixWord ++ tailWord_2046652).sum := by decide
  have hdescent : baseEnd_2046652 < baseStart_2046652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046682 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 1, 7]
def baseStart_2046682 : Nat := 118140960795 + 2046682 * 2 ^ 59
def prefixEnd_2046682 : Nat := 4983230072969 + 3 ^ 40 * 2046682 * 2
def baseEnd_2046682 : Nat := 700621075270311053974991

theorem tailTrace_2046682 : CollatzResearch.WordTrace tailWord_2046682 prefixEnd_2046682 700621075270311053974991 := by
  unfold tailWord_2046682
  simp only [CollatzResearch.WordTrace]
  refine ⟨18662156292807033575493575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49765750114152089534649533 18662156292807033575493575)
  ·
    refine ⟨27993234439210550363240363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18662156292807033575493575 27993234439210550363240363)
    ·
      refine ⟨41989851658815825544860545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27993234439210550363240363 41989851658815825544860545)
      ·
        refine ⟨31492388744111869158645409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41989851658815825544860545 31492388744111869158645409)
        ·
          refine ⟨23619291558083901868984057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31492388744111869158645409 23619291558083901868984057)
          ·
            refine ⟨17714468668562926401738043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23619291558083901868984057 17714468668562926401738043)
            ·
              refine ⟨26571703002844389602607065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17714468668562926401738043 26571703002844389602607065)
              ·
                refine ⟨19928777252133292201955299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26571703002844389602607065 19928777252133292201955299)
                ·
                  refine ⟨29893165878199938302932949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19928777252133292201955299 29893165878199938302932949)
                  ·
                    refine ⟨700621075270311053974991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29893165878199938302932949 700621075270311053974991)
                    ·
                      rfl

theorem cell22_2046682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_2046682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046682 prefixEnd_2046682 := by exact prefixLift 2046682
  have htrace : WordTrace (prefixWord ++ tailWord_2046682) baseStart_2046682 baseEnd_2046682 := by
    simpa [prefixWord, tailWord_2046682, baseEnd_2046682] using wordTrace_append hprefix tailTrace_2046682
  have hstable : (prefixWord ++ tailWord_2046682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046682).length < 2 ^ (prefixWord ++ tailWord_2046682).sum := by decide
  have hdescent : baseEnd_2046682 < baseStart_2046682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046718 : List Nat := [4, 2, 2, 1, 2, 2, 3, 1, 5]
def baseStart_2046718 : Nat := 118140960795 + 2046718 * 2 ^ 59
def prefixEnd_2046718 : Nat := 4983230072969 + 3 ^ 40 * 2046718 * 2
def baseEnd_2046718 : Nat := 233544466268672986691627

theorem tailTrace_2046718 : CollatzResearch.WordTrace tailWord_2046718 prefixEnd_2046718 233544466268672986691627 := by
  unfold tailWord_2046718
  simp only [CollatzResearch.WordTrace]
  refine ⟨9331242274887214056285601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49766625466065141633523205 9331242274887214056285601)
  ·
    refine ⟨6998431706165410542214201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9331242274887214056285601 6998431706165410542214201)
    ·
      refine ⟨5248823779624057906660651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6998431706165410542214201 5248823779624057906660651)
      ·
        refine ⟨7873235669436086859990977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5248823779624057906660651 7873235669436086859990977)
        ·
          refine ⟨5904926752077065144993233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7873235669436086859990977 5904926752077065144993233)
          ·
            refine ⟨4428695064057798858744925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5904926752077065144993233 4428695064057798858744925)
            ·
              refine ⟨1660760649021674572029347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4428695064057798858744925 1660760649021674572029347)
              ·
                refine ⟨2491140973532511858044021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1660760649021674572029347 2491140973532511858044021)
                ·
                  refine ⟨233544466268672986691627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2491140973532511858044021 233544466268672986691627)
                  ·
                    rfl

theorem cell22_2046718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_2046718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046718 prefixEnd_2046718 := by exact prefixLift 2046718
  have htrace : WordTrace (prefixWord ++ tailWord_2046718) baseStart_2046718 baseEnd_2046718 := by
    simpa [prefixWord, tailWord_2046718, baseEnd_2046718] using wordTrace_append hprefix tailTrace_2046718
  have hstable : (prefixWord ++ tailWord_2046718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046718).length < 2 ^ (prefixWord ++ tailWord_2046718).sum := by decide
  have hdescent : baseEnd_2046718 < baseStart_2046718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046778 : List Nat := [3, 1, 1, 1, 6, 1, 1, 3, 2, 3]
def baseStart_2046778 : Nat := 118140960795 + 2046778 * 2 ^ 59
def prefixEnd_2046778 : Nat := 4983230072969 + 3 ^ 40 * 2046778 * 2
def baseEnd_2046778 : Nat := 700653938032198803574697

theorem tailTrace_2046778 : CollatzResearch.WordTrace tailWord_2046778 prefixEnd_2046778 700653938032198803574697 := by
  unfold tailWord_2046778
  simp only [CollatzResearch.WordTrace]
  refine ⟨18663031644720085674367247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49768084385920228464979325 18663031644720085674367247)
  ·
    refine ⟨27994547467080128511550871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18663031644720085674367247 27994547467080128511550871)
    ·
      refine ⟨41991821200620192767326307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27994547467080128511550871 41991821200620192767326307)
      ·
        refine ⟨62987731800930289150989461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41991821200620192767326307 62987731800930289150989461)
        ·
          refine ⟨2952549928168607303952631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62987731800930289150989461 2952549928168607303952631)
          ·
            refine ⟨4428824892252910955928947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2952549928168607303952631 4428824892252910955928947)
            ·
              refine ⟨6643237338379366433893421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4428824892252910955928947 6643237338379366433893421)
              ·
                refine ⟨2491214001892262412710033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6643237338379366433893421 2491214001892262412710033)
                ·
                  refine ⟨1868410501419196809532525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2491214001892262412710033 1868410501419196809532525)
                  ·
                    refine ⟨700653938032198803574697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1868410501419196809532525 700653938032198803574697)
                    ·
                      rfl

theorem cell22_2046778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 2, 3].length) (baseStart_2046778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046778 prefixEnd_2046778 := by exact prefixLift 2046778
  have htrace : WordTrace (prefixWord ++ tailWord_2046778) baseStart_2046778 baseEnd_2046778 := by
    simpa [prefixWord, tailWord_2046778, baseEnd_2046778] using wordTrace_append hprefix tailTrace_2046778
  have hstable : (prefixWord ++ tailWord_2046778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046778).length < 2 ^ (prefixWord ++ tailWord_2046778).sum := by decide
  have hdescent : baseEnd_2046778 < baseStart_2046778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046834 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_2046834 : Nat := 118140960795 + 2046834 * 2 ^ 59
def prefixEnd_2046834 : Nat := 4983230072969 + 3 ^ 40 * 2046834 * 2
def baseEnd_2046834 : Nat := 700673107976633324174525

theorem tailTrace_2046834 : CollatzResearch.WordTrace tailWord_2046834 prefixEnd_2046834 700673107976633324174525 := by
  unfold tailWord_2046834
  simp only [CollatzResearch.WordTrace]
  refine ⟨18663542266669366065376889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49769446044451642841005037 18663542266669366065376889)
  ·
    refine ⟨13997656700002024549032667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18663542266669366065376889 13997656700002024549032667)
    ·
      refine ⟨20996485050003036823549001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13997656700002024549032667 20996485050003036823549001)
      ·
        refine ⟨15747363787502277617661751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20996485050003036823549001 15747363787502277617661751)
        ·
          refine ⟨23621045681253416426492627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15747363787502277617661751 23621045681253416426492627)
          ·
            refine ⟨35431568521880124639738941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23621045681253416426492627 35431568521880124639738941)
            ·
              refine ⟨13286838195705046739902103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35431568521880124639738941 13286838195705046739902103)
              ·
                refine ⟨19930257293557570109853155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13286838195705046739902103 19930257293557570109853155)
                ·
                  refine ⟨29895385940336355164779733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19930257293557570109853155 29895385940336355164779733)
                  ·
                    refine ⟨700673107976633324174525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29895385940336355164779733 700673107976633324174525)
                    ·
                      rfl

theorem cell22_2046834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_2046834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046834 prefixEnd_2046834 := by exact prefixLift 2046834
  have htrace : WordTrace (prefixWord ++ tailWord_2046834) baseStart_2046834 baseEnd_2046834 := by
    simpa [prefixWord, tailWord_2046834, baseEnd_2046834] using wordTrace_append hprefix tailTrace_2046834
  have hstable : (prefixWord ++ tailWord_2046834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046834).length < 2 ^ (prefixWord ++ tailWord_2046834).sum := by decide
  have hdescent : baseEnd_2046834 < baseStart_2046834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046870 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 7]
def baseStart_2046870 : Nat := 118140960795 + 2046870 * 2 ^ 59
def prefixEnd_2046870 : Nat := 4983230072969 + 3 ^ 40 * 2046870 * 2
def baseEnd_2046870 : Nat := 233561810504113743424805

theorem tailTrace_2046870 : CollatzResearch.WordTrace tailWord_2046870 prefixEnd_2046870 233561810504113743424805 := by
  unfold tailWord_2046870
  simp only [CollatzResearch.WordTrace]
  refine ⟨4665967630909190150613629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49770321396364694939878709 4665967630909190150613629)
  ·
    refine ⟨1749737861590946306480111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4665967630909190150613629 1749737861590946306480111)
    ·
      refine ⟨2624606792386419459720167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1749737861590946306480111 2624606792386419459720167)
      ·
        refine ⟨3936910188579629189580251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2624606792386419459720167 3936910188579629189580251)
        ·
          refine ⟨5905365282869443784370377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3936910188579629189580251 5905365282869443784370377)
          ·
            refine ⟨4429023962152082838277783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5905365282869443784370377 4429023962152082838277783)
            ·
              refine ⟨6643535943228124257416675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4429023962152082838277783 6643535943228124257416675)
              ·
                refine ⟨9965303914842186386125013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6643535943228124257416675 9965303914842186386125013)
                ·
                  refine ⟨233561810504113743424805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9965303914842186386125013 233561810504113743424805)
                  ·
                    rfl

theorem cell22_2046870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_2046870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046870 prefixEnd_2046870 := by exact prefixLift 2046870
  have htrace : WordTrace (prefixWord ++ tailWord_2046870) baseStart_2046870 baseEnd_2046870 := by
    simpa [prefixWord, tailWord_2046870, baseEnd_2046870] using wordTrace_append hprefix tailTrace_2046870
  have hstable : (prefixWord ++ tailWord_2046870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046870).length < 2 ^ (prefixWord ++ tailWord_2046870).sum := by decide
  have hdescent : baseEnd_2046870 < baseStart_2046870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046881 : List Nat := [1, 2, 3, 4, 1, 1, 1, 3, 6]
def baseStart_2046881 : Nat := 118140960795 + 2046881 * 2 ^ 59
def prefixEnd_2046881 : Nat := 4983230072969 + 3 ^ 40 * 2046881 * 2
def baseEnd_2046881 : Nat := 233563065679046956083127

theorem tailTrace_2046881 : CollatzResearch.WordTrace tailWord_2046881 prefixEnd_2046881 233563065679046956083127 := by
  unfold tailWord_2046881
  simp only [CollatzResearch.WordTrace]
  refine ⟨74655883297507191288468497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49770588865004794192312331 74655883297507191288468497)
  ·
    refine ⟨55991912473130393466351373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74655883297507191288468497 55991912473130393466351373)
    ·
      refine ⟨20996967177423897549881765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55991912473130393466351373 20996967177423897549881765)
      ·
        refine ⟨3936931345766980790602831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20996967177423897549881765 3936931345766980790602831)
        ·
          refine ⟨5905397018650471185904247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3936931345766980790602831 5905397018650471185904247)
          ·
            refine ⟨8858095527975706778856371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5905397018650471185904247 8858095527975706778856371)
            ·
              refine ⟨13287143291963560168284557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8858095527975706778856371 13287143291963560168284557)
              ·
                refine ⟨4982678734486335063106709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13287143291963560168284557 4982678734486335063106709)
                ·
                  refine ⟨233563065679046956083127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4982678734486335063106709 233563065679046956083127)
                  ·
                    rfl

theorem cell22_2046881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 6].length) (baseStart_2046881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046881 prefixEnd_2046881 := by exact prefixLift 2046881
  have htrace : WordTrace (prefixWord ++ tailWord_2046881) baseStart_2046881 baseEnd_2046881 := by
    simpa [prefixWord, tailWord_2046881, baseEnd_2046881] using wordTrace_append hprefix tailTrace_2046881
  have hstable : (prefixWord ++ tailWord_2046881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046881).length < 2 ^ (prefixWord ++ tailWord_2046881).sum := by decide
  have hdescent : baseEnd_2046881 < baseStart_2046881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046900 : List Nat := [2, 5, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_2046900 : Nat := 118140960795 + 2046900 * 2 ^ 59
def prefixEnd_2046900 : Nat := 4983230072969 + 3 ^ 40 * 2046900 * 2
def baseEnd_2046900 : Nat := 700695701125431152024323

theorem tailTrace_2046900 : CollatzResearch.WordTrace tailWord_2046900 prefixEnd_2046900 700695701125431152024323 := by
  unfold tailWord_2046900
  simp only [CollatzResearch.WordTrace]
  refine ⟨37328288142219178766705077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49771050856292238355606769 37328288142219178766705077)
  ·
    refine ⟨3499527013333048009378601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37328288142219178766705077 3499527013333048009378601)
    ·
      refine ⟨2624645259999786007033951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3499527013333048009378601 2624645259999786007033951)
      ·
        refine ⟨3936967889999679010550927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2624645259999786007033951 3936967889999679010550927)
        ·
          refine ⟨5905451834999518515826391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3936967889999679010550927 5905451834999518515826391)
          ·
            refine ⟨8858177752499277773739587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5905451834999518515826391 8858177752499277773739587)
            ·
              refine ⟨13287266628748916660609381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8858177752499277773739587 13287266628748916660609381)
              ·
                refine ⟨2491362492890421873864259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13287266628748916660609381 2491362492890421873864259)
                ·
                  refine ⟨3737043739335632810796389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2491362492890421873864259 3737043739335632810796389)
                  ·
                    refine ⟨700695701125431152024323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3737043739335632810796389 700695701125431152024323)
                    ·
                      rfl

theorem cell22_2046900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_2046900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046900 prefixEnd_2046900 := by exact prefixLift 2046900
  have htrace : WordTrace (prefixWord ++ tailWord_2046900) baseStart_2046900 baseEnd_2046900 := by
    simpa [prefixWord, tailWord_2046900, baseEnd_2046900] using wordTrace_append hprefix tailTrace_2046900
  have hstable : (prefixWord ++ tailWord_2046900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046900).length < 2 ^ (prefixWord ++ tailWord_2046900).sum := by decide
  have hdescent : baseEnd_2046900 < baseStart_2046900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046926 : List Nat := [4, 1, 1, 1, 2, 5, 8]
def baseStart_2046926 : Nat := 118140960795 + 2046926 * 2 ^ 59
def prefixEnd_2046926 : Nat := 4983230072969 + 3 ^ 40 * 2046926 * 2
def baseEnd_2046926 : Nat := 25952022276176879662009

theorem tailTrace_2046926 : CollatzResearch.WordTrace tailWord_2046926 prefixEnd_2046926 25952022276176879662009 := by
  unfold tailWord_2046926
  simp only [CollatzResearch.WordTrace]
  refine ⟨9332190572793020496732079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49771683054896109315904421 9332190572793020496732079)
  ·
    refine ⟨13998285859189530745098119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9332190572793020496732079 13998285859189530745098119)
    ·
      refine ⟨20997428788784296117647179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13998285859189530745098119 20997428788784296117647179)
      ·
        refine ⟨31496143183176444176470769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20997428788784296117647179 31496143183176444176470769)
        ·
          refine ⟨23622107387382333132353077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31496143183176444176470769 23622107387382333132353077)
          ·
            refine ⟨2214572567567093731158101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23622107387382333132353077 2214572567567093731158101)
            ·
              refine ⟨25952022276176879662009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2214572567567093731158101 25952022276176879662009)
              ·
                rfl

theorem cell22_2046926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 8].length) (baseStart_2046926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046926 prefixEnd_2046926 := by exact prefixLift 2046926
  have htrace : WordTrace (prefixWord ++ tailWord_2046926) baseStart_2046926 baseEnd_2046926 := by
    simpa [prefixWord, tailWord_2046926, baseEnd_2046926] using wordTrace_append hprefix tailTrace_2046926
  have hstable : (prefixWord ++ tailWord_2046926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046926).length < 2 ^ (prefixWord ++ tailWord_2046926).sum := by decide
  have hdescent : baseEnd_2046926 < baseStart_2046926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046964 : List Nat := [2, 6, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2046964 : Nat := 118140960795 + 2046964 * 2 ^ 59
def prefixEnd_2046964 : Nat := 4983230072969 + 3 ^ 40 * 2046964 * 2
def baseEnd_2046964 : Nat := 700717609633356318424127

theorem tailTrace_2046964 : CollatzResearch.WordTrace tailWord_2046964 prefixEnd_2046964 700717609633356318424127 := by
  unfold tailWord_2046964
  simp only [CollatzResearch.WordTrace]
  refine ⟨37329455278103248231869973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49772607037470997642493297 37329455278103248231869973)
  ·
    refine ⟨1749818216161089760868905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37329455278103248231869973 1749818216161089760868905)
    ·
      refine ⟨1312363662120817320651679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1749818216161089760868905 1312363662120817320651679)
      ·
        refine ⟨1968545493181225980977519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1312363662120817320651679 1968545493181225980977519)
        ·
          refine ⟨2952818239771838971466279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1968545493181225980977519 2952818239771838971466279)
          ·
            refine ⟨4429227359657758457199419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2952818239771838971466279 4429227359657758457199419)
            ·
              refine ⟨6643841039486637685799129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4429227359657758457199419 6643841039486637685799129)
              ·
                refine ⟨4982880779614978264349347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6643841039486637685799129 4982880779614978264349347)
                ·
                  refine ⟨7474321169422467396524021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4982880779614978264349347 7474321169422467396524021)
                  ·
                    refine ⟨700717609633356318424127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7474321169422467396524021 700717609633356318424127)
                    ·
                      rfl

theorem cell22_2046964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2046964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046964 prefixEnd_2046964 := by exact prefixLift 2046964
  have htrace : WordTrace (prefixWord ++ tailWord_2046964) baseStart_2046964 baseEnd_2046964 := by
    simpa [prefixWord, tailWord_2046964, baseEnd_2046964] using wordTrace_append hprefix tailTrace_2046964
  have hstable : (prefixWord ++ tailWord_2046964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046964).length < 2 ^ (prefixWord ++ tailWord_2046964).sum := by decide
  have hdescent : baseEnd_2046964 < baseStart_2046964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046988 : List Nat := [2, 2, 1, 2, 3, 3, 2, 2, 5]
def baseStart_2046988 : Nat := 118140960795 + 2046988 * 2 ^ 59
def prefixEnd_2046988 : Nat := 4983230072969 + 3 ^ 40 * 2046988 * 2
def baseEnd_2046988 : Nat := 233575275107942751941351

theorem tailTrace_2046988 : CollatzResearch.WordTrace tailWord_2046988 prefixEnd_2046988 233575275107942751941351 := by
  unfold tailWord_2046988
  simp only [CollatzResearch.WordTrace]
  refine ⟨37329892954059774281306809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49773190605413032375075745 37329892954059774281306809)
  ·
    refine ⟨27997419715544830710980107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37329892954059774281306809 27997419715544830710980107)
    ·
      refine ⟨41996129573317246066470161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27997419715544830710980107 41996129573317246066470161)
      ·
        refine ⟨31497097179987934549852621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41996129573317246066470161 31497097179987934549852621)
        ·
          refine ⟨11811411442495475456194733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31497097179987934549852621 11811411442495475456194733)
          ·
            refine ⟨4429279290935803296073025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11811411442495475456194733 4429279290935803296073025)
            ·
              refine ⟨3321959468201852472054769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4429279290935803296073025 3321959468201852472054769)
              ·
                refine ⟨2491469601151389354041077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3321959468201852472054769 2491469601151389354041077)
                ·
                  refine ⟨233575275107942751941351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2491469601151389354041077 233575275107942751941351)
                  ·
                    rfl

theorem cell22_2046988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_2046988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046988 prefixEnd_2046988 := by exact prefixLift 2046988
  have htrace : WordTrace (prefixWord ++ tailWord_2046988) baseStart_2046988 baseEnd_2046988 := by
    simpa [prefixWord, tailWord_2046988, baseEnd_2046988] using wordTrace_append hprefix tailTrace_2046988
  have hstable : (prefixWord ++ tailWord_2046988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046988).length < 2 ^ (prefixWord ++ tailWord_2046988).sum := by decide
  have hdescent : baseEnd_2046988 < baseStart_2046988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046994 : List Nat := [3, 2, 5, 1, 2, 1, 1, 7]
def baseStart_2046994 : Nat := 118140960795 + 2046994 * 2 ^ 59
def prefixEnd_2046994 : Nat := 4983230072969 + 3 ^ 40 * 2046994 * 2
def baseEnd_2046994 : Nat := 77858653249605137797115

theorem tailTrace_2046994 : CollatzResearch.WordTrace tailWord_2046994 prefixEnd_2046994 77858653249605137797115 := by
  unfold tailWord_2046994
  simp only [CollatzResearch.WordTrace]
  refine ⟨18665001186524452896833009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49773336497398541058221357 18665001186524452896833009)
  ·
    refine ⟨13998750889893339672624757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18665001186524452896833009 13998750889893339672624757)
    ·
      refine ⟨1312382895927500594308571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13998750889893339672624757 1312382895927500594308571)
      ·
        refine ⟨1968574343891250891462857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1312382895927500594308571 1968574343891250891462857)
        ·
          refine ⟨1476430757918438168597143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1968574343891250891462857 1476430757918438168597143)
          ·
            refine ⟨2214646136877657252895715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1476430757918438168597143 2214646136877657252895715)
            ·
              refine ⟨3321969205316485879343573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2214646136877657252895715 3321969205316485879343573)
              ·
                refine ⟨77858653249605137797115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3321969205316485879343573 77858653249605137797115)
                ·
                  rfl

theorem cell22_2046994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 7].length) (baseStart_2046994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2046994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2046994 prefixEnd_2046994 := by exact prefixLift 2046994
  have htrace : WordTrace (prefixWord ++ tailWord_2046994) baseStart_2046994 baseEnd_2046994 := by
    simpa [prefixWord, tailWord_2046994, baseEnd_2046994] using wordTrace_append hprefix tailTrace_2046994
  have hstable : (prefixWord ++ tailWord_2046994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046994).length < 2 ^ (prefixWord ++ tailWord_2046994).sum := by decide
  have hdescent : baseEnd_2046994 < baseStart_2046994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047001 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 3, 4]
def baseStart_2047001 : Nat := 118140960795 + 2047001 * 2 ^ 59
def prefixEnd_2047001 : Nat := 4983230072969 + 3 ^ 40 * 2047001 * 2
def baseEnd_2047001 : Nat := 700730275489500555249013

theorem tailTrace_2047001 : CollatzResearch.WordTrace tailWord_2047001 prefixEnd_2047001 700730275489500555249013 := by
  unfold tailWord_2047001
  simp only [CollatzResearch.WordTrace]
  refine ⟨74660260057072451782836857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49773506704714967855224571 74660260057072451782836857)
  ·
    refine ⟨55995195042804338837127643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74660260057072451782836857 55995195042804338837127643)
    ·
      refine ⟨83992792564206508255691465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55995195042804338837127643 83992792564206508255691465)
      ·
        refine ⟨62994594423154881191768599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83992792564206508255691465 62994594423154881191768599)
        ·
          refine ⟨94491891634732321787652899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62994594423154881191768599 94491891634732321787652899)
          ·
            refine ⟨141737837452098482681479349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94491891634732321787652899 141737837452098482681479349)
            ·
              refine ⟨13287922261134232751388689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141737837452098482681479349 13287922261134232751388689)
              ·
                refine ⟨9965941695850674563541517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13287922261134232751388689 9965941695850674563541517)
                ·
                  refine ⟨3737228135944002961328069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9965941695850674563541517 3737228135944002961328069)
                  ·
                    refine ⟨700730275489500555249013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3737228135944002961328069 700730275489500555249013)
                    ·
                      rfl

theorem cell22_2047001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 4].length) (baseStart_2047001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047001 prefixEnd_2047001 := by exact prefixLift 2047001
  have htrace : WordTrace (prefixWord ++ tailWord_2047001) baseStart_2047001 baseEnd_2047001 := by
    simpa [prefixWord, tailWord_2047001, baseEnd_2047001] using wordTrace_append hprefix tailTrace_2047001
  have hstable : (prefixWord ++ tailWord_2047001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047001).length < 2 ^ (prefixWord ++ tailWord_2047001).sum := by decide
  have hdescent : baseEnd_2047001 < baseStart_2047001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047048 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 4, 3]
def baseStart_2047048 : Nat := 118140960795 + 2047048 * 2 ^ 59
def prefixEnd_2047048 : Nat := 4983230072969 + 3 ^ 40 * 2047048 * 2
def baseEnd_2047048 : Nat := 700746364550008099323869

theorem tailTrace_2047048 : CollatzResearch.WordTrace tailWord_2047048 prefixEnd_2047048 700746364550008099323869 := by
  unfold tailWord_2047048
  simp only [CollatzResearch.WordTrace]
  refine ⟨37330987143951089404898899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49774649525268119206531865 37330987143951089404898899)
  ·
    refine ⟨55996480715926634107348349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37330987143951089404898899 55996480715926634107348349)
    ·
      refine ⟨20998680268472487790255631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55996480715926634107348349 20998680268472487790255631)
      ·
        refine ⟨31498020402708731685383447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20998680268472487790255631 31498020402708731685383447)
        ·
          refine ⟨47247030604063097528075171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31498020402708731685383447 47247030604063097528075171)
          ·
            refine ⟨70870545906094646292112757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47247030604063097528075171 70870545906094646292112757)
            ·
              refine ⟨6644113678696373089885571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70870545906094646292112757 6644113678696373089885571)
              ·
                refine ⟨9966170518044559634828357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6644113678696373089885571 9966170518044559634828357)
                ·
                  refine ⟨1868656972133354931530317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9966170518044559634828357 1868656972133354931530317)
                  ·
                    refine ⟨700746364550008099323869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1868656972133354931530317 700746364550008099323869)
                    ·
                      rfl

theorem cell22_2047048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_2047048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047048 prefixEnd_2047048 := by exact prefixLift 2047048
  have htrace : WordTrace (prefixWord ++ tailWord_2047048) baseStart_2047048 baseEnd_2047048 := by
    simpa [prefixWord, tailWord_2047048, baseEnd_2047048] using wordTrace_append hprefix tailTrace_2047048
  have hstable : (prefixWord ++ tailWord_2047048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047048).length < 2 ^ (prefixWord ++ tailWord_2047048).sum := by decide
  have hdescent : baseEnd_2047048 < baseStart_2047048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047061 : List Nat := [1, 3, 2, 2, 1, 2, 2, 9]
def baseStart_2047061 : Nat := 118140960795 + 2047061 * 2 ^ 59
def prefixEnd_2047061 : Nat := 4983230072969 + 3 ^ 40 * 2047061 * 2
def baseEnd_2047061 : Nat := 77861201635075599860981

theorem tailTrace_2047061 : CollatzResearch.WordTrace tailWord_2047061 prefixEnd_2047061 77861201635075599860981 := by
  unfold tailWord_2047061
  simp only [CollatzResearch.WordTrace]
  refine ⟨74662448436855082030021037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49774965624570054686680691 74662448436855082030021037)
  ·
    refine ⟨27998418163820655761257889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74662448436855082030021037 27998418163820655761257889)
    ·
      refine ⟨20998813622865491820943417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27998418163820655761257889 20998813622865491820943417)
      ·
        refine ⟨15749110217149118865707563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20998813622865491820943417 15749110217149118865707563)
        ·
          refine ⟨23623665325723678298561345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15749110217149118865707563 23623665325723678298561345)
          ·
            refine ⟨17717748994292758723921009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23623665325723678298561345 17717748994292758723921009)
            ·
              refine ⟨13288311745719569042940757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17717748994292758723921009 13288311745719569042940757)
              ·
                refine ⟨77861201635075599860981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13288311745719569042940757 77861201635075599860981)
                ·
                  rfl

theorem cell22_2047061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 9].length) (baseStart_2047061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047061 prefixEnd_2047061 := by exact prefixLift 2047061
  have htrace : WordTrace (prefixWord ++ tailWord_2047061) baseStart_2047061 baseEnd_2047061 := by
    simpa [prefixWord, tailWord_2047061, baseEnd_2047061] using wordTrace_append hprefix tailTrace_2047061
  have hstable : (prefixWord ++ tailWord_2047061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047061).length < 2 ^ (prefixWord ++ tailWord_2047061).sum := by decide
  have hdescent : baseEnd_2047061 < baseStart_2047061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047076 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_2047076 : Nat := 118140960795 + 2047076 * 2 ^ 59
def prefixEnd_2047076 : Nat := 4983230072969 + 3 ^ 40 * 2047076 * 2
def baseEnd_2047076 : Nat := 700755949522225359623783

theorem tailTrace_2047076 : CollatzResearch.WordTrace tailWord_2047076 prefixEnd_2047076 700755949522225359623783 := by
  unfold tailWord_2047076
  simp only [CollatzResearch.WordTrace]
  refine ⟨37331497765900369795908541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49775330354533826394544721 37331497765900369795908541)
  ·
    refine ⟨13999311662212638673465703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37331497765900369795908541 13999311662212638673465703)
    ·
      refine ⟨20998967493318958010198555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13999311662212638673465703 20998967493318958010198555)
      ·
        refine ⟨31498451239978437015297833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20998967493318958010198555 31498451239978437015297833)
        ·
          refine ⟨23623838429983827761473375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31498451239978437015297833 23623838429983827761473375)
          ·
            refine ⟨35435757644975741642210063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23623838429983827761473375 35435757644975741642210063)
            ·
              refine ⟨53153636467463612463315095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35435757644975741642210063 53153636467463612463315095)
              ·
                refine ⟨79730454701195418694972643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53153636467463612463315095 79730454701195418694972643)
                ·
                  refine ⟨119595682051793128042458965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79730454701195418694972643 119595682051793128042458965)
                  ·
                    refine ⟨700755949522225359623783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 119595682051793128042458965 700755949522225359623783)
                    ·
                      rfl

theorem cell22_2047076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_2047076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047076 prefixEnd_2047076 := by exact prefixLift 2047076
  have htrace : WordTrace (prefixWord ++ tailWord_2047076) baseStart_2047076 baseEnd_2047076 := by
    simpa [prefixWord, tailWord_2047076, baseEnd_2047076] using wordTrace_append hprefix tailTrace_2047076
  have hstable : (prefixWord ++ tailWord_2047076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047076).length < 2 ^ (prefixWord ++ tailWord_2047076).sum := by decide
  have hdescent : baseEnd_2047076 < baseStart_2047076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047234 : List Nat := [3, 4, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_2047234 : Nat := 118140960795 + 2047234 * 2 ^ 59
def prefixEnd_2047234 : Nat := 4983230072969 + 3 ^ 40 * 2047234 * 2
def baseEnd_2047234 : Nat := 700810036151165614173299

theorem tailTrace_2047234 : CollatzResearch.WordTrace tailWord_2047234 prefixEnd_2047234 700810036151165614173299 := by
  unfold tailWord_2047234
  simp only [CollatzResearch.WordTrace]
  refine ⟨18667189566307083144017189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49779172176818888384045837 18667189566307083144017189)
  ·
    refine ⟨3500098043682578089503223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18667189566307083144017189 3500098043682578089503223)
    ·
      refine ⟨5250147065523867134254835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3500098043682578089503223 5250147065523867134254835)
      ·
        refine ⟨7875220598285800701382253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5250147065523867134254835 7875220598285800701382253)
        ·
          refine ⟨2953207724357175263018345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7875220598285800701382253 2953207724357175263018345)
          ·
            refine ⟨2214905793267881447263759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2953207724357175263018345 2214905793267881447263759)
            ·
              refine ⟨3322358689901822170895639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2214905793267881447263759 3322358689901822170895639)
              ·
                refine ⟨4983538034852733256343459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3322358689901822170895639 4983538034852733256343459)
                ·
                  refine ⟨7475307052279099884515189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4983538034852733256343459 7475307052279099884515189)
                  ·
                    refine ⟨700810036151165614173299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7475307052279099884515189 700810036151165614173299)
                    ·
                      rfl

theorem cell22_2047234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_2047234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047234 prefixEnd_2047234 := by exact prefixLift 2047234
  have htrace : WordTrace (prefixWord ++ tailWord_2047234) baseStart_2047234 baseEnd_2047234 := by
    simpa [prefixWord, tailWord_2047234, baseEnd_2047234] using wordTrace_append hprefix tailTrace_2047234
  have hstable : (prefixWord ++ tailWord_2047234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047234).length < 2 ^ (prefixWord ++ tailWord_2047234).sum := by decide
  have hdescent : baseEnd_2047234 < baseStart_2047234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047288 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 2, 8]
def baseStart_2047288 : Nat := 118140960795 + 2047288 * 2 ^ 59
def prefixEnd_2047288 : Nat := 4983230072969 + 3 ^ 40 * 2047288 * 2
def baseEnd_2047288 : Nat := 700828521454727473323133

theorem tailTrace_2047288 : CollatzResearch.WordTrace tailWord_2047288 prefixEnd_2047288 700828521454727473323133 := by
  unfold tailWord_2047288
  simp only [CollatzResearch.WordTrace]
  refine ⟨37335363903516349899267259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49780485204688466532356345 37335363903516349899267259)
  ·
    refine ⟨56003045855274524848900889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37335363903516349899267259 56003045855274524848900889)
    ·
      refine ⟨42002284391455893636675667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56003045855274524848900889 42002284391455893636675667)
      ·
        refine ⟨63003426587183840455013501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42002284391455893636675667 63003426587183840455013501)
        ·
          refine ⟨23626284970193940170630063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63003426587183840455013501 23626284970193940170630063)
          ·
            refine ⟨35439427455290910255945095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23626284970193940170630063 35439427455290910255945095)
            ·
              refine ⟨53159141182936365383917643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35439427455290910255945095 53159141182936365383917643)
              ·
                refine ⟨79738711774404548075876465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53159141182936365383917643 79738711774404548075876465)
                ·
                  refine ⟨59804033830803411056907349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79738711774404548075876465 59804033830803411056907349)
                  ·
                    refine ⟨700828521454727473323133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59804033830803411056907349 700828521454727473323133)
                    ·
                      rfl

theorem cell22_2047288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_2047288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047288 prefixEnd_2047288 := by exact prefixLift 2047288
  have htrace : WordTrace (prefixWord ++ tailWord_2047288) baseStart_2047288 baseEnd_2047288 := by
    simpa [prefixWord, tailWord_2047288, baseEnd_2047288] using wordTrace_append hprefix tailTrace_2047288
  have hstable : (prefixWord ++ tailWord_2047288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047288).length < 2 ^ (prefixWord ++ tailWord_2047288).sum := by decide
  have hdescent : baseEnd_2047288 < baseStart_2047288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047292 : List Nat := [2, 2, 2, 2, 1, 3, 4, 1, 5]
def baseStart_2047292 : Nat := 118140960795 + 2047292 * 2 ^ 59
def prefixEnd_2047292 : Nat := 4983230072969 + 3 ^ 40 * 2047292 * 2
def baseEnd_2047292 : Nat := 233609963578824265407707

theorem tailTrace_2047292 : CollatzResearch.WordTrace tailWord_2047292 prefixEnd_2047292 233609963578824265407707 := by
  unfold tailWord_2047292
  simp only [CollatzResearch.WordTrace]
  refine ⟨37335436849509104240840065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49780582466012138987786753 37335436849509104240840065)
  ·
    refine ⟨28001577637131828180630049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37335436849509104240840065 28001577637131828180630049)
    ·
      refine ⟨21001183227848871135472537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28001577637131828180630049 21001183227848871135472537)
      ·
        refine ⟨15750887420886653351604403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21001183227848871135472537 15750887420886653351604403)
        ·
          refine ⟨23626331131329980027406605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15750887420886653351604403 23626331131329980027406605)
          ·
            refine ⟨8859874174248742510277477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23626331131329980027406605 8859874174248742510277477)
            ·
              refine ⟨1661226407671639220677027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8859874174248742510277477 1661226407671639220677027)
              ·
                refine ⟨2491839611507458831015541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1661226407671639220677027 2491839611507458831015541)
                ·
                  refine ⟨233609963578824265407707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2491839611507458831015541 233609963578824265407707)
                  ·
                    rfl

theorem cell22_2047292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 5].length) (baseStart_2047292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047292 prefixEnd_2047292 := by exact prefixLift 2047292
  have htrace : WordTrace (prefixWord ++ tailWord_2047292) baseStart_2047292 baseEnd_2047292 := by
    simpa [prefixWord, tailWord_2047292, baseEnd_2047292] using wordTrace_append hprefix tailTrace_2047292
  have hstable : (prefixWord ++ tailWord_2047292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047292).length < 2 ^ (prefixWord ++ tailWord_2047292).sum := by decide
  have hdescent : baseEnd_2047292 < baseStart_2047292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047367 : List Nat := [1, 1, 4, 2, 2, 2, 3, 1, 2, 4]
def baseStart_2047367 : Nat := 118140960795 + 2047367 * 2 ^ 59
def prefixEnd_2047367 : Nat := 4983230072969 + 3 ^ 40 * 2047367 * 2
def baseEnd_2047367 : Nat := 700855564769197600597891

theorem tailTrace_2047367 : CollatzResearch.WordTrace tailWord_2047367 prefixEnd_2047367 700855564769197600597891 := by
  unfold tailWord_2047367
  simp only [CollatzResearch.WordTrace]
  refine ⟨74673609173746496290660355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49782406115830997527106903 74673609173746496290660355)
  ·
    refine ⟨112010413760619744435990533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74673609173746496290660355 112010413760619744435990533)
    ·
      refine ⟨21001952580116202081748225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112010413760619744435990533 21001952580116202081748225)
      ·
        refine ⟨15751464435087151561311169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21001952580116202081748225 15751464435087151561311169)
        ·
          refine ⟨11813598326315363670983377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15751464435087151561311169 11813598326315363670983377)
          ·
            refine ⟨8860198744736522753237533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11813598326315363670983377 8860198744736522753237533)
            ·
              refine ⟨3322574529276196032464075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8860198744736522753237533 3322574529276196032464075)
              ·
                refine ⟨4983861793914294048696113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3322574529276196032464075 4983861793914294048696113)
                ·
                  refine ⟨3737896345435720536522085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4983861793914294048696113 3737896345435720536522085)
                  ·
                    refine ⟨700855564769197600597891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3737896345435720536522085 700855564769197600597891)
                    ·
                      rfl

theorem cell22_2047367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_2047367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047367 prefixEnd_2047367 := by exact prefixLift 2047367
  have htrace : WordTrace (prefixWord ++ tailWord_2047367) baseStart_2047367 baseEnd_2047367 := by
    simpa [prefixWord, tailWord_2047367, baseEnd_2047367] using wordTrace_append hprefix tailTrace_2047367
  have hstable : (prefixWord ++ tailWord_2047367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047367).length < 2 ^ (prefixWord ++ tailWord_2047367).sum := by decide
  have hdescent : baseEnd_2047367 < baseStart_2047367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047461 : List Nat := [1, 3, 1, 5, 1, 3, 2, 1, 5]
def baseStart_2047461 : Nat := 118140960795 + 2047461 * 2 ^ 59
def prefixEnd_2047461 : Nat := 4983230072969 + 3 ^ 40 * 2047461 * 2
def baseEnd_2047461 : Nat := 233629247630070896249201

theorem tailTrace_2047461 : CollatzResearch.WordTrace tailWord_2047461 prefixEnd_2047461 233629247630070896249201 := by
  unfold tailWord_2047461
  simp only [CollatzResearch.WordTrace]
  refine ⟨74677037635405950344582237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49784691756937300229721491 74677037635405950344582237)
  ·
    refine ⟨28003889113277231379218339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74677037635405950344582237 28003889113277231379218339)
    ·
      refine ⟨42005833669915847068827509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28003889113277231379218339 42005833669915847068827509)
      ·
        refine ⟨3938046906554610662702579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42005833669915847068827509 3938046906554610662702579)
        ·
          refine ⟨5907070359831915994053869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3938046906554610662702579 5907070359831915994053869)
          ·
            refine ⟨2215151384936968497770201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5907070359831915994053869 2215151384936968497770201)
            ·
              refine ⟨1661363538702726373327651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2215151384936968497770201 1661363538702726373327651)
              ·
                refine ⟨2492045308054089559991477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1661363538702726373327651 2492045308054089559991477)
                ·
                  refine ⟨233629247630070896249201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2492045308054089559991477 233629247630070896249201)
                  ·
                    rfl

theorem cell22_2047461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 5].length) (baseStart_2047461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047461 prefixEnd_2047461 := by exact prefixLift 2047461
  have htrace : WordTrace (prefixWord ++ tailWord_2047461) baseStart_2047461 baseEnd_2047461 := by
    simpa [prefixWord, tailWord_2047461, baseEnd_2047461] using wordTrace_append hprefix tailTrace_2047461
  have hstable : (prefixWord ++ tailWord_2047461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047461).length < 2 ^ (prefixWord ++ tailWord_2047461).sum := by decide
  have hdescent : baseEnd_2047461 < baseStart_2047461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047474 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 3, 4]
def baseStart_2047474 : Nat := 118140960795 + 2047474 * 2 ^ 59
def prefixEnd_2047474 : Nat := 4983230072969 + 3 ^ 40 * 2047474 * 2
def baseEnd_2047474 : Nat := 700892193055884988172563

theorem tailTrace_2047474 : CollatzResearch.WordTrace tailWord_2047474 prefixEnd_2047474 700892193055884988172563 := by
  unfold tailWord_2047474
  simp only [CollatzResearch.WordTrace]
  refine ⟨18669377946089713391201369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49785007856239235709870317 18669377946089713391201369)
  ·
    refine ⟨14002033459567285043401027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18669377946089713391201369 14002033459567285043401027)
    ·
      refine ⟨21003050189350927565101541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14002033459567285043401027 21003050189350927565101541)
      ·
        refine ⟨3938071910503298918456539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21003050189350927565101541 3938071910503298918456539)
        ·
          refine ⟨5907107865754948377684809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3938071910503298918456539 5907107865754948377684809)
          ·
            refine ⟨4430330899316211283263607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5907107865754948377684809 4430330899316211283263607)
            ·
              refine ⟨6645496348974316924895411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4430330899316211283263607 6645496348974316924895411)
              ·
                refine ⟨9968244523461475387343117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6645496348974316924895411 9968244523461475387343117)
                ·
                  refine ⟨3738091696298053270253669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9968244523461475387343117 3738091696298053270253669)
                  ·
                    refine ⟨700892193055884988172563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3738091696298053270253669 700892193055884988172563)
                    ·
                      rfl

theorem cell22_2047474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_2047474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047474 prefixEnd_2047474 := by exact prefixLift 2047474
  have htrace : WordTrace (prefixWord ++ tailWord_2047474) baseStart_2047474 baseEnd_2047474 := by
    simpa [prefixWord, tailWord_2047474, baseEnd_2047474] using wordTrace_append hprefix tailTrace_2047474
  have hstable : (prefixWord ++ tailWord_2047474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047474).length < 2 ^ (prefixWord ++ tailWord_2047474).sum := by decide
  have hdescent : baseEnd_2047474 < baseStart_2047474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047487 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 4, 3]
def baseStart_2047487 : Nat := 118140960795 + 2047487 * 2 ^ 59
def prefixEnd_2047487 : Nat := 4983230072969 + 3 ^ 40 * 2047487 * 2
def baseEnd_2047487 : Nat := 700896643221557287597523

theorem tailTrace_2047487 : CollatzResearch.WordTrace tailWord_2047487 prefixEnd_2047487 700896643221557287597523 := by
  unfold tailWord_2047487
  simp only [CollatzResearch.WordTrace]
  refine ⟨74677985933311756785028715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49785323955541171190019143 74677985933311756785028715)
  ·
    refine ⟨112016978899967635177543073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74677985933311756785028715 112016978899967635177543073)
    ·
      refine ⟨84012734174975726383157305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112016978899967635177543073 84012734174975726383157305)
      ·
        refine ⟨63009550631231794787367979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84012734174975726383157305 63009550631231794787367979)
        ·
          refine ⟨94514325946847692181051969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63009550631231794787367979 94514325946847692181051969)
          ·
            refine ⟨70885744460135769135788977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94514325946847692181051969 70885744460135769135788977)
            ·
              refine ⟨53164308345101826851841733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70885744460135769135788977 53164308345101826851841733)
              ·
                refine ⟨9968307814706592534720325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53164308345101826851841733 9968307814706592534720325)
                ·
                  refine ⟨1869057715257486100260061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9968307814706592534720325 1869057715257486100260061)
                  ·
                    refine ⟨700896643221557287597523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1869057715257486100260061 700896643221557287597523)
                    ·
                      rfl

theorem cell22_2047487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 3].length) (baseStart_2047487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047487 prefixEnd_2047487 := by exact prefixLift 2047487
  have htrace : WordTrace (prefixWord ++ tailWord_2047487) baseStart_2047487 baseEnd_2047487 := by
    simpa [prefixWord, tailWord_2047487, baseEnd_2047487] using wordTrace_append hprefix tailTrace_2047487
  have hstable : (prefixWord ++ tailWord_2047487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047487).length < 2 ^ (prefixWord ++ tailWord_2047487).sum := by decide
  have hdescent : baseEnd_2047487 < baseStart_2047487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047500 : List Nat := [2, 2, 1, 2, 15]
def baseStart_2047500 : Nat := 118140960795 + 2047500 * 2 ^ 59
def prefixEnd_2047500 : Nat := 4983230072969 + 3 ^ 40 * 2047500 * 2
def baseEnd_2047500 : Nat := 2884366639453619699681

theorem tailTrace_2047500 : CollatzResearch.WordTrace tailWord_2047500 prefixEnd_2047500 2884366639453619699681 := by
  unfold tailWord_2047500
  simp only [CollatzResearch.WordTrace]
  refine ⟨37339230041132330002625977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49785640054843106670167969 37339230041132330002625977)
  ·
    refine ⟨28004422530849247501969483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37339230041132330002625977 28004422530849247501969483)
    ·
      refine ⟨42006633796273871252954225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28004422530849247501969483 42006633796273871252954225)
      ·
        refine ⟨31504975347205403439715669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42006633796273871252954225 31504975347205403439715669)
        ·
          refine ⟨2884366639453619699681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 31504975347205403439715669 2884366639453619699681)
          ·
            rfl

theorem cell22_2047500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 15].length) (baseStart_2047500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047500 prefixEnd_2047500 := by exact prefixLift 2047500
  have htrace : WordTrace (prefixWord ++ tailWord_2047500) baseStart_2047500 baseEnd_2047500 := by
    simpa [prefixWord, tailWord_2047500, baseEnd_2047500] using wordTrace_append hprefix tailTrace_2047500
  have hstable : (prefixWord ++ tailWord_2047500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047500).length < 2 ^ (prefixWord ++ tailWord_2047500).sum := by decide
  have hdescent : baseEnd_2047500 < baseStart_2047500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047562 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 7]
def baseStart_2047562 : Nat := 118140960795 + 2047562 * 2 ^ 59
def prefixEnd_2047562 : Nat := 4983230072969 + 3 ^ 40 * 2047562 * 2
def baseEnd_2047562 : Nat := 233640772418094030657431

theorem tailTrace_2047562 : CollatzResearch.WordTrace tailWord_2047562 prefixEnd_2047562 233640772418094030657431 := by
  unfold tailWord_2047562
  simp only [CollatzResearch.WordTrace]
  refine ⟨18670180352010011148502235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49787147605360029729339293 18670180352010011148502235)
  ·
    refine ⟨28005270528015016722753353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18670180352010011148502235 28005270528015016722753353)
    ·
      refine ⟨21003952896011262542065015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28005270528015016722753353 21003952896011262542065015)
      ·
        refine ⟨31505929344016893813097523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21003952896011262542065015 31505929344016893813097523)
        ·
          refine ⟨47258894016025340719646285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31505929344016893813097523 47258894016025340719646285)
          ·
            refine ⟨17722085256009502769867357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47258894016025340719646285 17722085256009502769867357)
            ·
              refine ⟨6645781971003563538700259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17722085256009502769867357 6645781971003563538700259)
              ·
                refine ⟨9968672956505345308050389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6645781971003563538700259 9968672956505345308050389)
                ·
                  refine ⟨233640772418094030657431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9968672956505345308050389 233640772418094030657431)
                  ·
                    rfl

theorem cell22_2047562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_2047562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047562 prefixEnd_2047562 := by exact prefixLift 2047562
  have htrace : WordTrace (prefixWord ++ tailWord_2047562) baseStart_2047562 baseEnd_2047562 := by
    simpa [prefixWord, tailWord_2047562, baseEnd_2047562] using wordTrace_append hprefix tailTrace_2047562
  have hstable : (prefixWord ++ tailWord_2047562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047562).length < 2 ^ (prefixWord ++ tailWord_2047562).sum := by decide
  have hdescent : baseEnd_2047562 < baseStart_2047562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047609 : List Nat := [1, 2, 1, 3, 3, 1, 1, 5, 1, 4]
def baseStart_2047609 : Nat := 118140960795 + 2047609 * 2 ^ 59
def prefixEnd_2047609 : Nat := 4983230072969 + 3 ^ 40 * 2047609 * 2
def baseEnd_2047609 : Nat := 700938406314789636047149

theorem tailTrace_2047609 : CollatzResearch.WordTrace tailWord_2047609 prefixEnd_2047609 700938406314789636047149 := by
  unfold tailWord_2047609
  simp only [CollatzResearch.WordTrace]
  refine ⟨74682435638869771620969881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49788290425913181080646587 74682435638869771620969881)
  ·
    refine ⟨56011826729152328715727411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74682435638869771620969881 56011826729152328715727411)
    ·
      refine ⟨84017740093728493073591117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56011826729152328715727411 84017740093728493073591117)
      ·
        refine ⟨31506652535148184902596669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84017740093728493073591117 31506652535148184902596669)
        ·
          refine ⟨11814994700680569338473751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31506652535148184902596669 11814994700680569338473751)
          ·
            refine ⟨17722492051020854007710627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11814994700680569338473751 17722492051020854007710627)
            ·
              refine ⟨26583738076531281011565941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17722492051020854007710627 26583738076531281011565941)
              ·
                refine ⟨2492225444674807594834307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26583738076531281011565941 2492225444674807594834307)
                ·
                  refine ⟨3738338167012211392251461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2492225444674807594834307 3738338167012211392251461)
                  ·
                    refine ⟨700938406314789636047149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3738338167012211392251461 700938406314789636047149)
                    ·
                      rfl

theorem cell22_2047609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 4].length) (baseStart_2047609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047609 prefixEnd_2047609 := by exact prefixLift 2047609
  have htrace : WordTrace (prefixWord ++ tailWord_2047609) baseStart_2047609 baseEnd_2047609 := by
    simpa [prefixWord, tailWord_2047609, baseEnd_2047609] using wordTrace_append hprefix tailTrace_2047609
  have hstable : (prefixWord ++ tailWord_2047609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047609).length < 2 ^ (prefixWord ++ tailWord_2047609).sum := by decide
  have hdescent : baseEnd_2047609 < baseStart_2047609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047637 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 3, 6]
def baseStart_2047637 : Nat := 118140960795 + 2047637 * 2 ^ 59
def prefixEnd_2047637 : Nat := 4983230072969 + 3 ^ 40 * 2047637 * 2
def baseEnd_2047637 : Nat := 700947991287006896347063

theorem tailTrace_2047637 : CollatzResearch.WordTrace tailWord_2047637 prefixEnd_2047637 700947991287006896347063 := by
  unfold tailWord_2047637
  simp only [CollatzResearch.WordTrace]
  refine ⟨74683456882768332402989165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49788971255178888268659443 74683456882768332402989165)
  ·
    refine ⟨28006296331038124651120937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74683456882768332402989165 28006296331038124651120937)
    ·
      refine ⟨21004722248278593488340703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28006296331038124651120937 21004722248278593488340703)
      ·
        refine ⟨31507083372417890232511055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21004722248278593488340703 31507083372417890232511055)
        ·
          refine ⟨47260625058626835348766583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31507083372417890232511055 47260625058626835348766583)
          ·
            refine ⟨70890937587940253023149875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47260625058626835348766583 70890937587940253023149875)
            ·
              refine ⟨106336406381910379534724813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70890937587940253023149875 106336406381910379534724813)
              ·
                refine ⟨39876152393216392325521805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106336406381910379534724813 39876152393216392325521805)
                ·
                  refine ⟨14953557147456147122070677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39876152393216392325521805 14953557147456147122070677)
                  ·
                    refine ⟨700947991287006896347063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14953557147456147122070677 700947991287006896347063)
                    ·
                      rfl

theorem cell22_2047637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_2047637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047637 prefixEnd_2047637 := by exact prefixLift 2047637
  have htrace : WordTrace (prefixWord ++ tailWord_2047637) baseStart_2047637 baseEnd_2047637 := by
    simpa [prefixWord, tailWord_2047637, baseEnd_2047637] using wordTrace_append hprefix tailTrace_2047637
  have hstable : (prefixWord ++ tailWord_2047637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047637).length < 2 ^ (prefixWord ++ tailWord_2047637).sum := by decide
  have hdescent : baseEnd_2047637 < baseStart_2047637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047669 : List Nat := [1, 3, 3, 3, 2, 10]
def baseStart_2047669 : Nat := 118140960795 + 2047669 * 2 ^ 59
def prefixEnd_2047669 : Nat := 4983230072969 + 3 ^ 40 * 2047669 * 2
def baseEnd_2047669 : Nat := 8653814142481104685765

theorem tailTrace_2047669 : CollatzResearch.WordTrace tailWord_2047669 prefixEnd_2047669 8653814142481104685765 := by
  unfold tailWord_2047669
  simp only [CollatzResearch.WordTrace]
  refine ⟨74684624018652401868154061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49789749345768267912102707 74684624018652401868154061)
  ·
    refine ⟨28006734006994650700557773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74684624018652401868154061 28006734006994650700557773)
    ·
      refine ⟨10502525252622994012709165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28006734006994650700557773 10502525252622994012709165)
      ·
        refine ⟨3938446969733622754765937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10502525252622994012709165 3938446969733622754765937)
        ·
          refine ⟨2953835227300217066074453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3938446969733622754765937 2953835227300217066074453)
          ·
            refine ⟨8653814142481104685765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2953835227300217066074453 8653814142481104685765)
            ·
              rfl

theorem cell22_2047669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 10].length) (baseStart_2047669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047669 prefixEnd_2047669 := by exact prefixLift 2047669
  have htrace : WordTrace (prefixWord ++ tailWord_2047669) baseStart_2047669 baseEnd_2047669 := by
    simpa [prefixWord, tailWord_2047669, baseEnd_2047669] using wordTrace_append hprefix tailTrace_2047669
  have hstable : (prefixWord ++ tailWord_2047669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047669).length < 2 ^ (prefixWord ++ tailWord_2047669).sum := by decide
  have hdescent : baseEnd_2047669 < baseStart_2047669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047729 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 2, 5]
def baseStart_2047729 : Nat := 118140960795 + 2047729 * 2 ^ 59
def prefixEnd_2047729 : Nat := 4983230072969 + 3 ^ 40 * 2047729 * 2
def baseEnd_2047729 : Nat := 700979484767149323046781

theorem tailTrace_2047729 : CollatzResearch.WordTrace tailWord_2047729 prefixEnd_2047729 700979484767149323046781 := by
  unfold tailWord_2047729
  simp only [CollatzResearch.WordTrace]
  refine ⟨74686812398435032115338241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49791208265623354743558827 74686812398435032115338241)
  ·
    refine ⟨56015109298826274086503681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74686812398435032115338241 56015109298826274086503681)
    ·
      refine ⟨42011331974119705564877761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56015109298826274086503681 42011331974119705564877761)
      ·
        refine ⟨31508498980589779173658321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42011331974119705564877761 31508498980589779173658321)
        ·
          refine ⟨23631374235442334380243741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31508498980589779173658321 23631374235442334380243741)
          ·
            refine ⟨8861765338290875392591403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23631374235442334380243741 8861765338290875392591403)
            ·
              refine ⟨13292648007436313088887105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8861765338290875392591403 13292648007436313088887105)
              ·
                refine ⟨9969486005577234816665329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13292648007436313088887105 9969486005577234816665329)
                ·
                  refine ⟨7477114504182926112498997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9969486005577234816665329 7477114504182926112498997)
                  ·
                    refine ⟨700979484767149323046781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7477114504182926112498997 700979484767149323046781)
                    ·
                      rfl

theorem cell22_2047729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_2047729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047729 prefixEnd_2047729 := by exact prefixLift 2047729
  have htrace : WordTrace (prefixWord ++ tailWord_2047729) baseStart_2047729 baseEnd_2047729 := by
    simpa [prefixWord, tailWord_2047729, baseEnd_2047729] using wordTrace_append hprefix tailTrace_2047729
  have hstable : (prefixWord ++ tailWord_2047729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047729).length < 2 ^ (prefixWord ++ tailWord_2047729).sum := by decide
  have hdescent : baseEnd_2047729 < baseStart_2047729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047746 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_2047746 : Nat := 118140960795 + 2047746 * 2 ^ 59
def prefixEnd_2047746 : Nat := 4983230072969 + 3 ^ 40 * 2047746 * 2
def baseEnd_2047746 : Nat := 700985304214566945371729

theorem tailTrace_2047746 : CollatzResearch.WordTrace tailWord_2047746 prefixEnd_2047746 700985304214566945371729 := by
  unfold tailWord_2047746
  simp only [CollatzResearch.WordTrace]
  refine ⟨18671858109843361004676773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49791621626248962679138061 18671858109843361004676773)
  ·
    refine ⟨3500973395595630188376895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18671858109843361004676773 3500973395595630188376895)
    ·
      refine ⟨5251460093393445282565343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3500973395595630188376895 5251460093393445282565343)
      ·
        refine ⟨7877190140090167923848015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5251460093393445282565343 7877190140090167923848015)
        ·
          refine ⟨11815785210135251885772023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7877190140090167923848015 11815785210135251885772023)
          ·
            refine ⟨17723677815202877828658035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11815785210135251885772023 17723677815202877828658035)
            ·
              refine ⟨26585516722804316742987053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17723677815202877828658035 26585516722804316742987053)
              ·
                refine ⟨9969568771051618778620145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26585516722804316742987053 9969568771051618778620145)
                ·
                  refine ⟨7477176578288714083965109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9969568771051618778620145 7477176578288714083965109)
                  ·
                    refine ⟨700985304214566945371729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7477176578288714083965109 700985304214566945371729)
                    ·
                      rfl

theorem cell22_2047746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_2047746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047746 prefixEnd_2047746 := by exact prefixLift 2047746
  have htrace : WordTrace (prefixWord ++ tailWord_2047746) baseStart_2047746 baseEnd_2047746 := by
    simpa [prefixWord, tailWord_2047746, baseEnd_2047746] using wordTrace_append hprefix tailTrace_2047746
  have hstable : (prefixWord ++ tailWord_2047746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047746).length < 2 ^ (prefixWord ++ tailWord_2047746).sum := by decide
  have hdescent : baseEnd_2047746 < baseStart_2047746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047748 : List Nat := [2, 3, 2, 2, 1, 3, 3, 1, 5]
def baseStart_2047748 : Nat := 118140960795 + 2047748 * 2 ^ 59
def prefixEnd_2047748 : Nat := 4983230072969 + 3 ^ 40 * 2047748 * 2
def baseEnd_2047748 : Nat := 233661996285146535607241

theorem tailTrace_2047748 : CollatzResearch.WordTrace tailWord_2047748 prefixEnd_2047748 233661996285146535607241 := by
  unfold tailWord_2047748
  simp only [CollatzResearch.WordTrace]
  refine ⟨37343752692683099180139949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49791670256910798906853265 37343752692683099180139949)
  ·
    refine ⟨14003907259756162192552481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37343752692683099180139949 14003907259756162192552481)
    ·
      refine ⟨10502930444817121644414361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14003907259756162192552481 10502930444817121644414361)
      ·
        refine ⟨7877197833612841233310771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10502930444817121644414361 7877197833612841233310771)
        ·
          refine ⟨11815796750419261849966157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7877197833612841233310771 11815796750419261849966157)
          ·
            refine ⟨4430923781407223193737309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11815796750419261849966157 4430923781407223193737309)
            ·
              refine ⟨1661596418027708697651491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4430923781407223193737309 1661596418027708697651491)
              ·
                refine ⟨2492394627041563046477237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1661596418027708697651491 2492394627041563046477237)
                ·
                  refine ⟨233661996285146535607241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2492394627041563046477237 233661996285146535607241)
                  ·
                    rfl

theorem cell22_2047748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_2047748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047748 prefixEnd_2047748 := by exact prefixLift 2047748
  have htrace : WordTrace (prefixWord ++ tailWord_2047748) baseStart_2047748 baseEnd_2047748 := by
    simpa [prefixWord, tailWord_2047748, baseEnd_2047748] using wordTrace_append hprefix tailTrace_2047748
  have hstable : (prefixWord ++ tailWord_2047748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047748).length < 2 ^ (prefixWord ++ tailWord_2047748).sum := by decide
  have hdescent : baseEnd_2047748 < baseStart_2047748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047804 : List Nat := [2, 2, 2, 2, 1, 1, 3, 9]
def baseStart_2047804 : Nat := 118140960795 + 2047804 * 2 ^ 59
def prefixEnd_2047804 : Nat := 4983230072969 + 3 ^ 40 * 2047804 * 2
def baseEnd_2047804 : Nat := 77889462088874903046839

theorem tailTrace_2047804 : CollatzResearch.WordTrace tailWord_2047804 prefixEnd_2047804 77889462088874903046839 := by
  unfold tailWord_2047804
  simp only [CollatzResearch.WordTrace]
  refine ⟨37344773936581659962159233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49793031915442213282878977 37344773936581659962159233)
  ·
    refine ⟨28008580452436244971619425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37344773936581659962159233 28008580452436244971619425)
    ·
      refine ⟨21006435339327183728714569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28008580452436244971619425 21006435339327183728714569)
      ·
        refine ⟨15754826504495387796535927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21006435339327183728714569 15754826504495387796535927)
        ·
          refine ⟨23632239756743081694803891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15754826504495387796535927 23632239756743081694803891)
          ·
            refine ⟨35448359635114622542205837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23632239756743081694803891 35448359635114622542205837)
            ·
              refine ⟨13293134863167983453327189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35448359635114622542205837 13293134863167983453327189)
              ·
                refine ⟨77889462088874903046839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13293134863167983453327189 77889462088874903046839)
                ·
                  rfl

theorem cell22_2047804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 9].length) (baseStart_2047804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047804 prefixEnd_2047804 := by exact prefixLift 2047804
  have htrace : WordTrace (prefixWord ++ tailWord_2047804) baseStart_2047804 baseEnd_2047804 := by
    simpa [prefixWord, tailWord_2047804, baseEnd_2047804] using wordTrace_append hprefix tailTrace_2047804
  have hstable : (prefixWord ++ tailWord_2047804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047804).length < 2 ^ (prefixWord ++ tailWord_2047804).sum := by decide
  have hdescent : baseEnd_2047804 < baseStart_2047804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047849 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 7]
def baseStart_2047849 : Nat := 118140960795 + 2047849 * 2 ^ 59
def prefixEnd_2047849 : Nat := 4983230072969 + 3 ^ 40 * 2047849 * 2
def baseEnd_2047849 : Nat := 233673521073169670015471

theorem tailTrace_2047849 : CollatzResearch.WordTrace tailWord_2047849 prefixEnd_2047849 233673521073169670015471 := by
  unfold tailWord_2047849
  simp only [CollatzResearch.WordTrace]
  refine ⟨74691189158000292609706601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49794126105333528406471067 74691189158000292609706601)
  ·
    refine ⟨56018391868500219457279951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74691189158000292609706601 56018391868500219457279951)
    ·
      refine ⟨84027587802750329185919927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56018391868500219457279951 84027587802750329185919927)
      ·
        refine ⟨126041381704125493778879891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84027587802750329185919927 126041381704125493778879891)
        ·
          refine ⟨189062072556188240668319837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126041381704125493778879891 189062072556188240668319837)
          ·
            refine ⟨70898277208570590250619939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189062072556188240668319837 70898277208570590250619939)
            ·
              refine ⟨106347415812855885375929909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70898277208570590250619939 106347415812855885375929909)
              ·
                refine ⟨9970070232455239253993429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106347415812855885375929909 9970070232455239253993429)
                ·
                  refine ⟨233673521073169670015471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9970070232455239253993429 233673521073169670015471)
                  ·
                    rfl

theorem cell22_2047849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 7].length) (baseStart_2047849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047849 prefixEnd_2047849 := by exact prefixLift 2047849
  have htrace : WordTrace (prefixWord ++ tailWord_2047849) baseStart_2047849 baseEnd_2047849 := by
    simpa [prefixWord, tailWord_2047849, baseEnd_2047849] using wordTrace_append hprefix tailTrace_2047849
  have hstable : (prefixWord ++ tailWord_2047849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047849).length < 2 ^ (prefixWord ++ tailWord_2047849).sum := by decide
  have hdescent : baseEnd_2047849 < baseStart_2047849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047866 : List Nat := [3, 1, 1, 1, 1, 1, 6, 3, 5]
def baseStart_2047866 : Nat := 118140960795 + 2047866 * 2 ^ 59
def prefixEnd_2047866 : Nat := 4983230072969 + 3 ^ 40 * 2047866 * 2
def baseEnd_2047866 : Nat := 233675460888975544123787

theorem tailTrace_2047866 : CollatzResearch.WordTrace tailWord_2047866 prefixEnd_2047866 233675460888975544123787 := by
  unfold tailWord_2047866
  simp only [CollatzResearch.WordTrace]
  refine ⟨18672952299734676128268863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49794539465959136342050301 18672952299734676128268863)
  ·
    refine ⟨28009428449602014192403295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18672952299734676128268863 28009428449602014192403295)
    ·
      refine ⟨42014142674403021288604943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28009428449602014192403295 42014142674403021288604943)
      ·
        refine ⟨63021214011604531932907415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42014142674403021288604943 63021214011604531932907415)
        ·
          refine ⟨94531821017406797899361123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63021214011604531932907415 94531821017406797899361123)
          ·
            refine ⟨141797731526110196849041685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94531821017406797899361123 141797731526110196849041685)
            ·
              refine ⟨6646768665286415477298829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141797731526110196849041685 6646768665286415477298829)
              ·
                refine ⟨2492538249482405803987061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6646768665286415477298829 2492538249482405803987061)
                ·
                  refine ⟨233675460888975544123787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2492538249482405803987061 233675460888975544123787)
                  ·
                    rfl

theorem cell22_2047866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_2047866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047866 prefixEnd_2047866 := by exact prefixLift 2047866
  have htrace : WordTrace (prefixWord ++ tailWord_2047866) baseStart_2047866 baseEnd_2047866 := by
    simpa [prefixWord, tailWord_2047866, baseEnd_2047866] using wordTrace_append hprefix tailTrace_2047866
  have hstable : (prefixWord ++ tailWord_2047866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047866).length < 2 ^ (prefixWord ++ tailWord_2047866).sum := by decide
  have hdescent : baseEnd_2047866 < baseStart_2047866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047870 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 5, 3]
def baseStart_2047870 : Nat := 118140960795 + 2047870 * 2 ^ 59
def prefixEnd_2047870 : Nat := 4983230072969 + 3 ^ 40 * 2047870 * 2
def baseEnd_2047870 : Nat := 701027751948671955271349

theorem tailTrace_2047870 : CollatzResearch.WordTrace tailWord_2047870 prefixEnd_2047870 701027751948671955271349 := by
  unfold tailWord_2047870
  simp only [CollatzResearch.WordTrace]
  refine ⟨9336494386365526649527633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49794636727282808797480709 9336494386365526649527633)
  ·
    refine ⟨7002370789774144987145725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9336494386365526649527633 7002370789774144987145725)
    ·
      refine ⟨2625889046165304370179647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7002370789774144987145725 2625889046165304370179647)
      ·
        refine ⟨3938833569247956555269471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2625889046165304370179647 3938833569247956555269471)
        ·
          refine ⟨5908250353871934832904207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3938833569247956555269471 5908250353871934832904207)
          ·
            refine ⟨8862375530807902249356311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5908250353871934832904207 8862375530807902249356311)
            ·
              refine ⟨13293563296211853374034467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8862375530807902249356311 13293563296211853374034467)
              ·
                refine ⟨19940344944317780061051701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13293563296211853374034467 19940344944317780061051701)
                ·
                  refine ⟨1869407338529791880723597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19940344944317780061051701 1869407338529791880723597)
                  ·
                    refine ⟨701027751948671955271349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1869407338529791880723597 701027751948671955271349)
                    ·
                      rfl

theorem cell22_2047870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_2047870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047870 prefixEnd_2047870 := by exact prefixLift 2047870
  have htrace : WordTrace (prefixWord ++ tailWord_2047870) baseStart_2047870 baseEnd_2047870 := by
    simpa [prefixWord, tailWord_2047870, baseEnd_2047870] using wordTrace_append hprefix tailTrace_2047870
  have hstable : (prefixWord ++ tailWord_2047870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047870).length < 2 ^ (prefixWord ++ tailWord_2047870).sum := by decide
  have hdescent : baseEnd_2047870 < baseStart_2047870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047900 : List Nat := [2, 2, 3, 3, 1, 3, 1, 2, 5]
def baseStart_2047900 : Nat := 118140960795 + 2047900 * 2 ^ 59
def prefixEnd_2047900 : Nat := 4983230072969 + 3 ^ 40 * 2047900 * 2
def baseEnd_2047900 : Nat := 233679340520587292340419

theorem tailTrace_2047900 : CollatzResearch.WordTrace tailWord_2047900 prefixEnd_2047900 233679340520587292340419 := by
  unfold tailWord_2047900
  simp only [CollatzResearch.WordTrace]
  refine ⟨37346524640407764159906577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49795366187210352213208769 37346524640407764159906577)
  ·
    refine ⟨28009893480305823119929933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37346524640407764159906577 28009893480305823119929933)
    ·
      refine ⟨10503710055114683669973725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28009893480305823119929933 10503710055114683669973725)
      ·
        refine ⟨3938891270668006376240147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10503710055114683669973725 3938891270668006376240147)
        ·
          refine ⟨5908336906002009564360221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3938891270668006376240147 5908336906002009564360221)
          ·
            refine ⟨2215626339750753586635083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5908336906002009564360221 2215626339750753586635083)
            ·
              refine ⟨3323439509626130379952625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2215626339750753586635083 3323439509626130379952625)
              ·
                refine ⟨2492579632219597784964469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3323439509626130379952625 2492579632219597784964469)
                ·
                  refine ⟨233679340520587292340419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2492579632219597784964469 233679340520587292340419)
                  ·
                    rfl

theorem cell22_2047900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 5].length) (baseStart_2047900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047900 prefixEnd_2047900 := by exact prefixLift 2047900
  have htrace : WordTrace (prefixWord ++ tailWord_2047900) baseStart_2047900 baseEnd_2047900 := by
    simpa [prefixWord, tailWord_2047900, baseEnd_2047900] using wordTrace_append hprefix tailTrace_2047900
  have hstable : (prefixWord ++ tailWord_2047900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047900).length < 2 ^ (prefixWord ++ tailWord_2047900).sum := by decide
  have hdescent : baseEnd_2047900 < baseStart_2047900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047962 : List Nat := [3, 1, 1, 2, 5, 1, 3, 2, 4]
def baseStart_2047962 : Nat := 118140960795 + 2047962 * 2 ^ 59
def prefixEnd_2047962 : Nat := 4983230072969 + 3 ^ 40 * 2047962 * 2
def baseEnd_2047962 : Nat := 233686415142938127323689

theorem tailTrace_2047962 : CollatzResearch.WordTrace tailWord_2047962 prefixEnd_2047962 233686415142938127323689 := by
  unfold tailWord_2047962
  simp only [CollatzResearch.WordTrace]
  refine ⟨18673827651647728227142535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49796873737727275272380093 18673827651647728227142535)
  ·
    refine ⟨28010741477471592340713803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18673827651647728227142535 28010741477471592340713803)
    ·
      refine ⟨42016112216207388511070705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28010741477471592340713803 42016112216207388511070705)
      ·
        refine ⟨31512084162155541383303029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42016112216207388511070705 31512084162155541383303029)
        ·
          refine ⟨2954257890202082004684659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31512084162155541383303029 2954257890202082004684659)
          ·
            refine ⟨4431386835303123007026989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2954257890202082004684659 4431386835303123007026989)
            ·
              refine ⟨1661770063238671127635121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4431386835303123007026989 1661770063238671127635121)
              ·
                refine ⟨1246327547429003345726341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1661770063238671127635121 1246327547429003345726341)
                ·
                  refine ⟨233686415142938127323689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1246327547429003345726341 233686415142938127323689)
                  ·
                    rfl

theorem cell22_2047962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 4].length) (baseStart_2047962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2047962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2047962 prefixEnd_2047962 := by exact prefixLift 2047962
  have htrace : WordTrace (prefixWord ++ tailWord_2047962) baseStart_2047962 baseEnd_2047962 := by
    simpa [prefixWord, tailWord_2047962, baseEnd_2047962] using wordTrace_append hprefix tailTrace_2047962
  have hstable : (prefixWord ++ tailWord_2047962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047962).length < 2 ^ (prefixWord ++ tailWord_2047962).sum := by decide
  have hdescent : baseEnd_2047962 < baseStart_2047962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048013 : List Nat := [1, 7, 1, 2, 1, 2, 2, 2, 4]
def baseStart_2048013 : Nat := 118140960795 + 2048013 * 2 ^ 59
def prefixEnd_2048013 : Nat := 4983230072969 + 3 ^ 40 * 2048013 * 2
def baseEnd_2048013 : Nat := 233692234590355749648637

theorem tailTrace_2048013 : CollatzResearch.WordTrace tailWord_2048013 prefixEnd_2048013 233692234590355749648637 := by
  unfold tailWord_2048013
  simp only [CollatzResearch.WordTrace]
  refine ⟨74697170729406148618676693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49798113819604099079117795 74697170729406148618676693)
  ·
    refine ⟨1750714938970456608250235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 74697170729406148618676693 1750714938970456608250235)
    ·
      refine ⟨2626072408455684912375353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1750714938970456608250235 2626072408455684912375353)
      ·
        refine ⟨1969554306341763684281515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2626072408455684912375353 1969554306341763684281515)
        ·
          refine ⟨2954331459512645526422273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1969554306341763684281515 2954331459512645526422273)
          ·
            refine ⟨2215748594634484144816705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2954331459512645526422273 2215748594634484144816705)
            ·
              refine ⟨1661811445975863108612529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2215748594634484144816705 1661811445975863108612529)
              ·
                refine ⟨1246358584481897331459397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1661811445975863108612529 1246358584481897331459397)
                ·
                  refine ⟨233692234590355749648637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1246358584481897331459397 233692234590355749648637)
                  ·
                    rfl

theorem cell22_2048013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_2048013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048013 prefixEnd_2048013 := by exact prefixLift 2048013
  have htrace : WordTrace (prefixWord ++ tailWord_2048013) baseStart_2048013 baseEnd_2048013 := by
    simpa [prefixWord, tailWord_2048013, baseEnd_2048013] using wordTrace_append hprefix tailTrace_2048013
  have hstable : (prefixWord ++ tailWord_2048013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048013).length < 2 ^ (prefixWord ++ tailWord_2048013).sum := by decide
  have hdescent : baseEnd_2048013 < baseStart_2048013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048016 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 4, 5]
def baseStart_2048016 : Nat := 118140960795 + 2048016 * 2 ^ 59
def prefixEnd_2048016 : Nat := 4983230072969 + 3 ^ 40 * 2048016 * 2
def baseEnd_2048016 : Nat := 701077730732376241120901

theorem tailTrace_2048016 : CollatzResearch.WordTrace tailWord_2048016 prefixEnd_2048016 701077730732376241120901 := by
  unfold tailWord_2048016
  simp only [CollatzResearch.WordTrace]
  refine ⟨37348640074197640065517951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49798186765596853420690601 37348640074197640065517951)
  ·
    refine ⟨56022960111296460098276927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37348640074197640065517951 56022960111296460098276927)
    ·
      refine ⟨84034440166944690147415391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56022960111296460098276927 84034440166944690147415391)
      ·
        refine ⟨126051660250417035221123087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84034440166944690147415391 126051660250417035221123087)
        ·
          refine ⟨189077490375625552831684631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126051660250417035221123087 189077490375625552831684631)
          ·
            refine ⟨283616235563438329247526947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189077490375625552831684631 283616235563438329247526947)
            ·
              refine ⟨425424353345157493871290421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283616235563438329247526947 425424353345157493871290421)
              ·
                refine ⟨39883533126108515050433477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 425424353345157493871290421 39883533126108515050433477)
                ·
                  refine ⟨7478162461145346571956277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39883533126108515050433477 7478162461145346571956277)
                  ·
                    refine ⟨701077730732376241120901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7478162461145346571956277 701077730732376241120901)
                    ·
                      rfl

theorem cell22_2048016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_2048016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048016 prefixEnd_2048016 := by exact prefixLift 2048016
  have htrace : WordTrace (prefixWord ++ tailWord_2048016) baseStart_2048016 baseEnd_2048016 := by
    simpa [prefixWord, tailWord_2048016, baseEnd_2048016] using wordTrace_append hprefix tailTrace_2048016
  have hstable : (prefixWord ++ tailWord_2048016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048016).length < 2 ^ (prefixWord ++ tailWord_2048016).sum := by decide
  have hdescent : baseEnd_2048016 < baseStart_2048016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048048 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 3, 4]
def baseStart_2048048 : Nat := 118140960795 + 2048048 * 2 ^ 59
def prefixEnd_2048048 : Nat := 4983230072969 + 3 ^ 40 * 2048048 * 2
def baseEnd_2048048 : Nat := 701088684986338824320803

theorem tailTrace_2048048 : CollatzResearch.WordTrace tailWord_2048048 prefixEnd_2048048 701088684986338824320803 := by
  unfold tailWord_2048048
  simp only [CollatzResearch.WordTrace]
  refine ⟨37349223642139674798100399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49798964856186233064133865 37349223642139674798100399)
  ·
    refine ⟨56023835463209512197150599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37349223642139674798100399 56023835463209512197150599)
    ·
      refine ⟨84035753194814268295725899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56023835463209512197150599 84035753194814268295725899)
      ·
        refine ⟨126053629792221402443588849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84035753194814268295725899 126053629792221402443588849)
        ·
          refine ⟨94540222344166051832691637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126053629792221402443588849 94540222344166051832691637)
          ·
            refine ⟨8863145844765567359314841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94540222344166051832691637 8863145844765567359314841)
            ·
              refine ⟨6647359383574175519486131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8863145844765567359314841 6647359383574175519486131)
              ·
                refine ⟨9971039075361263279229197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6647359383574175519486131 9971039075361263279229197)
                ·
                  refine ⟨3739139653260473729710949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9971039075361263279229197 3739139653260473729710949)
                  ·
                    refine ⟨701088684986338824320803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3739139653260473729710949 701088684986338824320803)
                    ·
                      rfl

theorem cell22_2048048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 3, 4].length) (baseStart_2048048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048048 prefixEnd_2048048 := by exact prefixLift 2048048
  have htrace : WordTrace (prefixWord ++ tailWord_2048048) baseStart_2048048 baseEnd_2048048 := by
    simpa [prefixWord, tailWord_2048048, baseEnd_2048048] using wordTrace_append hprefix tailTrace_2048048
  have hstable : (prefixWord ++ tailWord_2048048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048048).length < 2 ^ (prefixWord ++ tailWord_2048048).sum := by decide
  have hdescent : baseEnd_2048048 < baseStart_2048048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048108 : List Nat := [2, 2, 1, 1, 3, 4, 1, 8]
def baseStart_2048108 : Nat := 118140960795 + 2048108 * 2 ^ 59
def prefixEnd_2048108 : Nat := 4983230072969 + 3 ^ 40 * 2048108 * 2
def baseEnd_2048108 : Nat := 77901024912502074202291

theorem tailTrace_2048108 : CollatzResearch.WordTrace tailWord_2048108 prefixEnd_2048108 77901024912502074202291 := by
  unfold tailWord_2048108
  simp only [CollatzResearch.WordTrace]
  refine ⟨37350317832030989921692489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49800423776041319895589985 37350317832030989921692489)
  ·
    refine ⟨28012738374023242441269367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37350317832030989921692489 28012738374023242441269367)
    ·
      refine ⟨42019107561034863661904051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28012738374023242441269367 42019107561034863661904051)
      ·
        refine ⟨63028661341552295492856077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42019107561034863661904051 63028661341552295492856077)
        ·
          refine ⟨23635748003082110809821029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63028661341552295492856077 23635748003082110809821029)
          ·
            refine ⟨4431702750577895776841443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23635748003082110809821029 4431702750577895776841443)
            ·
              refine ⟨6647554125866843665262165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4431702750577895776841443 6647554125866843665262165)
              ·
                refine ⟨77901024912502074202291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6647554125866843665262165 77901024912502074202291)
                ·
                  rfl

theorem cell22_2048108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 8].length) (baseStart_2048108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048108 prefixEnd_2048108 := by exact prefixLift 2048108
  have htrace : WordTrace (prefixWord ++ tailWord_2048108) baseStart_2048108 baseEnd_2048108 := by
    simpa [prefixWord, tailWord_2048108, baseEnd_2048108] using wordTrace_append hprefix tailTrace_2048108
  have hstable : (prefixWord ++ tailWord_2048108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048108).length < 2 ^ (prefixWord ++ tailWord_2048108).sum := by decide
  have hdescent : baseEnd_2048108 < baseStart_2048108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048110 : List Nat := [4, 1, 2, 2, 1, 1, 2, 3, 2, 4]
def baseStart_2048110 : Nat := 118140960795 + 2048110 * 2 ^ 59
def prefixEnd_2048110 : Nat := 4983230072969 + 3 ^ 40 * 2048110 * 2
def baseEnd_2048110 : Nat := 701109908853391329270613

theorem tailTrace_2048110 : CollatzResearch.WordTrace tailWord_2048110 prefixEnd_2048110 701109908853391329270613 := by
  unfold tailWord_2048110
  simp only [CollatzResearch.WordTrace]
  refine ⟨9337588576256841773119723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49800472406703156123305189 9337588576256841773119723)
  ·
    refine ⟨14006382864385262659679585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9337588576256841773119723 14006382864385262659679585)
    ·
      refine ⟨10504787148288946994759689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14006382864385262659679585 10504787148288946994759689)
      ·
        refine ⟨7878590361216710246069767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10504787148288946994759689 7878590361216710246069767)
        ·
          refine ⟨11817885541825065369104651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7878590361216710246069767 11817885541825065369104651)
          ·
            refine ⟨17726828312737598053656977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11817885541825065369104651 17726828312737598053656977)
            ·
              refine ⟨13295121234553198540242733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17726828312737598053656977 13295121234553198540242733)
              ·
                refine ⟨4985670462957449452591025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13295121234553198540242733 4985670462957449452591025)
                ·
                  refine ⟨3739252847218087089443269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4985670462957449452591025 3739252847218087089443269)
                  ·
                    refine ⟨701109908853391329270613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3739252847218087089443269 701109908853391329270613)
                    ·
                      rfl

theorem cell22_2048110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_2048110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048110 prefixEnd_2048110 := by exact prefixLift 2048110
  have htrace : WordTrace (prefixWord ++ tailWord_2048110) baseStart_2048110 baseEnd_2048110 := by
    simpa [prefixWord, tailWord_2048110, baseEnd_2048110] using wordTrace_append hprefix tailTrace_2048110
  have hstable : (prefixWord ++ tailWord_2048110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048110).length < 2 ^ (prefixWord ++ tailWord_2048110).sum := by decide
  have hdescent : baseEnd_2048110 < baseStart_2048110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048150 : List Nat := [5, 3, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_2048150 : Nat := 118140960795 + 2048150 * 2 ^ 59
def prefixEnd_2048150 : Nat := 4983230072969 + 3 ^ 40 * 2048150 * 2
def baseEnd_2048150 : Nat := 701123601670844558270491

theorem tailTrace_2048150 : CollatzResearch.WordTrace tailWord_2048150 prefixEnd_2048150 701123601670844558270491 := by
  unfold tailWord_2048150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4668885470619363813525869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49801445019939880677609269 4668885470619363813525869)
  ·
    refine ⟨1750832051482261430072201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4668885470619363813525869 1750832051482261430072201)
    ·
      refine ⟨1313124038611696072554151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1750832051482261430072201 1313124038611696072554151)
      ·
        refine ⟨1969686057917544108831227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1313124038611696072554151 1969686057917544108831227)
        ·
          refine ⟨2954529086876316163246841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1969686057917544108831227 2954529086876316163246841)
          ·
            refine ⟨2215896815157237122435131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2954529086876316163246841 2215896815157237122435131)
            ·
              refine ⟨3323845222735855683652697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2215896815157237122435131 3323845222735855683652697)
              ·
                refine ⟨2492883917051891762739523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3323845222735855683652697 2492883917051891762739523)
                ·
                  refine ⟨3739325875577837644109285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2492883917051891762739523 3739325875577837644109285)
                  ·
                    refine ⟨701123601670844558270491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3739325875577837644109285 701123601670844558270491)
                    ·
                      rfl

theorem cell22_2048150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_2048150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048150 prefixEnd_2048150 := by exact prefixLift 2048150
  have htrace : WordTrace (prefixWord ++ tailWord_2048150) baseStart_2048150 baseEnd_2048150 := by
    simpa [prefixWord, tailWord_2048150, baseEnd_2048150] using wordTrace_append hprefix tailTrace_2048150
  have hstable : (prefixWord ++ tailWord_2048150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048150).length < 2 ^ (prefixWord ++ tailWord_2048150).sum := by decide
  have hdescent : baseEnd_2048150 < baseStart_2048150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048232 : List Nat := [2, 1, 4, 1, 2, 2, 1, 5, 4]
def baseStart_2048232 : Nat := 118140960795 + 2048232 * 2 ^ 59
def prefixEnd_2048232 : Nat := 4983230072969 + 3 ^ 40 * 2048232 * 2
def baseEnd_2048232 : Nat := 233717223982207892573413

theorem tailTrace_2048232 : CollatzResearch.WordTrace tailWord_2048232 prefixEnd_2048232 233717223982207892573413 := by
  unfold tailWord_2048232
  simp only [CollatzResearch.WordTrace]
  refine ⟨37352579157806374510449475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49803438877075166013932633 37352579157806374510449475)
  ·
    refine ⟨56028868736709561765674213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37352579157806374510449475 56028868736709561765674213)
    ·
      refine ⟨10505412888133042831063915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56028868736709561765674213 10505412888133042831063915)
      ·
        refine ⟨15758119332199564246595873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10505412888133042831063915 15758119332199564246595873)
        ·
          refine ⟨11818589499149673184946905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15758119332199564246595873 11818589499149673184946905)
          ·
            refine ⟨8863942124362254888710179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11818589499149673184946905 8863942124362254888710179)
            ·
              refine ⟨13295913186543382333065269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8863942124362254888710179 13295913186543382333065269)
              ·
                refine ⟨1246491861238442093724869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13295913186543382333065269 1246491861238442093724869)
                ·
                  refine ⟨233717223982207892573413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1246491861238442093724869 233717223982207892573413)
                  ·
                    rfl

theorem cell22_2048232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 4].length) (baseStart_2048232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048232 prefixEnd_2048232 := by exact prefixLift 2048232
  have htrace : WordTrace (prefixWord ++ tailWord_2048232) baseStart_2048232 baseEnd_2048232 := by
    simpa [prefixWord, tailWord_2048232, baseEnd_2048232] using wordTrace_append hprefix tailTrace_2048232
  have hstable : (prefixWord ++ tailWord_2048232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048232).length < 2 ^ (prefixWord ++ tailWord_2048232).sum := by decide
  have hdescent : baseEnd_2048232 < baseStart_2048232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048243 : List Nat := [1, 1, 1, 2, 2, 4, 11]
def baseStart_2048243 : Nat := 118140960795 + 2048243 * 2 ^ 59
def prefixEnd_2048243 : Nat := 4983230072969 + 3 ^ 40 * 2048243 * 2
def baseEnd_2048243 : Nat := 25968719906349011692415

theorem tailTrace_2048243 : CollatzResearch.WordTrace tailWord_2048243 prefixEnd_2048243 25968719906349011692415 := by
  unfold tailWord_2048243
  simp only [CollatzResearch.WordTrace]
  refine ⟨74705559518572897899549383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49803706345715265266366255 74705559518572897899549383)
  ·
    refine ⟨112058339277859346849324075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74705559518572897899549383 112058339277859346849324075)
    ·
      refine ⟨168087508916789020273986113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112058339277859346849324075 168087508916789020273986113)
      ·
        refine ⟨126065631687591765205489585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168087508916789020273986113 126065631687591765205489585)
        ·
          refine ⟨94549223765693823904117189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126065631687591765205489585 94549223765693823904117189)
          ·
            refine ⟨17727979456067591982021973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94549223765693823904117189 17727979456067591982021973)
            ·
              refine ⟨25968719906349011692415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17727979456067591982021973 25968719906349011692415)
              ·
                rfl

theorem cell22_2048243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 11].length) (baseStart_2048243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048243 prefixEnd_2048243 := by exact prefixLift 2048243
  have htrace : WordTrace (prefixWord ++ tailWord_2048243) baseStart_2048243 baseEnd_2048243 := by
    simpa [prefixWord, tailWord_2048243, baseEnd_2048243] using wordTrace_append hprefix tailTrace_2048243
  have hstable : (prefixWord ++ tailWord_2048243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048243).length < 2 ^ (prefixWord ++ tailWord_2048243).sum := by decide
  have hdescent : baseEnd_2048243 < baseStart_2048243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048416 : List Nat := [2, 1, 1, 4, 1, 5, 1, 2, 2, 3]
def baseStart_2048416 : Nat := 118140960795 + 2048416 * 2 ^ 59
def prefixEnd_2048416 : Nat := 4983230072969 + 3 ^ 40 * 2048416 * 2
def baseEnd_2048416 : Nat := 701214658906908531119675

theorem tailTrace_2048416 : CollatzResearch.WordTrace tailWord_2048416 prefixEnd_2048416 701214658906908531119675 := by
  unfold tailWord_2048416
  simp only [CollatzResearch.WordTrace]
  refine ⟨37355934673473074222798551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49807912897964098963731401 37355934673473074222798551)
  ·
    refine ⟨56033902010209611334197827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37355934673473074222798551 56033902010209611334197827)
    ·
      refine ⟨84050853015314417001296741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56033902010209611334197827 84050853015314417001296741)
      ·
        refine ⟨15759534940371453187743139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84050853015314417001296741 15759534940371453187743139)
        ·
          refine ⟨23639302410557179781614709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15759534940371453187743139 23639302410557179781614709)
          ·
            refine ⟨2216184600989735604526379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23639302410557179781614709 2216184600989735604526379)
            ·
              refine ⟨3324276901484603406789569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2216184600989735604526379 3324276901484603406789569)
              ·
                refine ⟨2493207676113452555092177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3324276901484603406789569 2493207676113452555092177)
                ·
                  refine ⟨1869905757085089416319133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2493207676113452555092177 1869905757085089416319133)
                  ·
                    refine ⟨701214658906908531119675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1869905757085089416319133 701214658906908531119675)
                    ·
                      rfl

theorem cell22_2048416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 2, 3].length) (baseStart_2048416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048416 prefixEnd_2048416 := by exact prefixLift 2048416
  have htrace : WordTrace (prefixWord ++ tailWord_2048416) baseStart_2048416 baseEnd_2048416 := by
    simpa [prefixWord, tailWord_2048416, baseEnd_2048416] using wordTrace_append hprefix tailTrace_2048416
  have hstable : (prefixWord ++ tailWord_2048416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048416).length < 2 ^ (prefixWord ++ tailWord_2048416).sum := by decide
  have hdescent : baseEnd_2048416 < baseStart_2048416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048425 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 1, 8]
def baseStart_2048425 : Nat := 118140960795 + 2048425 * 2 ^ 59
def prefixEnd_2048425 : Nat := 4983230072969 + 3 ^ 40 * 2048425 * 2
def baseEnd_2048425 : Nat := 701217739790835507644647

theorem tailTrace_2048425 : CollatzResearch.WordTrace tailWord_2048425 prefixEnd_2048425 701217739790835507644647 := by
  unfold tailWord_2048425
  simp only [CollatzResearch.WordTrace]
  refine ⟨74712197603913542982674729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49808131735942361988449819 74712197603913542982674729)
  ·
    refine ⟨56034148202935157237006047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74712197603913542982674729 56034148202935157237006047)
    ·
      refine ⟨84051222304402735855509071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56034148202935157237006047 84051222304402735855509071)
      ·
        refine ⟨126076833456604103783263607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84051222304402735855509071 126076833456604103783263607)
        ·
          refine ⟨189115250184906155674895411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126076833456604103783263607 189115250184906155674895411)
          ·
            refine ⟨283672875277359233512343117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189115250184906155674895411 283672875277359233512343117)
            ·
              refine ⟨106377328229009712567128669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283672875277359233512343117 106377328229009712567128669)
              ·
                refine ⟨39891498085878642212673251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106377328229009712567128669 39891498085878642212673251)
                ·
                  refine ⟨59837247128817963319009877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39891498085878642212673251 59837247128817963319009877)
                  ·
                    refine ⟨701217739790835507644647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59837247128817963319009877 701217739790835507644647)
                    ·
                      rfl

theorem cell22_2048425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_2048425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048425 prefixEnd_2048425 := by exact prefixLift 2048425
  have htrace : WordTrace (prefixWord ++ tailWord_2048425) baseStart_2048425 baseEnd_2048425 := by
    simpa [prefixWord, tailWord_2048425, baseEnd_2048425] using wordTrace_append hprefix tailTrace_2048425
  have hstable : (prefixWord ++ tailWord_2048425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048425).length < 2 ^ (prefixWord ++ tailWord_2048425).sum := by decide
  have hdescent : baseEnd_2048425 < baseStart_2048425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048517 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 3, 5]
def baseStart_2048517 : Nat := 118140960795 + 2048517 * 2 ^ 59
def prefixEnd_2048517 : Nat := 4983230072969 + 3 ^ 40 * 2048517 * 2
def baseEnd_2048517 : Nat := 701249233270977934344365

theorem tailTrace_2048517 : CollatzResearch.WordTrace tailWord_2048517 prefixEnd_2048517 701249233270977934344365 := by
  unfold tailWord_2048517
  simp only [CollatzResearch.WordTrace]
  refine ⟨74715553119580242695023805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49810368746386828463349203 74715553119580242695023805)
  ·
    refine ⟨28018332419842591010633927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74715553119580242695023805 28018332419842591010633927)
    ·
      refine ⟨42027498629763886515950891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28018332419842591010633927 42027498629763886515950891)
      ·
        refine ⟨63041247944645829773926337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42027498629763886515950891 63041247944645829773926337)
        ·
          refine ⟨47280935958484372330444753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63041247944645829773926337 47280935958484372330444753)
          ·
            refine ⟨35460701968863279247833565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47280935958484372330444753 35460701968863279247833565)
            ·
              refine ⟨13297763238323729717937587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35460701968863279247833565 13297763238323729717937587)
              ·
                refine ⟨19946644857485594576906381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13297763238323729717937587 19946644857485594576906381)
                ·
                  refine ⟨7479991821557097966339893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19946644857485594576906381 7479991821557097966339893)
                  ·
                    refine ⟨701249233270977934344365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7479991821557097966339893 701249233270977934344365)
                    ·
                      rfl

theorem cell22_2048517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_2048517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048517 prefixEnd_2048517 := by exact prefixLift 2048517
  have htrace : WordTrace (prefixWord ++ tailWord_2048517) baseStart_2048517 baseEnd_2048517 := by
    simpa [prefixWord, tailWord_2048517, baseEnd_2048517] using wordTrace_append hprefix tailTrace_2048517
  have hstable : (prefixWord ++ tailWord_2048517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048517).length < 2 ^ (prefixWord ++ tailWord_2048517).sum := by decide
  have hdescent : baseEnd_2048517 < baseStart_2048517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048536 : List Nat := [2, 1, 2, 3, 3, 2, 1, 4, 4]
def baseStart_2048536 : Nat := 118140960795 + 2048536 * 2 ^ 59
def prefixEnd_2048536 : Nat := 4983230072969 + 3 ^ 40 * 2048536 * 2
def baseEnd_2048536 : Nat := 233751912453089406039769

theorem tailTrace_2048536 : CollatzResearch.WordTrace tailWord_2048536 prefixEnd_2048536 233751912453089406039769 := by
  unfold tailWord_2048536
  simp only [CollatzResearch.WordTrace]
  refine ⟨37358123053255704469982731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49810830737674272626643641 37358123053255704469982731)
  ·
    refine ⟨56037184579883556704974097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37358123053255704469982731 56037184579883556704974097)
    ·
      refine ⟨42027888434912667528730573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56037184579883556704974097 42027888434912667528730573)
      ·
        refine ⟨15760458163092250323273965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42027888434912667528730573 15760458163092250323273965)
        ·
          refine ⟨5910171811159593871227737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15760458163092250323273965 5910171811159593871227737)
          ·
            refine ⟨4432628858369695403420803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5910171811159593871227737 4432628858369695403420803)
            ·
              refine ⟨6648943287554543105131205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4432628858369695403420803 6648943287554543105131205)
              ·
                refine ⟨1246676866416476832212101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6648943287554543105131205 1246676866416476832212101)
                ·
                  refine ⟨233751912453089406039769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1246676866416476832212101 233751912453089406039769)
                  ·
                    rfl

theorem cell22_2048536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 4].length) (baseStart_2048536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048536 prefixEnd_2048536 := by exact prefixLift 2048536
  have htrace : WordTrace (prefixWord ++ tailWord_2048536) baseStart_2048536 baseEnd_2048536 := by
    simpa [prefixWord, tailWord_2048536, baseEnd_2048536] using wordTrace_append hprefix tailTrace_2048536
  have hstable : (prefixWord ++ tailWord_2048536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048536).length < 2 ^ (prefixWord ++ tailWord_2048536).sum := by decide
  have hdescent : baseEnd_2048536 < baseStart_2048536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048566 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_2048566 : Nat := 118140960795 + 2048566 * 2 ^ 59
def prefixEnd_2048566 : Nat := 4983230072969 + 3 ^ 40 * 2048566 * 2
def baseEnd_2048566 : Nat := 701266006972358139869215

theorem tailTrace_2048566 : CollatzResearch.WordTrace tailWord_2048566 prefixEnd_2048566 701266006972358139869215 := by
  unfold tailWord_2048566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4669833768525170253972347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49811560197601816042371701 4669833768525170253972347)
  ·
    refine ⟨7004750652787755380958521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4669833768525170253972347 7004750652787755380958521)
    ·
      refine ⟨5253562989590816535718891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7004750652787755380958521 5253562989590816535718891)
      ·
        refine ⟨7880344484386224803578337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5253562989590816535718891 7880344484386224803578337)
        ·
          refine ⟨5910258363289668602683753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7880344484386224803578337 5910258363289668602683753)
          ·
            refine ⟨4432693772467251452012815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5910258363289668602683753 4432693772467251452012815)
            ·
              refine ⟨6649040658700877178019223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4432693772467251452012815 6649040658700877178019223)
              ·
                refine ⟨9973560988051315767028835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6649040658700877178019223 9973560988051315767028835)
                ·
                  refine ⟨14960341482076973650543253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9973560988051315767028835 14960341482076973650543253)
                  ·
                    refine ⟨701266006972358139869215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14960341482076973650543253 701266006972358139869215)
                    ·
                      rfl

theorem cell22_2048566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_2048566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048566 prefixEnd_2048566 := by exact prefixLift 2048566
  have htrace : WordTrace (prefixWord ++ tailWord_2048566) baseStart_2048566 baseEnd_2048566 := by
    simpa [prefixWord, tailWord_2048566, baseEnd_2048566] using wordTrace_append hprefix tailTrace_2048566
  have hstable : (prefixWord ++ tailWord_2048566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048566).length < 2 ^ (prefixWord ++ tailWord_2048566).sum := by decide
  have hdescent : baseEnd_2048566 < baseStart_2048566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048596 : List Nat := [2, 4, 1, 1, 1, 3, 1, 3, 3, 3]
def baseStart_2048596 : Nat := 118140960795 + 2048596 * 2 ^ 59
def prefixEnd_2048596 : Nat := 4983230072969 + 3 ^ 40 * 2048596 * 2
def baseEnd_2048596 : Nat := 701276276585448061619123

theorem tailTrace_2048596 : CollatzResearch.WordTrace tailWord_2048596 prefixEnd_2048596 701276276585448061619123 := by
  unfold tailWord_2048596
  simp only [CollatzResearch.WordTrace]
  refine ⟨37359217243147019593574821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49812289657529359458099761 37359217243147019593574821)
  ·
    refine ⟨7004853233090066173795279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37359217243147019593574821 7004853233090066173795279)
    ·
      refine ⟨10507279849635099260692919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7004853233090066173795279 10507279849635099260692919)
      ·
        refine ⟨15760919774452648891039379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10507279849635099260692919 15760919774452648891039379)
        ·
          refine ⟨23641379661678973336559069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15760919774452648891039379 23641379661678973336559069)
          ·
            refine ⟨8865517373129615001209651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23641379661678973336559069 8865517373129615001209651)
            ·
              refine ⟨13298276059694422501814477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8865517373129615001209651 13298276059694422501814477)
              ·
                refine ⟨4986853522385408438180429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13298276059694422501814477 4986853522385408438180429)
                ·
                  refine ⟨1870070070894528164317661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4986853522385408438180429 1870070070894528164317661)
                  ·
                    refine ⟨701276276585448061619123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1870070070894528164317661 701276276585448061619123)
                    ·
                      rfl

theorem cell22_2048596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_2048596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048596 prefixEnd_2048596 := by exact prefixLift 2048596
  have htrace : WordTrace (prefixWord ++ tailWord_2048596) baseStart_2048596 baseEnd_2048596 := by
    simpa [prefixWord, tailWord_2048596, baseEnd_2048596] using wordTrace_append hprefix tailTrace_2048596
  have hstable : (prefixWord ++ tailWord_2048596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048596).length < 2 ^ (prefixWord ++ tailWord_2048596).sum := by decide
  have hdescent : baseEnd_2048596 < baseStart_2048596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048660 : List Nat := [2, 4, 2, 2, 1, 3, 2, 1, 5]
def baseStart_2048660 : Nat := 118140960795 + 2048660 * 2 ^ 59
def prefixEnd_2048660 : Nat := 4983230072969 + 3 ^ 40 * 2048660 * 2
def baseEnd_2048660 : Nat := 233766061697791076006309

theorem tailTrace_2048660 : CollatzResearch.WordTrace tailWord_2048660 prefixEnd_2048660 233766061697791076006309 := by
  unfold tailWord_2048660
  simp only [CollatzResearch.WordTrace]
  refine ⟨37360384379031089058739717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49813845838708118744986289 37360384379031089058739717)
  ·
    refine ⟨7005072071068329198513697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37360384379031089058739717 7005072071068329198513697)
    ·
      refine ⟨5253804053301246898885273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7005072071068329198513697 5253804053301246898885273)
      ·
        refine ⟨3940353039975935174163955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5253804053301246898885273 3940353039975935174163955)
        ·
          refine ⟨5910529559963902761245933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3940353039975935174163955 5910529559963902761245933)
          ·
            refine ⟨2216448584986463535467225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5910529559963902761245933 2216448584986463535467225)
            ·
              refine ⟨1662336438739847651600419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2216448584986463535467225 1662336438739847651600419)
              ·
                refine ⟨2493504658109771477400629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1662336438739847651600419 2493504658109771477400629)
                ·
                  refine ⟨233766061697791076006309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2493504658109771477400629 233766061697791076006309)
                  ·
                    rfl

theorem cell22_2048660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_2048660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048660 prefixEnd_2048660 := by exact prefixLift 2048660
  have htrace : WordTrace (prefixWord ++ tailWord_2048660) baseStart_2048660 baseEnd_2048660 := by
    simpa [prefixWord, tailWord_2048660, baseEnd_2048660] using wordTrace_append hprefix tailTrace_2048660
  have hstable : (prefixWord ++ tailWord_2048660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048660).length < 2 ^ (prefixWord ++ tailWord_2048660).sum := by decide
  have hdescent : baseEnd_2048660 < baseStart_2048660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048701 : List Nat := [1, 4, 1, 2, 1, 3, 2, 2, 2, 4]
def baseStart_2048701 : Nat := 118140960795 + 2048701 * 2 ^ 59
def prefixEnd_2048701 : Nat := 4983230072969 + 3 ^ 40 * 2048701 * 2
def baseEnd_2048701 : Nat := 701312220231262787743801

theorem tailTrace_2048701 : CollatzResearch.WordTrace tailWord_2048701 prefixEnd_2048701 701312220231262787743801 := by
  unfold tailWord_2048701
  simp only [CollatzResearch.WordTrace]
  refine ⟨74722264150913642119721957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49814842767275761413147971 74722264150913642119721957)
  ·
    refine ⟨14010424528296307897447867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74722264150913642119721957 14010424528296307897447867)
    ·
      refine ⟨21015636792444461846171801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14010424528296307897447867 21015636792444461846171801)
      ·
        refine ⟨15761727594333346384628851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21015636792444461846171801 15761727594333346384628851)
        ·
          refine ⟨23642591391500019576943277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15761727594333346384628851 23642591391500019576943277)
          ·
            refine ⟨8865971771812507341353729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23642591391500019576943277 8865971771812507341353729)
            ·
              refine ⟨6649478828859380506015297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8865971771812507341353729 6649478828859380506015297)
              ·
                refine ⟨4987109121644535379511473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6649478828859380506015297 4987109121644535379511473)
                ·
                  refine ⟨3740331841233401534633605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4987109121644535379511473 3740331841233401534633605)
                  ·
                    refine ⟨701312220231262787743801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3740331841233401534633605 701312220231262787743801)
                    ·
                      rfl

theorem cell22_2048701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_2048701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048701 prefixEnd_2048701 := by exact prefixLift 2048701
  have htrace : WordTrace (prefixWord ++ tailWord_2048701) baseStart_2048701 baseEnd_2048701 := by
    simpa [prefixWord, tailWord_2048701, baseEnd_2048701] using wordTrace_append hprefix tailTrace_2048701
  have hstable : (prefixWord ++ tailWord_2048701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048701).length < 2 ^ (prefixWord ++ tailWord_2048701).sum := by decide
  have hdescent : baseEnd_2048701 < baseStart_2048701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048703 : List Nat := [1, 1, 2, 2, 2, 5, 2, 2, 2, 3]
def baseStart_2048703 : Nat := 118140960795 + 2048703 * 2 ^ 59
def prefixEnd_2048703 : Nat := 4983230072969 + 3 ^ 40 * 2048703 * 2
def baseEnd_2048703 : Nat := 701312904872135449193795

theorem tailTrace_2048703 : CollatzResearch.WordTrace tailWord_2048703 prefixEnd_2048703 701312904872135449193795 := by
  unfold tailWord_2048703
  simp only [CollatzResearch.WordTrace]
  refine ⟨74722337096906396461294763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49814891397937597640863175 74722337096906396461294763)
  ·
    refine ⟨112083505645359594691942145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74722337096906396461294763 112083505645359594691942145)
    ·
      refine ⟨84062629234019696018956609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112083505645359594691942145 84062629234019696018956609)
      ·
        refine ⟨63046971925514772014217457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84062629234019696018956609 63046971925514772014217457)
        ·
          refine ⟨47285228944136079010663093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63046971925514772014217457 47285228944136079010663093)
          ·
            refine ⟨4432990213512757407249665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47285228944136079010663093 4432990213512757407249665)
            ·
              refine ⟨3324742660134568055437249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4432990213512757407249665 3324742660134568055437249)
              ·
                refine ⟨2493556995100926041577937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3324742660134568055437249 2493556995100926041577937)
                ·
                  refine ⟨1870167746325694531183453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2493556995100926041577937 1870167746325694531183453)
                  ·
                    refine ⟨701312904872135449193795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1870167746325694531183453 701312904872135449193795)
                    ·
                      rfl

theorem cell22_2048703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 3].length) (baseStart_2048703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048703 prefixEnd_2048703 := by exact prefixLift 2048703
  have htrace : WordTrace (prefixWord ++ tailWord_2048703) baseStart_2048703 baseEnd_2048703 := by
    simpa [prefixWord, tailWord_2048703, baseEnd_2048703] using wordTrace_append hprefix tailTrace_2048703
  have hstable : (prefixWord ++ tailWord_2048703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048703).length < 2 ^ (prefixWord ++ tailWord_2048703).sum := by decide
  have hdescent : baseEnd_2048703 < baseStart_2048703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048716 : List Nat := [2, 2, 1, 5, 1, 1, 3, 7]
def baseStart_2048716 : Nat := 118140960795 + 2048716 * 2 ^ 59
def prefixEnd_2048716 : Nat := 4983230072969 + 3 ^ 40 * 2048716 * 2
def baseEnd_2048716 : Nat := 77924150559756416513195

theorem tailTrace_2048716 : CollatzResearch.WordTrace tailWord_2048716 prefixEnd_2048716 77924150559756416513195 := by
  unfold tailWord_2048716
  simp only [CollatzResearch.WordTrace]
  refine ⟨37361405622929649840759001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49815207497239533121012001 37361405622929649840759001)
  ·
    refine ⟨28021054217197237380569251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37361405622929649840759001 28021054217197237380569251)
    ·
      refine ⟨42031581325795856070853877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28021054217197237380569251 42031581325795856070853877)
      ·
        refine ⟨3940460749293361506642551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42031581325795856070853877 3940460749293361506642551)
        ·
          refine ⟨5910691123940042259963827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3940460749293361506642551 5910691123940042259963827)
          ·
            refine ⟨8866036685910063389945741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5910691123940042259963827 8866036685910063389945741)
            ·
              refine ⟨3324763757216273771229653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8866036685910063389945741 3324763757216273771229653)
              ·
                refine ⟨77924150559756416513195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3324763757216273771229653 77924150559756416513195)
                ·
                  rfl

theorem cell22_2048716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 7].length) (baseStart_2048716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048716 prefixEnd_2048716 := by exact prefixLift 2048716
  have htrace : WordTrace (prefixWord ++ tailWord_2048716) baseStart_2048716 baseEnd_2048716 := by
    simpa [prefixWord, tailWord_2048716, baseEnd_2048716] using wordTrace_append hprefix tailTrace_2048716
  have hstable : (prefixWord ++ tailWord_2048716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048716).length < 2 ^ (prefixWord ++ tailWord_2048716).sum := by decide
  have hdescent : baseEnd_2048716 < baseStart_2048716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048729 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 2, 6]
def baseStart_2048729 : Nat := 118140960795 + 2048729 * 2 ^ 59
def prefixEnd_2048729 : Nat := 4983230072969 + 3 ^ 40 * 2048729 * 2
def baseEnd_2048729 : Nat := 701321805203480048043715

theorem tailTrace_2048729 : CollatzResearch.WordTrace tailWord_2048729 prefixEnd_2048729 701321805203480048043715 := by
  unfold tailWord_2048729
  simp only [CollatzResearch.WordTrace]
  refine ⟨74723285394812202901741241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49815523596541468601160827 74723285394812202901741241)
  ·
    refine ⟨56042464046109152176305931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74723285394812202901741241 56042464046109152176305931)
    ·
      refine ⟨84063696069163728264458897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56042464046109152176305931 84063696069163728264458897)
      ·
        refine ⟨63047772051872796198344173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84063696069163728264458897 63047772051872796198344173)
        ·
          refine ⟨23642914519452298574379065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63047772051872796198344173 23642914519452298574379065)
          ·
            refine ⟨17732185889589223930784299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23642914519452298574379065 17732185889589223930784299)
            ·
              refine ⟨26598278834383835896176449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17732185889589223930784299 26598278834383835896176449)
              ·
                refine ⟨19948709125787876922132337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26598278834383835896176449 19948709125787876922132337)
                ·
                  refine ⟨14961531844340907691599253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19948709125787876922132337 14961531844340907691599253)
                  ·
                    refine ⟨701321805203480048043715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14961531844340907691599253 701321805203480048043715)
                    ·
                      rfl

theorem cell22_2048729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_2048729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048729 prefixEnd_2048729 := by exact prefixLift 2048729
  have htrace : WordTrace (prefixWord ++ tailWord_2048729) baseStart_2048729 baseEnd_2048729 := by
    simpa [prefixWord, tailWord_2048729, baseEnd_2048729] using wordTrace_append hprefix tailTrace_2048729
  have hstable : (prefixWord ++ tailWord_2048729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048729).length < 2 ^ (prefixWord ++ tailWord_2048729).sum := by decide
  have hdescent : baseEnd_2048729 < baseStart_2048729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048776 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 2, 5]
def baseStart_2048776 : Nat := 118140960795 + 2048776 * 2 ^ 59
def prefixEnd_2048776 : Nat := 4983230072969 + 3 ^ 40 * 2048776 * 2
def baseEnd_2048776 : Nat := 701337894263987592118571

theorem tailTrace_2048776 : CollatzResearch.WordTrace tailWord_2048776 prefixEnd_2048776 701337894263987592118571 := by
  unfold tailWord_2048776
  simp only [CollatzResearch.WordTrace]
  refine ⟨37362499812820964964351091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49816666417094619952468121 37362499812820964964351091)
  ·
    refine ⟨56043749719231447446526637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37362499812820964964351091 56043749719231447446526637)
    ·
      refine ⟨21016406144711792792447489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56043749719231447446526637 21016406144711792792447489)
      ·
        refine ⟨15762304608533844594335617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21016406144711792792447489 15762304608533844594335617)
        ·
          refine ⟨11821728456400383445751713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15762304608533844594335617 11821728456400383445751713)
          ·
            refine ⟨8866296342300287584313785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11821728456400383445751713 8866296342300287584313785)
            ·
              refine ⟨6649722256725215688235339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8866296342300287584313785 6649722256725215688235339)
              ·
                refine ⟨9974583385087823532353009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6649722256725215688235339 9974583385087823532353009)
                ·
                  refine ⟨7480937538815867649264757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9974583385087823532353009 7480937538815867649264757)
                  ·
                    refine ⟨701337894263987592118571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7480937538815867649264757 701337894263987592118571)
                    ·
                      rfl

theorem cell22_2048776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_2048776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048776 prefixEnd_2048776 := by exact prefixLift 2048776
  have htrace : WordTrace (prefixWord ++ tailWord_2048776) baseStart_2048776 baseEnd_2048776 := by
    simpa [prefixWord, tailWord_2048776, baseEnd_2048776] using wordTrace_append hprefix tailTrace_2048776
  have hstable : (prefixWord ++ tailWord_2048776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048776).length < 2 ^ (prefixWord ++ tailWord_2048776).sum := by decide
  have hdescent : baseEnd_2048776 < baseStart_2048776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048778 : List Nat := [3, 1, 2, 2, 1, 2, 5, 1, 5]
def baseStart_2048778 : Nat := 118140960795 + 2048778 * 2 ^ 59
def prefixEnd_2048778 : Nat := 4983230072969 + 3 ^ 40 * 2048778 * 2
def baseEnd_2048778 : Nat := 233779526301620084522855

theorem tailTrace_2048778 : CollatzResearch.WordTrace tailWord_2048778 prefixEnd_2048778 233779526301620084522855 := by
  unfold tailWord_2048778
  simp only [CollatzResearch.WordTrace]
  refine ⟨18681268142908671067568747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49816715047756456180183325 18681268142908671067568747)
  ·
    refine ⟨28021902214363006601353121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18681268142908671067568747 28021902214363006601353121)
    ·
      refine ⟨21016426660772254951014841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28021902214363006601353121 21016426660772254951014841)
      ·
        refine ⟨15762319995579191213261131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21016426660772254951014841 15762319995579191213261131)
        ·
          refine ⟨23643479993368786819891697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15762319995579191213261131 23643479993368786819891697)
          ·
            refine ⟨17732609995026590114918773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23643479993368786819891697 17732609995026590114918773)
            ·
              refine ⟨1662432187033742823273635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17732609995026590114918773 1662432187033742823273635)
              ·
                refine ⟨2493648280550614234910453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1662432187033742823273635 2493648280550614234910453)
                ·
                  refine ⟨233779526301620084522855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2493648280550614234910453 233779526301620084522855)
                  ·
                    rfl

theorem cell22_2048778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 5].length) (baseStart_2048778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048778 prefixEnd_2048778 := by exact prefixLift 2048778
  have htrace : WordTrace (prefixWord ++ tailWord_2048778) baseStart_2048778 baseEnd_2048778 := by
    simpa [prefixWord, tailWord_2048778, baseEnd_2048778] using wordTrace_append hprefix tailTrace_2048778
  have hstable : (prefixWord ++ tailWord_2048778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048778).length < 2 ^ (prefixWord ++ tailWord_2048778).sum := by decide
  have hdescent : baseEnd_2048778 < baseStart_2048778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048808 : List Nat := [2, 1, 5, 1, 1, 1, 1, 5, 1, 4]
def baseStart_2048808 : Nat := 118140960795 + 2048808 * 2 ^ 59
def prefixEnd_2048808 : Nat := 4983230072969 + 3 ^ 40 * 2048808 * 2
def baseEnd_2048808 : Nat := 701348848517950175318473

theorem tailTrace_2048808 : CollatzResearch.WordTrace tailWord_2048808 prefixEnd_2048808 701348848517950175318473 := by
  unfold tailWord_2048808
  simp only [CollatzResearch.WordTrace]
  refine ⟨37363083380762999696933539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49817444507683999595911385 37363083380762999696933539)
  ·
    refine ⟨56044625071144499545400309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37363083380762999696933539 56044625071144499545400309)
    ·
      refine ⟨5254183600419796832381279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56044625071144499545400309 5254183600419796832381279)
      ·
        refine ⟨7881275400629695248571919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5254183600419796832381279 7881275400629695248571919)
        ·
          refine ⟨11821913100944542872857879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7881275400629695248571919 11821913100944542872857879)
          ·
            refine ⟨17732869651416814309286819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11821913100944542872857879 17732869651416814309286819)
            ·
              refine ⟨26599304477125221463930229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17732869651416814309286819 26599304477125221463930229)
              ·
                refine ⟨2493684794730489512243459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26599304477125221463930229 2493684794730489512243459)
                ·
                  refine ⟨3740527192095734268365189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2493684794730489512243459 3740527192095734268365189)
                  ·
                    refine ⟨701348848517950175318473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3740527192095734268365189 701348848517950175318473)
                    ·
                      rfl

theorem cell22_2048808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_2048808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048808 prefixEnd_2048808 := by exact prefixLift 2048808
  have htrace : WordTrace (prefixWord ++ tailWord_2048808) baseStart_2048808 baseEnd_2048808 := by
    simpa [prefixWord, tailWord_2048808, baseEnd_2048808] using wordTrace_append hprefix tailTrace_2048808
  have hstable : (prefixWord ++ tailWord_2048808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048808).length < 2 ^ (prefixWord ++ tailWord_2048808).sum := by decide
  have hdescent : baseEnd_2048808 < baseStart_2048808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048853 : List Nat := [1, 3, 2, 2, 2, 1, 4, 1, 2, 4]
def baseStart_2048853 : Nat := 118140960795 + 2048853 * 2 ^ 59
def prefixEnd_2048853 : Nat := 4983230072969 + 3 ^ 40 * 2048853 * 2
def baseEnd_2048853 : Nat := 701364252937585057943335

theorem tailTrace_2048853 : CollatzResearch.WordTrace tailWord_2048853 prefixEnd_2048853 701364252937585057943335 := by
  unfold tailWord_2048853
  simp only [CollatzResearch.WordTrace]
  refine ⟨74727808046362972079255213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49818538697575314719503475 74727808046362972079255213)
  ·
    refine ⟨28022928017386114529720705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74727808046362972079255213 28022928017386114529720705)
    ·
      refine ⟨21017196013039585897290529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28022928017386114529720705 21017196013039585897290529)
      ·
        refine ⟨15762897009779689422967897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21017196013039585897290529 15762897009779689422967897)
        ·
          refine ⟨11822172757334767067225923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15762897009779689422967897 11822172757334767067225923)
          ·
            refine ⟨17733259136002150600838885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11822172757334767067225923 17733259136002150600838885)
            ·
              refine ⟨3324986088000403237657291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17733259136002150600838885 3324986088000403237657291)
              ·
                refine ⟨4987479132000604856485937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3324986088000403237657291 4987479132000604856485937)
                ·
                  refine ⟨3740609349000453642364453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4987479132000604856485937 3740609349000453642364453)
                  ·
                    refine ⟨701364252937585057943335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3740609349000453642364453 701364252937585057943335)
                    ·
                      rfl

theorem cell22_2048853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_2048853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048853 prefixEnd_2048853 := by exact prefixLift 2048853
  have htrace : WordTrace (prefixWord ++ tailWord_2048853) baseStart_2048853 baseEnd_2048853 := by
    simpa [prefixWord, tailWord_2048853, baseEnd_2048853] using wordTrace_append hprefix tailTrace_2048853
  have hstable : (prefixWord ++ tailWord_2048853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048853).length < 2 ^ (prefixWord ++ tailWord_2048853).sum := by decide
  have hdescent : baseEnd_2048853 < baseStart_2048853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048881 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 2, 6]
def baseStart_2048881 : Nat := 118140960795 + 2048881 * 2 ^ 59
def prefixEnd_2048881 : Nat := 4983230072969 + 3 ^ 40 * 2048881 * 2
def baseEnd_2048881 : Nat := 701373837909802318243249

theorem tailTrace_2048881 : CollatzResearch.WordTrace tailWord_2048881 prefixEnd_2048881 701373837909802318243249 := by
  unfold tailWord_2048881
  simp only [CollatzResearch.WordTrace]
  refine ⟨74728829290261532861274497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49819219526841021907516331 74728829290261532861274497)
  ·
    refine ⟨56046621967696149645955873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74728829290261532861274497 56046621967696149645955873)
    ·
      refine ⟨42034966475772112234466905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56046621967696149645955873 42034966475772112234466905)
      ·
        refine ⟨31526224856829084175850179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42034966475772112234466905 31526224856829084175850179)
        ·
          refine ⟨47289337285243626263775269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31526224856829084175850179 47289337285243626263775269)
          ·
            refine ⟨8866750740983179924457863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47289337285243626263775269 8866750740983179924457863)
            ·
              refine ⟨13300126111474769886686795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8866750740983179924457863 13300126111474769886686795)
              ·
                refine ⟨19950189167212154830030193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13300126111474769886686795 19950189167212154830030193)
                ·
                  refine ⟨14962641875409116122522645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19950189167212154830030193 14962641875409116122522645)
                  ·
                    refine ⟨701373837909802318243249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14962641875409116122522645 701373837909802318243249)
                    ·
                      rfl

theorem cell22_2048881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_2048881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048881 prefixEnd_2048881 := by exact prefixLift 2048881
  have htrace : WordTrace (prefixWord ++ tailWord_2048881) baseStart_2048881 baseEnd_2048881 := by
    simpa [prefixWord, tailWord_2048881, baseEnd_2048881] using wordTrace_append hprefix tailTrace_2048881
  have hstable : (prefixWord ++ tailWord_2048881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048881).length < 2 ^ (prefixWord ++ tailWord_2048881).sum := by decide
  have hdescent : baseEnd_2048881 < baseStart_2048881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048917 : List Nat := [1, 3, 2, 1, 1, 5, 2, 3, 1, 3]
def baseStart_2048917 : Nat := 118140960795 + 2048917 * 2 ^ 59
def prefixEnd_2048917 : Nat := 4983230072969 + 3 ^ 40 * 2048917 * 2
def baseEnd_2048917 : Nat := 701386161445510224343139

theorem tailTrace_2048917 : CollatzResearch.WordTrace tailWord_2048917 prefixEnd_2048917 701386161445510224343139 := by
  unfold tailWord_2048917
  simp only [CollatzResearch.WordTrace]
  refine ⟨74730142318131111009585005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49820094878754074006390003 74730142318131111009585005)
  ·
    refine ⟨28023803369299166628594377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74730142318131111009585005 28023803369299166628594377)
    ·
      refine ⟨21017852526974374971445783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28023803369299166628594377 21017852526974374971445783)
      ·
        refine ⟨31526778790461562457168675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21017852526974374971445783 31526778790461562457168675)
        ·
          refine ⟨47290168185692343685753013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31526778790461562457168675 47290168185692343685753013)
          ·
            refine ⟨4433453267408657220539345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47290168185692343685753013 4433453267408657220539345)
            ·
              refine ⟨3325089950556492915404509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4433453267408657220539345 3325089950556492915404509)
              ·
                refine ⟨1246908731458684843276691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3325089950556492915404509 1246908731458684843276691)
                ·
                  refine ⟨1870363097188027264915037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1246908731458684843276691 1870363097188027264915037)
                  ·
                    refine ⟨701386161445510224343139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1870363097188027264915037 701386161445510224343139)
                    ·
                      rfl

theorem cell22_2048917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_2048917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048917 prefixEnd_2048917 := by exact prefixLift 2048917
  have htrace : WordTrace (prefixWord ++ tailWord_2048917) baseStart_2048917 baseEnd_2048917 := by
    simpa [prefixWord, tailWord_2048917, baseEnd_2048917] using wordTrace_append hprefix tailTrace_2048917
  have hstable : (prefixWord ++ tailWord_2048917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048917).length < 2 ^ (prefixWord ++ tailWord_2048917).sum := by decide
  have hdescent : baseEnd_2048917 < baseStart_2048917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048930 : List Nat := [3, 3, 1, 2, 2, 1, 3, 2, 5]
def baseStart_2048930 : Nat := 118140960795 + 2048930 * 2 ^ 59
def prefixEnd_2048930 : Nat := 4983230072969 + 3 ^ 40 * 2048930 * 2
def baseEnd_2048930 : Nat := 233796870537060841256033

theorem tailTrace_2048930 : CollatzResearch.WordTrace tailWord_2048930 prefixEnd_2048930 233796870537060841256033 := by
  unfold tailWord_2048930
  simp only [CollatzResearch.WordTrace]
  refine ⟨18682654116771003557452061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49820410978056009486538829 18682654116771003557452061)
  ·
    refine ⟨7005995293789126334044523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18682654116771003557452061 7005995293789126334044523)
    ·
      refine ⟨10508992940683689501066785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7005995293789126334044523 10508992940683689501066785)
      ·
        refine ⟨7881744705512767125800089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10508992940683689501066785 7881744705512767125800089)
        ·
          refine ⟨5911308529134575344350067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7881744705512767125800089 5911308529134575344350067)
          ·
            refine ⟨8866962793701863016525101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5911308529134575344350067 8866962793701863016525101)
            ·
              refine ⟨3325111047638198631196913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8866962793701863016525101 3325111047638198631196913)
              ·
                refine ⟨2493833285728648973397685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3325111047638198631196913 2493833285728648973397685)
                ·
                  refine ⟨233796870537060841256033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2493833285728648973397685 233796870537060841256033)
                  ·
                    rfl

theorem cell22_2048930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_2048930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048930 prefixEnd_2048930 := by exact prefixLift 2048930
  have htrace : WordTrace (prefixWord ++ tailWord_2048930) baseStart_2048930 baseEnd_2048930 := by
    simpa [prefixWord, tailWord_2048930, baseEnd_2048930] using wordTrace_append hprefix tailTrace_2048930
  have hstable : (prefixWord ++ tailWord_2048930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048930).length < 2 ^ (prefixWord ++ tailWord_2048930).sum := by decide
  have hdescent : baseEnd_2048930 < baseStart_2048930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048958 : List Nat := [4, 2, 1, 1, 1, 2, 1, 4, 6]
def baseStart_2048958 : Nat := 118140960795 + 2048958 * 2 ^ 59
def prefixEnd_2048958 : Nat := 4983230072969 + 3 ^ 40 * 2048958 * 2
def baseEnd_2048958 : Nat := 233800065527799928022671

theorem tailTrace_2048958 : CollatzResearch.WordTrace tailWord_2048958 prefixEnd_2048958 233800065527799928022671 := by
  unfold tailWord_2048958
  simp only [CollatzResearch.WordTrace]
  refine ⟨9341454713872821876478441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49821091807321716674551685 9341454713872821876478441)
  ·
    refine ⟨7006091035404616407358831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9341454713872821876478441 7006091035404616407358831)
    ·
      refine ⟨10509136553106924611038247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7006091035404616407358831 10509136553106924611038247)
      ·
        refine ⟨15763704829660386916557371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10509136553106924611038247 15763704829660386916557371)
        ·
          refine ⟨23645557244490580374836057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15763704829660386916557371 23645557244490580374836057)
          ·
            refine ⟨17734167933367935281127043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23645557244490580374836057 17734167933367935281127043)
            ·
              refine ⟨26601251900051902921690565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17734167933367935281127043 26601251900051902921690565)
              ·
                refine ⟨4987734731259731797816981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26601251900051902921690565 4987734731259731797816981)
                ·
                  refine ⟨233800065527799928022671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4987734731259731797816981 233800065527799928022671)
                  ·
                    rfl

theorem cell22_2048958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_2048958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048958 prefixEnd_2048958 := by exact prefixLift 2048958
  have htrace : WordTrace (prefixWord ++ tailWord_2048958) baseStart_2048958 baseEnd_2048958 := by
    simpa [prefixWord, tailWord_2048958, baseEnd_2048958] using wordTrace_append hprefix tailTrace_2048958
  have hstable : (prefixWord ++ tailWord_2048958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048958).length < 2 ^ (prefixWord ++ tailWord_2048958).sum := by decide
  have hdescent : baseEnd_2048958 < baseStart_2048958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048960 : List Nat := [2, 1, 1, 2, 3, 4, 2, 2, 1, 4]
def baseStart_2048960 : Nat := 118140960795 + 2048960 * 2 ^ 59
def prefixEnd_2048960 : Nat := 4983230072969 + 3 ^ 40 * 2048960 * 2
def baseEnd_2048960 : Nat := 701400881224272445518007

theorem tailTrace_2048960 : CollatzResearch.WordTrace tailWord_2048960 prefixEnd_2048960 701400881224272445518007 := by
  unfold tailWord_2048960
  simp only [CollatzResearch.WordTrace]
  refine ⟨37365855328487664676700167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49821140437983552902266889 37365855328487664676700167)
  ·
    refine ⟨56048782992731497015050251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37365855328487664676700167 56048782992731497015050251)
    ·
      refine ⟨84073174489097245522575377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56048782992731497015050251 84073174489097245522575377)
      ·
        refine ⟨63054880866822934141931533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84073174489097245522575377 63054880866822934141931533)
        ·
          refine ⟨23645580325058600303224325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63054880866822934141931533 23645580325058600303224325)
          ·
            refine ⟨4433546310948487556854561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23645580325058600303224325 4433546310948487556854561)
            ·
              refine ⟨3325159733211365667640921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4433546310948487556854561 3325159733211365667640921)
              ·
                refine ⟨2493869799908524250730691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3325159733211365667640921 2493869799908524250730691)
                ·
                  refine ⟨3740804699862786376096037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2493869799908524250730691 3740804699862786376096037)
                  ·
                    refine ⟨701400881224272445518007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3740804699862786376096037 701400881224272445518007)
                    ·
                      rfl

theorem cell22_2048960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 1, 4].length) (baseStart_2048960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048960 prefixEnd_2048960 := by exact prefixLift 2048960
  have htrace : WordTrace (prefixWord ++ tailWord_2048960) baseStart_2048960 baseEnd_2048960 := by
    simpa [prefixWord, tailWord_2048960, baseEnd_2048960] using wordTrace_append hprefix tailTrace_2048960
  have hstable : (prefixWord ++ tailWord_2048960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048960).length < 2 ^ (prefixWord ++ tailWord_2048960).sum := by decide
  have hdescent : baseEnd_2048960 < baseStart_2048960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048975 : List Nat := [1, 1, 2, 1, 1, 6, 3, 3, 4]
def baseStart_2048975 : Nat := 118140960795 + 2048975 * 2 ^ 59
def prefixEnd_2048975 : Nat := 4983230072969 + 3 ^ 40 * 2048975 * 2
def baseEnd_2048975 : Nat := 233802005343605802130987

theorem tailTrace_2048975 : CollatzResearch.WordTrace tailWord_2048975 prefixEnd_2048975 233802005343605802130987 := by
  unfold tailWord_2048975
  simp only [CollatzResearch.WordTrace]
  refine ⟨74732257751920986915196379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49821505167947324610130919 74732257751920986915196379)
  ·
    refine ⟨112098386627881480372794569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74732257751920986915196379 112098386627881480372794569)
    ·
      refine ⟨84073789970911110279595927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112098386627881480372794569 84073789970911110279595927)
      ·
        refine ⟨126110684956366665419393891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84073789970911110279595927 126110684956366665419393891)
        ·
          refine ⟨189166027434549998129090837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126110684956366665419393891 189166027434549998129090837)
          ·
            refine ⟨8867157535994531162301133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 189166027434549998129090837 8867157535994531162301133)
            ·
              refine ⟨3325184075997949185862925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8867157535994531162301133 3325184075997949185862925)
              ·
                refine ⟨1246944028499230944698597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3325184075997949185862925 1246944028499230944698597)
                ·
                  refine ⟨233802005343605802130987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1246944028499230944698597 233802005343605802130987)
                  ·
                    rfl

theorem cell22_2048975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 4].length) (baseStart_2048975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2048975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2048975 prefixEnd_2048975 := by exact prefixLift 2048975
  have htrace : WordTrace (prefixWord ++ tailWord_2048975) baseStart_2048975 baseEnd_2048975 := by
    simpa [prefixWord, tailWord_2048975, baseEnd_2048975] using wordTrace_append hprefix tailTrace_2048975
  have hstable : (prefixWord ++ tailWord_2048975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048975).length < 2 ^ (prefixWord ++ tailWord_2048975).sum := by decide
  have hdescent : baseEnd_2048975 < baseStart_2048975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049007 : List Nat := [1, 1, 2, 1, 4, 3, 4, 1, 2, 3]
def baseStart_2049007 : Nat := 118140960795 + 2049007 * 2 ^ 59
def prefixEnd_2049007 : Nat := 4983230072969 + 3 ^ 40 * 2049007 * 2
def baseEnd_2049007 : Nat := 701416970284779989592863

theorem tailTrace_2049007 : CollatzResearch.WordTrace tailWord_2049007 prefixEnd_2049007 701416970284779989592863 := by
  unfold tailWord_2049007
  simp only [CollatzResearch.WordTrace]
  refine ⟨74733424887805056380361275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49822283258536704253574183 74733424887805056380361275)
  ·
    refine ⟨112100137331707584570541913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74733424887805056380361275 112100137331707584570541913)
    ·
      refine ⟨84075102998780688427906435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112100137331707584570541913 84075102998780688427906435)
      ·
        refine ⟨126112654498171032641859653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84075102998780688427906435 126112654498171032641859653)
        ·
          refine ⟨23646122718407068620348685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126112654498171032641859653 23646122718407068620348685)
          ·
            refine ⟨8867296019402650732630757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23646122718407068620348685 8867296019402650732630757)
            ·
              refine ⟨1662618003637997012368267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8867296019402650732630757 1662618003637997012368267)
              ·
                refine ⟨2493927005456995518552401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1662618003637997012368267 2493927005456995518552401)
                ·
                  refine ⟨1870445254092746638914301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2493927005456995518552401 1870445254092746638914301)
                  ·
                    refine ⟨701416970284779989592863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1870445254092746638914301 701416970284779989592863)
                    ·
                      rfl

theorem cell22_2049007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 2, 3].length) (baseStart_2049007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049007 prefixEnd_2049007 := by exact prefixLift 2049007
  have htrace : WordTrace (prefixWord ++ tailWord_2049007) baseStart_2049007 baseEnd_2049007 := by
    simpa [prefixWord, tailWord_2049007, baseEnd_2049007] using wordTrace_append hprefix tailTrace_2049007
  have hstable : (prefixWord ++ tailWord_2049007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049007).length < 2 ^ (prefixWord ++ tailWord_2049007).sum := by decide
  have hdescent : baseEnd_2049007 < baseStart_2049007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049086 : List Nat := [4, 2, 1, 3, 1, 2, 2, 3, 1, 3]
def baseStart_2049086 : Nat := 118140960795 + 2049086 * 2 ^ 59
def prefixEnd_2049086 : Nat := 4983230072969 + 3 ^ 40 * 2049086 * 2
def baseEnd_2049086 : Nat := 701444013599250116867621

theorem tailTrace_2049086 : CollatzResearch.WordTrace tailWord_2049086 prefixEnd_2049086 701444013599250116867621 := by
  unfold tailWord_2049086
  simp only [CollatzResearch.WordTrace]
  refine ⟨9342038281814856609060889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49824204169679235248324741 9342038281814856609060889)
  ·
    refine ⟨7006528711361142456795667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9342038281814856609060889 7006528711361142456795667)
    ·
      refine ⟨10509793067041713685193501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7006528711361142456795667 10509793067041713685193501)
      ·
        refine ⟨3941172400140642631947563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10509793067041713685193501 3941172400140642631947563)
        ·
          refine ⟨5911758600210963947921345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3941172400140642631947563 5911758600210963947921345)
          ·
            refine ⟨4433818950158222960941009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5911758600210963947921345 4433818950158222960941009)
            ·
              refine ⟨3325364212618667220705757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4433818950158222960941009 3325364212618667220705757)
              ·
                refine ⟨1247011579732000207764659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3325364212618667220705757 1247011579732000207764659)
                ·
                  refine ⟨1870517369598000311646989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1247011579732000207764659 1870517369598000311646989)
                  ·
                    refine ⟨701444013599250116867621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1870517369598000311646989 701444013599250116867621)
                    ·
                      rfl

theorem cell22_2049086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_2049086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049086 prefixEnd_2049086 := by exact prefixLift 2049086
  have htrace : WordTrace (prefixWord ++ tailWord_2049086) baseStart_2049086 baseEnd_2049086 := by
    simpa [prefixWord, tailWord_2049086, baseEnd_2049086] using wordTrace_append hprefix tailTrace_2049086
  have hstable : (prefixWord ++ tailWord_2049086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049086).length < 2 ^ (prefixWord ++ tailWord_2049086).sum := by decide
  have hdescent : baseEnd_2049086 < baseStart_2049086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049142 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 6, 3]
def baseStart_2049142 : Nat := 118140960795 + 2049142 * 2 ^ 59
def prefixEnd_2049142 : Nat := 4983230072969 + 3 ^ 40 * 2049142 * 2
def baseEnd_2049142 : Nat := 701463183543684637467449

theorem tailTrace_2049142 : CollatzResearch.WordTrace tailWord_2049142 prefixEnd_2049142 701463183543684637467449 := by
  unfold tailWord_2049142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4671146796394748402282855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49825565828210649624350453 4671146796394748402282855)
  ·
    refine ⟨7006720194592122603424283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4671146796394748402282855 7006720194592122603424283)
    ·
      refine ⟨10510080291888183905136425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7006720194592122603424283 10510080291888183905136425)
      ·
        refine ⟨7882560218916137928852319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10510080291888183905136425 7882560218916137928852319)
        ·
          refine ⟨11823840328374206893278479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7882560218916137928852319 11823840328374206893278479)
          ·
            refine ⟨17735760492561310339917719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11823840328374206893278479 17735760492561310339917719)
            ·
              refine ⟨26603640738841965509876579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17735760492561310339917719 26603640738841965509876579)
              ·
                refine ⟨39905461108262948264814869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26603640738841965509876579 39905461108262948264814869)
                ·
                  refine ⟨1870568489449825699913197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39905461108262948264814869 1870568489449825699913197)
                  ·
                    refine ⟨701463183543684637467449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1870568489449825699913197 701463183543684637467449)
                    ·
                      rfl

theorem cell22_2049142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_2049142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049142 prefixEnd_2049142 := by exact prefixLift 2049142
  have htrace : WordTrace (prefixWord ++ tailWord_2049142) baseStart_2049142 baseEnd_2049142 := by
    simpa [prefixWord, tailWord_2049142, baseEnd_2049142] using wordTrace_append hprefix tailTrace_2049142
  have hstable : (prefixWord ++ tailWord_2049142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049142).length < 2 ^ (prefixWord ++ tailWord_2049142).sum := by decide
  have hdescent : baseEnd_2049142 < baseStart_2049142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049157 : List Nat := [1, 3, 1, 1, 6, 1, 1, 2, 2, 4]
def baseStart_2049157 : Nat := 118140960795 + 2049157 * 2 ^ 59
def prefixEnd_2049157 : Nat := 4983230072969 + 3 ^ 40 * 2049157 * 2
def baseEnd_2049157 : Nat := 701468318350229598342403

theorem tailTrace_2049157 : CollatzResearch.WordTrace tailWord_2049157 prefixEnd_2049157 701468318350229598342403 := by
  unfold tailWord_2049157
  simp only [CollatzResearch.WordTrace]
  refine ⟨74738895837261631998321725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49825930558174421332214483 74738895837261631998321725)
  ·
    refine ⟨28027085938973111999370647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74738895837261631998321725 28027085938973111999370647)
    ·
      refine ⟨42040628908459667999055971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28027085938973111999370647 42040628908459667999055971)
      ·
        refine ⟨63060943362689501998583957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42040628908459667999055971 63060943362689501998583957)
        ·
          refine ⟨2955981720126070406183623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63060943362689501998583957 2955981720126070406183623)
          ·
            refine ⟨4433972580189105609275435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2955981720126070406183623 4433972580189105609275435)
            ·
              refine ⟨6650958870283658413913153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4433972580189105609275435 6650958870283658413913153)
              ·
                refine ⟨4988219152712743810434865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6650958870283658413913153 4988219152712743810434865)
                ·
                  refine ⟨3741164364534557857826149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4988219152712743810434865 3741164364534557857826149)
                  ·
                    refine ⟨701468318350229598342403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3741164364534557857826149 701468318350229598342403)
                    ·
                      rfl

theorem cell22_2049157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_2049157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049157 prefixEnd_2049157 := by exact prefixLift 2049157
  have htrace : WordTrace (prefixWord ++ tailWord_2049157) baseStart_2049157 baseEnd_2049157 := by
    simpa [prefixWord, tailWord_2049157, baseEnd_2049157] using wordTrace_append hprefix tailTrace_2049157
  have hstable : (prefixWord ++ tailWord_2049157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049157).length < 2 ^ (prefixWord ++ tailWord_2049157).sum := by decide
  have hdescent : baseEnd_2049157 < baseStart_2049157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049176 : List Nat := [2, 1, 2, 4, 2, 3, 2, 1, 2, 3]
def baseStart_2049176 : Nat := 118140960795 + 2049176 * 2 ^ 59
def prefixEnd_2049176 : Nat := 4983230072969 + 3 ^ 40 * 2049176 * 2
def baseEnd_2049176 : Nat := 701474822438519882117345

theorem tailTrace_2049176 : CollatzResearch.WordTrace tailWord_2049176 prefixEnd_2049176 701474822438519882117345 := by
  unfold tailWord_2049176
  simp only [CollatzResearch.WordTrace]
  refine ⟨37369794412096399121631691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49826392549461865495508921 37369794412096399121631691)
  ·
    refine ⟨56054691618144598682447537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37369794412096399121631691 56054691618144598682447537)
    ·
      refine ⟨42041018713608449011835653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56054691618144598682447537 42041018713608449011835653)
      ·
        refine ⟨7882691008801584189719185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42041018713608449011835653 7882691008801584189719185)
        ·
          refine ⟨5912018256601188142289389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7882691008801584189719185 5912018256601188142289389)
          ·
            refine ⟨2217006846225445553358521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5912018256601188142289389 2217006846225445553358521)
            ·
              refine ⟨1662755134669084165018891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2217006846225445553358521 1662755134669084165018891)
              ·
                refine ⟨2494132702003626247528337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1662755134669084165018891 2494132702003626247528337)
                ·
                  refine ⟨1870599526502719685646253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2494132702003626247528337 1870599526502719685646253)
                  ·
                    refine ⟨701474822438519882117345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1870599526502719685646253 701474822438519882117345)
                    ·
                      rfl

theorem cell22_2049176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 2, 3].length) (baseStart_2049176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049176 prefixEnd_2049176 := by exact prefixLift 2049176
  have htrace : WordTrace (prefixWord ++ tailWord_2049176) baseStart_2049176 baseEnd_2049176 := by
    simpa [prefixWord, tailWord_2049176, baseEnd_2049176] using wordTrace_append hprefix tailTrace_2049176
  have hstable : (prefixWord ++ tailWord_2049176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049176).length < 2 ^ (prefixWord ++ tailWord_2049176).sum := by decide
  have hdescent : baseEnd_2049176 < baseStart_2049176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049290 : List Nat := [3, 1, 2, 2, 1, 1, 1, 11]
def baseStart_2049290 : Nat := 118140960795 + 2049290 * 2 ^ 59
def prefixEnd_2049290 : Nat := 4983230072969 + 3 ^ 40 * 2049290 * 2
def baseEnd_2049290 : Nat := 77945982996473509418555

theorem tailTrace_2049290 : CollatzResearch.WordTrace tailWord_2049290 prefixEnd_2049290 77945982996473509418555 := by
  unfold tailWord_2049290
  simp only [CollatzResearch.WordTrace]
  refine ⟨18685936686444948928228331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49829164497186530475275549 18685936686444948928228331)
  ·
    refine ⟨28028905029667423392342497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18685936686444948928228331 28028905029667423392342497)
    ·
      refine ⟨21021678772250567544256873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28028905029667423392342497 21021678772250567544256873)
      ·
        refine ⟨15766259079187925658192655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21021678772250567544256873 15766259079187925658192655)
        ·
          refine ⟨23649388618781888487288983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15766259079187925658192655 23649388618781888487288983)
          ·
            refine ⟨35474082928172832730933475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23649388618781888487288983 35474082928172832730933475)
            ·
              refine ⟨53211124392259249096400213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35474082928172832730933475 53211124392259249096400213)
              ·
                refine ⟨77945982996473509418555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 53211124392259249096400213 77945982996473509418555)
                ·
                  rfl

theorem cell22_2049290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 11].length) (baseStart_2049290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049290 prefixEnd_2049290 := by exact prefixLift 2049290
  have htrace : WordTrace (prefixWord ++ tailWord_2049290) baseStart_2049290 baseEnd_2049290 := by
    simpa [prefixWord, tailWord_2049290, baseEnd_2049290] using wordTrace_append hprefix tailTrace_2049290
  have hstable : (prefixWord ++ tailWord_2049290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049290).length < 2 ^ (prefixWord ++ tailWord_2049290).sum := by decide
  have hdescent : baseEnd_2049290 < baseStart_2049290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049294 : List Nat := [4, 1, 1, 2, 1, 5, 1, 1, 1, 5]
def baseStart_2049294 : Nat := 118140960795 + 2049294 * 2 ^ 59
def prefixEnd_2049294 : Nat := 4983230072969 + 3 ^ 40 * 2049294 * 2
def baseEnd_2049294 : Nat := 701515216250006907666983

theorem tailTrace_2049294 : CollatzResearch.WordTrace tailWord_2049294 prefixEnd_2049294 701515216250006907666983 := by
  unfold tailWord_2049294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9342986579720663049507367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49829261758510202930705957 9342986579720663049507367)
  ·
    refine ⟨14014479869580994574261051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9342986579720663049507367 14014479869580994574261051)
    ·
      refine ⟨21021719804371491861391577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14014479869580994574261051 21021719804371491861391577)
      ·
        refine ⟨15766289853278618896043683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21021719804371491861391577 15766289853278618896043683)
        ·
          refine ⟨23649434779917928344065525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15766289853278618896043683 23649434779917928344065525)
          ·
            refine ⟨2217134510617305782256143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23649434779917928344065525 2217134510617305782256143)
            ·
              refine ⟨3325701765925958673384215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2217134510617305782256143 3325701765925958673384215)
              ·
                refine ⟨4988552648888938010076323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3325701765925958673384215 4988552648888938010076323)
                ·
                  refine ⟨7482828973333407015114485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4988552648888938010076323 7482828973333407015114485)
                  ·
                    refine ⟨701515216250006907666983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7482828973333407015114485 701515216250006907666983)
                    ·
                      rfl

theorem cell22_2049294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_2049294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049294 prefixEnd_2049294 := by exact prefixLift 2049294
  have htrace : WordTrace (prefixWord ++ tailWord_2049294) baseStart_2049294 baseEnd_2049294 := by
    simpa [prefixWord, tailWord_2049294, baseEnd_2049294] using wordTrace_append hprefix tailTrace_2049294
  have hstable : (prefixWord ++ tailWord_2049294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049294).length < 2 ^ (prefixWord ++ tailWord_2049294).sum := by decide
  have hdescent : baseEnd_2049294 < baseStart_2049294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049298 : List Nat := [3, 2, 4, 2, 1, 1, 2, 2, 1, 4]
def baseStart_2049298 : Nat := 118140960795 + 2049298 * 2 ^ 59
def prefixEnd_2049298 : Nat := 4983230072969 + 3 ^ 40 * 2049298 * 2
def baseEnd_2049298 : Nat := 701516585531752230566971

theorem tailTrace_2049298 : CollatzResearch.WordTrace tailWord_2049298 prefixEnd_2049298 701516585531752230566971 := by
  unfold tailWord_2049298
  simp only [CollatzResearch.WordTrace]
  refine ⟨18686009632437703269801137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49829359019833875386136365 18686009632437703269801137)
  ·
    refine ⟨14014507224328277452350853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18686009632437703269801137 14014507224328277452350853)
    ·
      refine ⟨2627720104561552022315785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14014507224328277452350853 2627720104561552022315785)
      ·
        refine ⟨1970790078421164016736839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2627720104561552022315785 1970790078421164016736839)
        ·
          refine ⟨2956185117631746025105259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1970790078421164016736839 2956185117631746025105259)
          ·
            refine ⟨4434277676447619037657889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956185117631746025105259 4434277676447619037657889)
            ·
              refine ⟨3325708257335714278243417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4434277676447619037657889 3325708257335714278243417)
              ·
                refine ⟨2494281193001785708682563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3325708257335714278243417 2494281193001785708682563)
                ·
                  refine ⟨3741421789502678563023845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2494281193001785708682563 3741421789502678563023845)
                  ·
                    refine ⟨701516585531752230566971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3741421789502678563023845 701516585531752230566971)
                    ·
                      rfl

theorem cell22_2049298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_2049298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049298 prefixEnd_2049298 := by exact prefixLift 2049298
  have htrace : WordTrace (prefixWord ++ tailWord_2049298) baseStart_2049298 baseEnd_2049298 := by
    simpa [prefixWord, tailWord_2049298, baseEnd_2049298] using wordTrace_append hprefix tailTrace_2049298
  have hstable : (prefixWord ++ tailWord_2049298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049298).length < 2 ^ (prefixWord ++ tailWord_2049298).sum := by decide
  have hdescent : baseEnd_2049298 < baseStart_2049298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049386 : List Nat := [3, 1, 3, 3, 2, 1, 2, 2, 5]
def baseStart_2049386 : Nat := 118140960795 + 2049386 * 2 ^ 59
def prefixEnd_2049386 : Nat := 4983230072969 + 3 ^ 40 * 2049386 * 2
def baseEnd_2049386 : Nat := 233848903243383111455567

theorem tailTrace_2049386 : CollatzResearch.WordTrace tailWord_2049386 prefixEnd_2049386 233848903243383111455567 := by
  unfold tailWord_2049386
  simp only [CollatzResearch.WordTrace]
  refine ⟨18686812038358001027102003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49831498768954669405605341 18686812038358001027102003)
  ·
    refine ⟨28030218057537001540653005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18686812038358001027102003 28030218057537001540653005)
    ·
      refine ⟨10511331771576375577744877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28030218057537001540653005 10511331771576375577744877)
      ·
        refine ⟨3941749414341140841654329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10511331771576375577744877 3941749414341140841654329)
        ·
          refine ⟨2956312060755855631240747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3941749414341140841654329 2956312060755855631240747)
          ·
            refine ⟨4434468091133783446861121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956312060755855631240747 4434468091133783446861121)
            ·
              refine ⟨3325851068350337585145841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4434468091133783446861121 3325851068350337585145841)
              ·
                refine ⟨2494388301262753188859381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3325851068350337585145841 2494388301262753188859381)
                ·
                  refine ⟨233848903243383111455567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2494388301262753188859381 233848903243383111455567)
                  ·
                    rfl

theorem cell22_2049386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_2049386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049386 prefixEnd_2049386 := by exact prefixLift 2049386
  have htrace : WordTrace (prefixWord ++ tailWord_2049386) baseStart_2049386 baseEnd_2049386 := by
    simpa [prefixWord, tailWord_2049386, baseEnd_2049386] using wordTrace_append hprefix tailTrace_2049386
  have hstable : (prefixWord ++ tailWord_2049386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049386).length < 2 ^ (prefixWord ++ tailWord_2049386).sum := by decide
  have hdescent : baseEnd_2049386 < baseStart_2049386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049390 : List Nat := [4, 1, 2, 4, 1, 1, 1, 4, 1, 3]
def baseStart_2049390 : Nat := 118140960795 + 2049390 * 2 ^ 59
def prefixEnd_2049390 : Nat := 4983230072969 + 3 ^ 40 * 2049390 * 2
def baseEnd_2049390 : Nat := 701548079011894657266689

theorem tailTrace_2049390 : CollatzResearch.WordTrace tailWord_2049390 prefixEnd_2049390 701548079011894657266689 := by
  unfold tailWord_2049390
  simp only [CollatzResearch.WordTrace]
  refine ⟨9343424255677189098944203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49831596030278341861035749 9343424255677189098944203)
  ·
    refine ⟨14015136383515783648416305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9343424255677189098944203 14015136383515783648416305)
    ·
      refine ⟨10511352287636837736312229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14015136383515783648416305 10511352287636837736312229)
      ·
        refine ⟨1970878553931907075558543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10511352287636837736312229 1970878553931907075558543)
        ·
          refine ⟨2956317830897860613337815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1970878553931907075558543 2956317830897860613337815)
          ·
            refine ⟨4434476746346790920006723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956317830897860613337815 4434476746346790920006723)
            ·
              refine ⟨6651715119520186380010085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4434476746346790920006723 6651715119520186380010085)
              ·
                refine ⟨1247196584910034946251891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6651715119520186380010085 1247196584910034946251891)
                ·
                  refine ⟨1870794877365052419377837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1247196584910034946251891 1870794877365052419377837)
                  ·
                    refine ⟨701548079011894657266689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1870794877365052419377837 701548079011894657266689)
                    ·
                      rfl

theorem cell22_2049390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_2049390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049390 prefixEnd_2049390 := by exact prefixLift 2049390
  have htrace : WordTrace (prefixWord ++ tailWord_2049390) baseStart_2049390 baseEnd_2049390 := by
    simpa [prefixWord, tailWord_2049390, baseEnd_2049390] using wordTrace_append hprefix tailTrace_2049390
  have hstable : (prefixWord ++ tailWord_2049390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049390).length < 2 ^ (prefixWord ++ tailWord_2049390).sum := by decide
  have hdescent : baseEnd_2049390 < baseStart_2049390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049472 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 2, 6]
def baseStart_2049472 : Nat := 118140960795 + 2049472 * 2 ^ 59
def prefixEnd_2049472 : Nat := 4983230072969 + 3 ^ 40 * 2049472 * 2
def baseEnd_2049472 : Nat := 701576149287673776716437

theorem tailTrace_2049472 : CollatzResearch.WordTrace tailWord_2049472 prefixEnd_2049472 701576149287673776716437 := by
  unfold tailWord_2049472
  simp only [CollatzResearch.WordTrace]
  refine ⟨37375192415560220398019335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49833589887413627197359113 37375192415560220398019335)
  ·
    refine ⟨56062788623340330597029003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37375192415560220398019335 56062788623340330597029003)
    ·
      refine ⟨84094182935010495895543505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56062788623340330597029003 84094182935010495895543505)
      ·
        refine ⟨63070637201257871921657629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84094182935010495895543505 63070637201257871921657629)
        ·
          refine ⟨23651488950471701970621611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63070637201257871921657629 23651488950471701970621611)
          ·
            refine ⟨35477233425707552955932417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23651488950471701970621611 35477233425707552955932417)
            ·
              refine ⟨26607925069280664716949313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35477233425707552955932417 26607925069280664716949313)
              ·
                refine ⟨19955943801960498537711985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26607925069280664716949313 19955943801960498537711985)
                ·
                  refine ⟨14966957851470373903283989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19955943801960498537711985 14966957851470373903283989)
                  ·
                    refine ⟨701576149287673776716437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14966957851470373903283989 701576149287673776716437)
                    ·
                      rfl

theorem cell22_2049472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_2049472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049472 prefixEnd_2049472 := by exact prefixLift 2049472
  have htrace : WordTrace (prefixWord ++ tailWord_2049472) baseStart_2049472 baseEnd_2049472 := by
    simpa [prefixWord, tailWord_2049472, baseEnd_2049472] using wordTrace_append hprefix tailTrace_2049472
  have hstable : (prefixWord ++ tailWord_2049472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049472).length < 2 ^ (prefixWord ++ tailWord_2049472).sum := by decide
  have hdescent : baseEnd_2049472 < baseStart_2049472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049476 : List Nat := [2, 3, 3, 2, 1, 1, 4, 6]
def baseStart_2049476 : Nat := 118140960795 + 2049476 * 2 ^ 59
def prefixEnd_2049476 : Nat := 4983230072969 + 3 ^ 40 * 2049476 * 2
def baseEnd_2049476 : Nat := 77953057618824344401825

theorem tailTrace_2049476 : CollatzResearch.WordTrace tailWord_2049476 prefixEnd_2049476 77953057618824344401825 := by
  unfold tailWord_2049476
  simp only [CollatzResearch.WordTrace]
  refine ⟨37375265361552974739592141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49833687148737299652789521 37375265361552974739592141)
  ·
    refine ⟨14015724510582365527347053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37375265361552974739592141 14015724510582365527347053)
    ·
      refine ⟨5255896691468387072755145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14015724510582365527347053 5255896691468387072755145)
      ·
        refine ⟨3941922518601290304566359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5255896691468387072755145 3941922518601290304566359)
        ·
          refine ⟨5912883777901935456849539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3941922518601290304566359 5912883777901935456849539)
          ·
            refine ⟨8869325666852903185274309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5912883777901935456849539 8869325666852903185274309)
            ·
              refine ⟨1662998562534919347238933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8869325666852903185274309 1662998562534919347238933)
              ·
                refine ⟨77953057618824344401825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1662998562534919347238933 77953057618824344401825)
                ·
                  rfl

theorem cell22_2049476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 6].length) (baseStart_2049476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049476 prefixEnd_2049476 := by exact prefixLift 2049476
  have htrace : WordTrace (prefixWord ++ tailWord_2049476) baseStart_2049476 baseEnd_2049476 := by
    simpa [prefixWord, tailWord_2049476, baseEnd_2049476] using wordTrace_append hprefix tailTrace_2049476
  have hstable : (prefixWord ++ tailWord_2049476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049476).length < 2 ^ (prefixWord ++ tailWord_2049476).sum := by decide
  have hdescent : baseEnd_2049476 < baseStart_2049476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049487 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 7]
def baseStart_2049487 : Nat := 118140960795 + 2049487 * 2 ^ 59
def prefixEnd_2049487 : Nat := 4983230072969 + 3 ^ 40 * 2049487 * 2
def baseEnd_2049487 : Nat := 233860428031406245863797

theorem tailTrace_2049487 : CollatzResearch.WordTrace tailWord_2049487 prefixEnd_2049487 233860428031406245863797 := by
  unfold tailWord_2049487
  simp only [CollatzResearch.WordTrace]
  refine ⟨74750931926066098357834715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49833954617377398905223143 74750931926066098357834715)
  ·
    refine ⟨112126397889099147536752073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74750931926066098357834715 112126397889099147536752073)
    ·
      refine ⟨84094798416824360652564055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112126397889099147536752073 84094798416824360652564055)
      ·
        refine ⟨126142197625236540978846083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84094798416824360652564055 126142197625236540978846083)
        ·
          refine ⟨189213296437854811468269125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126142197625236540978846083 189213296437854811468269125)
          ·
            refine ⟨35477493082097777150300461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189213296437854811468269125 35477493082097777150300461)
            ·
              refine ⟨13304059905786666431362673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35477493082097777150300461 13304059905786666431362673)
              ·
                refine ⟨9978044929339999823522005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13304059905786666431362673 9978044929339999823522005)
                ·
                  refine ⟨233860428031406245863797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9978044929339999823522005 233860428031406245863797)
                  ·
                    rfl

theorem cell22_2049487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 7].length) (baseStart_2049487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049487 prefixEnd_2049487 := by exact prefixLift 2049487
  have htrace : WordTrace (prefixWord ++ tailWord_2049487) baseStart_2049487 baseEnd_2049487 := by
    simpa [prefixWord, tailWord_2049487, baseEnd_2049487] using wordTrace_append hprefix tailTrace_2049487
  have hstable : (prefixWord ++ tailWord_2049487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049487).length < 2 ^ (prefixWord ++ tailWord_2049487).sum := by decide
  have hdescent : baseEnd_2049487 < baseStart_2049487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049521 : List Nat := [1, 2, 2, 2, 3, 2, 4, 1, 5]
def baseStart_2049521 : Nat := 118140960795 + 2049521 * 2 ^ 59
def prefixEnd_2049521 : Nat := 4983230072969 + 3 ^ 40 * 2049521 * 2
def baseEnd_2049521 : Nat := 233864307663017994080429

theorem tailTrace_2049521 : CollatzResearch.WordTrace tailWord_2049521 prefixEnd_2049521 233864307663017994080429 := by
  unfold tailWord_2049521
  simp only [CollatzResearch.WordTrace]
  refine ⟨74752172007942922164572417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49834781338628614776381611 74752172007942922164572417)
  ·
    refine ⟨56064129005957191623429313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74752172007942922164572417 56064129005957191623429313)
    ·
      refine ⟨42048096754467893717571985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56064129005957191623429313 42048096754467893717571985)
      ·
        refine ⟨31536072565850920288178989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42048096754467893717571985 31536072565850920288178989)
        ·
          refine ⟨11826027212194095108067121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31536072565850920288178989 11826027212194095108067121)
          ·
            refine ⟨8869520409145571331050341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11826027212194095108067121 8869520409145571331050341)
            ·
              refine ⟨1663035076714794624571939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8869520409145571331050341 1663035076714794624571939)
              ·
                refine ⟨2494552615072191936857909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663035076714794624571939 2494552615072191936857909)
                ·
                  refine ⟨233864307663017994080429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2494552615072191936857909 233864307663017994080429)
                  ·
                    rfl

theorem cell22_2049521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 5].length) (baseStart_2049521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049521 prefixEnd_2049521 := by exact prefixLift 2049521
  have htrace : WordTrace (prefixWord ++ tailWord_2049521) baseStart_2049521 baseEnd_2049521 := by
    simpa [prefixWord, tailWord_2049521, baseEnd_2049521] using wordTrace_append hprefix tailTrace_2049521
  have hstable : (prefixWord ++ tailWord_2049521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049521).length < 2 ^ (prefixWord ++ tailWord_2049521).sum := by decide
  have hdescent : baseEnd_2049521 < baseStart_2049521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049564 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 3, 5]
def baseStart_2049564 : Nat := 118140960795 + 2049564 * 2 ^ 59
def prefixEnd_2049564 : Nat := 4983230072969 + 3 ^ 40 * 2049564 * 2
def baseEnd_2049564 : Nat := 701607642767816203416155

theorem tailTrace_2049564 : CollatzResearch.WordTrace tailWord_2049564 prefixEnd_2049564 701607642767816203416155 := by
  unfold tailWord_2049564
  simp only [CollatzResearch.WordTrace]
  refine ⟨37376870173393570254193873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49835826897858093672258497 37376870173393570254193873)
  ·
    refine ⟨28032652630045177690645405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37376870173393570254193873 28032652630045177690645405)
    ·
      refine ⟨10512244736266941633992027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28032652630045177690645405 10512244736266941633992027)
      ·
        refine ⟨15768367104400412450988041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10512244736266941633992027 15768367104400412450988041)
        ·
          refine ⟨11826275328300309338241031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15768367104400412450988041 11826275328300309338241031)
          ·
            refine ⟨17739412992450464007361547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11826275328300309338241031 17739412992450464007361547)
            ·
              refine ⟨26609119488675696011042321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17739412992450464007361547 26609119488675696011042321)
              ·
                refine ⟨19956839616506772008281741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26609119488675696011042321 19956839616506772008281741)
                ·
                  refine ⟨7483814856190039503105653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19956839616506772008281741 7483814856190039503105653)
                  ·
                    refine ⟨701607642767816203416155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7483814856190039503105653 701607642767816203416155)
                    ·
                      rfl

theorem cell22_2049564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_2049564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049564 prefixEnd_2049564 := by exact prefixLift 2049564
  have htrace : WordTrace (prefixWord ++ tailWord_2049564) baseStart_2049564 baseEnd_2049564 := by
    simpa [prefixWord, tailWord_2049564, baseEnd_2049564] using wordTrace_append hprefix tailTrace_2049564
  have hstable : (prefixWord ++ tailWord_2049564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049564).length < 2 ^ (prefixWord ++ tailWord_2049564).sum := by decide
  have hdescent : baseEnd_2049564 < baseStart_2049564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049596 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 1, 6]
def baseStart_2049596 : Nat := 118140960795 + 2049596 * 2 ^ 59
def prefixEnd_2049596 : Nat := 4983230072969 + 3 ^ 40 * 2049596 * 2
def baseEnd_2049596 : Nat := 701618597021778786616057

theorem tailTrace_2049596 : CollatzResearch.WordTrace tailWord_2049596 prefixEnd_2049596 701618597021778786616057 := by
  unfold tailWord_2049596
  simp only [CollatzResearch.WordTrace]
  refine ⟨37377453741335604986776321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49836604988447473315701761 37377453741335604986776321)
  ·
    refine ⟨28033090306001703740082241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37377453741335604986776321 28033090306001703740082241)
    ·
      refine ⟨21024817729501277805061681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28033090306001703740082241 21024817729501277805061681)
      ·
        refine ⟨15768613297125958353796261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21024817729501277805061681 15768613297125958353796261)
        ·
          refine ⟨2956614993211117191336799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15768613297125958353796261 2956614993211117191336799)
          ·
            refine ⟨4434922489816675787005199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956614993211117191336799 4434922489816675787005199)
            ·
              refine ⟨6652383734725013680507799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4434922489816675787005199 6652383734725013680507799)
              ·
                refine ⟨9978575602087520520761699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6652383734725013680507799 9978575602087520520761699)
                ·
                  refine ⟨14967863403131280781142549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9978575602087520520761699 14967863403131280781142549)
                  ·
                    refine ⟨701618597021778786616057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14967863403131280781142549 701618597021778786616057)
                    ·
                      rfl

theorem cell22_2049596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_2049596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049596 prefixEnd_2049596 := by exact prefixLift 2049596
  have htrace : WordTrace (prefixWord ++ tailWord_2049596) baseStart_2049596 baseEnd_2049596 := by
    simpa [prefixWord, tailWord_2049596, baseEnd_2049596] using wordTrace_append hprefix tailTrace_2049596
  have hstable : (prefixWord ++ tailWord_2049596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049596).length < 2 ^ (prefixWord ++ tailWord_2049596).sum := by decide
  have hdescent : baseEnd_2049596 < baseStart_2049596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049645 : List Nat := [1, 5, 1, 1, 5, 1, 2, 6]
def baseStart_2049645 : Nat := 118140960795 + 2049645 * 2 ^ 59
def prefixEnd_2049645 : Nat := 4983230072969 + 3 ^ 40 * 2049645 * 2
def baseEnd_2049645 : Nat := 77959485635906554682323

theorem tailTrace_2049645 : CollatzResearch.WordTrace tailWord_2049645 prefixEnd_2049645 77959485635906554682323 := by
  unfold tailWord_2049645
  simp only [CollatzResearch.WordTrace]
  refine ⟨74756694659493691342086389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49837796439662460894724259 74756694659493691342086389)
  ·
    refine ⟨7008440124327533563320599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74756694659493691342086389 7008440124327533563320599)
    ·
      refine ⟨10512660186491300344980899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7008440124327533563320599 10512660186491300344980899)
      ·
        refine ⟨15768990279736950517471349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10512660186491300344980899 15768990279736950517471349)
        ·
          refine ⟨1478342838725339111012939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15768990279736950517471349 1478342838725339111012939)
          ·
            refine ⟨2217514258088008666519409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478342838725339111012939 2217514258088008666519409)
            ·
              refine ⟨1663135693566006499889557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2217514258088008666519409 1663135693566006499889557)
              ·
                refine ⟨77959485635906554682323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1663135693566006499889557 77959485635906554682323)
                ·
                  rfl

theorem cell22_2049645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 6].length) (baseStart_2049645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049645 prefixEnd_2049645 := by exact prefixLift 2049645
  have htrace : WordTrace (prefixWord ++ tailWord_2049645) baseStart_2049645 baseEnd_2049645 := by
    simpa [prefixWord, tailWord_2049645, baseEnd_2049645] using wordTrace_append hprefix tailTrace_2049645
  have hstable : (prefixWord ++ tailWord_2049645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049645).length < 2 ^ (prefixWord ++ tailWord_2049645).sum := by decide
  have hdescent : baseEnd_2049645 < baseStart_2049645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049778 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 5, 3]
def baseStart_2049778 : Nat := 118140960795 + 2049778 * 2 ^ 59
def prefixEnd_2049778 : Nat := 4983230072969 + 3 ^ 40 * 2049778 * 2
def baseEnd_2049778 : Nat := 701680899341190978565499

theorem tailTrace_2049778 : CollatzResearch.WordTrace tailWord_2049778 prefixEnd_2049778 701680899341190978565499 := by
  unfold tailWord_2049778
  simp only [CollatzResearch.WordTrace]
  refine ⟨18690386392002963764169497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49841030378674570037785325 18690386392002963764169497)
  ·
    refine ⟨14017789794002222823127123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18690386392002963764169497 14017789794002222823127123)
    ·
      refine ⟨21026684691003334234690685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14017789794002222823127123 21026684691003334234690685)
      ·
        refine ⟨7885006759126250338009007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21026684691003334234690685 7885006759126250338009007)
        ·
          refine ⟨11827510138689375507013511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7885006759126250338009007 11827510138689375507013511)
          ·
            refine ⟨17741265208034063260520267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11827510138689375507013511 17741265208034063260520267)
            ·
              refine ⟨26611897812051094890780401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17741265208034063260520267 26611897812051094890780401)
              ·
                refine ⟨19958923359038321168085301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26611897812051094890780401 19958923359038321168085301)
                ·
                  refine ⟨1871149064909842609507997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19958923359038321168085301 1871149064909842609507997)
                  ·
                    refine ⟨701680899341190978565499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1871149064909842609507997 701680899341190978565499)
                    ·
                      rfl

theorem cell22_2049778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_2049778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049778 prefixEnd_2049778 := by exact prefixLift 2049778
  have htrace : WordTrace (prefixWord ++ tailWord_2049778) baseStart_2049778 baseEnd_2049778 := by
    simpa [prefixWord, tailWord_2049778, baseEnd_2049778] using wordTrace_append hprefix tailTrace_2049778
  have hstable : (prefixWord ++ tailWord_2049778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049778).length < 2 ^ (prefixWord ++ tailWord_2049778).sum := by decide
  have hdescent : baseEnd_2049778 < baseStart_2049778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049780 : List Nat := [2, 6, 1, 1, 1, 2, 9]
def baseStart_2049780 : Nat := 118140960795 + 2049780 * 2 ^ 59
def prefixEnd_2049780 : Nat := 4983230072969 + 3 ^ 40 * 2049780 * 2
def baseEnd_2049780 : Nat := 25988206814150505185759

theorem tailTrace_2049780 : CollatzResearch.WordTrace tailWord_2049780 prefixEnd_2049780 25988206814150505185759 := by
  unfold tailWord_2049780
  simp only [CollatzResearch.WordTrace]
  refine ⟨37380809257002304699125397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49841079009336406265500529 37380809257002304699125397)
  ·
    refine ⟨1752225433921983032771503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37380809257002304699125397 1752225433921983032771503)
    ·
      refine ⟨2628338150882974549157255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1752225433921983032771503 2628338150882974549157255)
      ·
        refine ⟨3942507226324461823735883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2628338150882974549157255 3942507226324461823735883)
        ·
          refine ⟨5913760839486692735603825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3942507226324461823735883 5913760839486692735603825)
          ·
            refine ⟨4435320629615019551702869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5913760839486692735603825 4435320629615019551702869)
            ·
              refine ⟨25988206814150505185759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4435320629615019551702869 25988206814150505185759)
              ·
                rfl

theorem cell22_2049780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 9].length) (baseStart_2049780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049780 prefixEnd_2049780 := by exact prefixLift 2049780
  have htrace : WordTrace (prefixWord ++ tailWord_2049780) baseStart_2049780 baseEnd_2049780 := by
    simpa [prefixWord, tailWord_2049780, baseEnd_2049780] using wordTrace_append hprefix tailTrace_2049780
  have hstable : (prefixWord ++ tailWord_2049780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049780).length < 2 ^ (prefixWord ++ tailWord_2049780).sum := by decide
  have hdescent : baseEnd_2049780 < baseStart_2049780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049795 : List Nat := [1, 1, 1, 3, 2, 2, 4, 4, 1, 3]
def baseStart_2049795 : Nat := 118140960795 + 2049795 * 2 ^ 59
def prefixEnd_2049795 : Nat := 4983230072969 + 3 ^ 40 * 2049795 * 2
def baseEnd_2049795 : Nat := 701686718788608600890447

theorem tailTrace_2049795 : CollatzResearch.WordTrace tailWord_2049795 prefixEnd_2049795 701686718788608600890447 := by
  unfold tailWord_2049795
  simp only [CollatzResearch.WordTrace]
  refine ⟨74762165608950266960046839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49841443739300177973364559 74762165608950266960046839)
  ·
    refine ⟨112143248413425400440070259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74762165608950266960046839 112143248413425400440070259)
    ·
      refine ⟨168214872620138100660105389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112143248413425400440070259 168214872620138100660105389)
      ·
        refine ⟨63080577232551787747539521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168214872620138100660105389 63080577232551787747539521)
        ·
          refine ⟨47310432924413840810654641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63080577232551787747539521 47310432924413840810654641)
          ·
            refine ⟨35482824693310380607990981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47310432924413840810654641 35482824693310380607990981)
            ·
              refine ⟨6653029629995696363998309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35482824693310380607990981 6653029629995696363998309)
              ·
                refine ⟨1247443055624193068249683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6653029629995696363998309 1247443055624193068249683)
                ·
                  refine ⟨1871164583436289602374525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1247443055624193068249683 1871164583436289602374525)
                  ·
                    refine ⟨701686718788608600890447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1871164583436289602374525 701686718788608600890447)
                    ·
                      rfl

theorem cell22_2049795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 1, 3].length) (baseStart_2049795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049795 prefixEnd_2049795 := by exact prefixLift 2049795
  have htrace : WordTrace (prefixWord ++ tailWord_2049795) baseStart_2049795 baseEnd_2049795 := by
    simpa [prefixWord, tailWord_2049795, baseEnd_2049795] using wordTrace_append hprefix tailTrace_2049795
  have hstable : (prefixWord ++ tailWord_2049795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049795).length < 2 ^ (prefixWord ++ tailWord_2049795).sum := by decide
  have hdescent : baseEnd_2049795 < baseStart_2049795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049846 : List Nat := [5, 1, 2, 2, 1, 2, 3, 2, 1, 3]
def baseStart_2049846 : Nat := 118140960795 + 2049846 * 2 ^ 59
def prefixEnd_2049846 : Nat := 4983230072969 + 3 ^ 40 * 2049846 * 2
def baseEnd_2049846 : Nat := 701704177130861467865291

theorem tailTrace_2049846 : CollatzResearch.WordTrace tailWord_2049846 prefixEnd_2049846 701704177130861467865291 := by
  unfold tailWord_2049846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4672751608235343916884587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49842683821177001780102261 4672751608235343916884587)
  ·
    refine ⟨7009127412353015875326881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4672751608235343916884587 7009127412353015875326881)
    ·
      refine ⟨5256845559264761906495161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7009127412353015875326881 5256845559264761906495161)
      ·
        refine ⟨3942634169448571429871371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5256845559264761906495161 3942634169448571429871371)
        ·
          refine ⟨5913951254172857144807057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3942634169448571429871371 5913951254172857144807057)
          ·
            refine ⟨4435463440629642858605293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5913951254172857144807057 4435463440629642858605293)
            ·
              refine ⟨1663298790236116071976985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4435463440629642858605293 1663298790236116071976985)
              ·
                refine ⟨1247474092677087053982739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1663298790236116071976985 1247474092677087053982739)
                ·
                  refine ⟨1871211139015630580974109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1247474092677087053982739 1871211139015630580974109)
                  ·
                    refine ⟨701704177130861467865291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1871211139015630580974109 701704177130861467865291)
                    ·
                      rfl

theorem cell22_2049846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_2049846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049846 prefixEnd_2049846 := by exact prefixLift 2049846
  have htrace : WordTrace (prefixWord ++ tailWord_2049846) baseStart_2049846 baseEnd_2049846 := by
    simpa [prefixWord, tailWord_2049846, baseEnd_2049846] using wordTrace_append hprefix tailTrace_2049846
  have hstable : (prefixWord ++ tailWord_2049846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049846).length < 2 ^ (prefixWord ++ tailWord_2049846).sum := by decide
  have hdescent : baseEnd_2049846 < baseStart_2049846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049881 : List Nat := [1, 2, 1, 2, 2, 3, 1, 10]
def baseStart_2049881 : Nat := 118140960795 + 2049881 * 2 ^ 59
def prefixEnd_2049881 : Nat := 4983230072969 + 3 ^ 40 * 2049881 * 2
def baseEnd_2049881 : Nat := 77968462038459227026687

theorem tailTrace_2049881 : CollatzResearch.WordTrace tailWord_2049881 prefixEnd_2049881 77968462038459227026687 := by
  unfold tailWord_2049881
  simp only [CollatzResearch.WordTrace]
  refine ⟨74765302286638703647677497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49843534857759135765118331 74765302286638703647677497)
  ·
    refine ⟨56073976714979027735758123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74765302286638703647677497 56073976714979027735758123)
    ·
      refine ⟨84110965072468541603637185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56073976714979027735758123 84110965072468541603637185)
      ·
        refine ⟨63083223804351406202727889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84110965072468541603637185 63083223804351406202727889)
        ·
          refine ⟨47312417853263554652045917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63083223804351406202727889 47312417853263554652045917)
          ·
            refine ⟨17742156694973832994517219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47312417853263554652045917 17742156694973832994517219)
            ·
              refine ⟨26613235042460749491775829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17742156694973832994517219 26613235042460749491775829)
              ·
                refine ⟨77968462038459227026687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26613235042460749491775829 77968462038459227026687)
                ·
                  rfl

theorem cell22_2049881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 10].length) (baseStart_2049881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049881 prefixEnd_2049881 := by exact prefixLift 2049881
  have htrace : WordTrace (prefixWord ++ tailWord_2049881) baseStart_2049881 baseEnd_2049881 := by
    simpa [prefixWord, tailWord_2049881, baseEnd_2049881] using wordTrace_append hprefix tailTrace_2049881
  have hstable : (prefixWord ++ tailWord_2049881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049881).length < 2 ^ (prefixWord ++ tailWord_2049881).sum := by decide
  have hdescent : baseEnd_2049881 < baseStart_2049881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049898 : List Nat := [3, 1, 3, 4, 11]
def baseStart_2049898 : Nat := 118140960795 + 2049898 * 2 ^ 59
def prefixEnd_2049898 : Nat := 4983230072969 + 3 ^ 40 * 2049898 * 2
def baseEnd_2049898 : Nat := 2887744764582513027017

theorem tailTrace_2049898 : CollatzResearch.WordTrace tailWord_2049898 prefixEnd_2049898 2887744764582513027017 := by
  unfold tailWord_2049898
  simp only [CollatzResearch.WordTrace]
  refine ⟨18691480581894278887761587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49843948218384743700697565 18691480581894278887761587)
  ·
    refine ⟨28037220872841418331642381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18691480581894278887761587 28037220872841418331642381)
    ·
      refine ⟨10513957827315531874365893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28037220872841418331642381 10513957827315531874365893)
      ·
        refine ⟨1971367092621662226443605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10513957827315531874365893 1971367092621662226443605)
        ·
          refine ⟨2887744764582513027017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1971367092621662226443605 2887744764582513027017)
          ·
            rfl

theorem cell22_2049898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 11].length) (baseStart_2049898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049898 prefixEnd_2049898 := by exact prefixLift 2049898
  have htrace : WordTrace (prefixWord ++ tailWord_2049898) baseStart_2049898 baseEnd_2049898 := by
    simpa [prefixWord, tailWord_2049898, baseEnd_2049898] using wordTrace_append hprefix tailTrace_2049898
  have hstable : (prefixWord ++ tailWord_2049898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049898).length < 2 ^ (prefixWord ++ tailWord_2049898).sum := by decide
  have hdescent : baseEnd_2049898 < baseStart_2049898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049902 : List Nat := [4, 1, 2, 3, 1, 1, 1, 4, 2, 3]
def baseStart_2049902 : Nat := 118140960795 + 2049902 * 2 ^ 59
def prefixEnd_2049902 : Nat := 4983230072969 + 3 ^ 40 * 2049902 * 2
def baseEnd_2049902 : Nat := 701723347075295988465119

theorem tailTrace_2049902 : CollatzResearch.WordTrace tailWord_2049902 prefixEnd_2049902 701723347075295988465119 := by
  unfold tailWord_2049902
  simp only [CollatzResearch.WordTrace]
  refine ⟨9345758527445328029273995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49844045479708416156127973 9345758527445328029273995)
  ·
    refine ⟨14018637791167992043910993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9345758527445328029273995 14018637791167992043910993)
    ·
      refine ⟨10513978343375994032933245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14018637791167992043910993 10513978343375994032933245)
      ·
        refine ⟨3942741878765997762349967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10513978343375994032933245 3942741878765997762349967)
        ·
          refine ⟨5914112818148996643524951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3942741878765997762349967 5914112818148996643524951)
          ·
            refine ⟨8871169227223494965287427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5914112818148996643524951 8871169227223494965287427)
            ·
              refine ⟨13306753840835242447931141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8871169227223494965287427 13306753840835242447931141)
              ·
                refine ⟨2495016345156607958987089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13306753840835242447931141 2495016345156607958987089)
                ·
                  refine ⟨1871262258867455969240317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2495016345156607958987089 1871262258867455969240317)
                  ·
                    refine ⟨701723347075295988465119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1871262258867455969240317 701723347075295988465119)
                    ·
                      rfl

theorem cell22_2049902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_2049902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049902 prefixEnd_2049902 := by exact prefixLift 2049902
  have htrace : WordTrace (prefixWord ++ tailWord_2049902) baseStart_2049902 baseEnd_2049902 := by
    simpa [prefixWord, tailWord_2049902, baseEnd_2049902] using wordTrace_append hprefix tailTrace_2049902
  have hstable : (prefixWord ++ tailWord_2049902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049902).length < 2 ^ (prefixWord ++ tailWord_2049902).sum := by decide
  have hdescent : baseEnd_2049902 < baseStart_2049902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049934 : List Nat := [4, 1, 1, 5, 1, 2, 1, 1, 2, 4]
def baseStart_2049934 : Nat := 118140960795 + 2049934 * 2 ^ 59
def prefixEnd_2049934 : Nat := 4983230072969 + 3 ^ 40 * 2049934 * 2
def baseEnd_2049934 : Nat := 701734301329258571665021

theorem tailTrace_2049934 : CollatzResearch.WordTrace tailWord_2049934 prefixEnd_2049934 701734301329258571665021 := by
  unfold tailWord_2049934
  simp only [CollatzResearch.WordTrace]
  refine ⟨9345904419430836712419607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49844823570297795799571237 9345904419430836712419607)
  ·
    refine ⟨14018856629146255068629411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9345904419430836712419607 14018856629146255068629411)
    ·
      refine ⟨21028284943719382602944117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14018856629146255068629411 21028284943719382602944117)
      ·
        refine ⟨1971401713473692119026011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21028284943719382602944117 1971401713473692119026011)
        ·
          refine ⟨2957102570210538178539017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1971401713473692119026011 2957102570210538178539017)
          ·
            refine ⟨2217826927657903633904263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2957102570210538178539017 2217826927657903633904263)
            ·
              refine ⟨3326740391486855450856395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2217826927657903633904263 3326740391486855450856395)
              ·
                refine ⟨4990110587230283176284593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3326740391486855450856395 4990110587230283176284593)
                ·
                  refine ⟨3742582940422712382213445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4990110587230283176284593 3742582940422712382213445)
                  ·
                    refine ⟨701734301329258571665021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3742582940422712382213445 701734301329258571665021)
                    ·
                      rfl

theorem cell22_2049934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_2049934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2049934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2049934 prefixEnd_2049934 := by exact prefixLift 2049934
  have htrace : WordTrace (prefixWord ++ tailWord_2049934) baseStart_2049934 baseEnd_2049934 := by
    simpa [prefixWord, tailWord_2049934, baseEnd_2049934] using wordTrace_append hprefix tailTrace_2049934
  have hstable : (prefixWord ++ tailWord_2049934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049934).length < 2 ^ (prefixWord ++ tailWord_2049934).sum := by decide
  have hdescent : baseEnd_2049934 < baseStart_2049934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050020 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 4, 3]
def baseStart_2050020 : Nat := 118140960795 + 2050020 * 2 ^ 59
def prefixEnd_2050020 : Nat := 4983230072969 + 3 ^ 40 * 2050020 * 2
def baseEnd_2050020 : Nat := 701763740886783014014757

theorem tailTrace_2050020 : CollatzResearch.WordTrace tailWord_2050020 prefixEnd_2050020 701763740886783014014757 := by
  unfold tailWord_2050020
  simp only [CollatzResearch.WordTrace]
  refine ⟨37385186016567565193493757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49846914688756753591325009 37385186016567565193493757)
  ·
    refine ⟨14019444756212836947560159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37385186016567565193493757 14019444756212836947560159)
    ·
      refine ⟨21029167134319255421340239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14019444756212836947560159 21029167134319255421340239)
      ·
        refine ⟨31543750701478883132010359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21029167134319255421340239 31543750701478883132010359)
        ·
          refine ⟨47315626052218324698015539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31543750701478883132010359 47315626052218324698015539)
          ·
            refine ⟨70973439078327487047023309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47315626052218324698015539 70973439078327487047023309)
            ·
              refine ⟨26615039654372807642633741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70973439078327487047023309 26615039654372807642633741)
              ·
                refine ⟨9980639870389802865987653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26615039654372807642633741 9980639870389802865987653)
                ·
                  refine ⟨1871369975698088037372685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9980639870389802865987653 1871369975698088037372685)
                  ·
                    refine ⟨701763740886783014014757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1871369975698088037372685 701763740886783014014757)
                    ·
                      rfl

theorem cell22_2050020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_2050020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050020 prefixEnd_2050020 := by exact prefixLift 2050020
  have htrace : WordTrace (prefixWord ++ tailWord_2050020) baseStart_2050020 baseEnd_2050020 := by
    simpa [prefixWord, tailWord_2050020, baseEnd_2050020] using wordTrace_append hprefix tailTrace_2050020
  have hstable : (prefixWord ++ tailWord_2050020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050020).length < 2 ^ (prefixWord ++ tailWord_2050020).sum := by decide
  have hdescent : baseEnd_2050020 < baseStart_2050020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050082 : List Nat := [3, 3, 1, 1, 1, 2, 2, 3, 3, 3]
def baseStart_2050082 : Nat := 118140960795 + 2050082 * 2 ^ 59
def prefixEnd_2050082 : Nat := 4983230072969 + 3 ^ 40 * 2050082 * 2
def baseEnd_2050082 : Nat := 701784964753835518964567

theorem tailTrace_2050082 : CollatzResearch.WordTrace tailWord_2050082 prefixEnd_2050082 701784964753835518964567 := by
  unfold tailWord_2050082
  simp only [CollatzResearch.WordTrace]
  refine ⟨18693158339727628743936125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49848422239273676650496333 18693158339727628743936125)
  ·
    refine ⟨7009934377397860778976047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18693158339727628743936125 7009934377397860778976047)
    ·
      refine ⟨10514901566096791168464071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7009934377397860778976047 10514901566096791168464071)
      ·
        refine ⟨15772352349145186752696107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10514901566096791168464071 15772352349145186752696107)
        ·
          refine ⟨23658528523717780129044161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15772352349145186752696107 23658528523717780129044161)
          ·
            refine ⟨17743896392788335096783121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23658528523717780129044161 17743896392788335096783121)
            ·
              refine ⟨13307922294591251322587341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17743896392788335096783121 13307922294591251322587341)
              ·
                refine ⟨4990470860471719245970253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13307922294591251322587341 4990470860471719245970253)
                ·
                  refine ⟨1871426572676894717238845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4990470860471719245970253 1871426572676894717238845)
                  ·
                    refine ⟨701784964753835518964567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1871426572676894717238845 701784964753835518964567)
                    ·
                      rfl

theorem cell22_2050082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_2050082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050082 prefixEnd_2050082 := by exact prefixLift 2050082
  have htrace : WordTrace (prefixWord ++ tailWord_2050082) baseStart_2050082 baseEnd_2050082 := by
    simpa [prefixWord, tailWord_2050082, baseEnd_2050082] using wordTrace_append hprefix tailTrace_2050082
  have hstable : (prefixWord ++ tailWord_2050082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050082).length < 2 ^ (prefixWord ++ tailWord_2050082).sum := by decide
  have hdescent : baseEnd_2050082 < baseStart_2050082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050084 : List Nat := [2, 3, 1, 4, 3, 1, 1, 7]
def baseStart_2050084 : Nat := 118140960795 + 2050084 * 2 ^ 59
def prefixEnd_2050084 : Nat := 4983230072969 + 3 ^ 40 * 2050084 * 2
def baseEnd_2050084 : Nat := 77976183266078686712729

theorem tailTrace_2050084 : CollatzResearch.WordTrace tailWord_2050084 prefixEnd_2050084 77976183266078686712729 := by
  unfold tailWord_2050084
  simp only [CollatzResearch.WordTrace]
  refine ⟨37386353152451634658658653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49848470869935512878211537 37386353152451634658658653)
  ·
    refine ⟨14019882432169362996996995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37386353152451634658658653 14019882432169362996996995)
    ·
      refine ⟨21029823648254044495495493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14019882432169362996996995 21029823648254044495495493)
      ·
        refine ⟨3943091934047633342905405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21029823648254044495495493 3943091934047633342905405)
        ·
          refine ⟨1478659475267862503589527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3943091934047633342905405 1478659475267862503589527)
          ·
            refine ⟨2217989212901793755384291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478659475267862503589527 2217989212901793755384291)
            ·
              refine ⟨3326983819352690633076437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2217989212901793755384291 3326983819352690633076437)
              ·
                refine ⟨77976183266078686712729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3326983819352690633076437 77976183266078686712729)
                ·
                  rfl

theorem cell22_2050084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 7].length) (baseStart_2050084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050084 prefixEnd_2050084 := by exact prefixLift 2050084
  have htrace : WordTrace (prefixWord ++ tailWord_2050084) baseStart_2050084 baseEnd_2050084 := by
    simpa [prefixWord, tailWord_2050084, baseEnd_2050084] using wordTrace_append hprefix tailTrace_2050084
  have hstable : (prefixWord ++ tailWord_2050084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050084).length < 2 ^ (prefixWord ++ tailWord_2050084).sum := by decide
  have hdescent : baseEnd_2050084 < baseStart_2050084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050146 : List Nat := [3, 3, 2, 2, 2, 1, 3, 1, 5]
def baseStart_2050146 : Nat := 118140960795 + 2050146 * 2 ^ 59
def prefixEnd_2050146 : Nat := 4983230072969 + 3 ^ 40 * 2050146 * 2
def baseEnd_2050146 : Nat := 233935624420586895121457

theorem tailTrace_2050146 : CollatzResearch.WordTrace tailWord_2050146 prefixEnd_2050146 233935624420586895121457 := by
  unfold tailWord_2050146
  simp only [CollatzResearch.WordTrace]
  refine ⟨18693741907669663476518573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49849978420452435937382861 18693741907669663476518573)
  ·
    refine ⟨7010153215376123803694465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18693741907669663476518573 7010153215376123803694465)
    ·
      refine ⟨5257614911532092852770849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7010153215376123803694465 5257614911532092852770849)
      ·
        refine ⟨3943211183649069639578137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5257614911532092852770849 3943211183649069639578137)
        ·
          refine ⟨2957408387736802229683603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3943211183649069639578137 2957408387736802229683603)
          ·
            refine ⟨4436112581605203344525405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957408387736802229683603 4436112581605203344525405)
            ·
              refine ⟨1663542218101951254197027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4436112581605203344525405 1663542218101951254197027)
              ·
                refine ⟨2495313327152926881295541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663542218101951254197027 2495313327152926881295541)
                ·
                  refine ⟨233935624420586895121457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2495313327152926881295541 233935624420586895121457)
                  ·
                    rfl

theorem cell22_2050146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_2050146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050146 prefixEnd_2050146 := by exact prefixLift 2050146
  have htrace : WordTrace (prefixWord ++ tailWord_2050146) baseStart_2050146 baseEnd_2050146 := by
    simpa [prefixWord, tailWord_2050146, baseEnd_2050146] using wordTrace_append hprefix tailTrace_2050146
  have hstable : (prefixWord ++ tailWord_2050146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050146).length < 2 ^ (prefixWord ++ tailWord_2050146).sum := by decide
  have hdescent : baseEnd_2050146 < baseStart_2050146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050170 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 8, 4]
def baseStart_2050170 : Nat := 118140960795 + 2050170 * 2 ^ 59
def prefixEnd_2050170 : Nat := 4983230072969 + 3 ^ 40 * 2050170 * 2
def baseEnd_2050170 : Nat := 701815088952232622764297

theorem tailTrace_2050170 : CollatzResearch.WordTrace tailWord_2050170 prefixEnd_2050170 701815088952232622764297 := by
  unfold tailWord_2050170
  simp only [CollatzResearch.WordTrace]
  refine ⟨18693960745647926501236991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49850561988394470669965309 18693960745647926501236991)
  ·
    refine ⟨28040941118471889751855487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18693960745647926501236991 28040941118471889751855487)
    ·
      refine ⟨42061411677707834627783231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28040941118471889751855487 42061411677707834627783231)
      ·
        refine ⟨63092117516561751941674847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42061411677707834627783231 63092117516561751941674847)
        ·
          refine ⟨94638176274842627912512271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63092117516561751941674847 94638176274842627912512271)
          ·
            refine ⟨141957264412263941868768407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94638176274842627912512271 141957264412263941868768407)
            ·
              refine ⟨212935896618395912803152611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141957264412263941868768407 212935896618395912803152611)
              ·
                refine ⟨319403844927593869204728917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212935896618395912803152611 319403844927593869204728917)
                ·
                  refine ⟨3743013807745240654742917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 319403844927593869204728917 3743013807745240654742917)
                  ·
                    refine ⟨701815088952232622764297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3743013807745240654742917 701815088952232622764297)
                    ·
                      rfl

theorem cell22_2050170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_2050170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050170 prefixEnd_2050170 := by exact prefixLift 2050170
  have htrace : WordTrace (prefixWord ++ tailWord_2050170) baseStart_2050170 baseEnd_2050170 := by
    simpa [prefixWord, tailWord_2050170, baseEnd_2050170] using wordTrace_append hprefix tailTrace_2050170
  have hstable : (prefixWord ++ tailWord_2050170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050170).length < 2 ^ (prefixWord ++ tailWord_2050170).sum := by decide
  have hdescent : baseEnd_2050170 < baseStart_2050170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050172 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 4, 3]
def baseStart_2050172 : Nat := 118140960795 + 2050172 * 2 ^ 59
def prefixEnd_2050172 : Nat := 4983230072969 + 3 ^ 40 * 2050172 * 2
def baseEnd_2050172 : Nat := 701815773593105284214291

theorem tailTrace_2050172 : CollatzResearch.WordTrace tailWord_2050172 prefixEnd_2050172 701815773593105284214291 := by
  unfold tailWord_2050172
  simp only [CollatzResearch.WordTrace]
  refine ⟨37387957964292230173260385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49850610619056306897680513 37387957964292230173260385)
  ·
    refine ⟨28040968473219172629945289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37387957964292230173260385 28040968473219172629945289)
    ·
      refine ⟨21030726354914379472458967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28040968473219172629945289 21030726354914379472458967)
      ·
        refine ⟨31546089532371569208688451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21030726354914379472458967 31546089532371569208688451)
        ·
          refine ⟨47319134298557353813032677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31546089532371569208688451 47319134298557353813032677)
          ·
            refine ⟨8872337680979503839943627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47319134298557353813032677 8872337680979503839943627)
            ·
              refine ⟨13308506521469255759915441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8872337680979503839943627 13308506521469255759915441)
              ·
                refine ⟨9981379891101941819936581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13308506521469255759915441 9981379891101941819936581)
                ·
                  refine ⟨1871508729581614091238109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9981379891101941819936581 1871508729581614091238109)
                  ·
                    refine ⟨701815773593105284214291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1871508729581614091238109 701815773593105284214291)
                    ·
                      rfl

theorem cell22_2050172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_2050172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050172 prefixEnd_2050172 := by exact prefixLift 2050172
  have htrace : WordTrace (prefixWord ++ tailWord_2050172) baseStart_2050172 baseEnd_2050172 := by
    simpa [prefixWord, tailWord_2050172, baseEnd_2050172] using wordTrace_append hprefix tailTrace_2050172
  have hstable : (prefixWord ++ tailWord_2050172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050172).length < 2 ^ (prefixWord ++ tailWord_2050172).sum := by decide
  have hdescent : baseEnd_2050172 < baseStart_2050172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050268 : List Nat := [2, 2, 5, 2, 1, 1, 1, 2, 3, 3]
def baseStart_2050268 : Nat := 118140960795 + 2050268 * 2 ^ 59
def prefixEnd_2050268 : Nat := 4983230072969 + 3 ^ 40 * 2050268 * 2
def baseEnd_2050268 : Nat := 701848636354993033813997

theorem tailTrace_2050268 : CollatzResearch.WordTrace tailWord_2050268 prefixEnd_2050268 701848636354993033813997 := by
  unfold tailWord_2050268
  simp only [CollatzResearch.WordTrace]
  refine ⟨37389708668118334371007729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49852944890824445828010305 37389708668118334371007729)
  ·
    refine ⟨28042281501088750778255797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37389708668118334371007729 28042281501088750778255797)
    ·
      refine ⟨2628963890727070385461481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28042281501088750778255797 2628963890727070385461481)
      ·
        refine ⟨1971722918045302789096111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2628963890727070385461481 1971722918045302789096111)
        ·
          refine ⟨2957584377067954183644167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1971722918045302789096111 2957584377067954183644167)
          ·
            refine ⟨4436376565601931275466251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957584377067954183644167 4436376565601931275466251)
            ·
              refine ⟨6654564848402896913199377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4436376565601931275466251 6654564848402896913199377)
              ·
                refine ⟨4990923636302172684899533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6654564848402896913199377 4990923636302172684899533)
                ·
                  refine ⟨1871596363613314756837325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4990923636302172684899533 1871596363613314756837325)
                  ·
                    refine ⟨701848636354993033813997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1871596363613314756837325 701848636354993033813997)
                    ·
                      rfl

theorem cell22_2050268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_2050268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050268 prefixEnd_2050268 := by exact prefixLift 2050268
  have htrace : WordTrace (prefixWord ++ tailWord_2050268) baseStart_2050268 baseEnd_2050268 := by
    simpa [prefixWord, tailWord_2050268, baseEnd_2050268] using wordTrace_append hprefix tailTrace_2050268
  have hstable : (prefixWord ++ tailWord_2050268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050268).length < 2 ^ (prefixWord ++ tailWord_2050268).sum := by decide
  have hdescent : baseEnd_2050268 < baseStart_2050268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050354 : List Nat := [3, 2, 1, 1, 5, 2, 8]
def baseStart_2050354 : Nat := 118140960795 + 2050354 * 2 ^ 59
def prefixEnd_2050354 : Nat := 4983230072969 + 3 ^ 40 * 2050354 * 2
def baseEnd_2050354 : Nat := 25995484293056202820879

theorem tailTrace_2050354 : CollatzResearch.WordTrace tailWord_2050354 prefixEnd_2050354 25995484293056202820879 := by
  unfold tailWord_2050354
  simp only [CollatzResearch.WordTrace]
  refine ⟨18695638503481276357411529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49855036009283403619764077 18695638503481276357411529)
  ·
    refine ⟨14021728877610957268058647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18695638503481276357411529 14021728877610957268058647)
    ·
      refine ⟨21032593316416435902087971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14021728877610957268058647 21032593316416435902087971)
      ·
        refine ⟨31548889974624653853131957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21032593316416435902087971 31548889974624653853131957)
        ·
          refine ⟨2957708435121061298731121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31548889974624653853131957 2957708435121061298731121)
          ·
            refine ⟨2218281326340795974048341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2957708435121061298731121 2218281326340795974048341)
            ·
              refine ⟨25995484293056202820879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2218281326340795974048341 25995484293056202820879)
              ·
                rfl

theorem cell22_2050354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 8].length) (baseStart_2050354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050354 prefixEnd_2050354 := by exact prefixLift 2050354
  have htrace : WordTrace (prefixWord ++ tailWord_2050354) baseStart_2050354 baseEnd_2050354 := by
    simpa [prefixWord, tailWord_2050354, baseEnd_2050354] using wordTrace_append hprefix tailTrace_2050354
  have hstable : (prefixWord ++ tailWord_2050354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050354).length < 2 ^ (prefixWord ++ tailWord_2050354).sum := by decide
  have hdescent : baseEnd_2050354 < baseStart_2050354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050356 : List Nat := [2, 5, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_2050356 : Nat := 118140960795 + 2050356 * 2 ^ 59
def prefixEnd_2050356 : Nat := 4983230072969 + 3 ^ 40 * 2050356 * 2
def baseEnd_2050356 : Nat := 701878760553390137613727

theorem tailTrace_2050356 : CollatzResearch.WordTrace tailWord_2050356 prefixEnd_2050356 701878760553390137613727 := by
  unfold tailWord_2050356
  simp only [CollatzResearch.WordTrace]
  refine ⟨37391313479958929885609461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49855084639945239847479281 37391313479958929885609461)
  ·
    refine ⟨3505435638746149676775887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37391313479958929885609461 3505435638746149676775887)
    ·
      refine ⟨5258153458119224515163831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3505435638746149676775887 5258153458119224515163831)
      ·
        refine ⟨7887230187178836772745747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5258153458119224515163831 7887230187178836772745747)
        ·
          refine ⟨11830845280768255159118621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7887230187178836772745747 11830845280768255159118621)
          ·
            refine ⟨4436566980288095684669483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11830845280768255159118621 4436566980288095684669483)
            ·
              refine ⟨6654850470432143527004225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4436566980288095684669483 6654850470432143527004225)
              ·
                refine ⟨4991137852824107645253169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6654850470432143527004225 4991137852824107645253169)
                ·
                  refine ⟨3743353389618080733939877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4991137852824107645253169 3743353389618080733939877)
                  ·
                    refine ⟨701878760553390137613727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3743353389618080733939877 701878760553390137613727)
                    ·
                      rfl

theorem cell22_2050356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_2050356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050356 prefixEnd_2050356 := by exact prefixLift 2050356
  have htrace : WordTrace (prefixWord ++ tailWord_2050356) baseStart_2050356 baseEnd_2050356 := by
    simpa [prefixWord, tailWord_2050356, baseEnd_2050356] using wordTrace_append hprefix tailTrace_2050356
  have hstable : (prefixWord ++ tailWord_2050356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050356).length < 2 ^ (prefixWord ++ tailWord_2050356).sum := by decide
  have hdescent : baseEnd_2050356 < baseStart_2050356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050367 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 2, 6]
def baseStart_2050367 : Nat := 118140960795 + 2050367 * 2 ^ 59
def prefixEnd_2050367 : Nat := 4983230072969 + 3 ^ 40 * 2050367 * 2
def baseEnd_2050367 : Nat := 701882526078189775588693

theorem tailTrace_2050367 : CollatzResearch.WordTrace tailWord_2050367 prefixEnd_2050367 701882526078189775588693 := by
  unfold tailWord_2050367
  simp only [CollatzResearch.WordTrace]
  refine ⟨74783028162878008649869355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49855352108585339099912903 74783028162878008649869355)
  ·
    refine ⟨112174542244317012974804033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74783028162878008649869355 112174542244317012974804033)
    ·
      refine ⟨84130906683237759731103025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112174542244317012974804033 84130906683237759731103025)
      ·
        refine ⟨63098180012428319798327269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84130906683237759731103025 63098180012428319798327269)
        ·
          refine ⟨11830908752330309962186363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63098180012428319798327269 11830908752330309962186363)
          ·
            refine ⟨17746363128495464943279545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11830908752330309962186363 17746363128495464943279545)
            ·
              refine ⟨13309772346371598707459659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17746363128495464943279545 13309772346371598707459659)
              ·
                refine ⟨19964658519557398061189489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13309772346371598707459659 19964658519557398061189489)
                ·
                  refine ⟨14973493889668048545892117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19964658519557398061189489 14973493889668048545892117)
                  ·
                    refine ⟨701882526078189775588693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14973493889668048545892117 701882526078189775588693)
                    ·
                      rfl

theorem cell22_2050367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_2050367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050367 prefixEnd_2050367 := by exact prefixLift 2050367
  have htrace : WordTrace (prefixWord ++ tailWord_2050367) baseStart_2050367 baseEnd_2050367 := by
    simpa [prefixWord, tailWord_2050367, baseEnd_2050367] using wordTrace_append hprefix tailTrace_2050367
  have hstable : (prefixWord ++ tailWord_2050367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050367).length < 2 ^ (prefixWord ++ tailWord_2050367).sum := by decide
  have hdescent : baseEnd_2050367 < baseStart_2050367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050382 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 9]
def baseStart_2050382 : Nat := 118140960795 + 2050382 * 2 ^ 59
def prefixEnd_2050382 : Nat := 4983230072969 + 3 ^ 40 * 2050382 * 2
def baseEnd_2050382 : Nat := 233962553628244912154549

theorem tailTrace_2050382 : CollatzResearch.WordTrace tailWord_2050382 prefixEnd_2050382 233962553628244912154549 := by
  unfold tailWord_2050382
  simp only [CollatzResearch.WordTrace]
  refine ⟨9347946907227958276458175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49855716838549110807776933 9347946907227958276458175)
  ·
    refine ⟨14021920360841937414687263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9347946907227958276458175 14021920360841937414687263)
    ·
      refine ⟨21032880541262906122030895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14021920360841937414687263 21032880541262906122030895)
      ·
        refine ⟨31549320811894359183046343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21032880541262906122030895 31549320811894359183046343)
        ·
          refine ⟨47323981217841538774569515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31549320811894359183046343 47323981217841538774569515)
          ·
            refine ⟨70985971826762308161854273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47323981217841538774569515 70985971826762308161854273)
            ·
              refine ⟨53239478870071731121390705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70985971826762308161854273 53239478870071731121390705)
              ·
                refine ⟨39929609152553798341043029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53239478870071731121390705 39929609152553798341043029)
                ·
                  refine ⟨233962553628244912154549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39929609152553798341043029 233962553628244912154549)
                  ·
                    rfl

theorem cell22_2050382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_2050382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050382 prefixEnd_2050382 := by exact prefixLift 2050382
  have htrace : WordTrace (prefixWord ++ tailWord_2050382) baseStart_2050382 baseEnd_2050382 := by
    simpa [prefixWord, tailWord_2050382, baseEnd_2050382] using wordTrace_append hprefix tailTrace_2050382
  have hstable : (prefixWord ++ tailWord_2050382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050382).length < 2 ^ (prefixWord ++ tailWord_2050382).sum := by decide
  have hdescent : baseEnd_2050382 < baseStart_2050382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050429 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 3, 4]
def baseStart_2050429 : Nat := 118140960795 + 2050429 * 2 ^ 59
def prefixEnd_2050429 : Nat := 4983230072969 + 3 ^ 40 * 2050429 * 2
def baseEnd_2050429 : Nat := 701903749945242280538503

theorem tailTrace_2050429 : CollatzResearch.WordTrace tailWord_2050429 prefixEnd_2050429 701903749945242280538503 := by
  unfold tailWord_2050429
  simp only [CollatzResearch.WordTrace]
  refine ⟨74785289488653393238626341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49856859659102262159084227 74785289488653393238626341)
  ·
    refine ⟨14022241779122511232242439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74785289488653393238626341 14022241779122511232242439)
    ·
      refine ⟨21033362668683766848363659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14022241779122511232242439 21033362668683766848363659)
      ·
        refine ⟨31550044003025650272545489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21033362668683766848363659 31550044003025650272545489)
        ·
          refine ⟨23662533002269237704409117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31550044003025650272545489 23662533002269237704409117)
          ·
            refine ⟨8873449875850964139153419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23662533002269237704409117 8873449875850964139153419)
            ·
              refine ⟨13310174813776446208730129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8873449875850964139153419 13310174813776446208730129)
              ·
                refine ⟨9982631110332334656547597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13310174813776446208730129 9982631110332334656547597)
                ·
                  refine ⟨3743486666374625496205349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9982631110332334656547597 3743486666374625496205349)
                  ·
                    refine ⟨701903749945242280538503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3743486666374625496205349 701903749945242280538503)
                    ·
                      rfl

theorem cell22_2050429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_2050429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050429 prefixEnd_2050429 := by exact prefixLift 2050429
  have htrace : WordTrace (prefixWord ++ tailWord_2050429) baseStart_2050429 baseEnd_2050429 := by
    simpa [prefixWord, tailWord_2050429, baseEnd_2050429] using wordTrace_append hprefix tailTrace_2050429
  have hstable : (prefixWord ++ tailWord_2050429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050429).length < 2 ^ (prefixWord ++ tailWord_2050429).sum := by decide
  have hdescent : baseEnd_2050429 < baseStart_2050429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050444 : List Nat := [2, 2, 1, 2, 1, 5, 1, 2, 6]
def baseStart_2050444 : Nat := 118140960795 + 2050444 * 2 ^ 59
def prefixEnd_2050444 : Nat := 4983230072969 + 3 ^ 40 * 2050444 * 2
def baseEnd_2050444 : Nat := 233969628250595747137819

theorem tailTrace_2050444 : CollatzResearch.WordTrace tailWord_2050444 prefixEnd_2050444 233969628250595747137819 := by
  unfold tailWord_2050444
  simp only [CollatzResearch.WordTrace]
  refine ⟨37392918291799525400211193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49857224389066033866948257 37392918291799525400211193)
  ·
    refine ⟨28044688718849644050158395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37392918291799525400211193 28044688718849644050158395)
    ·
      refine ⟨42067033078274466075237593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28044688718849644050158395 42067033078274466075237593)
      ·
        refine ⟨31550274808705849556428195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42067033078274466075237593 31550274808705849556428195)
        ·
          refine ⟨47325412213058774334642293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31550274808705849556428195 47325412213058774334642293)
          ·
            refine ⟨4436757394974260093872715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47325412213058774334642293 4436757394974260093872715)
            ·
              refine ⟨6655136092461390140809073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4436757394974260093872715 6655136092461390140809073)
              ·
                refine ⟨4991352069346042605606805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6655136092461390140809073 4991352069346042605606805)
                ·
                  refine ⟨233969628250595747137819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4991352069346042605606805 233969628250595747137819)
                  ·
                    rfl

theorem cell22_2050444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_2050444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050444 prefixEnd_2050444 := by exact prefixLift 2050444
  have htrace : WordTrace (prefixWord ++ tailWord_2050444) baseStart_2050444 baseEnd_2050444 := by
    simpa [prefixWord, tailWord_2050444, baseEnd_2050444] using wordTrace_append hprefix tailTrace_2050444
  have hstable : (prefixWord ++ tailWord_2050444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050444).length < 2 ^ (prefixWord ++ tailWord_2050444).sum := by decide
  have hdescent : baseEnd_2050444 < baseStart_2050444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050446 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 3, 4]
def baseStart_2050446 : Nat := 118140960795 + 2050446 * 2 ^ 59
def prefixEnd_2050446 : Nat := 4983230072969 + 3 ^ 40 * 2050446 * 2
def baseEnd_2050446 : Nat := 701909569392659902863451

theorem tailTrace_2050446 : CollatzResearch.WordTrace tailWord_2050446 prefixEnd_2050446 701909569392659902863451 := by
  unfold tailWord_2050446
  simp only [CollatzResearch.WordTrace]
  refine ⟨9348238691198975642749399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49857273019727870094663461 9348238691198975642749399)
  ·
    refine ⟨14022358036798463464124099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9348238691198975642749399 14022358036798463464124099)
    ·
      refine ⟨21033537055197695196186149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14022358036798463464124099 21033537055197695196186149)
      ·
        refine ⟨3943788197849567849284903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21033537055197695196186149 3943788197849567849284903)
        ·
          refine ⟨5915682296774351773927355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3943788197849567849284903 5915682296774351773927355)
          ·
            refine ⟨8873523445161527660891033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5915682296774351773927355 8873523445161527660891033)
            ·
              refine ⟨6655142583871145745668275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8873523445161527660891033 6655142583871145745668275)
              ·
                refine ⟨9982713875806718618502413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6655142583871145745668275 9982713875806718618502413)
                ·
                  refine ⟨3743517703427519481938405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9982713875806718618502413 3743517703427519481938405)
                  ·
                    refine ⟨701909569392659902863451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3743517703427519481938405 701909569392659902863451)
                    ·
                      rfl

theorem cell22_2050446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_2050446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050446 prefixEnd_2050446 := by exact prefixLift 2050446
  have htrace : WordTrace (prefixWord ++ tailWord_2050446) baseStart_2050446 baseEnd_2050446 := by
    simpa [prefixWord, tailWord_2050446, baseEnd_2050446] using wordTrace_append hprefix tailTrace_2050446
  have hstable : (prefixWord ++ tailWord_2050446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050446).length < 2 ^ (prefixWord ++ tailWord_2050446).sum := by decide
  have hdescent : baseEnd_2050446 < baseStart_2050446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050497 : List Nat := [1, 2, 7, 1, 1, 1, 2, 2, 1, 4]
def baseStart_2050497 : Nat := 118140960795 + 2050497 * 2 ^ 59
def prefixEnd_2050497 : Nat := 4983230072969 + 3 ^ 40 * 2050497 * 2
def baseEnd_2050497 : Nat := 701927027734912769838295

theorem tailTrace_2050497 : CollatzResearch.WordTrace tailWord_2050497 prefixEnd_2050497 701927027734912769838295 := by
  unfold tailWord_2050497
  simp only [CollatzResearch.WordTrace]
  refine ⟨74787769652407040852101745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49858513101604693901401163 74787769652407040852101745)
  ·
    refine ⟨56090827239305280639076309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74787769652407040852101745 56090827239305280639076309)
    ·
      refine ⟨1314628763421217514978351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 56090827239305280639076309 1314628763421217514978351)
      ·
        refine ⟨1971943145131826272467527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1314628763421217514978351 1971943145131826272467527)
        ·
          refine ⟨2957914717697739408701291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1971943145131826272467527 2957914717697739408701291)
          ·
            refine ⟨4436872076546609113051937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957914717697739408701291 4436872076546609113051937)
            ·
              refine ⟨3327654057409956834788953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4436872076546609113051937 3327654057409956834788953)
              ·
                refine ⟨2495740543057467626091715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3327654057409956834788953 2495740543057467626091715)
                ·
                  refine ⟨3743610814586201439137573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2495740543057467626091715 3743610814586201439137573)
                  ·
                    refine ⟨701927027734912769838295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3743610814586201439137573 701927027734912769838295)
                    ·
                      rfl

theorem cell22_2050497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_2050497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050497 prefixEnd_2050497 := by exact prefixLift 2050497
  have htrace : WordTrace (prefixWord ++ tailWord_2050497) baseStart_2050497 baseEnd_2050497 := by
    simpa [prefixWord, tailWord_2050497, baseEnd_2050497] using wordTrace_append hprefix tailTrace_2050497
  have hstable : (prefixWord ++ tailWord_2050497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050497).length < 2 ^ (prefixWord ++ tailWord_2050497).sum := by decide
  have hdescent : baseEnd_2050497 < baseStart_2050497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050538 : List Nat := [3, 1, 3, 1, 3, 1, 3, 1, 3, 3]
def baseStart_2050538 : Nat := 118140960795 + 2050538 * 2 ^ 59
def prefixEnd_2050538 : Nat := 4983230072969 + 3 ^ 40 * 2050538 * 2
def baseEnd_2050538 : Nat := 701941062872802329563169

theorem tailTrace_2050538 : CollatzResearch.WordTrace tailWord_2050538 prefixEnd_2050538 701941062872802329563169 := by
  unfold tailWord_2050538
  simp only [CollatzResearch.WordTrace]
  refine ⟨18697316261314626213586067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49859510030172336569562845 18697316261314626213586067)
  ·
    refine ⟨28045974391971939320379101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18697316261314626213586067 28045974391971939320379101)
    ·
      refine ⟨10517240396989477245142163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28045974391971939320379101 10517240396989477245142163)
      ·
        refine ⟨15775860595484215867713245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10517240396989477245142163 15775860595484215867713245)
        ·
          refine ⟨5915947723306580950392467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15775860595484215867713245 5915947723306580950392467)
          ·
            refine ⟨8873921584959871425588701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5915947723306580950392467 8873921584959871425588701)
            ·
              refine ⟨3327720594359951784595763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8873921584959871425588701 3327720594359951784595763)
              ·
                refine ⟨4991580891539927676893645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3327720594359951784595763 4991580891539927676893645)
                ·
                  refine ⟨1871842834327472878835117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4991580891539927676893645 1871842834327472878835117)
                  ·
                    refine ⟨701941062872802329563169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1871842834327472878835117 701941062872802329563169)
                    ·
                      rfl

theorem cell22_2050538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_2050538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050538 prefixEnd_2050538 := by exact prefixLift 2050538
  have htrace : WordTrace (prefixWord ++ tailWord_2050538) baseStart_2050538 baseEnd_2050538 := by
    simpa [prefixWord, tailWord_2050538, baseEnd_2050538] using wordTrace_append hprefix tailTrace_2050538
  have hstable : (prefixWord ++ tailWord_2050538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050538).length < 2 ^ (prefixWord ++ tailWord_2050538).sum := by decide
  have hdescent : baseEnd_2050538 < baseStart_2050538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050611 : List Nat := [1, 1, 1, 2, 4, 2, 4, 1, 1, 5]
def baseStart_2050611 : Nat := 118140960795 + 2050611 * 2 ^ 59
def prefixEnd_2050611 : Nat := 4983230072969 + 3 ^ 40 * 2050611 * 2
def baseEnd_2050611 : Nat := 701966052264654472487945

theorem tailTrace_2050611 : CollatzResearch.WordTrace tailWord_2050611 prefixEnd_2050611 701966052264654472487945 := by
  unfold tailWord_2050611
  simp only [CollatzResearch.WordTrace]
  refine ⟨74791927573994038321751687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49861285049329358881167791 74791927573994038321751687)
  ·
    refine ⟨112187891360991057482627531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74791927573994038321751687 112187891360991057482627531)
    ·
      refine ⟨168281837041486586223941297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112187891360991057482627531 168281837041486586223941297)
      ·
        refine ⟨126211377781114939667955973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168281837041486586223941297 126211377781114939667955973)
        ·
          refine ⟨23664633333959051187741745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126211377781114939667955973 23664633333959051187741745)
          ·
            refine ⟨17748475000469288390806309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23664633333959051187741745 17748475000469288390806309)
            ·
              refine ⟨3327839062587991573276183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17748475000469288390806309 3327839062587991573276183)
              ·
                refine ⟨4991758593881987359914275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3327839062587991573276183 4991758593881987359914275)
                ·
                  refine ⟨7487637890822981039871413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4991758593881987359914275 7487637890822981039871413)
                  ·
                    refine ⟨701966052264654472487945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7487637890822981039871413 701966052264654472487945)
                    ·
                      rfl

theorem cell22_2050611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 5].length) (baseStart_2050611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2050611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2050611 prefixEnd_2050611 := by exact prefixLift 2050611
  have htrace : WordTrace (prefixWord ++ tailWord_2050611) baseStart_2050611 baseEnd_2050611 := by
    simpa [prefixWord, tailWord_2050611, baseEnd_2050611] using wordTrace_append hprefix tailTrace_2050611
  have hstable : (prefixWord ++ tailWord_2050611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050611).length < 2 ^ (prefixWord ++ tailWord_2050611).sum := by decide
  have hdescent : baseEnd_2050611 < baseStart_2050611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
