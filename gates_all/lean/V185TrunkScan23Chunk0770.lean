import V185TrunkScan23Chunk0769

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4554007 : List Nat := [1, 1, 3, 4, 1, 1, 1, 5, 1, 1, 4]
def baseStart_4554007 : Nat := 118140960795 + 4554007 * 2 ^ 59
def prefixEnd_4554007 : Nat := 4983230072969 + 3 ^ 40 * 4554007 * 2
def baseEnd_4554007 : Nat := 2338394494939869160369009

theorem tailTrace_4554007 : CollatzResearch.WordTrace tailWord_4554007 prefixEnd_4554007 2338394494939869160369009 := by
  unfold tailWord_4554007
  simp only [CollatzResearch.WordTrace]
  refine ⟨166098280812617876319876275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110732187208411917546584183 166098280812617876319876275)
  ·
    refine ⟨249147421218926814479814413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166098280812617876319876275 249147421218926814479814413)
    ·
      refine ⟨93430282957097555429930405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249147421218926814479814413 93430282957097555429930405)
      ·
        refine ⟨17518178054455791643111951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93430282957097555429930405 17518178054455791643111951)
        ·
          refine ⟨26277267081683687464667927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17518178054455791643111951 26277267081683687464667927)
          ·
            refine ⟨39415900622525531197001891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26277267081683687464667927 39415900622525531197001891)
            ·
              refine ⟨59123850933788296795502837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39415900622525531197001891 59123850933788296795502837)
              ·
                refine ⟨5542861025042652824578391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59123850933788296795502837 5542861025042652824578391)
                ·
                  refine ⟨8314291537563979236867587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5542861025042652824578391 8314291537563979236867587)
                  ·
                    refine ⟨12471437306345968855301381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8314291537563979236867587 12471437306345968855301381)
                    ·
                      refine ⟨2338394494939869160369009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12471437306345968855301381 2338394494939869160369009)
                      ·
                        rfl

theorem cell23_4554007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_4554007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554007 prefixEnd_4554007 := by exact prefixLift 4554007
  have htrace : WordTrace (prefixWord ++ tailWord_4554007) baseStart_4554007 baseEnd_4554007 := by
    simpa [prefixWord, tailWord_4554007, baseEnd_4554007] using wordTrace_append hprefix tailTrace_4554007
  have hstable : (prefixWord ++ tailWord_4554007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554007).length < 2 ^ (prefixWord ++ tailWord_4554007).sum := by decide
  have hdescent : baseEnd_4554007 < baseStart_4554007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554017 : List Nat := [1, 2, 3, 2, 1, 1, 1, 6, 2, 4]
def baseStart_4554017 : Nat := 118140960795 + 4554017 * 2 ^ 59
def prefixEnd_4554017 : Nat := 4983230072969 + 3 ^ 40 * 4554017 * 2
def baseEnd_4554017 : Nat := 779466543248804707081321

theorem tailTrace_4554017 : CollatzResearch.WordTrace tailWord_4554017 prefixEnd_4554017 779466543248804707081321 := by
  unfold tailWord_4554017
  simp only [CollatzResearch.WordTrace]
  refine ⟨166098645542581648027740305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110732430361721098685160203 166098645542581648027740305)
  ·
    refine ⟨124573984156936236020805229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166098645542581648027740305 124573984156936236020805229)
    ·
      refine ⟨46715244058851088507801961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124573984156936236020805229 46715244058851088507801961)
      ·
        refine ⟨35036433044138316380851471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46715244058851088507801961 35036433044138316380851471)
        ·
          refine ⟨52554649566207474571277207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35036433044138316380851471 52554649566207474571277207)
          ·
            refine ⟨78831974349311211856915811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52554649566207474571277207 78831974349311211856915811)
            ·
              refine ⟨118247961523966817785373717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78831974349311211856915811 118247961523966817785373717)
              ·
                refine ⟨5542873196435944583689393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 118247961523966817785373717 5542873196435944583689393)
                ·
                  refine ⟨4157154897326958437767045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5542873196435944583689393 4157154897326958437767045)
                  ·
                    refine ⟨779466543248804707081321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4157154897326958437767045 779466543248804707081321)
                    ·
                      rfl

theorem cell23_4554017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_4554017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554017 prefixEnd_4554017 := by exact prefixLift 4554017
  have htrace : WordTrace (prefixWord ++ tailWord_4554017) baseStart_4554017 baseEnd_4554017 := by
    simpa [prefixWord, tailWord_4554017, baseEnd_4554017] using wordTrace_append hprefix tailTrace_4554017
  have hstable : (prefixWord ++ tailWord_4554017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554017).length < 2 ^ (prefixWord ++ tailWord_4554017).sum := by decide
  have hdescent : baseEnd_4554017 < baseStart_4554017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554018 : List Nat := [3, 3, 1, 1, 5, 1, 1, 1, 3, 1, 3]
def baseStart_4554018 : Nat := 118140960795 + 4554018 * 2 ^ 59
def prefixEnd_4554018 : Nat := 4983230072969 + 3 ^ 40 * 4554018 * 2
def baseEnd_4554018 : Nat := 2338400143227068617331459

theorem tailTrace_4554018 : CollatzResearch.WordTrace tailWord_4554018 prefixEnd_4554018 2338400143227068617331459 := by
  unfold tailWord_4554018
  simp only [CollatzResearch.WordTrace]
  refine ⟨41524670503894506299631677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110732454677052016799017805 41524670503894506299631677)
  ·
    refine ⟨15571751438960439862361879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41524670503894506299631677 15571751438960439862361879)
    ·
      refine ⟨23357627158440659793542819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15571751438960439862361879 23357627158440659793542819)
      ·
        refine ⟨35036440737660989690314229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23357627158440659793542819 35036440737660989690314229)
        ·
          refine ⟨3284666319155717783466959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35036440737660989690314229 3284666319155717783466959)
          ·
            refine ⟨4926999478733576675200439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3284666319155717783466959 4926999478733576675200439)
            ·
              refine ⟨7390499218100365012800659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4926999478733576675200439 7390499218100365012800659)
              ·
                refine ⟨11085748827150547519200989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7390499218100365012800659 11085748827150547519200989)
                ·
                  refine ⟨4157155810181455319700371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11085748827150547519200989 4157155810181455319700371)
                  ·
                    refine ⟨6235733715272182979550557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4157155810181455319700371 6235733715272182979550557)
                    ·
                      refine ⟨2338400143227068617331459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6235733715272182979550557 2338400143227068617331459)
                      ·
                        rfl

theorem cell23_4554018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_4554018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554018 prefixEnd_4554018 := by exact prefixLift 4554018
  have htrace : WordTrace (prefixWord ++ tailWord_4554018) baseStart_4554018 baseEnd_4554018 := by
    simpa [prefixWord, tailWord_4554018, baseEnd_4554018] using wordTrace_append hprefix tailTrace_4554018
  have hstable : (prefixWord ++ tailWord_4554018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554018).length < 2 ^ (prefixWord ++ tailWord_4554018).sum := by decide
  have hdescent : baseEnd_4554018 < baseStart_4554018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554020 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 3, 1, 6]
def baseStart_4554020 : Nat := 118140960795 + 4554020 * 2 ^ 59
def prefixEnd_4554020 : Nat := 4983230072969 + 3 ^ 40 * 4554020 * 2
def baseEnd_4554020 : Nat := 2338401170188377609506449

theorem tailTrace_4554020 : CollatzResearch.WordTrace tailWord_4554020 prefixEnd_4554020 2338401170188377609506449 := by
  unfold tailWord_4554020
  simp only [CollatzResearch.WordTrace]
  refine ⟨83049377480785389770049757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110732503307713853026733009 83049377480785389770049757)
  ·
    refine ⟨31143516555294521163768659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83049377480785389770049757 31143516555294521163768659)
    ·
      refine ⟨46715274832941781745652989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31143516555294521163768659 46715274832941781745652989)
      ·
        refine ⟨17518228062353168154619871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46715274832941781745652989 17518228062353168154619871)
        ·
          refine ⟨26277342093529752231929807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17518228062353168154619871 26277342093529752231929807)
          ·
            refine ⟨39416013140294628347894711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26277342093529752231929807 39416013140294628347894711)
            ·
              refine ⟨59124019710441942521842067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39416013140294628347894711 59124019710441942521842067)
              ·
                refine ⟨88686029565662913782763101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59124019710441942521842067 88686029565662913782763101)
                ·
                  refine ⟨33257261087123592668536163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88686029565662913782763101 33257261087123592668536163)
                  ·
                    refine ⟨49885891630685389002804245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33257261087123592668536163 49885891630685389002804245)
                    ·
                      refine ⟨2338401170188377609506449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49885891630685389002804245 2338401170188377609506449)
                      ·
                        rfl

theorem cell23_4554020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_4554020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554020 prefixEnd_4554020 := by exact prefixLift 4554020
  have htrace : WordTrace (prefixWord ++ tailWord_4554020) baseStart_4554020 baseEnd_4554020 := by
    simpa [prefixWord, tailWord_4554020, baseEnd_4554020] using wordTrace_append hprefix tailTrace_4554020
  have hstable : (prefixWord ++ tailWord_4554020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554020).length < 2 ^ (prefixWord ++ tailWord_4554020).sum := by decide
  have hdescent : baseEnd_4554020 < baseStart_4554020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554034 : List Nat := [3, 2, 1, 1, 4, 2, 1, 3, 2, 4]
def baseStart_4554034 : Nat := 118140960795 + 4554034 * 2 ^ 59
def prefixEnd_4554034 : Nat := 4983230072969 + 3 ^ 40 * 4554034 * 2
def baseEnd_4554034 : Nat := 779469452972513518243795

theorem tailTrace_4554034 : CollatzResearch.WordTrace tailWord_4554034 prefixEnd_4554034 779469452972513518243795 := by
  unfold tailWord_4554034
  simp only [CollatzResearch.WordTrace]
  refine ⟨41524816395880014982777289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110732843722346706620739437 41524816395880014982777289)
  ·
    refine ⟨31143612296910011237082967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41524816395880014982777289 31143612296910011237082967)
    ·
      refine ⟨46715418445365016855624451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31143612296910011237082967 46715418445365016855624451)
      ·
        refine ⟨70073127668047525283436677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46715418445365016855624451 70073127668047525283436677)
        ·
          refine ⟨13138711437758910990644377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70073127668047525283436677 13138711437758910990644377)
          ·
            refine ⟨9854033578319183242983283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13138711437758910990644377 9854033578319183242983283)
            ·
              refine ⟨14781050367478774864474925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9854033578319183242983283 14781050367478774864474925)
              ·
                refine ⟨5542893887804540574178097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14781050367478774864474925 5542893887804540574178097)
                ·
                  refine ⟨4157170415853405430633573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5542893887804540574178097 4157170415853405430633573)
                  ·
                    refine ⟨779469452972513518243795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4157170415853405430633573 779469452972513518243795)
                    ·
                      rfl

theorem cell23_4554034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_4554034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554034 prefixEnd_4554034 := by exact prefixLift 4554034
  have htrace : WordTrace (prefixWord ++ tailWord_4554034) baseStart_4554034 baseEnd_4554034 := by
    simpa [prefixWord, tailWord_4554034, baseEnd_4554034] using wordTrace_append hprefix tailTrace_4554034
  have hstable : (prefixWord ++ tailWord_4554034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554034).length < 2 ^ (prefixWord ++ tailWord_4554034).sum := by decide
  have hdescent : baseEnd_4554034 < baseStart_4554034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554038 : List Nat := [5, 1, 2, 3, 1, 2, 1, 2, 1, 5]
def baseStart_4554038 : Nat := 118140960795 + 4554038 * 2 ^ 59
def prefixEnd_4554038 : Nat := 4983230072969 + 3 ^ 40 * 4554038 * 2
def baseEnd_4554038 : Nat := 779470137613386179693789

theorem tailTrace_4554038 : CollatzResearch.WordTrace tailWord_4554038 prefixEnd_4554038 779470137613386179693789 := by
  unfold tailWord_4554038
  simp only [CollatzResearch.WordTrace]
  refine ⟨10381213217219098038390923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110732940983670379076169845 10381213217219098038390923)
  ·
    refine ⟨15571819825828647057586385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10381213217219098038390923 15571819825828647057586385)
    ·
      refine ⟨11678864869371485293189789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15571819825828647057586385 11678864869371485293189789)
      ·
        refine ⟨4379574326014306984946171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11678864869371485293189789 4379574326014306984946171)
        ·
          refine ⟨6569361489021460477419257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4379574326014306984946171 6569361489021460477419257)
          ·
            refine ⟨4927021116766095358064443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6569361489021460477419257 4927021116766095358064443)
            ·
              refine ⟨7390531675149143037096665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4927021116766095358064443 7390531675149143037096665)
              ·
                refine ⟨5542898756361857277822499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7390531675149143037096665 5542898756361857277822499)
                ·
                  refine ⟨8314348134542785916733749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5542898756361857277822499 8314348134542785916733749)
                  ·
                    refine ⟨779470137613386179693789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8314348134542785916733749 779470137613386179693789)
                    ·
                      rfl

theorem cell23_4554038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_4554038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554038 prefixEnd_4554038 := by exact prefixLift 4554038
  have htrace : WordTrace (prefixWord ++ tailWord_4554038) baseStart_4554038 baseEnd_4554038 := by
    simpa [prefixWord, tailWord_4554038, baseEnd_4554038] using wordTrace_append hprefix tailTrace_4554038
  have hstable : (prefixWord ++ tailWord_4554038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554038).length < 2 ^ (prefixWord ++ tailWord_4554038).sum := by decide
  have hdescent : baseEnd_4554038 < baseStart_4554038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554041 : List Nat := [1, 2, 1, 6, 2, 2, 1, 2, 1, 1, 4]
def baseStart_4554041 : Nat := 118140960795 + 4554041 * 2 ^ 59
def prefixEnd_4554041 : Nat := 4983230072969 + 3 ^ 40 * 4554041 * 2
def baseEnd_4554041 : Nat := 2338411953282122027343853

theorem tailTrace_4554041 : CollatzResearch.WordTrace tailWord_4554041 prefixEnd_4554041 2338411953282122027343853 := by
  unfold tailWord_4554041
  simp only [CollatzResearch.WordTrace]
  refine ⟨166099520894494700126613977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110733013929663133417742651 166099520894494700126613977)
  ·
    refine ⟨124574640670871025094960483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166099520894494700126613977 124574640670871025094960483)
    ·
      refine ⟨186861961006306537642440725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124574640670871025094960483 186861961006306537642440725)
      ·
        refine ⟨8759154422170618951989409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 186861961006306537642440725 8759154422170618951989409)
        ·
          refine ⟨6569365816627964213992057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8759154422170618951989409 6569365816627964213992057)
          ·
            refine ⟨4927024362470973160494043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6569365816627964213992057 4927024362470973160494043)
            ·
              refine ⟨7390536543706459740741065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4927024362470973160494043 7390536543706459740741065)
              ·
                refine ⟨5542902407779844805555799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7390536543706459740741065 5542902407779844805555799)
                ·
                  refine ⟨8314353611669767208333699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5542902407779844805555799 8314353611669767208333699)
                  ·
                    refine ⟨12471530417504650812500549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8314353611669767208333699 12471530417504650812500549)
                    ·
                      refine ⟨2338411953282122027343853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12471530417504650812500549 2338411953282122027343853)
                      ·
                        rfl

theorem cell23_4554041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_4554041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554041 prefixEnd_4554041 := by exact prefixLift 4554041
  have htrace : WordTrace (prefixWord ++ tailWord_4554041) baseStart_4554041 baseEnd_4554041 := by
    simpa [prefixWord, tailWord_4554041, baseEnd_4554041] using wordTrace_append hprefix tailTrace_4554041
  have hstable : (prefixWord ++ tailWord_4554041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554041).length < 2 ^ (prefixWord ++ tailWord_4554041).sum := by decide
  have hdescent : baseEnd_4554041 < baseStart_4554041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554044 : List Nat := [2, 2, 2, 2, 1, 3, 3, 2, 1, 2, 3]
def baseStart_4554044 : Nat := 118140960795 + 4554044 * 2 ^ 59
def prefixEnd_4554044 : Nat := 4983230072969 + 3 ^ 40 * 4554044 * 2
def baseEnd_4554044 : Nat := 2338413493724085515606339

theorem tailTrace_4554044 : CollatzResearch.WordTrace tailWord_4554044 prefixEnd_4554044 2338413493724085515606339 := by
  unfold tailWord_4554044
  simp only [CollatzResearch.WordTrace]
  refine ⟨83049815156741915819486593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110733086875655887759315457 83049815156741915819486593)
  ·
    refine ⟨62287361367556436864614945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83049815156741915819486593 62287361367556436864614945)
    ·
      refine ⟨46715521025667327648461209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62287361367556436864614945 46715521025667327648461209)
      ·
        refine ⟨35036640769250495736345907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46715521025667327648461209 35036640769250495736345907)
        ·
          refine ⟨52554961153875743604518861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35036640769250495736345907 52554961153875743604518861)
          ·
            refine ⟨19708110432703403851694573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52554961153875743604518861 19708110432703403851694573)
            ·
              refine ⟨7390541412263776444385465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19708110432703403851694573 7390541412263776444385465)
              ·
                refine ⟨5542906059197832333289099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7390541412263776444385465 5542906059197832333289099)
                ·
                  refine ⟨8314359088796748499933649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5542906059197832333289099 8314359088796748499933649)
                  ·
                    refine ⟨6235769316597561374950237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8314359088796748499933649 6235769316597561374950237)
                    ·
                      refine ⟨2338413493724085515606339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6235769316597561374950237 2338413493724085515606339)
                      ·
                        rfl

theorem cell23_4554044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_4554044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554044 prefixEnd_4554044 := by exact prefixLift 4554044
  have htrace : WordTrace (prefixWord ++ tailWord_4554044) baseStart_4554044 baseEnd_4554044 := by
    simpa [prefixWord, tailWord_4554044, baseEnd_4554044] using wordTrace_append hprefix tailTrace_4554044
  have hstable : (prefixWord ++ tailWord_4554044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554044).length < 2 ^ (prefixWord ++ tailWord_4554044).sum := by decide
  have hdescent : baseEnd_4554044 < baseStart_4554044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554057 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 6, 1, 3]
def baseStart_4554057 : Nat := 118140960795 + 4554057 * 2 ^ 59
def prefixEnd_4554057 : Nat := 4983230072969 + 3 ^ 40 * 4554057 * 2
def baseEnd_4554057 : Nat := 2338420168972593964743779

theorem tailTrace_4554057 : CollatzResearch.WordTrace tailWord_4554057 prefixEnd_4554057 2338420168972593964743779 := by
  unfold tailWord_4554057
  simp only [CollatzResearch.WordTrace]
  refine ⟨166100104462436734859196425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110733402974957823239464283 166100104462436734859196425)
  ·
    refine ⟨124575078346827551144397319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166100104462436734859196425 124575078346827551144397319)
    ·
      refine ⟨186862617520241326716595979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124575078346827551144397319 186862617520241326716595979)
      ·
        refine ⟨280293926280361990074893969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186862617520241326716595979 280293926280361990074893969)
        ·
          refine ⟨210220444710271492556170477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280293926280361990074893969 210220444710271492556170477)
          ·
            refine ⟨78832666766351809708563929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210220444710271492556170477 78832666766351809708563929)
            ·
              refine ⟨59124500074763857281422947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78832666766351809708563929 59124500074763857281422947)
              ·
                refine ⟨88686750112145785922134421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59124500074763857281422947 88686750112145785922134421)
                ·
                  refine ⟨4157191411506833715100051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88686750112145785922134421 4157191411506833715100051)
                  ·
                    refine ⟨6235787117260250572650077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4157191411506833715100051 6235787117260250572650077)
                    ·
                      refine ⟨2338420168972593964743779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6235787117260250572650077 2338420168972593964743779)
                      ·
                        rfl

theorem cell23_4554057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 1, 3].length) (baseStart_4554057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554057 prefixEnd_4554057 := by exact prefixLift 4554057
  have htrace : WordTrace (prefixWord ++ tailWord_4554057) baseStart_4554057 baseEnd_4554057 := by
    simpa [prefixWord, tailWord_4554057, baseEnd_4554057] using wordTrace_append hprefix tailTrace_4554057
  have hstable : (prefixWord ++ tailWord_4554057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554057).length < 2 ^ (prefixWord ++ tailWord_4554057).sum := by decide
  have hdescent : baseEnd_4554057 < baseStart_4554057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554074 : List Nat := [3, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3]
def baseStart_4554074 : Nat := 118140960795 + 4554074 * 2 ^ 59
def prefixEnd_4554074 : Nat := 4983230072969 + 3 ^ 40 * 4554074 * 2
def baseEnd_4554074 : Nat := 2338428898143720398231201

theorem tailTrace_4554074 : CollatzResearch.WordTrace tailWord_4554074 prefixEnd_4554074 2338428898143720398231201 := by
  unfold tailWord_4554074
  simp only [CollatzResearch.WordTrace]
  refine ⟨41525181125843786690641319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110733816335583431175043517 41525181125843786690641319)
  ·
    refine ⟨62287771688765680035961979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41525181125843786690641319 62287771688765680035961979)
    ·
      refine ⟨93431657533148520053942969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62287771688765680035961979 93431657533148520053942969)
      ·
        refine ⟨70073743149861390040457227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93431657533148520053942969 70073743149861390040457227)
        ·
          refine ⟨105110614724792085060685841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70073743149861390040457227 105110614724792085060685841)
          ·
            refine ⟨78832961043594063795514381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105110614724792085060685841 78832961043594063795514381)
            ·
              refine ⟨29562360391347773923317893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78832961043594063795514381 29562360391347773923317893)
              ·
                refine ⟨5542942573377707610622105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29562360391347773923317893 5542942573377707610622105)
                ·
                  refine ⟨4157206930033280707966579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5542942573377707610622105 4157206930033280707966579)
                  ·
                    refine ⟨6235810395049921061949869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4157206930033280707966579 6235810395049921061949869)
                    ·
                      refine ⟨2338428898143720398231201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6235810395049921061949869 2338428898143720398231201)
                      ·
                        rfl

theorem cell23_4554074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_4554074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554074 prefixEnd_4554074 := by exact prefixLift 4554074
  have htrace : WordTrace (prefixWord ++ tailWord_4554074) baseStart_4554074 baseEnd_4554074 := by
    simpa [prefixWord, tailWord_4554074, baseEnd_4554074] using wordTrace_append hprefix tailTrace_4554074
  have hstable : (prefixWord ++ tailWord_4554074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554074).length < 2 ^ (prefixWord ++ tailWord_4554074).sum := by decide
  have hdescent : baseEnd_4554074 < baseStart_4554074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554084 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 3, 3, 2]
def baseStart_4554084 : Nat := 118140960795 + 4554084 * 2 ^ 59
def prefixEnd_4554084 : Nat := 4983230072969 + 3 ^ 40 * 4554084 * 2
def baseEnd_4554084 : Nat := 2338434032950265359106155

theorem tailTrace_4554084 : CollatzResearch.WordTrace tailWord_4554084 prefixEnd_4554084 2338434032950265359106155 := by
  unfold tailWord_4554084
  simp only [CollatzResearch.WordTrace]
  refine ⟨83050544616669459235214653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110734059488892612313619537 83050544616669459235214653)
  ·
    refine ⟨31143954231251047213205495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83050544616669459235214653 31143954231251047213205495)
    ·
      refine ⟨46715931346876570819808243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31143954231251047213205495 46715931346876570819808243)
      ·
        refine ⟨70073897020314856229712365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46715931346876570819808243 70073897020314856229712365)
        ·
          refine ⟨26277711382618071086142137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70073897020314856229712365 26277711382618071086142137)
          ·
            refine ⟨19708283536963553314606603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26277711382618071086142137 19708283536963553314606603)
            ·
              refine ⟨29562425305445329971909905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19708283536963553314606603 29562425305445329971909905)
              ·
                refine ⟨22171818979083997478932429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29562425305445329971909905 22171818979083997478932429)
                ·
                  refine ⟨8314432117156499054599661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22171818979083997478932429 8314432117156499054599661)
                  ·
                    refine ⟨3117912043933687145474873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8314432117156499054599661 3117912043933687145474873)
                    ·
                      refine ⟨2338434032950265359106155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3117912043933687145474873 2338434032950265359106155)
                      ·
                        rfl

theorem cell23_4554084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_4554084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554084 prefixEnd_4554084 := by exact prefixLift 4554084
  have htrace : WordTrace (prefixWord ++ tailWord_4554084) baseStart_4554084 baseEnd_4554084 := by
    simpa [prefixWord, tailWord_4554084, baseEnd_4554084] using wordTrace_append hprefix tailTrace_4554084
  have hstable : (prefixWord ++ tailWord_4554084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554084).length < 2 ^ (prefixWord ++ tailWord_4554084).sum := by decide
  have hdescent : baseEnd_4554084 < baseStart_4554084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554137 : List Nat := [1, 2, 1, 2, 1, 6, 2, 1, 7]
def baseStart_4554137 : Nat := 118140960795 + 4554137 * 2 ^ 59
def prefixEnd_4554137 : Nat := 4983230072969 + 3 ^ 40 * 4554137 * 2
def baseEnd_4554137 : Nat := 259829027491661516860379

theorem tailTrace_4554137 : CollatzResearch.WordTrace tailWord_4554137 prefixEnd_4554137 259829027491661516860379 := by
  unfold tailWord_4554137
  simp only [CollatzResearch.WordTrace]
  refine ⟨166103022302146908522108665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110735348201431272348072443 166103022302146908522108665)
  ·
    refine ⟨124577266726610181391581499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166103022302146908522108665 124577266726610181391581499)
    ·
      refine ⟨186865900089915272087372249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124577266726610181391581499 186865900089915272087372249)
      ·
        refine ⟨140149425067436454065529187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186865900089915272087372249 140149425067436454065529187)
        ·
          refine ⟨210224137601154681098293781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140149425067436454065529187 210224137601154681098293781)
          ·
            refine ⟨9854256450054125676482521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 210224137601154681098293781 9854256450054125676482521)
            ·
              refine ⟨7390692337540594257361891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9854256450054125676482521 7390692337540594257361891)
              ·
                refine ⟨11086038506310891386042837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7390692337540594257361891 11086038506310891386042837)
                ·
                  refine ⟨259829027491661516860379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11086038506310891386042837 259829027491661516860379)
                  ·
                    rfl

theorem cell23_4554137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 7].length) (baseStart_4554137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554137 prefixEnd_4554137 := by exact prefixLift 4554137
  have htrace : WordTrace (prefixWord ++ tailWord_4554137) baseStart_4554137 baseEnd_4554137 := by
    simpa [prefixWord, tailWord_4554137, baseEnd_4554137] using wordTrace_append hprefix tailTrace_4554137
  have hstable : (prefixWord ++ tailWord_4554137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554137).length < 2 ^ (prefixWord ++ tailWord_4554137).sum := by decide
  have hdescent : baseEnd_4554137 < baseStart_4554137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554147 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 3]
def baseStart_4554147 : Nat := 118140960795 + 4554147 * 2 ^ 59
def prefixEnd_4554147 : Nat := 4983230072969 + 3 ^ 40 * 4554147 * 2
def baseEnd_4554147 : Nat := 2338466382231498612618365

theorem tailTrace_4554147 : CollatzResearch.WordTrace tailWord_4554147 prefixEnd_4554147 2338466382231498612618365 := by
  unfold tailWord_4554147
  simp only [CollatzResearch.WordTrace]
  refine ⟨166103387032110680229972695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110735591354740453486648463 166103387032110680229972695)
  ·
    refine ⟨249155080548166020344959043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166103387032110680229972695 249155080548166020344959043)
    ·
      refine ⟨373732620822249030517438565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249155080548166020344959043 373732620822249030517438565)
      ·
        refine ⟨70074866404171693222019731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 373732620822249030517438565 70074866404171693222019731)
        ·
          refine ⟨105112299606257539833029597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70074866404171693222019731 105112299606257539833029597)
          ·
            refine ⟨39417112352346577437386099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105112299606257539833029597 39417112352346577437386099)
            ·
              refine ⟨59125668528519866156079149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39417112352346577437386099 59125668528519866156079149)
              ·
                refine ⟨22172125698194949808529681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59125668528519866156079149 22172125698194949808529681)
                ·
                  refine ⟨16629094273646212356397261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22172125698194949808529681 16629094273646212356397261)
                  ·
                    refine ⟨6235910352617329633648973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16629094273646212356397261 6235910352617329633648973)
                    ·
                      refine ⟨2338466382231498612618365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6235910352617329633648973 2338466382231498612618365)
                      ·
                        rfl

theorem cell23_4554147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_4554147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554147 prefixEnd_4554147 := by exact prefixLift 4554147
  have htrace : WordTrace (prefixWord ++ tailWord_4554147) baseStart_4554147 baseEnd_4554147 := by
    simpa [prefixWord, tailWord_4554147, baseEnd_4554147] using wordTrace_append hprefix tailTrace_4554147
  have hstable : (prefixWord ++ tailWord_4554147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554147).length < 2 ^ (prefixWord ++ tailWord_4554147).sum := by decide
  have hdescent : baseEnd_4554147 < baseStart_4554147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554160 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 7]
def baseStart_4554160 : Nat := 118140960795 + 4554160 * 2 ^ 59
def prefixEnd_4554160 : Nat := 4983230072969 + 3 ^ 40 * 4554160 * 2
def baseEnd_4554160 : Nat := 2338473057480007061755805

theorem tailTrace_4554160 : CollatzResearch.WordTrace tailWord_4554160 prefixEnd_4554160 2338473057480007061755805 := by
  unfold tailWord_4554160
  simp only [CollatzResearch.WordTrace]
  refine ⟨83051930590531791725097967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110735907454042388966797289 83051930590531791725097967)
  ·
    refine ⟨124577895885797687587646951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83051930590531791725097967 124577895885797687587646951)
    ·
      refine ⟨186866843828696531381470427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124577895885797687587646951 186866843828696531381470427)
      ·
        refine ⟨280300265743044797072205641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186866843828696531381470427 280300265743044797072205641)
        ·
          refine ⟨210225199307283597804154231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280300265743044797072205641 210225199307283597804154231)
          ·
            refine ⟨315337798960925396706231347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210225199307283597804154231 315337798960925396706231347)
            ·
              refine ⟨473006698441388095059347021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315337798960925396706231347 473006698441388095059347021)
              ·
                refine ⟨177377511915520535647255133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 473006698441388095059347021 177377511915520535647255133)
                ·
                  refine ⟨66516566968320200867720675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177377511915520535647255133 66516566968320200867720675)
                  ·
                    refine ⟨99774850452480301301581013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66516566968320200867720675 99774850452480301301581013)
                    ·
                      refine ⟨2338473057480007061755805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99774850452480301301581013 2338473057480007061755805)
                      ·
                        rfl

theorem cell23_4554160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_4554160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554160 prefixEnd_4554160 := by exact prefixLift 4554160
  have htrace : WordTrace (prefixWord ++ tailWord_4554160) baseStart_4554160 baseEnd_4554160 := by
    simpa [prefixWord, tailWord_4554160, baseEnd_4554160] using wordTrace_append hprefix tailTrace_4554160
  have hstable : (prefixWord ++ tailWord_4554160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554160).length < 2 ^ (prefixWord ++ tailWord_4554160).sum := by decide
  have hdescent : baseEnd_4554160 < baseStart_4554160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554167 : List Nat := [1, 1, 3, 1, 3, 2, 2, 3, 2, 5]
def baseStart_4554167 : Nat := 118140960795 + 4554167 * 2 ^ 59
def prefixEnd_4554167 : Nat := 4983230072969 + 3 ^ 40 * 4554167 * 2
def baseEnd_4554167 : Nat := 779492217281529511456091

theorem tailTrace_4554167 : CollatzResearch.WordTrace tailWord_4554167 prefixEnd_4554167 779492217281529511456091 := by
  unfold tailWord_4554167
  simp only [CollatzResearch.WordTrace]
  refine ⟨166104116492038223645700755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110736077661358815763800503 166104116492038223645700755)
  ·
    refine ⟨249156174738057335468551133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166104116492038223645700755 249156174738057335468551133)
    ·
      refine ⟨93433565526771500800706675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249156174738057335468551133 93433565526771500800706675)
      ·
        refine ⟨140150348290157251201060013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93433565526771500800706675 140150348290157251201060013)
        ·
          refine ⟨52556380608808969200397505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140150348290157251201060013 52556380608808969200397505)
          ·
            refine ⟨39417285456606726900298129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52556380608808969200397505 39417285456606726900298129)
            ·
              refine ⟨29562964092455045175223597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39417285456606726900298129 29562964092455045175223597)
              ·
                refine ⟨11086111534670641940708849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29562964092455045175223597 11086111534670641940708849)
                ·
                  refine ⟨8314583651002981455531637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11086111534670641940708849 8314583651002981455531637)
                  ·
                    refine ⟨779492217281529511456091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8314583651002981455531637 779492217281529511456091)
                    ·
                      rfl

theorem cell23_4554167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_4554167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554167 prefixEnd_4554167 := by exact prefixLift 4554167
  have htrace : WordTrace (prefixWord ++ tailWord_4554167) baseStart_4554167 baseEnd_4554167 := by
    simpa [prefixWord, tailWord_4554167, baseEnd_4554167] using wordTrace_append hprefix tailTrace_4554167
  have hstable : (prefixWord ++ tailWord_4554167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554167).length < 2 ^ (prefixWord ++ tailWord_4554167).sum := by decide
  have hdescent : baseEnd_4554167 < baseStart_4554167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554174 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2]
def baseStart_4554174 : Nat := 118140960795 + 4554174 * 2 ^ 59
def prefixEnd_4554174 : Nat := 4983230072969 + 3 ^ 40 * 4554174 * 2
def baseEnd_4554174 : Nat := 2338480246209170006980741

theorem tailTrace_4554174 : CollatzResearch.WordTrace tailWord_4554174 prefixEnd_4554174 2338480246209170006980741 := by
  unfold tailWord_4554174
  simp only [CollatzResearch.WordTrace]
  refine ⟨20763046475376607980150697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110736247868675242560803717 20763046475376607980150697)
  ·
    refine ⟨15572284856532455985113023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20763046475376607980150697 15572284856532455985113023)
    ·
      refine ⟨23358427284798683977669535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15572284856532455985113023 23358427284798683977669535)
      ·
        refine ⟨35037640927198025966504303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23358427284798683977669535 35037640927198025966504303)
        ·
          refine ⟨52556461390797038949756455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35037640927198025966504303 52556461390797038949756455)
          ·
            refine ⟨78834692086195558424634683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52556461390797038949756455 78834692086195558424634683)
            ·
              refine ⟨118252038129293337636952025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78834692086195558424634683 118252038129293337636952025)
              ·
                refine ⟨88689028596970003227714019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118252038129293337636952025 88689028596970003227714019)
                ·
                  refine ⟨133033542895455004841571029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88689028596970003227714019 133033542895455004841571029)
                  ·
                    refine ⟨3117973661612226675974321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 133033542895455004841571029 3117973661612226675974321)
                    ·
                      refine ⟨2338480246209170006980741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3117973661612226675974321 2338480246209170006980741)
                      ·
                        rfl

theorem cell23_4554174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_4554174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554174 prefixEnd_4554174 := by exact prefixLift 4554174
  have htrace : WordTrace (prefixWord ++ tailWord_4554174) baseStart_4554174 baseEnd_4554174 := by
    simpa [prefixWord, tailWord_4554174, baseEnd_4554174] using wordTrace_append hprefix tailTrace_4554174
  have hstable : (prefixWord ++ tailWord_4554174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554174).length < 2 ^ (prefixWord ++ tailWord_4554174).sum := by decide
  have hdescent : baseEnd_4554174 < baseStart_4554174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554187 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 4]
def baseStart_4554187 : Nat := 118140960795 + 4554187 * 2 ^ 59
def prefixEnd_4554187 : Nat := 4983230072969 + 3 ^ 40 * 4554187 * 2
def baseEnd_4554187 : Nat := 2338486921457678456118181

theorem tailTrace_4554187 : CollatzResearch.WordTrace tailWord_4554187 prefixEnd_4554187 2338486921457678456118181 := by
  unfold tailWord_4554187
  simp only [CollatzResearch.WordTrace]
  refine ⟨166104845951965767061428815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110736563967977178040952543 166104845951965767061428815)
  ·
    refine ⟨249157268927948650592143223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166104845951965767061428815 249157268927948650592143223)
    ·
      refine ⟨373735903391922975888214835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249157268927948650592143223 373735903391922975888214835)
      ·
        refine ⟨560603855087884463832322253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373735903391922975888214835 560603855087884463832322253)
        ·
          refine ⟨210226445657956673937120845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 560603855087884463832322253 210226445657956673937120845)
          ·
            refine ⟨78834917121733752726420317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210226445657956673937120845 78834917121733752726420317)
            ·
              refine ⟨29563093920650157272407619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78834917121733752726420317 29563093920650157272407619)
              ·
                refine ⟨44344640880975235908611429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29563093920650157272407619 44344640880975235908611429)
                ·
                  refine ⟨8314620165182856732864643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44344640880975235908611429 8314620165182856732864643)
                  ·
                    refine ⟨12471930247774285099296965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8314620165182856732864643 12471930247774285099296965)
                    ·
                      refine ⟨2338486921457678456118181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12471930247774285099296965 2338486921457678456118181)
                      ·
                        rfl

theorem cell23_4554187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 4].length) (baseStart_4554187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554187 prefixEnd_4554187 := by exact prefixLift 4554187
  have htrace : WordTrace (prefixWord ++ tailWord_4554187) baseStart_4554187 baseEnd_4554187 := by
    simpa [prefixWord, tailWord_4554187, baseEnd_4554187] using wordTrace_append hprefix tailTrace_4554187
  have hstable : (prefixWord ++ tailWord_4554187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554187).length < 2 ^ (prefixWord ++ tailWord_4554187).sum := by decide
  have hdescent : baseEnd_4554187 < baseStart_4554187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554224 : List Nat := [2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 3]
def baseStart_4554224 : Nat := 118140960795 + 4554224 * 2 ^ 59
def prefixEnd_4554224 : Nat := 4983230072969 + 3 ^ 40 * 4554224 * 2
def baseEnd_4554224 : Nat := 2338505920241894811355511

theorem tailTrace_4554224 : CollatzResearch.WordTrace tailWord_4554224 prefixEnd_4554224 2338505920241894811355511 := by
  unfold tailWord_4554224
  simp only [CollatzResearch.WordTrace]
  refine ⟨83053097726415861190262863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110737463635221148253683817 83053097726415861190262863)
  ·
    refine ⟨124579646589623791785394295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83053097726415861190262863 124579646589623791785394295)
    ·
      refine ⟨186869469884435687678091443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124579646589623791785394295 186869469884435687678091443)
      ·
        refine ⟨280304204826653531517137165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186869469884435687678091443 280304204826653531517137165)
        ·
          refine ⟨105114076809995074318926437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 280304204826653531517137165 105114076809995074318926437)
          ·
            refine ⟨19708889401874076434798707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105114076809995074318926437 19708889401874076434798707)
            ·
              refine ⟨29563334102811114652198061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19708889401874076434798707 29563334102811114652198061)
              ·
                refine ⟨11086250288554167994574273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29563334102811114652198061 11086250288554167994574273)
                ·
                  refine ⟨8314687716415625995930705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11086250288554167994574273 8314687716415625995930705)
                  ·
                    refine ⟨6236015787311719496948029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8314687716415625995930705 6236015787311719496948029)
                    ·
                      refine ⟨2338505920241894811355511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6236015787311719496948029 2338505920241894811355511)
                      ·
                        rfl

theorem cell23_4554224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 3].length) (baseStart_4554224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554224 prefixEnd_4554224 := by exact prefixLift 4554224
  have htrace : WordTrace (prefixWord ++ tailWord_4554224) baseStart_4554224 baseEnd_4554224 := by
    simpa [prefixWord, tailWord_4554224, baseEnd_4554224] using wordTrace_append hprefix tailTrace_4554224
  have hstable : (prefixWord ++ tailWord_4554224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554224).length < 2 ^ (prefixWord ++ tailWord_4554224).sum := by decide
  have hdescent : baseEnd_4554224 < baseStart_4554224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554248 : List Nat := [2, 1, 3, 2, 1, 1, 6, 2, 1, 4]
def baseStart_4554248 : Nat := 118140960795 + 4554248 * 2 ^ 59
def prefixEnd_4554248 : Nat := 4983230072969 + 3 ^ 40 * 4554248 * 2
def baseEnd_4554248 : Nat := 779506081259200905818467

theorem tailTrace_4554248 : CollatzResearch.WordTrace tailWord_4554248 prefixEnd_4554248 779506081259200905818467 := by
  unfold tailWord_4554248
  simp only [CollatzResearch.WordTrace]
  refine ⟨83053535402372387239699699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110738047203163182986266265 83053535402372387239699699)
  ·
    refine ⟨124580303103558580859549549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83053535402372387239699699 124580303103558580859549549)
    ·
      refine ⟨46717613663834467822331081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124580303103558580859549549 46717613663834467822331081)
      ·
        refine ⟨35038210247875850866748311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46717613663834467822331081 35038210247875850866748311)
        ·
          refine ⟨52557315371813776300122467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35038210247875850866748311 52557315371813776300122467)
          ·
            refine ⟨78835973057720664450183701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52557315371813776300122467 78835973057720664450183701)
            ·
              refine ⟨3695436237080656146102361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78835973057720664450183701 3695436237080656146102361)
              ·
                refine ⟨2771577177810492109576771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3695436237080656146102361 2771577177810492109576771)
                ·
                  refine ⟨4157365766715738164365157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2771577177810492109576771 4157365766715738164365157)
                  ·
                    refine ⟨779506081259200905818467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4157365766715738164365157 779506081259200905818467)
                    ·
                      rfl

theorem cell23_4554248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_4554248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554248 prefixEnd_4554248 := by exact prefixLift 4554248
  have htrace : WordTrace (prefixWord ++ tailWord_4554248) baseStart_4554248 baseEnd_4554248 := by
    simpa [prefixWord, tailWord_4554248, baseEnd_4554248] using wordTrace_append hprefix tailTrace_4554248
  have hstable : (prefixWord ++ tailWord_4554248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554248).length < 2 ^ (prefixWord ++ tailWord_4554248).sum := by decide
  have hdescent : baseEnd_4554248 < baseStart_4554248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554257 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 5, 5]
def baseStart_4554257 : Nat := 118140960795 + 4554257 * 2 ^ 59
def prefixEnd_4554257 : Nat := 4983230072969 + 3 ^ 40 * 4554257 * 2
def baseEnd_4554257 : Nat := 779507621701164394080953

theorem tailTrace_4554257 : CollatzResearch.WordTrace tailWord_4554257 prefixEnd_4554257 779507621701164394080953 := by
  unfold tailWord_4554257
  simp only [CollatzResearch.WordTrace]
  refine ⟨166107399061712169016477025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110738266041141446010984683 166107399061712169016477025)
  ·
    refine ⟨124580549296284126762357769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166107399061712169016477025 124580549296284126762357769)
    ·
      refine ⟨93435411972213095071768327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124580549296284126762357769 93435411972213095071768327)
      ·
        refine ⟨140153117958319642607652491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93435411972213095071768327 140153117958319642607652491)
        ·
          refine ⟨210229676937479463911478737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140153117958319642607652491 210229676937479463911478737)
          ·
            refine ⟨157672257703109597933609053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210229676937479463911478737 157672257703109597933609053)
            ·
              refine ⟨59127096638666099225103395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157672257703109597933609053 59127096638666099225103395)
              ·
                refine ⟨88690644957999148837655093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59127096638666099225103395 88690644957999148837655093)
                ·
                  refine ⟨8314747964812420203530165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88690644957999148837655093 8314747964812420203530165)
                  ·
                    refine ⟨779507621701164394080953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8314747964812420203530165 779507621701164394080953)
                    ·
                      rfl

theorem cell23_4554257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_4554257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554257 prefixEnd_4554257 := by exact prefixLift 4554257
  have htrace : WordTrace (prefixWord ++ tailWord_4554257) baseStart_4554257 baseEnd_4554257 := by
    simpa [prefixWord, tailWord_4554257, baseEnd_4554257] using wordTrace_append hprefix tailTrace_4554257
  have hstable : (prefixWord ++ tailWord_4554257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554257).length < 2 ^ (prefixWord ++ tailWord_4554257).sum := by decide
  have hdescent : baseEnd_4554257 < baseStart_4554257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554274 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_4554274 : Nat := 118140960795 + 4554274 * 2 ^ 59
def prefixEnd_4554274 : Nat := 4983230072969 + 3 ^ 40 * 4554274 * 2
def baseEnd_4554274 : Nat := 779510531424873205243427

theorem tailTrace_4554274 : CollatzResearch.WordTrace tailWord_4554274 prefixEnd_4554274 779510531424873205243427 := by
  unfold tailWord_4554274
  simp only [CollatzResearch.WordTrace]
  refine ⟨41527004775662645229961469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110738679401767053946563917 41527004775662645229961469)
  ·
    refine ⟨15572626790873491961235551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41527004775662645229961469 15572626790873491961235551)
    ·
      refine ⟨23358940186310237941853327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15572626790873491961235551 23358940186310237941853327)
      ·
        refine ⟨35038410279465356912779991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23358940186310237941853327 35038410279465356912779991)
        ·
          refine ⟨52557615419198035369169987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35038410279465356912779991 52557615419198035369169987)
          ·
            refine ⟨78836423128797053053754981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52557615419198035369169987 78836423128797053053754981)
            ·
              refine ⟨14781829336649447447579059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78836423128797053053754981 14781829336649447447579059)
              ·
                refine ⟨22172744004974171171368589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14781829336649447447579059 22172744004974171171368589)
                ·
                  refine ⟨8314779001865314189263221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22172744004974171171368589 8314779001865314189263221)
                  ·
                    refine ⟨779510531424873205243427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8314779001865314189263221 779510531424873205243427)
                    ·
                      rfl

theorem cell23_4554274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_4554274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554274 prefixEnd_4554274 := by exact prefixLift 4554274
  have htrace : WordTrace (prefixWord ++ tailWord_4554274) baseStart_4554274 baseEnd_4554274 := by
    simpa [prefixWord, tailWord_4554274, baseEnd_4554274] using wordTrace_append hprefix tailTrace_4554274
  have hstable : (prefixWord ++ tailWord_4554274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554274).length < 2 ^ (prefixWord ++ tailWord_4554274).sum := by decide
  have hdescent : baseEnd_4554274 < baseStart_4554274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554291 : List Nat := [1, 1, 1, 2, 4, 3, 4, 1, 1, 5]
def baseStart_4554291 : Nat := 118140960795 + 4554291 * 2 ^ 59
def prefixEnd_4554291 : Nat := 4983230072969 + 3 ^ 40 * 4554291 * 2
def baseEnd_4554291 : Nat := 779513441148582016405901

theorem tailTrace_4554291 : CollatzResearch.WordTrace tailWord_4554291 prefixEnd_4554291 779513441148582016405901 := by
  unfold tailWord_4554291
  simp only [CollatzResearch.WordTrace]
  refine ⟨166108639143588992823214727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110739092762392661882143151 166108639143588992823214727)
  ·
    refine ⟨249162958715383489234822091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166108639143588992823214727 249162958715383489234822091)
    ·
      refine ⟨373744438073075233852233137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249162958715383489234822091 373744438073075233852233137)
      ·
        refine ⟨280308328554806425389174853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 373744438073075233852233137 280308328554806425389174853)
        ·
          refine ⟨52557811604026204760470285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 280308328554806425389174853 52557811604026204760470285)
          ·
            refine ⟨19709179351509826785176357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52557811604026204760470285 19709179351509826785176357)
            ·
              refine ⟨3695471128408092522220567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19709179351509826785176357 3695471128408092522220567)
              ·
                refine ⟨5543206692612138783330851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3695471128408092522220567 5543206692612138783330851)
                ·
                  refine ⟨8314810038918208174996277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5543206692612138783330851 8314810038918208174996277)
                  ·
                    refine ⟨779513441148582016405901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8314810038918208174996277 779513441148582016405901)
                    ·
                      rfl

theorem cell23_4554291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 1, 5].length) (baseStart_4554291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554291 prefixEnd_4554291 := by exact prefixLift 4554291
  have htrace : WordTrace (prefixWord ++ tailWord_4554291) baseStart_4554291 baseEnd_4554291 := by
    simpa [prefixWord, tailWord_4554291, baseEnd_4554291] using wordTrace_append hprefix tailTrace_4554291
  have hstable : (prefixWord ++ tailWord_4554291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554291).length < 2 ^ (prefixWord ++ tailWord_4554291).sum := by decide
  have hdescent : baseEnd_4554291 < baseStart_4554291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554307 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 4]
def baseStart_4554307 : Nat := 118140960795 + 4554307 * 2 ^ 59
def prefixEnd_4554307 : Nat := 4983230072969 + 3 ^ 40 * 4554307 * 2
def baseEnd_4554307 : Nat := 2338548539136217986617629

theorem tailTrace_4554307 : CollatzResearch.WordTrace tailWord_4554307 prefixEnd_4554307 2338548539136217986617629 := by
  unfold tailWord_4554307
  simp only [CollatzResearch.WordTrace]
  refine ⟨166109222711531027555797175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110739481807687351703864783 166109222711531027555797175)
  ·
    refine ⟨249163834067296541333695763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166109222711531027555797175 249163834067296541333695763)
    ·
      refine ⟨373745751100944812000543645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249163834067296541333695763 373745751100944812000543645)
      ·
        refine ⟨140154656662854304500203867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 373745751100944812000543645 140154656662854304500203867)
        ·
          refine ⟨210231984994281456750305801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140154656662854304500203867 210231984994281456750305801)
          ·
            refine ⟨157673988745711092562729351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210231984994281456750305801 157673988745711092562729351)
            ·
              refine ⟨236510983118566638844094027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157673988745711092562729351 236510983118566638844094027)
              ·
                refine ⟨354766474677849958266141041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236510983118566638844094027 354766474677849958266141041)
                ·
                  refine ⟨266074856008387468699605781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 354766474677849958266141041 266074856008387468699605781)
                  ·
                    refine ⟨12472258875393162595294021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 266074856008387468699605781 12472258875393162595294021)
                    ·
                      refine ⟨2338548539136217986617629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12472258875393162595294021 2338548539136217986617629)
                      ·
                        rfl

theorem cell23_4554307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_4554307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554307 prefixEnd_4554307 := by exact prefixLift 4554307
  have htrace : WordTrace (prefixWord ++ tailWord_4554307) baseStart_4554307 baseEnd_4554307 := by
    simpa [prefixWord, tailWord_4554307, baseEnd_4554307] using wordTrace_append hprefix tailTrace_4554307
  have hstable : (prefixWord ++ tailWord_4554307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554307).length < 2 ^ (prefixWord ++ tailWord_4554307).sum := by decide
  have hdescent : baseEnd_4554307 < baseStart_4554307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554314 : List Nat := [3, 1, 2, 1, 1, 3, 3, 2, 1, 1, 5]
def baseStart_4554314 : Nat := 118140960795 + 4554314 * 2 ^ 59
def prefixEnd_4554314 : Nat := 4983230072969 + 3 ^ 40 * 4554314 * 2
def baseEnd_4554314 : Nat := 2338552133500799459230097

theorem tailTrace_4554314 : CollatzResearch.WordTrace tailWord_4554314 prefixEnd_4554314 2338552133500799459230097 := by
  unfold tailWord_4554314
  simp only [CollatzResearch.WordTrace]
  refine ⟨41527369505626416937825499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110739652015003778500867997 41527369505626416937825499)
  ·
    refine ⟨62291054258439625406738249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41527369505626416937825499 62291054258439625406738249)
    ·
      refine ⟨46718290693829719055053687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62291054258439625406738249 46718290693829719055053687)
      ·
        refine ⟨70077436040744578582580531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46718290693829719055053687 70077436040744578582580531)
        ·
          refine ⟨105116154061116867873870797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70077436040744578582580531 105116154061116867873870797)
          ·
            refine ⟨39418557772918825452701549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105116154061116867873870797 39418557772918825452701549)
            ·
              refine ⟨14781959164844559544763081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39418557772918825452701549 14781959164844559544763081)
              ·
                refine ⟨11086469373633419658572311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14781959164844559544763081 11086469373633419658572311)
                ·
                  refine ⟨16629704060450129487858467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11086469373633419658572311 16629704060450129487858467)
                  ·
                    refine ⟨24944556090675194231787701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16629704060450129487858467 24944556090675194231787701)
                    ·
                      refine ⟨2338552133500799459230097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24944556090675194231787701 2338552133500799459230097)
                      ·
                        rfl

theorem cell23_4554314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_4554314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554314 prefixEnd_4554314 := by exact prefixLift 4554314
  have htrace : WordTrace (prefixWord ++ tailWord_4554314) baseStart_4554314 baseEnd_4554314 := by
    simpa [prefixWord, tailWord_4554314, baseEnd_4554314] using wordTrace_append hprefix tailTrace_4554314
  have hstable : (prefixWord ++ tailWord_4554314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554314).length < 2 ^ (prefixWord ++ tailWord_4554314).sum := by decide
  have hdescent : baseEnd_4554314 < baseStart_4554314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554324 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_4554324 : Nat := 118140960795 + 4554324 * 2 ^ 59
def prefixEnd_4554324 : Nat := 4983230072969 + 3 ^ 40 * 4554324 * 2
def baseEnd_4554324 : Nat := 2338557268307344420105051

theorem tailTrace_4554324 : CollatzResearch.WordTrace tailWord_4554324 prefixEnd_4554324 2338557268307344420105051 := by
  unfold tailWord_4554324
  simp only [CollatzResearch.WordTrace]
  refine ⟨83054921376234719729583013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110739895168312959639444017 83054921376234719729583013)
  ·
    refine ⟨15572797758044009949296815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83054921376234719729583013 15572797758044009949296815)
    ·
      refine ⟨23359196637066014923945223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15572797758044009949296815 23359196637066014923945223)
      ·
        refine ⟨35038794955599022385917835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23359196637066014923945223 35038794955599022385917835)
        ·
          refine ⟨52558192433398533578876753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35038794955599022385917835 52558192433398533578876753)
          ·
            refine ⟨39418644325048900184157565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52558192433398533578876753 39418644325048900184157565)
            ·
              refine ⟨14781991621893337569059087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39418644325048900184157565 14781991621893337569059087)
              ·
                refine ⟨22172987432840006353588631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14781991621893337569059087 22172987432840006353588631)
                ·
                  refine ⟨33259481149260009530382947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22172987432840006353588631 33259481149260009530382947)
                  ·
                    refine ⟨49889221723890014295574421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33259481149260009530382947 49889221723890014295574421)
                    ·
                      refine ⟨2338557268307344420105051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49889221723890014295574421 2338557268307344420105051)
                      ·
                        rfl

theorem cell23_4554324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_4554324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554324 prefixEnd_4554324 := by exact prefixLift 4554324
  have htrace : WordTrace (prefixWord ++ tailWord_4554324) baseStart_4554324 baseEnd_4554324 := by
    simpa [prefixWord, tailWord_4554324, baseEnd_4554324] using wordTrace_append hprefix tailTrace_4554324
  have hstable : (prefixWord ++ tailWord_4554324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554324).length < 2 ^ (prefixWord ++ tailWord_4554324).sum := by decide
  have hdescent : baseEnd_4554324 < baseStart_4554324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554345 : List Nat := [1, 2, 1, 1, 1, 4, 5, 3, 1, 2, 2]
def baseStart_4554345 : Nat := 118140960795 + 4554345 * 2 ^ 59
def prefixEnd_4554345 : Nat := 4983230072969 + 3 ^ 40 * 4554345 * 2
def baseEnd_4554345 : Nat := 2338568051401088837942455

theorem tailTrace_4554345 : CollatzResearch.WordTrace tailWord_4554345 prefixEnd_4554345 2338568051401088837942455 := by
  unfold tailWord_4554345
  simp only [CollatzResearch.WordTrace]
  refine ⟨166110608685393360045680489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110740405790262240030453659 166110608685393360045680489)
  ·
    refine ⟨124582956514045020034260367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166110608685393360045680489 124582956514045020034260367)
    ·
      refine ⟨186874434771067530051390551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124582956514045020034260367 186874434771067530051390551)
      ·
        refine ⟨280311652156601295077085827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186874434771067530051390551 280311652156601295077085827)
        ·
          refine ⟨420467478234901942615628741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280311652156601295077085827 420467478234901942615628741)
          ·
            refine ⟨78837652169044114240430389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 420467478234901942615628741 78837652169044114240430389)
            ·
              refine ⟨7391029890847885710040349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78837652169044114240430389 7391029890847885710040349)
              ·
                refine ⟨2771636209067957141265131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7391029890847885710040349 2771636209067957141265131)
                ·
                  refine ⟨4157454313601935711897697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2771636209067957141265131 4157454313601935711897697)
                  ·
                    refine ⟨3118090735201451783923273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4157454313601935711897697 3118090735201451783923273)
                    ·
                      refine ⟨2338568051401088837942455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3118090735201451783923273 2338568051401088837942455)
                      ·
                        rfl

theorem cell23_4554345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 1, 2, 2].length) (baseStart_4554345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554345 prefixEnd_4554345 := by exact prefixLift 4554345
  have htrace : WordTrace (prefixWord ++ tailWord_4554345) baseStart_4554345 baseEnd_4554345 := by
    simpa [prefixWord, tailWord_4554345, baseEnd_4554345] using wordTrace_append hprefix tailTrace_4554345
  have hstable : (prefixWord ++ tailWord_4554345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554345).length < 2 ^ (prefixWord ++ tailWord_4554345).sum := by decide
  have hdescent : baseEnd_4554345 < baseStart_4554345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554361 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 4, 1, 3]
def baseStart_4554361 : Nat := 118140960795 + 4554361 * 2 ^ 59
def prefixEnd_4554361 : Nat := 4983230072969 + 3 ^ 40 * 4554361 * 2
def baseEnd_4554361 : Nat := 2338576267091560775342381

theorem tailTrace_4554361 : CollatzResearch.WordTrace tailWord_4554361 prefixEnd_4554361 2338576267091560775342381 := by
  unfold tailWord_4554361
  simp only [CollatzResearch.WordTrace]
  refine ⟨166111192253335394778262937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110740794835556929852175291 166111192253335394778262937)
  ·
    refine ⟨124583394190001546083697203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166111192253335394778262937 124583394190001546083697203)
    ·
      refine ⟨186875091285002319125545805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124583394190001546083697203 186875091285002319125545805)
      ·
        refine ⟨70078159231875869672079677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186875091285002319125545805 70078159231875869672079677)
        ·
          refine ⟨26279309711953451127029879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70078159231875869672079677 26279309711953451127029879)
          ·
            refine ⟨39418964567930176690544819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26279309711953451127029879 39418964567930176690544819)
            ·
              refine ⟨59128446851895265035817229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39418964567930176690544819 59128446851895265035817229)
              ·
                refine ⟨22173167569460724388431461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59128446851895265035817229 22173167569460724388431461)
                ·
                  refine ⟨4157468919273885822830899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22173167569460724388431461 4157468919273885822830899)
                  ·
                    refine ⟨6236203378910828734246349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4157468919273885822830899 6236203378910828734246349)
                    ·
                      refine ⟨2338576267091560775342381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6236203378910828734246349 2338576267091560775342381)
                      ·
                        rfl

theorem cell23_4554361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_4554361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554361 prefixEnd_4554361 := by exact prefixLift 4554361
  have htrace : WordTrace (prefixWord ++ tailWord_4554361) baseStart_4554361 baseEnd_4554361 := by
    simpa [prefixWord, tailWord_4554361, baseEnd_4554361] using wordTrace_append hprefix tailTrace_4554361
  have hstable : (prefixWord ++ tailWord_4554361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554361).length < 2 ^ (prefixWord ++ tailWord_4554361).sum := by decide
  have hdescent : baseEnd_4554361 < baseStart_4554361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554367 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 10]
def baseStart_4554367 : Nat := 118140960795 + 4554367 * 2 ^ 59
def prefixEnd_4554367 : Nat := 4983230072969 + 3 ^ 40 * 4554367 * 2
def baseEnd_4554367 : Nat := 2338579347975487751867353

theorem tailTrace_4554367 : CollatzResearch.WordTrace tailWord_4554367 prefixEnd_4554367 2338579347975487751867353 := by
  unfold tailWord_4554367
  simp only [CollatzResearch.WordTrace]
  refine ⟨166111411091313657802981355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110740940727542438535320903 166111411091313657802981355)
  ·
    refine ⟨249167116636970486704472033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166111411091313657802981355 249167116636970486704472033)
    ·
      refine ⟨186875337477727865028354025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249167116636970486704472033 186875337477727865028354025)
      ·
        refine ⟨140156503108295898771265519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186875337477727865028354025 140156503108295898771265519)
        ·
          refine ⟨210234754662443848156898279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140156503108295898771265519 210234754662443848156898279)
          ·
            refine ⟨315352131993665772235347419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210234754662443848156898279 315352131993665772235347419)
            ·
              refine ⟨473028197990498658353021129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315352131993665772235347419 473028197990498658353021129)
              ·
                refine ⟨354771148492873993764765847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 473028197990498658353021129 354771148492873993764765847)
                ·
                  refine ⟨532156722739310990647148771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 354771148492873993764765847 532156722739310990647148771)
                  ·
                    refine ⟨798235084108966485970723157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 532156722739310990647148771 798235084108966485970723157)
                    ·
                      refine ⟨2338579347975487751867353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 798235084108966485970723157 2338579347975487751867353)
                      ·
                        rfl

theorem cell23_4554367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_4554367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554367 prefixEnd_4554367 := by exact prefixLift 4554367
  have htrace : WordTrace (prefixWord ++ tailWord_4554367) baseStart_4554367 baseEnd_4554367 := by
    simpa [prefixWord, tailWord_4554367, baseEnd_4554367] using wordTrace_append hprefix tailTrace_4554367
  have hstable : (prefixWord ++ tailWord_4554367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554367).length < 2 ^ (prefixWord ++ tailWord_4554367).sum := by decide
  have hdescent : baseEnd_4554367 < baseStart_4554367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554371 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 3, 3, 2]
def baseStart_4554371 : Nat := 118140960795 + 4554371 * 2 ^ 59
def prefixEnd_4554371 : Nat := 4983230072969 + 3 ^ 40 * 4554371 * 2
def baseEnd_4554371 : Nat := 2338581401898105736217335

theorem tailTrace_4554371 : CollatzResearch.WordTrace tailWord_4554371 prefixEnd_4554371 2338581401898105736217335 := by
  unfold tailWord_4554371
  simp only [CollatzResearch.WordTrace]
  refine ⟨166111556983299166486126967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110741037988866110990751311 166111556983299166486126967)
  ·
    refine ⟨249167335474948749729190451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166111556983299166486126967 249167335474948749729190451)
    ·
      refine ⟨373751003212423124593785677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249167335474948749729190451 373751003212423124593785677)
      ·
        refine ⟨140156626204658671722669629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 373751003212423124593785677 140156626204658671722669629)
        ·
          refine ⟨52558734826747001896001111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140156626204658671722669629 52558734826747001896001111)
          ·
            refine ⟨78838102240120502844001667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52558734826747001896001111 78838102240120502844001667)
            ·
              refine ⟨118257153360180754266002501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78838102240120502844001667 118257153360180754266002501)
              ·
                refine ⟨22173216255033891424875469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118257153360180754266002501 22173216255033891424875469)
                ·
                  refine ⟨8314956095637709284328301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22173216255033891424875469 8314956095637709284328301)
                  ·
                    refine ⟨3118108535864140981623113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8314956095637709284328301 3118108535864140981623113)
                    ·
                      refine ⟨2338581401898105736217335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3118108535864140981623113 2338581401898105736217335)
                      ·
                        rfl

theorem cell23_4554371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 3, 2].length) (baseStart_4554371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554371 prefixEnd_4554371 := by exact prefixLift 4554371
  have htrace : WordTrace (prefixWord ++ tailWord_4554371) baseStart_4554371 baseEnd_4554371 := by
    simpa [prefixWord, tailWord_4554371, baseEnd_4554371] using wordTrace_append hprefix tailTrace_4554371
  have hstable : (prefixWord ++ tailWord_4554371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554371).length < 2 ^ (prefixWord ++ tailWord_4554371).sum := by decide
  have hdescent : baseEnd_4554371 < baseStart_4554371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554372 : List Nat := [2, 3, 2, 1, 5, 1, 2, 1, 2, 4]
def baseStart_4554372 : Nat := 118140960795 + 4554372 * 2 ^ 59
def prefixEnd_4554372 : Nat := 4983230072969 + 3 ^ 40 * 4554372 * 2
def baseEnd_4554372 : Nat := 779527305126253410768277

theorem tailTrace_4554372 : CollatzResearch.WordTrace tailWord_4554372 prefixEnd_4554372 779527305126253410768277 := by
  unfold tailWord_4554372
  simp only [CollatzResearch.WordTrace]
  refine ⟨83055796728147771828456685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110741062304197029104608913 83055796728147771828456685)
  ·
    refine ⟨31145923773055414435671257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83055796728147771828456685 31145923773055414435671257)
    ·
      refine ⟨23359442829791560826753443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31145923773055414435671257 23359442829791560826753443)
      ·
        refine ⟨35039164244687341240130165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23359442829791560826753443 35039164244687341240130165)
        ·
          refine ⟨3284921647939438241262203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35039164244687341240130165 3284921647939438241262203)
          ·
            refine ⟨4927382471909157361893305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3284921647939438241262203 4927382471909157361893305)
            ·
              refine ⟨3695536853931868021419979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4927382471909157361893305 3695536853931868021419979)
              ·
                refine ⟨5543305280897802032129969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3695536853931868021419979 5543305280897802032129969)
                ·
                  refine ⟨4157478960673351524097477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5543305280897802032129969 4157478960673351524097477)
                  ·
                    refine ⟨779527305126253410768277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4157478960673351524097477 779527305126253410768277)
                    ·
                      rfl

theorem cell23_4554372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_4554372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554372 prefixEnd_4554372 := by exact prefixLift 4554372
  have htrace : WordTrace (prefixWord ++ tailWord_4554372) baseStart_4554372 baseEnd_4554372 := by
    simpa [prefixWord, tailWord_4554372, baseEnd_4554372] using wordTrace_append hprefix tailTrace_4554372
  have hstable : (prefixWord ++ tailWord_4554372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554372).length < 2 ^ (prefixWord ++ tailWord_4554372).sum := by decide
  have hdescent : baseEnd_4554372 < baseStart_4554372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554418 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2]
def baseStart_4554418 : Nat := 118140960795 + 4554418 * 2 ^ 59
def prefixEnd_4554418 : Nat := 4983230072969 + 3 ^ 40 * 4554418 * 2
def baseEnd_4554418 : Nat := 2338605535488867052329619

theorem tailTrace_4554418 : CollatzResearch.WordTrace tailWord_4554418 prefixEnd_4554418 2338605535488867052329619 := by
  unfold tailWord_4554418
  simp only [CollatzResearch.WordTrace]
  refine ⟨41528317803532223378271977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110742180809419262342058605 41528317803532223378271977)
  ·
    refine ⟨31146238352649167533703983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41528317803532223378271977 31146238352649167533703983)
    ·
      refine ⟨46719357528973751300555975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31146238352649167533703983 46719357528973751300555975)
      ·
        refine ⟨70079036293460626950833963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46719357528973751300555975 70079036293460626950833963)
        ·
          refine ⟨105118554440190940426250945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70079036293460626950833963 105118554440190940426250945)
          ·
            refine ⟨78838915830143205319688209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105118554440190940426250945 78838915830143205319688209)
            ·
              refine ⟨59129186872607403989766157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78838915830143205319688209 59129186872607403989766157)
              ·
                refine ⟨22173445077227776496162309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59129186872607403989766157 22173445077227776496162309)
                ·
                  refine ⟨4157520951980208093030433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22173445077227776496162309 4157520951980208093030433)
                  ·
                    refine ⟨3118140713985156069772825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4157520951980208093030433 3118140713985156069772825)
                    ·
                      refine ⟨2338605535488867052329619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3118140713985156069772825 2338605535488867052329619)
                      ·
                        rfl

theorem cell23_4554418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_4554418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554418 prefixEnd_4554418 := by exact prefixLift 4554418
  have htrace : WordTrace (prefixWord ++ tailWord_4554418) baseStart_4554418 baseEnd_4554418 := by
    simpa [prefixWord, tailWord_4554418, baseEnd_4554418] using wordTrace_append hprefix tailTrace_4554418
  have hstable : (prefixWord ++ tailWord_4554418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554418).length < 2 ^ (prefixWord ++ tailWord_4554418).sum := by decide
  have hdescent : baseEnd_4554418 < baseStart_4554418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554458 : List Nat := [3, 1, 1, 2, 2, 4, 2, 3, 5]
def baseStart_4554458 : Nat := 118140960795 + 4554458 * 2 ^ 59
def prefixEnd_4554458 : Nat := 4983230072969 + 3 ^ 40 * 4554458 * 2
def baseEnd_4554458 : Nat := 259847341635005210647715

theorem tailTrace_4554458 : CollatzResearch.WordTrace tailWord_4554458 prefixEnd_4554458 259847341635005210647715 := by
  unfold tailWord_4554458
  simp only [CollatzResearch.WordTrace]
  refine ⟨41528682533495995086136007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110743153422655986896362685 41528682533495995086136007)
  ·
    refine ⟨62293023800243992629204011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41528682533495995086136007 62293023800243992629204011)
    ·
      refine ⟨93439535700365988943806017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62293023800243992629204011 93439535700365988943806017)
      ·
        refine ⟨70079651775274491707854513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93439535700365988943806017 70079651775274491707854513)
        ·
          refine ⟨52559738831455868780890885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70079651775274491707854513 52559738831455868780890885)
          ·
            refine ⟨9854951030897975396417041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52559738831455868780890885 9854951030897975396417041)
            ·
              refine ⟨7391213273173481547312781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9854951030897975396417041 7391213273173481547312781)
              ·
                refine ⟨2771704977440055580242293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7391213273173481547312781 2771704977440055580242293)
                ·
                  refine ⟨259847341635005210647715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2771704977440055580242293 259847341635005210647715)
                  ·
                    rfl

theorem cell23_4554458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 5].length) (baseStart_4554458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554458 prefixEnd_4554458 := by exact prefixLift 4554458
  have htrace : WordTrace (prefixWord ++ tailWord_4554458) baseStart_4554458 baseEnd_4554458 := by
    simpa [prefixWord, tailWord_4554458, baseEnd_4554458] using wordTrace_append hprefix tailTrace_4554458
  have hstable : (prefixWord ++ tailWord_4554458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554458).length < 2 ^ (prefixWord ++ tailWord_4554458).sum := by decide
  have hdescent : baseEnd_4554458 < baseStart_4554458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554464 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 5]
def baseStart_4554464 : Nat := 118140960795 + 4554464 * 2 ^ 59
def prefixEnd_4554464 : Nat := 4983230072969 + 3 ^ 40 * 4554464 * 2
def baseEnd_4554464 : Nat := 2338629155598973872354407

theorem tailTrace_4554464 : CollatzResearch.WordTrace tailWord_4554464 prefixEnd_4554464 2338629155598973872354407 := by
  unfold tailWord_4554464
  simp only [CollatzResearch.WordTrace]
  refine ⟨83057474485981121684631223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110743299314641495579508297 83057474485981121684631223)
  ·
    refine ⟨124586211728971682526946835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83057474485981121684631223 124586211728971682526946835)
    ·
      refine ⟨186879317593457523790420253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124586211728971682526946835 186879317593457523790420253)
      ·
        refine ⟨70079744097546571421407595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186879317593457523790420253 70079744097546571421407595)
        ·
          refine ⟨105119616146319857132111393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70079744097546571421407595 105119616146319857132111393)
          ·
            refine ⟨78839712109739892849083545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105119616146319857132111393 78839712109739892849083545)
            ·
              refine ⟨59129784082304919636812659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78839712109739892849083545 59129784082304919636812659)
              ·
                refine ⟨88694676123457379455218989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59129784082304919636812659 88694676123457379455218989)
                ·
                  refine ⟨33260503546296517295707121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88694676123457379455218989 33260503546296517295707121)
                  ·
                    refine ⟨24945377659722387971780341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33260503546296517295707121 24945377659722387971780341)
                    ·
                      refine ⟨2338629155598973872354407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24945377659722387971780341 2338629155598973872354407)
                      ·
                        rfl

theorem cell23_4554464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_4554464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554464 prefixEnd_4554464 := by exact prefixLift 4554464
  have htrace : WordTrace (prefixWord ++ tailWord_4554464) baseStart_4554464 baseEnd_4554464 := by
    simpa [prefixWord, tailWord_4554464, baseEnd_4554464] using wordTrace_append hprefix tailTrace_4554464
  have hstable : (prefixWord ++ tailWord_4554464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554464).length < 2 ^ (prefixWord ++ tailWord_4554464).sum := by decide
  have hdescent : baseEnd_4554464 < baseStart_4554464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554491 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 1, 6, 2]
def baseStart_4554491 : Nat := 118140960795 + 4554491 * 2 ^ 59
def prefixEnd_4554491 : Nat := 4983230072969 + 3 ^ 40 * 4554491 * 2
def baseEnd_4554491 : Nat := 2338643019576645266716783

theorem tailTrace_4554491 : CollatzResearch.WordTrace tailWord_4554491 prefixEnd_4554491 2338643019576645266716783 := by
  unfold tailWord_4554491
  simp only [CollatzResearch.WordTrace]
  refine ⟨166115933742864426980495327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110743955828576284653663551 166115933742864426980495327)
  ·
    refine ⟨249173900614296640470742991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166115933742864426980495327 249173900614296640470742991)
    ·
      refine ⟨373760850921444960706114487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249173900614296640470742991 373760850921444960706114487)
      ·
        refine ⟨560641276382167441059171731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373760850921444960706114487 560641276382167441059171731)
        ·
          refine ⟨840961914573251161588757597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560641276382167441059171731 840961914573251161588757597)
          ·
            refine ⟨315360717964969185595784099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 840961914573251161588757597 315360717964969185595784099)
            ·
              refine ⟨473041076947453778393676149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315360717964969185595784099 473041076947453778393676149)
              ·
                refine ⟨44347600963823791724407139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 473041076947453778393676149 44347600963823791724407139)
                ·
                  refine ⟨66521401445735687586610709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44347600963823791724407139 66521401445735687586610709)
                  ·
                    refine ⟨3118190692768860355622377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66521401445735687586610709 3118190692768860355622377)
                    ·
                      refine ⟨2338643019576645266716783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3118190692768860355622377 2338643019576645266716783)
                      ·
                        rfl

theorem cell23_4554491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 6, 2].length) (baseStart_4554491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554491 prefixEnd_4554491 := by exact prefixLift 4554491
  have htrace : WordTrace (prefixWord ++ tailWord_4554491) baseStart_4554491 baseEnd_4554491 := by
    simpa [prefixWord, tailWord_4554491, baseEnd_4554491] using wordTrace_append hprefix tailTrace_4554491
  have hstable : (prefixWord ++ tailWord_4554491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554491).length < 2 ^ (prefixWord ++ tailWord_4554491).sum := by decide
  have hdescent : baseEnd_4554491 < baseStart_4554491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554528 : List Nat := [2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 3]
def baseStart_4554528 : Nat := 118140960795 + 4554528 * 2 ^ 59
def prefixEnd_4554528 : Nat := 4983230072969 + 3 ^ 40 * 4554528 * 2
def baseEnd_4554528 : Nat := 2338662018360861621954113

theorem tailTrace_4554528 : CollatzResearch.WordTrace tailWord_4554528 prefixEnd_4554528 2338662018360861621954113 := by
  unfold tailWord_4554528
  simp only [CollatzResearch.WordTrace]
  refine ⟨83058641621865191149796119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110744855495820254866394825 83058641621865191149796119)
  ·
    refine ⟨124587962432797786724694179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83058641621865191149796119 124587962432797786724694179)
    ·
      refine ⟨186881943649196680087041269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124587962432797786724694179 186881943649196680087041269)
      ·
        refine ⟨17520182217112188758160119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 186881943649196680087041269 17520182217112188758160119)
        ·
          refine ⟨26280273325668283137240179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17520182217112188758160119 26280273325668283137240179)
          ·
            refine ⟨39420409988502424705860269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26280273325668283137240179 39420409988502424705860269)
            ·
              refine ⟨14782653745688409264697601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39420409988502424705860269 14782653745688409264697601)
              ·
                refine ⟨11086990309266306948523201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14782653745688409264697601 11086990309266306948523201)
                ·
                  refine ⟨8315242731949730211392401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11086990309266306948523201 8315242731949730211392401)
                  ·
                    refine ⟨6236432048962297658544301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8315242731949730211392401 6236432048962297658544301)
                    ·
                      refine ⟨2338662018360861621954113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6236432048962297658544301 2338662018360861621954113)
                      ·
                        rfl

theorem cell23_4554528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_4554528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554528 prefixEnd_4554528 := by exact prefixLift 4554528
  have htrace : WordTrace (prefixWord ++ tailWord_4554528) baseStart_4554528 baseEnd_4554528 := by
    simpa [prefixWord, tailWord_4554528, baseEnd_4554528] using wordTrace_append hprefix tailTrace_4554528
  have hstable : (prefixWord ++ tailWord_4554528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554528).length < 2 ^ (prefixWord ++ tailWord_4554528).sum := by decide
  have hdescent : baseEnd_4554528 < baseStart_4554528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554544 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 1, 11]
def baseStart_4554544 : Nat := 118140960795 + 4554544 * 2 ^ 59
def prefixEnd_4554544 : Nat := 4983230072969 + 3 ^ 40 * 4554544 * 2
def baseEnd_4554544 : Nat := 779556744683777853118013

theorem tailTrace_4554544 : CollatzResearch.WordTrace tailWord_4554544 prefixEnd_4554544 779556744683777853118013 := by
  unfold tailWord_4554544
  simp only [CollatzResearch.WordTrace]
  refine ⟨83058933405836208516087343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110745244541114944688116457 83058933405836208516087343)
  ·
    refine ⟨124588400108754312774131015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83058933405836208516087343 124588400108754312774131015)
    ·
      refine ⟨186882600163131469161196523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124588400108754312774131015 186882600163131469161196523)
      ·
        refine ⟨280323900244697203741794785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186882600163131469161196523 280323900244697203741794785)
        ·
          refine ⟨210242925183522902806346089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280323900244697203741794785 210242925183522902806346089)
          ·
            refine ⟨157682193887642177104759567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210242925183522902806346089 157682193887642177104759567)
            ·
              refine ⟨236523290831463265657139351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157682193887642177104759567 236523290831463265657139351)
              ·
                refine ⟨354784936247194898485709027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236523290831463265657139351 354784936247194898485709027)
                ·
                  refine ⟨532177404370792347728563541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 354784936247194898485709027 532177404370792347728563541)
                  ·
                    refine ⟨779556744683777853118013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 532177404370792347728563541 779556744683777853118013)
                    ·
                      rfl

theorem cell23_4554544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 11].length) (baseStart_4554544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554544 prefixEnd_4554544 := by exact prefixLift 4554544
  have htrace : WordTrace (prefixWord ++ tailWord_4554544) baseStart_4554544 baseEnd_4554544 := by
    simpa [prefixWord, tailWord_4554544, baseEnd_4554544] using wordTrace_append hprefix tailTrace_4554544
  have hstable : (prefixWord ++ tailWord_4554544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554544).length < 2 ^ (prefixWord ++ tailWord_4554544).sum := by decide
  have hdescent : baseEnd_4554544 < baseStart_4554544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554592 : List Nat := [2, 1, 1, 3, 3, 3, 1, 4, 1, 1, 3]
def baseStart_4554592 : Nat := 118140960795 + 4554592 * 2 ^ 59
def prefixEnd_4554592 : Nat := 4983230072969 + 3 ^ 40 * 4554592 * 2
def baseEnd_4554592 : Nat := 2338694881122749371553819

theorem tailTrace_4554592 : CollatzResearch.WordTrace tailWord_4554592 prefixEnd_4554592 2338694881122749371553819 := by
  unfold tailWord_4554592
  simp only [CollatzResearch.WordTrace]
  refine ⟨83059808757749260614961015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110746411676999014153281353 83059808757749260614961015)
  ·
    refine ⟨124589713136623890922441523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83059808757749260614961015 124589713136623890922441523)
    ·
      refine ⟨186884569704935836383662285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124589713136623890922441523 186884569704935836383662285)
      ·
        refine ⟨70081713639350938643873357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186884569704935836383662285 70081713639350938643873357)
        ·
          refine ⟨26280642614756601991452509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70081713639350938643873357 26280642614756601991452509)
          ·
            refine ⟨9855240980533725746794691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26280642614756601991452509 9855240980533725746794691)
            ·
              refine ⟨14782861470800588620192037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9855240980533725746794691 14782861470800588620192037)
              ·
                refine ⟨2771786525775110366286007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14782861470800588620192037 2771786525775110366286007)
                ·
                  refine ⟨4157679788662665549429011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2771786525775110366286007 4157679788662665549429011)
                  ·
                    refine ⟨6236519682993998324143517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4157679788662665549429011 6236519682993998324143517)
                    ·
                      refine ⟨2338694881122749371553819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6236519682993998324143517 2338694881122749371553819)
                      ·
                        rfl

theorem cell23_4554592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 1, 1, 3].length) (baseStart_4554592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554592 prefixEnd_4554592 := by exact prefixLift 4554592
  have htrace : WordTrace (prefixWord ++ tailWord_4554592) baseStart_4554592 baseEnd_4554592 := by
    simpa [prefixWord, tailWord_4554592, baseEnd_4554592] using wordTrace_append hprefix tailTrace_4554592
  have hstable : (prefixWord ++ tailWord_4554592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554592).length < 2 ^ (prefixWord ++ tailWord_4554592).sum := by decide
  have hdescent : baseEnd_4554592 < baseStart_4554592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554601 : List Nat := [1, 2, 1, 1, 1, 3, 1, 6, 1, 1, 5]
def baseStart_4554601 : Nat := 118140960795 + 4554601 * 2 ^ 59
def prefixEnd_4554601 : Nat := 4983230072969 + 3 ^ 40 * 4554601 * 2
def baseEnd_4554601 : Nat := 2338699502448639836341277

theorem tailTrace_4554601 : CollatzResearch.WordTrace tailWord_4554601 prefixEnd_4554601 2338699502448639836341277 := by
  unfold tailWord_4554601
  simp only [CollatzResearch.WordTrace]
  refine ⟨166119945772465915766999657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110746630514977277177999771 166119945772465915766999657)
  ·
    refine ⟨124589959329349436825249743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166119945772465915766999657 124589959329349436825249743)
    ·
      refine ⟨186884938994024155237874615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124589959329349436825249743 186884938994024155237874615)
      ·
        refine ⟨280327408491036232856811923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186884938994024155237874615 280327408491036232856811923)
        ·
          refine ⟨420491112736554349285217885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280327408491036232856811923 420491112736554349285217885)
          ·
            refine ⟨157684167276207880981956707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 420491112736554349285217885 157684167276207880981956707)
            ·
              refine ⟨236526250914311821472935061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157684167276207880981956707 236526250914311821472935061)
              ·
                refine ⟨11087168011608366631543831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 236526250914311821472935061 11087168011608366631543831)
                ·
                  refine ⟨16630752017412549947315747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11087168011608366631543831 16630752017412549947315747)
                  ·
                    refine ⟨24946128026118824920973621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16630752017412549947315747 24946128026118824920973621)
                    ·
                      refine ⟨2338699502448639836341277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24946128026118824920973621 2338699502448639836341277)
                      ·
                        rfl

theorem cell23_4554601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 1, 5].length) (baseStart_4554601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554601 prefixEnd_4554601 := by exact prefixLift 4554601
  have htrace : WordTrace (prefixWord ++ tailWord_4554601) baseStart_4554601 baseEnd_4554601 := by
    simpa [prefixWord, tailWord_4554601, baseEnd_4554601] using wordTrace_append hprefix tailTrace_4554601
  have hstable : (prefixWord ++ tailWord_4554601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554601).length < 2 ^ (prefixWord ++ tailWord_4554601).sum := by decide
  have hdescent : baseEnd_4554601 < baseStart_4554601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554618 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3]
def baseStart_4554618 : Nat := 118140960795 + 4554618 * 2 ^ 59
def prefixEnd_4554618 : Nat := 4983230072969 + 3 ^ 40 * 4554618 * 2
def baseEnd_4554618 : Nat := 2338708231619766269828699

theorem tailTrace_4554618 : CollatzResearch.WordTrace tailWord_4554618 prefixEnd_4554618 2338708231619766269828699 := by
  unfold tailWord_4554618
  simp only [CollatzResearch.WordTrace]
  refine ⟨41530141453351081917592127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110747043875602885113579005 41530141453351081917592127)
  ·
    refine ⟨62295212180026622876388191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41530141453351081917592127 62295212180026622876388191)
    ·
      refine ⟨93442818270039934314582287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62295212180026622876388191 93442818270039934314582287)
      ·
        refine ⟨140164227405059901471873431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93442818270039934314582287 140164227405059901471873431)
        ·
          refine ⟨210246341107589852207810147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140164227405059901471873431 210246341107589852207810147)
          ·
            refine ⟨315369511661384778311715221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210246341107589852207810147 315369511661384778311715221)
            ·
              refine ⟨14782945859127411483361651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 315369511661384778311715221 14782945859127411483361651)
              ·
                refine ⟨22174418788691117225042477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14782945859127411483361651 22174418788691117225042477)
                ·
                  refine ⟨8315407045759168959390929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22174418788691117225042477 8315407045759168959390929)
                  ·
                    refine ⟨6236555284319376719543197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8315407045759168959390929 6236555284319376719543197)
                    ·
                      refine ⟨2338708231619766269828699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6236555284319376719543197 2338708231619766269828699)
                      ·
                        rfl

theorem cell23_4554618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3].length) (baseStart_4554618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554618 prefixEnd_4554618 := by exact prefixLift 4554618
  have htrace : WordTrace (prefixWord ++ tailWord_4554618) baseStart_4554618 baseEnd_4554618 := by
    simpa [prefixWord, tailWord_4554618, baseEnd_4554618] using wordTrace_append hprefix tailTrace_4554618
  have hstable : (prefixWord ++ tailWord_4554618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554618).length < 2 ^ (prefixWord ++ tailWord_4554618).sum := by decide
  have hdescent : baseEnd_4554618 < baseStart_4554618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554628 : List Nat := [2, 3, 2, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_4554628 : Nat := 118140960795 + 4554628 * 2 ^ 59
def prefixEnd_4554628 : Nat := 4983230072969 + 3 ^ 40 * 4554628 * 2
def baseEnd_4554628 : Nat := 2338713366426311230703653

theorem tailTrace_4554628 : CollatzResearch.WordTrace tailWord_4554628 prefixEnd_4554628 2338713366426311230703653 := by
  unfold tailWord_4554628
  simp only [CollatzResearch.WordTrace]
  refine ⟨83060465271684049689116269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110747287028912066252155025 83060465271684049689116269)
  ·
    refine ⟨31147674476881518633418601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83060465271684049689116269 31147674476881518633418601)
    ·
      refine ⟨23360755857661138975063951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31147674476881518633418601 23360755857661138975063951)
      ·
        refine ⟨35041133786491708462595927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23360755857661138975063951 35041133786491708462595927)
        ·
          refine ⟨52561700679737562693893891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35041133786491708462595927 52561700679737562693893891)
          ·
            refine ⟨78842551019606344040840837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52561700679737562693893891 78842551019606344040840837)
            ·
              refine ⟨14782978316176189507657657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78842551019606344040840837 14782978316176189507657657)
              ·
                refine ⟨11087233737132142130743243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14782978316176189507657657 11087233737132142130743243)
                ·
                  refine ⟨16630850605698213196114865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11087233737132142130743243 16630850605698213196114865)
                  ·
                    refine ⟨12473137954273659897086149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16630850605698213196114865 12473137954273659897086149)
                    ·
                      refine ⟨2338713366426311230703653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12473137954273659897086149 2338713366426311230703653)
                      ·
                        rfl

theorem cell23_4554628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_4554628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554628 prefixEnd_4554628 := by exact prefixLift 4554628
  have htrace : WordTrace (prefixWord ++ tailWord_4554628) baseStart_4554628 baseEnd_4554628 := by
    simpa [prefixWord, tailWord_4554628, baseEnd_4554628] using wordTrace_append hprefix tailTrace_4554628
  have hstable : (prefixWord ++ tailWord_4554628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554628).length < 2 ^ (prefixWord ++ tailWord_4554628).sum := by decide
  have hdescent : baseEnd_4554628 < baseStart_4554628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554642 : List Nat := [3, 2, 3, 2, 1, 1, 3, 2, 2, 4]
def baseStart_4554642 : Nat := 118140960795 + 4554642 * 2 ^ 59
def prefixEnd_4554642 : Nat := 4983230072969 + 3 ^ 40 * 4554642 * 2
def baseEnd_4554642 : Nat := 779573518385158058642863

theorem tailTrace_4554642 : CollatzResearch.WordTrace tailWord_4554642 prefixEnd_4554642 779573518385158058642863 := by
  unfold tailWord_4554642
  simp only [CollatzResearch.WordTrace]
  refine ⟨41530360291329344942310545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110747627443544919846161453 41530360291329344942310545)
  ·
    refine ⟨31147770218497008706732909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41530360291329344942310545 31147770218497008706732909)
    ·
      refine ⟨11680413831936378265024841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31147770218497008706732909 11680413831936378265024841)
      ·
        refine ⟨8760310373952283698768631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11680413831936378265024841 8760310373952283698768631)
        ·
          refine ⟨13140465560928425548152947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8760310373952283698768631 13140465560928425548152947)
          ·
            refine ⟨19710698341392638322229421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13140465560928425548152947 19710698341392638322229421)
            ·
              refine ⟨7391511878022239370836033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19710698341392638322229421 7391511878022239370836033)
              ·
                refine ⟨5543633908516679528127025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7391511878022239370836033 5543633908516679528127025)
                ·
                  refine ⟨4157725431387509646095269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5543633908516679528127025 4157725431387509646095269)
                  ·
                    refine ⟨779573518385158058642863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4157725431387509646095269 779573518385158058642863)
                    ·
                      rfl

theorem cell23_4554642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_4554642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554642 prefixEnd_4554642 := by exact prefixLift 4554642
  have htrace : WordTrace (prefixWord ++ tailWord_4554642) baseStart_4554642 baseEnd_4554642 := by
    simpa [prefixWord, tailWord_4554642, baseEnd_4554642] using wordTrace_append hprefix tailTrace_4554642
  have hstable : (prefixWord ++ tailWord_4554642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554642).length < 2 ^ (prefixWord ++ tailWord_4554642).sum := by decide
  have hdescent : baseEnd_4554642 < baseStart_4554642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554661 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 4, 2, 5]
def baseStart_4554661 : Nat := 118140960795 + 4554661 * 2 ^ 59
def prefixEnd_4554661 : Nat := 4983230072969 + 3 ^ 40 * 4554661 * 2
def baseEnd_4554661 : Nat := 2338730311287909601591001

theorem tailTrace_4554661 : CollatzResearch.WordTrace tailWord_4554661 prefixEnd_4554661 2338730311287909601591001 := by
  unfold tailWord_4554661
  simp only [CollatzResearch.WordTrace]
  refine ⟨166122134152248546014183837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110748089434832364009455891 166122134152248546014183837)
  ·
    refine ⟨62295800307093204755318939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166122134152248546014183837 62295800307093204755318939)
    ·
      refine ⟨93443700460639807132978409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62295800307093204755318939 93443700460639807132978409)
      ·
        refine ⟨70082775345479855349733807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93443700460639807132978409 70082775345479855349733807)
        ·
          refine ⟨105124163018219783024600711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70082775345479855349733807 105124163018219783024600711)
          ·
            refine ⟨157686244527329674536901067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105124163018219783024600711 157686244527329674536901067)
            ·
              refine ⟨236529366790994511805351601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157686244527329674536901067 236529366790994511805351601)
              ·
                refine ⟨177397025093245883854013701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236529366790994511805351601 177397025093245883854013701)
                ·
                  refine ⟨33261942204983603222627569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 177397025093245883854013701 33261942204983603222627569)
                  ·
                    refine ⟨24946456653737702416970677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33261942204983603222627569 24946456653737702416970677)
                    ·
                      refine ⟨2338730311287909601591001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24946456653737702416970677 2338730311287909601591001)
                      ·
                        rfl

theorem cell23_4554661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_4554661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554661 prefixEnd_4554661 := by exact prefixLift 4554661
  have htrace : WordTrace (prefixWord ++ tailWord_4554661) baseStart_4554661 baseEnd_4554661 := by
    simpa [prefixWord, tailWord_4554661, baseEnd_4554661] using wordTrace_append hprefix tailTrace_4554661
  have hstable : (prefixWord ++ tailWord_4554661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554661).length < 2 ^ (prefixWord ++ tailWord_4554661).sum := by decide
  have hdescent : baseEnd_4554661 < baseStart_4554661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554708 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_4554708 : Nat := 118140960795 + 4554708 * 2 ^ 59
def prefixEnd_4554708 : Nat := 4983230072969 + 3 ^ 40 * 4554708 * 2
def baseEnd_4554708 : Nat := 2338754444878670917703285

theorem tailTrace_4554708 : CollatzResearch.WordTrace tailWord_4554708 prefixEnd_4554708 2338754444878670917703285 := by
  unfold tailWord_4554708
  simp only [CollatzResearch.WordTrace]
  refine ⟨83061924191539136520572389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110749232255385515360763185 83061924191539136520572389)
  ·
    refine ⟨15574110785913588097607323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83061924191539136520572389 15574110785913588097607323)
    ·
      refine ⟨23361166178870382146410985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15574110785913588097607323 23361166178870382146410985)
      ·
        refine ⟨17520874634152786609808239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23361166178870382146410985 17520874634152786609808239)
        ·
          refine ⟨26281311951229179914712359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17520874634152786609808239 26281311951229179914712359)
          ·
            refine ⟨39421967926843769872068539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26281311951229179914712359 39421967926843769872068539)
            ·
              refine ⟨59132951890265654808102809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39421967926843769872068539 59132951890265654808102809)
              ·
                refine ⟨44349713917699241106077107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59132951890265654808102809 44349713917699241106077107)
                ·
                  refine ⟨66524570876548861659115661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44349713917699241106077107 66524570876548861659115661)
                  ·
                    refine ⟨24946714078705823122168373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66524570876548861659115661 24946714078705823122168373)
                    ·
                      refine ⟨2338754444878670917703285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24946714078705823122168373 2338754444878670917703285)
                      ·
                        rfl

theorem cell23_4554708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_4554708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554708 prefixEnd_4554708 := by exact prefixLift 4554708
  have htrace : WordTrace (prefixWord ++ tailWord_4554708) baseStart_4554708 baseEnd_4554708 := by
    simpa [prefixWord, tailWord_4554708, baseEnd_4554708] using wordTrace_append hprefix tailTrace_4554708
  have hstable : (prefixWord ++ tailWord_4554708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554708).length < 2 ^ (prefixWord ++ tailWord_4554708).sum := by decide
  have hdescent : baseEnd_4554708 < baseStart_4554708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554731 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 8]
def baseStart_4554731 : Nat := 118140960795 + 4554731 * 2 ^ 59
def prefixEnd_4554731 : Nat := 4983230072969 + 3 ^ 40 * 4554731 * 2
def baseEnd_4554731 : Nat := 2338766254933724327715679

theorem tailTrace_4554731 : CollatzResearch.WordTrace tailWord_4554731 prefixEnd_4554731 2338766254933724327715679 := by
  unfold tailWord_4554731
  simp only [CollatzResearch.WordTrace]
  refine ⟨166124687261994947969232047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110749791507996631979488031 166124687261994947969232047)
  ·
    refine ⟨249187030892992421953848071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166124687261994947969232047 249187030892992421953848071)
    ·
      refine ⟨373780546339488632930772107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249187030892992421953848071 373780546339488632930772107)
      ·
        refine ⟨560670819509232949396158161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373780546339488632930772107 560670819509232949396158161)
        ·
          refine ⟨420503114631924712047118621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 560670819509232949396158161 420503114631924712047118621)
          ·
            refine ⟨157688667986971767017669483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 420503114631924712047118621 157688667986971767017669483)
            ·
              refine ⟨236533001980457650526504225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157688667986971767017669483 236533001980457650526504225)
              ·
                refine ⟨177399751485343237894878169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236533001980457650526504225 177399751485343237894878169)
                ·
                  refine ⟨133049813614007428421158627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177399751485343237894878169 133049813614007428421158627)
                  ·
                    refine ⟨199574720421011142631737941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 133049813614007428421158627 199574720421011142631737941)
                    ·
                      refine ⟨2338766254933724327715679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 199574720421011142631737941 2338766254933724327715679)
                      ·
                        rfl

theorem cell23_4554731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 8].length) (baseStart_4554731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554731 prefixEnd_4554731 := by exact prefixLift 4554731
  have htrace : WordTrace (prefixWord ++ tailWord_4554731) baseStart_4554731 baseEnd_4554731 := by
    simpa [prefixWord, tailWord_4554731, baseEnd_4554731] using wordTrace_append hprefix tailTrace_4554731
  have hstable : (prefixWord ++ tailWord_4554731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554731).length < 2 ^ (prefixWord ++ tailWord_4554731).sum := by decide
  have hdescent : baseEnd_4554731 < baseStart_4554731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554762 : List Nat := [3, 1, 2, 2, 4, 1, 1, 4, 5]
def baseStart_4554762 : Nat := 118140960795 + 4554762 * 2 ^ 59
def prefixEnd_4554762 : Nat := 4983230072969 + 3 ^ 40 * 4554762 * 2
def baseEnd_4554762 : Nat := 259864685870445967380893

theorem tailTrace_4554762 : CollatzResearch.WordTrace tailWord_4554762 prefixEnd_4554762 259864685870445967380893 := by
  unfold tailWord_4554762
  simp only [CollatzResearch.WordTrace]
  refine ⟨41531454481220660065902635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110750545283255093509073693 41531454481220660065902635)
  ·
    refine ⟨62297181721830990098853953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41531454481220660065902635 62297181721830990098853953)
    ·
      refine ⟨46722886291373242574140465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62297181721830990098853953 46722886291373242574140465)
      ·
        refine ⟨35042164718529931930605349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46722886291373242574140465 35042164718529931930605349)
        ·
          refine ⟨6570405884724362236988503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35042164718529931930605349 6570405884724362236988503)
          ·
            refine ⟨9855608827086543355482755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6570405884724362236988503 9855608827086543355482755)
            ·
              refine ⟨14783413240629815033224133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9855608827086543355482755 14783413240629815033224133)
              ·
                refine ⟨2771889982618090318729525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14783413240629815033224133 2771889982618090318729525)
                ·
                  refine ⟨259864685870445967380893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2771889982618090318729525 259864685870445967380893)
                  ·
                    rfl

theorem cell23_4554762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 5].length) (baseStart_4554762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554762 prefixEnd_4554762 := by exact prefixLift 4554762
  have htrace : WordTrace (prefixWord ++ tailWord_4554762) baseStart_4554762 baseEnd_4554762 := by
    simpa [prefixWord, tailWord_4554762, baseEnd_4554762] using wordTrace_append hprefix tailTrace_4554762
  have hstable : (prefixWord ++ tailWord_4554762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554762).length < 2 ^ (prefixWord ++ tailWord_4554762).sum := by decide
  have hdescent : baseEnd_4554762 < baseStart_4554762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554792 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 1, 7]
def baseStart_4554792 : Nat := 118140960795 + 4554792 * 2 ^ 59
def prefixEnd_4554792 : Nat := 4983230072969 + 3 ^ 40 * 4554792 * 2
def baseEnd_4554792 : Nat := 779599192417882863017633

theorem tailTrace_4554792 : CollatzResearch.WordTrace tailWord_4554792 prefixEnd_4554792 779599192417882863017633 := by
  unfold tailWord_4554792
  simp only [CollatzResearch.WordTrace]
  refine ⟨83063456057386977693601315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110751274743182636924801753 83063456057386977693601315)
  ·
    refine ⟨124595184086080466540401973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83063456057386977693601315 124595184086080466540401973)
    ·
      refine ⟨11680798508070043738162685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124595184086080466540401973 11680798508070043738162685)
      ·
        refine ⟨4380299440526266401811007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11680798508070043738162685 4380299440526266401811007)
        ·
          refine ⟨6570449160789399602716511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4380299440526266401811007 6570449160789399602716511)
          ·
            refine ⟨9855673741184099404074767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6570449160789399602716511 9855673741184099404074767)
            ·
              refine ⟨14783510611776149106112151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9855673741184099404074767 14783510611776149106112151)
              ·
                refine ⟨22175265917664223659168227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14783510611776149106112151 22175265917664223659168227)
                ·
                  refine ⟨33262898876496335488752341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22175265917664223659168227 33262898876496335488752341)
                  ·
                    refine ⟨779599192417882863017633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33262898876496335488752341 779599192417882863017633)
                    ·
                      rfl

theorem cell23_4554792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_4554792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554792 prefixEnd_4554792 := by exact prefixLift 4554792
  have htrace : WordTrace (prefixWord ++ tailWord_4554792) baseStart_4554792 baseEnd_4554792 := by
    simpa [prefixWord, tailWord_4554792, baseEnd_4554792] using wordTrace_append hprefix tailTrace_4554792
  have hstable : (prefixWord ++ tailWord_4554792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554792).length < 2 ^ (prefixWord ++ tailWord_4554792).sum := by decide
  have hdescent : baseEnd_4554792 < baseStart_4554792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554815 : List Nat := [1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 3]
def baseStart_4554815 : Nat := 118140960795 + 4554815 * 2 ^ 59
def prefixEnd_4554815 : Nat := 4983230072969 + 3 ^ 40 * 4554815 * 2
def baseEnd_4554815 : Nat := 2338809387308701999065293

theorem tailTrace_4554815 : CollatzResearch.WordTrace tailWord_4554815 prefixEnd_4554815 2338809387308701999065293 := by
  unfold tailWord_4554815
  simp only [CollatzResearch.WordTrace]
  refine ⟨166127750993690630315289899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110751833995793753543526599 166127750993690630315289899)
  ·
    refine ⟨249191626490535945472934849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166127750993690630315289899 249191626490535945472934849)
    ·
      refine ⟨186893719867901959104701137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249191626490535945472934849 186893719867901959104701137)
      ·
        refine ⟨140170289900926469328525853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186893719867901959104701137 140170289900926469328525853)
        ·
          refine ⟨52563858712847425998197195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140170289900926469328525853 52563858712847425998197195)
          ·
            refine ⟨78845788069271138997295793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52563858712847425998197195 78845788069271138997295793)
            ·
              refine ⟨59134341051953354247971845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78845788069271138997295793 59134341051953354247971845)
              ·
                refine ⟨11087688947241253921494721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59134341051953354247971845 11087688947241253921494721)
                ·
                  refine ⟨8315766710430940441121041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11087688947241253921494721 8315766710430940441121041)
                  ·
                    refine ⟨6236825032823205330840781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8315766710430940441121041 6236825032823205330840781)
                    ·
                      refine ⟨2338809387308701999065293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6236825032823205330840781 2338809387308701999065293)
                      ·
                        rfl

theorem cell23_4554815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 3].length) (baseStart_4554815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554815 prefixEnd_4554815 := by exact prefixLift 4554815
  have htrace : WordTrace (prefixWord ++ tailWord_4554815) baseStart_4554815 baseEnd_4554815 := by
    simpa [prefixWord, tailWord_4554815, baseEnd_4554815] using wordTrace_append hprefix tailTrace_4554815
  have hstable : (prefixWord ++ tailWord_4554815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554815).length < 2 ^ (prefixWord ++ tailWord_4554815).sum := by decide
  have hdescent : baseEnd_4554815 < baseStart_4554815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554865 : List Nat := [1, 2, 2, 2, 1, 1, 3, 5, 1, 5]
def baseStart_4554865 : Nat := 118140960795 + 4554865 * 2 ^ 59
def prefixEnd_4554865 : Nat := 4983230072969 + 3 ^ 40 * 4554865 * 2
def baseEnd_4554865 : Nat := 779611687113808934480021

theorem tailTrace_4554865 : CollatzResearch.WordTrace tailWord_4554865 prefixEnd_4554865 779611687113808934480021 := by
  unfold tailWord_4554865
  simp only [CollatzResearch.WordTrace]
  refine ⟨166129574643509488854610049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110753049762339659236406699 166129574643509488854610049)
  ·
    refine ⟨124597180982632116640957537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166129574643509488854610049 124597180982632116640957537)
    ·
      refine ⟨93447885736974087480718153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124597180982632116640957537 93447885736974087480718153)
      ·
        refine ⟨70085914302730565610538615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93447885736974087480718153 70085914302730565610538615)
        ·
          refine ⟨105128871454095848415807923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70085914302730565610538615 105128871454095848415807923)
          ·
            refine ⟨157693307181143772623711885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105128871454095848415807923 157693307181143772623711885)
            ·
              refine ⟨59134990192928914733891957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157693307181143772623711885 59134990192928914733891957)
              ·
                refine ⟨5543905330587085756302371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59134990192928914733891957 5543905330587085756302371)
                ·
                  refine ⟨8315857995880628634453557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5543905330587085756302371 8315857995880628634453557)
                  ·
                    refine ⟨779611687113808934480021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8315857995880628634453557 779611687113808934480021)
                    ·
                      rfl

theorem cell23_4554865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 5].length) (baseStart_4554865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554865 prefixEnd_4554865 := by exact prefixLift 4554865
  have htrace : WordTrace (prefixWord ++ tailWord_4554865) baseStart_4554865 baseEnd_4554865 := by
    simpa [prefixWord, tailWord_4554865, baseEnd_4554865] using wordTrace_append hprefix tailTrace_4554865
  have hstable : (prefixWord ++ tailWord_4554865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554865).length < 2 ^ (prefixWord ++ tailWord_4554865).sum := by decide
  have hdescent : baseEnd_4554865 < baseStart_4554865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554906 : List Nat := [3, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2]
def baseStart_4554906 : Nat := 118140960795 + 4554906 * 2 ^ 59
def prefixEnd_4554906 : Nat := 4983230072969 + 3 ^ 40 * 4554906 * 2
def baseEnd_4554906 : Nat := 2338856114048261143027375

theorem tailTrace_4554906 : CollatzResearch.WordTrace tailWord_4554906 prefixEnd_4554906 2338856114048261143027375 := by
  unfold tailWord_4554906
  simp only [CollatzResearch.WordTrace]
  refine ⟨41532767509090238214213143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110754046690907301904568381 41532767509090238214213143)
  ·
    refine ⟨62299151263635357321319715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41532767509090238214213143 62299151263635357321319715)
    ·
      refine ⟨93448726895453035981979573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62299151263635357321319715 93448726895453035981979573)
      ·
        refine ⟨8760818146448722123310585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93448726895453035981979573 8760818146448722123310585)
        ·
          refine ⟨6570613609836541592482939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8760818146448722123310585 6570613609836541592482939)
          ·
            refine ⟨9855920414754812388724409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6570613609836541592482939 9855920414754812388724409)
            ·
              refine ⟨7391940311066109291543307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9855920414754812388724409 7391940311066109291543307)
              ·
                refine ⟨11087910466599163937314961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7391940311066109291543307 11087910466599163937314961)
                ·
                  refine ⟨8315932849949372952986221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11087910466599163937314961 8315932849949372952986221)
                  ·
                    refine ⟨3118474818731014857369833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8315932849949372952986221 3118474818731014857369833)
                    ·
                      refine ⟨2338856114048261143027375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3118474818731014857369833 2338856114048261143027375)
                      ·
                        rfl

theorem cell23_4554906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_4554906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554906 prefixEnd_4554906 := by exact prefixLift 4554906
  have htrace : WordTrace (prefixWord ++ tailWord_4554906) baseStart_4554906 baseEnd_4554906 := by
    simpa [prefixWord, tailWord_4554906, baseEnd_4554906] using wordTrace_append hprefix tailTrace_4554906
  have hstable : (prefixWord ++ tailWord_4554906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554906).length < 2 ^ (prefixWord ++ tailWord_4554906).sum := by decide
  have hdescent : baseEnd_4554906 < baseStart_4554906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554925 : List Nat := [1, 5, 2, 1, 2, 12]
def baseStart_4554925 : Nat := 118140960795 + 4554925 * 2 ^ 59
def prefixEnd_4554925 : Nat := 4983230072969 + 3 ^ 40 * 4554925 * 2
def baseEnd_4554925 : Nat := 9624962428727146373209

theorem tailTrace_4554925 : CollatzResearch.WordTrace tailWord_4554925 prefixEnd_4554925 9624962428727146373209 := by
  unfold tailWord_4554925
  simp only [CollatzResearch.WordTrace]
  refine ⟨166131763023292119101794229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110754508682194746067862819 166131763023292119101794229)
  ·
    refine ⟨15574852783433636165793209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166131763023292119101794229 15574852783433636165793209)
    ·
      refine ⟨11681139587575227124344907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15574852783433636165793209 11681139587575227124344907)
      ·
        refine ⟨17521709381362840686517361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11681139587575227124344907 17521709381362840686517361)
        ·
          refine ⟨13141282036022130514888021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17521709381362840686517361 13141282036022130514888021)
          ·
            refine ⟨9624962428727146373209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 13141282036022130514888021 9624962428727146373209)
            ·
              rfl

theorem cell23_4554925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 12].length) (baseStart_4554925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554925 prefixEnd_4554925 := by exact prefixLift 4554925
  have htrace : WordTrace (prefixWord ++ tailWord_4554925) baseStart_4554925 baseEnd_4554925 := by
    simpa [prefixWord, tailWord_4554925, baseEnd_4554925] using wordTrace_append hprefix tailTrace_4554925
  have hstable : (prefixWord ++ tailWord_4554925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554925).length < 2 ^ (prefixWord ++ tailWord_4554925).sum := by decide
  have hdescent : baseEnd_4554925 < baseStart_4554925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554936 : List Nat := [2, 1, 2, 1, 2, 1, 5, 4, 1, 2, 2]
def baseStart_4554936 : Nat := 118140960795 + 4554936 * 2 ^ 59
def prefixEnd_4554936 : Nat := 4983230072969 + 3 ^ 40 * 4554936 * 2
def baseEnd_4554936 : Nat := 2338871518467896025652237

theorem tailTrace_4554936 : CollatzResearch.WordTrace tailWord_4554936 prefixEnd_4554936 2338871518467896025652237 := by
  unfold tailWord_4554936
  simp only [CollatzResearch.WordTrace]
  refine ⟨83066082113126133990222331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110754776150834845320296441 83066082113126133990222331)
  ·
    refine ⟨124599123169689200985333497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83066082113126133990222331 124599123169689200985333497)
    ·
      refine ⟨93449342377266900739000123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124599123169689200985333497 93449342377266900739000123)
      ·
        refine ⟨140174013565900351108500185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93449342377266900739000123 140174013565900351108500185)
        ·
          refine ⟨105130510174425263331375139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140174013565900351108500185 105130510174425263331375139)
          ·
            refine ⟨157695765261637894997062709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105130510174425263331375139 157695765261637894997062709)
            ·
              refine ⟨14783977993278552655974629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 157695765261637894997062709 14783977993278552655974629)
              ·
                refine ⟨2771995873739728622995243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14783977993278552655974629 2771995873739728622995243)
                ·
                  refine ⟨4157993810609592934492865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2771995873739728622995243 4157993810609592934492865)
                  ·
                    refine ⟨3118495357957194700869649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4157993810609592934492865 3118495357957194700869649)
                    ·
                      refine ⟨2338871518467896025652237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3118495357957194700869649 2338871518467896025652237)
                      ·
                        rfl

theorem cell23_4554936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 1, 2, 2].length) (baseStart_4554936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554936 prefixEnd_4554936 := by exact prefixLift 4554936
  have htrace : WordTrace (prefixWord ++ tailWord_4554936) baseStart_4554936 baseEnd_4554936 := by
    simpa [prefixWord, tailWord_4554936, baseEnd_4554936] using wordTrace_append hprefix tailTrace_4554936
  have hstable : (prefixWord ++ tailWord_4554936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554936).length < 2 ^ (prefixWord ++ tailWord_4554936).sum := by decide
  have hdescent : baseEnd_4554936 < baseStart_4554936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554946 : List Nat := [3, 5, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_4554946 : Nat := 118140960795 + 4554946 * 2 ^ 59
def prefixEnd_4554946 : Nat := 4983230072969 + 3 ^ 40 * 4554946 * 2
def baseEnd_4554946 : Nat := 779625551091480328842397

theorem tailTrace_4554946 : CollatzResearch.WordTrace tailWord_4554946 prefixEnd_4554946 779625551091480328842397 := by
  unfold tailWord_4554946
  simp only [CollatzResearch.WordTrace]
  refine ⟨41533132239054009922077173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110755019304144026458872461 41533132239054009922077173)
  ·
    refine ⟨3893731147411313430194735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41533132239054009922077173 3893731147411313430194735)
    ·
      refine ⟨5840596721116970145292103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3893731147411313430194735 5840596721116970145292103)
      ·
        refine ⟨8760895081675455217938155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5840596721116970145292103 8760895081675455217938155)
        ·
          refine ⟨13141342622513182826907233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8760895081675455217938155 13141342622513182826907233)
          ·
            refine ⟨9856006966884887120180425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13141342622513182826907233 9856006966884887120180425)
            ·
              refine ⟨7392005225163665340135319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9856006966884887120180425 7392005225163665340135319)
              ·
                refine ⟨11088007837745498010202979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7392005225163665340135319 11088007837745498010202979)
                ·
                  refine ⟨16632011756618247015304469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11088007837745498010202979 16632011756618247015304469)
                  ·
                    refine ⟨779625551091480328842397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16632011756618247015304469 779625551091480328842397)
                    ·
                      rfl

theorem cell23_4554946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_4554946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554946 prefixEnd_4554946 := by exact prefixLift 4554946
  have htrace : WordTrace (prefixWord ++ tailWord_4554946) baseStart_4554946 baseEnd_4554946 := by
    simpa [prefixWord, tailWord_4554946, baseEnd_4554946] using wordTrace_append hprefix tailTrace_4554946
  have hstable : (prefixWord ++ tailWord_4554946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554946).length < 2 ^ (prefixWord ++ tailWord_4554946).sum := by decide
  have hdescent : baseEnd_4554946 < baseStart_4554946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554952 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 6, 1, 3]
def baseStart_4554952 : Nat := 118140960795 + 4554952 * 2 ^ 59
def prefixEnd_4554952 : Nat := 4983230072969 + 3 ^ 40 * 4554952 * 2
def baseEnd_4554952 : Nat := 2338879734158367963052163

theorem tailTrace_4554952 : CollatzResearch.WordTrace tailWord_4554952 prefixEnd_4554952 2338879734158367963052163 := by
  unfold tailWord_4554952
  simp only [CollatzResearch.WordTrace]
  refine ⟨83066373897097151356513555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110755165196129535142018073 83066373897097151356513555)
  ·
    refine ⟨124599560845645727034770333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83066373897097151356513555 124599560845645727034770333)
    ·
      refine ⟨46724835317117147638038875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124599560845645727034770333 46724835317117147638038875)
      ·
        refine ⟨70087252975675721457058313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46724835317117147638038875 70087252975675721457058313)
        ·
          refine ⟨52565439731756791092793735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70087252975675721457058313 52565439731756791092793735)
          ·
            refine ⟨78848159597635186639190603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52565439731756791092793735 78848159597635186639190603)
            ·
              refine ⟨118272239396452779958785905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78848159597635186639190603 118272239396452779958785905)
              ·
                refine ⟨88704179547339584969089429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118272239396452779958785905 88704179547339584969089429)
                ·
                  refine ⟨4158008416281543045426067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88704179547339584969089429 4158008416281543045426067)
                  ·
                    refine ⟨6237012624422314568139101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4158008416281543045426067 6237012624422314568139101)
                    ·
                      refine ⟨2338879734158367963052163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6237012624422314568139101 2338879734158367963052163)
                      ·
                        rfl

theorem cell23_4554952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_4554952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554952 prefixEnd_4554952 := by exact prefixLift 4554952
  have htrace : WordTrace (prefixWord ++ tailWord_4554952) baseStart_4554952 baseEnd_4554952 := by
    simpa [prefixWord, tailWord_4554952, baseEnd_4554952] using wordTrace_append hprefix tailTrace_4554952
  have hstable : (prefixWord ++ tailWord_4554952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554952).length < 2 ^ (prefixWord ++ tailWord_4554952).sum := by decide
  have hdescent : baseEnd_4554952 < baseStart_4554952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554973 : List Nat := [1, 4, 3, 2, 1, 3, 2, 1, 1, 2, 3]
def baseStart_4554973 : Nat := 118140960795 + 4554973 * 2 ^ 59
def prefixEnd_4554973 : Nat := 4983230072969 + 3 ^ 40 * 4554973 * 2
def baseEnd_4554973 : Nat := 2338890517252112380889567

theorem tailTrace_4554973 : CollatzResearch.WordTrace tailWord_4554973 prefixEnd_4554973 2338890517252112380889567 := by
  unfold tailWord_4554973
  simp only [CollatzResearch.WordTrace]
  refine ⟨166133513727118223299541573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110755675818078815533027715 166133513727118223299541573)
  ·
    refine ⟨31150033823834666868664045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166133513727118223299541573 31150033823834666868664045)
    ·
      refine ⟨11681262683938000075749017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31150033823834666868664045 11681262683938000075749017)
      ·
        refine ⟨8760947012953500056811763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11681262683938000075749017 8760947012953500056811763)
        ·
          refine ⟨13141420519430250085217645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8760947012953500056811763 13141420519430250085217645)
          ·
            refine ⟨4928032694786343781956617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13141420519430250085217645 4928032694786343781956617)
            ·
              refine ⟨3696024521089757836467463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4928032694786343781956617 3696024521089757836467463)
              ·
                refine ⟨5544036781634636754701195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3696024521089757836467463 5544036781634636754701195)
                ·
                  refine ⟨8316055172451955132051793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5544036781634636754701195 8316055172451955132051793)
                  ·
                    refine ⟨6237041379338966349038845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8316055172451955132051793 6237041379338966349038845)
                    ·
                      refine ⟨2338890517252112380889567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6237041379338966349038845 2338890517252112380889567)
                      ·
                        rfl

theorem cell23_4554973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_4554973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554973 prefixEnd_4554973 := by exact prefixLift 4554973
  have htrace : WordTrace (prefixWord ++ tailWord_4554973) baseStart_4554973 baseEnd_4554973 := by
    simpa [prefixWord, tailWord_4554973, baseEnd_4554973] using wordTrace_append hprefix tailTrace_4554973
  have hstable : (prefixWord ++ tailWord_4554973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554973).length < 2 ^ (prefixWord ++ tailWord_4554973).sum := by decide
  have hdescent : baseEnd_4554973 < baseStart_4554973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4554992 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 3, 4, 2]
def baseStart_4554992 : Nat := 118140960795 + 4554992 * 2 ^ 59
def prefixEnd_4554992 : Nat := 4983230072969 + 3 ^ 40 * 4554992 * 2
def baseEnd_4554992 : Nat := 2338900273384547806551979

theorem tailTrace_4554992 : CollatzResearch.WordTrace tailWord_4554992 prefixEnd_4554992 2338900273384547806551979 := by
  unfold tailWord_4554992
  simp only [CollatzResearch.WordTrace]
  refine ⟨83067103357024694772241615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110756137809366259696322153 83067103357024694772241615)
  ·
    refine ⟨124600655035537042158362423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83067103357024694772241615 124600655035537042158362423)
    ·
      refine ⟨186900982553305563237543635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124600655035537042158362423 186900982553305563237543635)
      ·
        refine ⟨280351473829958344856315453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186900982553305563237543635 280351473829958344856315453)
        ·
          refine ⟨105131802686234379321118295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 280351473829958344856315453 105131802686234379321118295)
          ·
            refine ⟨157697704029351568981677443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105131802686234379321118295 157697704029351568981677443)
            ·
              refine ⟨236546556044027353472516165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157697704029351568981677443 236546556044027353472516165)
              ·
                refine ⟨44352479258255128776096781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 236546556044027353472516165 44352479258255128776096781)
                ·
                  refine ⟨16632179721845673291036293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44352479258255128776096781 16632179721845673291036293)
                  ·
                    refine ⟨3118533697846063742069305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16632179721845673291036293 3118533697846063742069305)
                    ·
                      refine ⟨2338900273384547806551979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3118533697846063742069305 2338900273384547806551979)
                      ·
                        rfl

theorem cell23_4554992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 3, 4, 2].length) (baseStart_4554992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4554992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4554992 prefixEnd_4554992 := by exact prefixLift 4554992
  have htrace : WordTrace (prefixWord ++ tailWord_4554992) baseStart_4554992 baseEnd_4554992 := by
    simpa [prefixWord, tailWord_4554992, baseEnd_4554992] using wordTrace_append hprefix tailTrace_4554992
  have hstable : (prefixWord ++ tailWord_4554992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4554992).length < 2 ^ (prefixWord ++ tailWord_4554992).sum := by decide
  have hdescent : baseEnd_4554992 < baseStart_4554992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4554992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555055 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 7]
def baseStart_4555055 : Nat := 118140960795 + 4555055 * 2 ^ 59
def prefixEnd_4555055 : Nat := 4983230072969 + 3 ^ 40 * 4555055 * 2
def baseEnd_4555055 : Nat := 2338932622665781060064189

theorem tailTrace_4555055 : CollatzResearch.WordTrace tailWord_4555055 prefixEnd_4555055 2338932622665781060064189 := by
  unfold tailWord_4555055
  simp only [CollatzResearch.WordTrace]
  refine ⟨166136504512821151304026619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110757669675214100869351079 166136504512821151304026619)
  ·
    refine ⟨249204756769231726956039929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166136504512821151304026619 249204756769231726956039929)
    ·
      refine ⟨186903567576923795217029947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249204756769231726956039929 186903567576923795217029947)
      ·
        refine ⟨280355351365385692825544921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186903567576923795217029947 280355351365385692825544921)
        ·
          refine ⟨210266513524039269619158691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280355351365385692825544921 210266513524039269619158691)
          ·
            refine ⟨315399770286058904428738037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210266513524039269619158691 315399770286058904428738037)
            ·
              refine ⟨29568728464318022290194191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 315399770286058904428738037 29568728464318022290194191)
              ·
                refine ⟨44353092696477033435291287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29568728464318022290194191 44353092696477033435291287)
                ·
                  refine ⟨66529639044715550152936931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44353092696477033435291287 66529639044715550152936931)
                  ·
                    refine ⟨99794458567073325229405397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66529639044715550152936931 99794458567073325229405397)
                    ·
                      refine ⟨2338932622665781060064189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99794458567073325229405397 2338932622665781060064189)
                      ·
                        rfl

theorem cell23_4555055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_4555055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555055 prefixEnd_4555055 := by exact prefixLift 4555055
  have htrace : WordTrace (prefixWord ++ tailWord_4555055) baseStart_4555055 baseEnd_4555055 := by
    simpa [prefixWord, tailWord_4555055, baseEnd_4555055] using wordTrace_append hprefix tailTrace_4555055
  have hstable : (prefixWord ++ tailWord_4555055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555055).length < 2 ^ (prefixWord ++ tailWord_4555055).sum := by decide
  have hdescent : baseEnd_4555055 < baseStart_4555055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555060 : List Nat := [2, 5, 1, 1, 1, 2, 4, 1, 2, 2, 2]
def baseStart_4555060 : Nat := 118140960795 + 4555060 * 2 ^ 59
def prefixEnd_4555060 : Nat := 4983230072969 + 3 ^ 40 * 4555060 * 2
def baseEnd_4555060 : Nat := 2338935190069053540501667

theorem tailTrace_4555060 : CollatzResearch.WordTrace tailWord_4555060 prefixEnd_4555060 2338935190069053540501667 := by
  unfold tailWord_4555060
  simp only [CollatzResearch.WordTrace]
  refine ⟨83068343438901518578979317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110757791251868691438639089 83068343438901518578979317)
  ·
    refine ⟨7787657197397017366779311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83068343438901518578979317 7787657197397017366779311)
    ·
      refine ⟨11681485796095526050168967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7787657197397017366779311 11681485796095526050168967)
      ·
        refine ⟨17522228694143289075253451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11681485796095526050168967 17522228694143289075253451)
        ·
          refine ⟨26283343041214933612880177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17522228694143289075253451 26283343041214933612880177)
          ·
            refine ⟨19712507280911200209660133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26283343041214933612880177 19712507280911200209660133)
            ·
              refine ⟨3696095115170850039311275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19712507280911200209660133 3696095115170850039311275)
              ·
                refine ⟨5544142672756275058966913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3696095115170850039311275 5544142672756275058966913)
                ·
                  refine ⟨4158107004567206294225185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5544142672756275058966913 4158107004567206294225185)
                  ·
                    refine ⟨3118580253425404720668889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4158107004567206294225185 3118580253425404720668889)
                    ·
                      refine ⟨2338935190069053540501667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3118580253425404720668889 2338935190069053540501667)
                      ·
                        rfl

theorem cell23_4555060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_4555060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555060 prefixEnd_4555060 := by exact prefixLift 4555060
  have htrace : WordTrace (prefixWord ++ tailWord_4555060) baseStart_4555060 baseEnd_4555060 := by
    simpa [prefixWord, tailWord_4555060, baseEnd_4555060] using wordTrace_append hprefix tailTrace_4555060
  have hstable : (prefixWord ++ tailWord_4555060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555060).length < 2 ^ (prefixWord ++ tailWord_4555060).sum := by decide
  have hdescent : baseEnd_4555060 < baseStart_4555060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555075 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 2, 8]
def baseStart_4555075 : Nat := 118140960795 + 4555075 * 2 ^ 59
def prefixEnd_4555075 : Nat := 4983230072969 + 3 ^ 40 * 4555075 * 2
def baseEnd_4555075 : Nat := 779647630759623660604699

theorem tailTrace_4555075 : CollatzResearch.WordTrace tailWord_4555075 prefixEnd_4555075 779647630759623660604699 := by
  unfold tailWord_4555075
  simp only [CollatzResearch.WordTrace]
  refine ⟨166137233972748694719754679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110758155981832463146503119 166137233972748694719754679)
  ·
    refine ⟨249205850959123042079632019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166137233972748694719754679 249205850959123042079632019)
    ·
      refine ⟨373808776438684563119448029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249205850959123042079632019 373808776438684563119448029)
      ·
        refine ⟨140178291164506711169793011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 373808776438684563119448029 140178291164506711169793011)
        ·
          refine ⟨210267436746760066754689517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140178291164506711169793011 210267436746760066754689517)
          ·
            refine ⟨78850288780035025033008569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210267436746760066754689517 78850288780035025033008569)
            ·
              refine ⟨59137716585026268774756427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78850288780035025033008569 59137716585026268774756427)
              ·
                refine ⟨88706574877539403162134641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59137716585026268774756427 88706574877539403162134641)
                ·
                  refine ⟨66529931158154552371600981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88706574877539403162134641 66529931158154552371600981)
                  ·
                    refine ⟨779647630759623660604699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66529931158154552371600981 779647630759623660604699)
                    ·
                      rfl

theorem cell23_4555075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 8].length) (baseStart_4555075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555075 prefixEnd_4555075 := by exact prefixLift 4555075
  have htrace : WordTrace (prefixWord ++ tailWord_4555075) baseStart_4555075 baseEnd_4555075 := by
    simpa [prefixWord, tailWord_4555075, baseEnd_4555075] using wordTrace_append hprefix tailTrace_4555075
  have hstable : (prefixWord ++ tailWord_4555075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555075).length < 2 ^ (prefixWord ++ tailWord_4555075).sum := by decide
  have hdescent : baseEnd_4555075 < baseStart_4555075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555100 : List Nat := [2, 2, 4, 3, 1, 2, 2, 2, 5]
def baseStart_4555100 : Nat := 118140960795 + 4555100 * 2 ^ 59
def prefixEnd_4555100 : Nat := 4983230072969 + 3 ^ 40 * 4555100 * 2
def baseEnd_4555100 : Nat := 259883969921692598222387

theorem tailTrace_4555100 : CollatzResearch.WordTrace tailWord_4555100 prefixEnd_4555100 259883969921692598222387 := by
  unfold tailWord_4555100
  simp only [CollatzResearch.WordTrace]
  refine ⟨83069072898829061994707377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110758763865105415992943169 83069072898829061994707377)
  ·
    refine ⟨62301804674121796496030533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83069072898829061994707377 62301804674121796496030533)
    ·
      refine ⟨11681588376397836843005725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62301804674121796496030533 11681588376397836843005725)
      ·
        refine ⟨4380595641149188816127147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11681588376397836843005725 4380595641149188816127147)
        ·
          refine ⟨6570893461723783224190721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4380595641149188816127147 6570893461723783224190721)
          ·
            refine ⟨4928170096292837418143041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6570893461723783224190721 4928170096292837418143041)
            ·
              refine ⟨3696127572219628063607281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4928170096292837418143041 3696127572219628063607281)
              ·
                refine ⟨2772095679164721047705461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3696127572219628063607281 2772095679164721047705461)
                ·
                  refine ⟨259883969921692598222387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2772095679164721047705461 259883969921692598222387)
                  ·
                    rfl

theorem cell23_4555100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 5].length) (baseStart_4555100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555100 prefixEnd_4555100 := by exact prefixLift 4555100
  have htrace : WordTrace (prefixWord ++ tailWord_4555100) baseStart_4555100 baseEnd_4555100 := by
    simpa [prefixWord, tailWord_4555100, baseEnd_4555100] using wordTrace_append hprefix tailTrace_4555100
  have hstable : (prefixWord ++ tailWord_4555100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555100).length < 2 ^ (prefixWord ++ tailWord_4555100).sum := by decide
  have hdescent : baseEnd_4555100 < baseStart_4555100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555116 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 2, 4, 2]
def baseStart_4555116 : Nat := 118140960795 + 4555116 * 2 ^ 59
def prefixEnd_4555116 : Nat := 4983230072969 + 3 ^ 40 * 4555116 * 2
def baseEnd_4555116 : Nat := 2338963944985705321401409

theorem tailTrace_4555116 : CollatzResearch.WordTrace tailWord_4555116 prefixEnd_4555116 2338963944985705321401409 := by
  unfold tailWord_4555116
  simp only [CollatzResearch.WordTrace]
  refine ⟨83069364682800079360998601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110759152910400105814664801 83069364682800079360998601)
  ·
    refine ⟨62302023512100059520748951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83069364682800079360998601 62302023512100059520748951)
    ·
      refine ⟨93453035268150089281123427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62302023512100059520748951 93453035268150089281123427)
      ·
        refine ⟨140179552902225133921685141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93453035268150089281123427 140179552902225133921685141)
        ·
          refine ⟨6570916542291803152578991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 140179552902225133921685141 6570916542291803152578991)
          ·
            refine ⟨9856374813437704728868487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6570916542291803152578991 9856374813437704728868487)
            ·
              refine ⟨14784562220156557093302731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9856374813437704728868487 14784562220156557093302731)
              ·
                refine ⟨22176843330234835639954097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14784562220156557093302731 22176843330234835639954097)
                ·
                  refine ⟨16632632497676126729965573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22176843330234835639954097 16632632497676126729965573)
                  ·
                    refine ⟨3118618593314273761868545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16632632497676126729965573 3118618593314273761868545)
                    ·
                      refine ⟨2338963944985705321401409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3118618593314273761868545 2338963944985705321401409)
                      ·
                        rfl

theorem cell23_4555116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 4, 2].length) (baseStart_4555116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555116 prefixEnd_4555116 := by exact prefixLift 4555116
  have htrace : WordTrace (prefixWord ++ tailWord_4555116) baseStart_4555116 baseEnd_4555116 := by
    simpa [prefixWord, tailWord_4555116, baseEnd_4555116] using wordTrace_append hprefix tailTrace_4555116
  have hstable : (prefixWord ++ tailWord_4555116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555116).length < 2 ^ (prefixWord ++ tailWord_4555116).sum := by decide
  have hdescent : baseEnd_4555116 < baseStart_4555116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555132 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 1, 7, 3]
def baseStart_4555132 : Nat := 118140960795 + 4555132 * 2 ^ 59
def prefixEnd_4555132 : Nat := 4983230072969 + 3 ^ 40 * 4555132 * 2
def baseEnd_4555132 : Nat := 2338972160676177258801335

theorem tailTrace_4555132 : CollatzResearch.WordTrace tailWord_4555132 prefixEnd_4555132 2338972160676177258801335 := by
  unfold tailWord_4555132
  simp only [CollatzResearch.WordTrace]
  refine ⟨83069656466771096727289825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110759541955694795636386433 83069656466771096727289825)
  ·
    refine ⟨62302242350078322545467369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83069656466771096727289825 62302242350078322545467369)
    ·
      refine ⟨46726681762558741909100527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62302242350078322545467369 46726681762558741909100527)
      ·
        refine ⟨70090022643838112863650791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46726681762558741909100527 70090022643838112863650791)
        ·
          refine ⟨105135033965757169295476187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70090022643838112863650791 105135033965757169295476187)
          ·
            refine ⟨157702550948635753943214281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105135033965757169295476187 157702550948635753943214281)
            ·
              refine ⟨118276913211476815457410711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157702550948635753943214281 118276913211476815457410711)
              ·
                refine ⟨177415369817215223186116067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118276913211476815457410711 177415369817215223186116067)
                ·
                  refine ⟨266123054725822834779174101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177415369817215223186116067 266123054725822834779174101)
                  ·
                    refine ⟨6237259095136472690136893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 266123054725822834779174101 6237259095136472690136893)
                    ·
                      refine ⟨2338972160676177258801335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6237259095136472690136893 2338972160676177258801335)
                      ·
                        rfl

theorem cell23_4555132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_4555132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555132 prefixEnd_4555132 := by exact prefixLift 4555132
  have htrace : WordTrace (prefixWord ++ tailWord_4555132) baseStart_4555132 baseEnd_4555132 := by
    simpa [prefixWord, tailWord_4555132, baseEnd_4555132] using wordTrace_append hprefix tailTrace_4555132
  have hstable : (prefixWord ++ tailWord_4555132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555132).length < 2 ^ (prefixWord ++ tailWord_4555132).sum := by decide
  have hdescent : baseEnd_4555132 < baseStart_4555132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555192 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 5, 1, 5]
def baseStart_4555192 : Nat := 118140960795 + 4555192 * 2 ^ 59
def prefixEnd_4555192 : Nat := 4983230072969 + 3 ^ 40 * 4555192 * 2
def baseEnd_4555192 : Nat := 2339002969515447024051059

theorem tailTrace_4555192 : CollatzResearch.WordTrace tailWord_4555192 prefixEnd_4555192 2339002969515447024051059 := by
  unfold tailWord_4555192
  simp only [CollatzResearch.WordTrace]
  refine ⟨83070750656662411850881915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110761000875549882467842553 83070750656662411850881915)
  ·
    refine ⟨124606125984993617776322873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83070750656662411850881915 124606125984993617776322873)
    ·
      refine ⟨93454594488745213332242155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124606125984993617776322873 93454594488745213332242155)
      ·
        refine ⟨140181891733117819998363233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93454594488745213332242155 140181891733117819998363233)
        ·
          refine ⟨105136418799838364998772425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140181891733117819998363233 105136418799838364998772425)
          ·
            refine ⟨78852314099878773749079319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105136418799838364998772425 78852314099878773749079319)
            ·
              refine ⟨118278471149818160623618979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78852314099878773749079319 118278471149818160623618979)
              ·
                refine ⟨177417706724727240935428469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118278471149818160623618979 177417706724727240935428469)
                ·
                  refine ⟨16632910005443178837696419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 177417706724727240935428469 16632910005443178837696419)
                  ·
                    refine ⟨24949365008164768256544629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16632910005443178837696419 24949365008164768256544629)
                    ·
                      refine ⟨2339002969515447024051059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24949365008164768256544629 2339002969515447024051059)
                      ·
                        rfl

theorem cell23_4555192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_4555192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555192 prefixEnd_4555192 := by exact prefixLift 4555192
  have htrace : WordTrace (prefixWord ++ tailWord_4555192) baseStart_4555192 baseEnd_4555192 := by
    simpa [prefixWord, tailWord_4555192, baseEnd_4555192] using wordTrace_append hprefix tailTrace_4555192
  have hstable : (prefixWord ++ tailWord_4555192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555192).length < 2 ^ (prefixWord ++ tailWord_4555192).sum := by decide
  have hdescent : baseEnd_4555192 < baseStart_4555192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555229 : List Nat := [1, 4, 3, 1, 1, 1, 4, 8]
def baseStart_4555229 : Nat := 118140960795 + 4555229 * 2 ^ 59
def prefixEnd_4555229 : Nat := 4983230072969 + 3 ^ 40 * 4555229 * 2
def baseEnd_4555229 : Nat := 86630443270357902936607

theorem tailTrace_4555229 : CollatzResearch.WordTrace tailWord_4555229 prefixEnd_4555229 86630443270357902936607 := by
  unfold tailWord_4555229
  simp only [CollatzResearch.WordTrace]
  refine ⟨166142850814190779020860741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110761900542793852680573827 166142850814190779020860741)
  ·
    refine ⟨31151784527660771066411389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166142850814190779020860741 31151784527660771066411389)
    ·
      refine ⟨11681919197872789149904271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31151784527660771066411389 11681919197872789149904271)
      ·
        refine ⟨17522878796809183724856407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11681919197872789149904271 17522878796809183724856407)
        ·
          refine ⟨26284318195213775587284611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17522878796809183724856407 26284318195213775587284611)
          ·
            refine ⟨39426477292820663380926917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26284318195213775587284611 39426477292820663380926917)
            ·
              refine ⟨7392464492403874383923797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39426477292820663380926917 7392464492403874383923797)
              ·
                refine ⟨86630443270357902936607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7392464492403874383923797 86630443270357902936607)
                ·
                  rfl

theorem cell23_4555229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 8].length) (baseStart_4555229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555229 prefixEnd_4555229 := by exact prefixLift 4555229
  have htrace : WordTrace (prefixWord ++ tailWord_4555229) baseStart_4555229 baseEnd_4555229 := by
    simpa [prefixWord, tailWord_4555229, baseEnd_4555229] using wordTrace_append hprefix tailTrace_4555229
  have hstable : (prefixWord ++ tailWord_4555229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555229).length < 2 ^ (prefixWord ++ tailWord_4555229).sum := by decide
  have hdescent : baseEnd_4555229 < baseStart_4555229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555232 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 6]
def baseStart_4555232 : Nat := 118140960795 + 4555232 * 2 ^ 59
def prefixEnd_4555232 : Nat := 4983230072969 + 3 ^ 40 * 4555232 * 2
def baseEnd_4555232 : Nat := 2339023508741626867550875

theorem tailTrace_4555232 : CollatzResearch.WordTrace tailWord_4555232 prefixEnd_4555232 2339023508741626867550875 := by
  unfold tailWord_4555232
  simp only [CollatzResearch.WordTrace]
  refine ⟨83071480116589955266609975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110761973488786607022146633 83071480116589955266609975)
  ·
    refine ⟨124607220174884932899914963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83071480116589955266609975 124607220174884932899914963)
    ·
      refine ⟨186910830262327399349872445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124607220174884932899914963 186910830262327399349872445)
      ·
        refine ⟨70091561348372774756202167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186910830262327399349872445 70091561348372774756202167)
        ·
          refine ⟨105137342022559162134303251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70091561348372774756202167 105137342022559162134303251)
          ·
            refine ⟨157706013033838743201454877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105137342022559162134303251 157706013033838743201454877)
            ·
              refine ⟨59139754887689528700545579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157706013033838743201454877 59139754887689528700545579)
              ·
                refine ⟨88709632331534293050818369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59139754887689528700545579 88709632331534293050818369)
                ·
                  refine ⟨66532224248650719788113777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88709632331534293050818369 66532224248650719788113777)
                  ·
                    refine ⟨49899168186488039841085333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66532224248650719788113777 49899168186488039841085333)
                    ·
                      refine ⟨2339023508741626867550875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49899168186488039841085333 2339023508741626867550875)
                      ·
                        rfl

theorem cell23_4555232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_4555232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555232 prefixEnd_4555232 := by exact prefixLift 4555232
  have htrace : WordTrace (prefixWord ++ tailWord_4555232) baseStart_4555232 baseEnd_4555232 := by
    simpa [prefixWord, tailWord_4555232, baseEnd_4555232] using wordTrace_append hprefix tailTrace_4555232
  have hstable : (prefixWord ++ tailWord_4555232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555232).length < 2 ^ (prefixWord ++ tailWord_4555232).sum := by decide
  have hdescent : baseEnd_4555232 < baseStart_4555232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555253 : List Nat := [1, 3, 5, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_4555253 : Nat := 118140960795 + 4555253 * 2 ^ 59
def prefixEnd_4555253 : Nat := 4983230072969 + 3 ^ 40 * 4555253 * 2
def baseEnd_4555253 : Nat := 2339034291835371285388279

theorem tailTrace_4555253 : CollatzResearch.WordTrace tailWord_4555253 prefixEnd_4555253 2339034291835371285388279 := by
  unfold tailWord_4555253
  simp only [CollatzResearch.WordTrace]
  refine ⟨166143726166103831119734413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110762484110735887413156275 166143726166103831119734413)
  ·
    refine ⟨62303897312288936669900405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166143726166103831119734413 62303897312288936669900405)
    ·
      refine ⟨5840990373027087812803163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62303897312288936669900405 5840990373027087812803163)
      ·
        refine ⟨8761485559540631719204745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5840990373027087812803163 8761485559540631719204745)
        ·
          refine ⟨6571114169655473789403559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8761485559540631719204745 6571114169655473789403559)
          ·
            refine ⟨9856671254483210684105339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6571114169655473789403559 9856671254483210684105339)
            ·
              refine ⟨14785006881724816026158009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9856671254483210684105339 14785006881724816026158009)
              ·
                refine ⟨11088755161293612019618507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14785006881724816026158009 11088755161293612019618507)
                ·
                  refine ⟨16633132741940418029427761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11088755161293612019618507 16633132741940418029427761)
                  ·
                    refine ⟨12474849556455313522070821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16633132741940418029427761 12474849556455313522070821)
                    ·
                      refine ⟨2339034291835371285388279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12474849556455313522070821 2339034291835371285388279)
                      ·
                        rfl

theorem cell23_4555253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_4555253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555253 prefixEnd_4555253 := by exact prefixLift 4555253
  have htrace : WordTrace (prefixWord ++ tailWord_4555253) baseStart_4555253 baseEnd_4555253 := by
    simpa [prefixWord, tailWord_4555253, baseEnd_4555253] using wordTrace_append hprefix tailTrace_4555253
  have hstable : (prefixWord ++ tailWord_4555253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555253).length < 2 ^ (prefixWord ++ tailWord_4555253).sum := by decide
  have hdescent : baseEnd_4555253 < baseStart_4555253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555346 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 2, 3, 3]
def baseStart_4555346 : Nat := 118140960795 + 4555346 * 2 ^ 59
def prefixEnd_4555346 : Nat := 4983230072969 + 3 ^ 40 * 4555346 * 2
def baseEnd_4555346 : Nat := 2339082045536239421525351

theorem tailTrace_4555346 : CollatzResearch.WordTrace tailWord_4555346 prefixEnd_4555346 2339082045536239421525351 := by
  unfold tailWord_4555346
  simp only [CollatzResearch.WordTrace]
  refine ⟨41536779538691727000717473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110764745436511272001913261 41536779538691727000717473)
  ·
    refine ⟨31152584654018795250538105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41536779538691727000717473 31152584654018795250538105)
    ·
      refine ⟨23364438490514096437903579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31152584654018795250538105 23364438490514096437903579)
      ·
        refine ⟨35046657735771144656855369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23364438490514096437903579 35046657735771144656855369)
        ·
          refine ⟨26284993301828358492641527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35046657735771144656855369 26284993301828358492641527)
          ·
            refine ⟨39427489952742537738962291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26284993301828358492641527 39427489952742537738962291)
            ·
              refine ⟨59141234929113806608443437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39427489952742537738962291 59141234929113806608443437)
              ·
                refine ⟨22177963098417677478166289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59141234929113806608443437 22177963098417677478166289)
                ·
                  refine ⟨16633472323813258108624717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22177963098417677478166289 16633472323813258108624717)
                  ·
                    refine ⟨6237552121429971790734269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16633472323813258108624717 6237552121429971790734269)
                    ·
                      refine ⟨2339082045536239421525351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6237552121429971790734269 2339082045536239421525351)
                      ·
                        rfl

theorem cell23_4555346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_4555346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555346 prefixEnd_4555346 := by exact prefixLift 4555346
  have htrace : WordTrace (prefixWord ++ tailWord_4555346) baseStart_4555346 baseEnd_4555346 := by
    simpa [prefixWord, tailWord_4555346, baseEnd_4555346] using wordTrace_append hprefix tailTrace_4555346
  have hstable : (prefixWord ++ tailWord_4555346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555346).length < 2 ^ (prefixWord ++ tailWord_4555346).sum := by decide
  have hdescent : baseEnd_4555346 < baseStart_4555346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555349 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 1, 7]
def baseStart_4555349 : Nat := 118140960795 + 4555349 * 2 ^ 59
def prefixEnd_4555349 : Nat := 4983230072969 + 3 ^ 40 * 4555349 * 2
def baseEnd_4555349 : Nat := 779694528659400969929279

theorem tailTrace_4555349 : CollatzResearch.WordTrace tailWord_4555349 prefixEnd_4555349 779694528659400969929279 := by
  unfold tailWord_4555349
  simp only [CollatzResearch.WordTrace]
  refine ⟨166147227573756039515229101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110764818382504026343486067 166147227573756039515229101)
  ·
    refine ⟨62305210340158514818210913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166147227573756039515229101 62305210340158514818210913)
    ·
      refine ⟨46728907755118886113658185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62305210340158514818210913 46728907755118886113658185)
      ·
        refine ⟨35046680816339164585243639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46728907755118886113658185 35046680816339164585243639)
        ·
          refine ⟨52570021224508746877865459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35046680816339164585243639 52570021224508746877865459)
          ·
            refine ⟨78855031836763120316798189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52570021224508746877865459 78855031836763120316798189)
            ·
              refine ⟨29570636938786170118799321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78855031836763120316798189 29570636938786170118799321)
              ·
                refine ⟨22177977704089627589099491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29570636938786170118799321 22177977704089627589099491)
                ·
                  refine ⟨33266966556134441383649237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22177977704089627589099491 33266966556134441383649237)
                  ·
                    refine ⟨779694528659400969929279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33266966556134441383649237 779694528659400969929279)
                    ·
                      rfl

theorem cell23_4555349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_4555349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555349 prefixEnd_4555349 := by exact prefixLift 4555349
  have htrace : WordTrace (prefixWord ++ tailWord_4555349) baseStart_4555349 baseEnd_4555349 := by
    simpa [prefixWord, tailWord_4555349, baseEnd_4555349] using wordTrace_append hprefix tailTrace_4555349
  have hstable : (prefixWord ++ tailWord_4555349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555349).length < 2 ^ (prefixWord ++ tailWord_4555349).sum := by decide
  have hdescent : baseEnd_4555349 < baseStart_4555349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555429 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 1, 1, 8]
def baseStart_4555429 : Nat := 118140960795 + 4555429 * 2 ^ 59
def prefixEnd_4555429 : Nat := 4983230072969 + 3 ^ 40 * 4555429 * 2
def baseEnd_4555429 : Nat := 2339124664430562596787469

theorem tailTrace_4555429 : CollatzResearch.WordTrace tailWord_4555429 prefixEnd_4555429 2339124664430562596787469 := by
  unfold tailWord_4555429
  simp only [CollatzResearch.WordTrace]
  refine ⟨166150145413466213178141341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110766763608977475452094227 166150145413466213178141341)
  ·
    refine ⟨62306304530049829941803003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166150145413466213178141341 62306304530049829941803003)
    ·
      refine ⟨93459456795074744912704505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62306304530049829941803003 93459456795074744912704505)
      ·
        refine ⟨70094592596306058684528379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93459456795074744912704505 70094592596306058684528379)
        ·
          refine ⟨105141888894459088026792569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70094592596306058684528379 105141888894459088026792569)
          ·
            refine ⟨78856416670844316020094427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105141888894459088026792569 78856416670844316020094427)
            ·
              refine ⟨118284625006266474030141641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78856416670844316020094427 118284625006266474030141641)
              ·
                refine ⟨88713468754699855522606231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118284625006266474030141641 88713468754699855522606231)
                ·
                  refine ⟨133070203132049783283909347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88713468754699855522606231 133070203132049783283909347)
                  ·
                    refine ⟨199605304698074674925864021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 133070203132049783283909347 199605304698074674925864021)
                    ·
                      refine ⟨2339124664430562596787469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 199605304698074674925864021 2339124664430562596787469)
                      ·
                        rfl

theorem cell23_4555429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_4555429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555429 prefixEnd_4555429 := by exact prefixLift 4555429
  have htrace : WordTrace (prefixWord ++ tailWord_4555429) baseStart_4555429 baseEnd_4555429 := by
    simpa [prefixWord, tailWord_4555429, baseEnd_4555429] using wordTrace_append hprefix tailTrace_4555429
  have hstable : (prefixWord ++ tailWord_4555429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555429).length < 2 ^ (prefixWord ++ tailWord_4555429).sum := by decide
  have hdescent : baseEnd_4555429 < baseStart_4555429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555456 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 3, 5]
def baseStart_4555456 : Nat := 118140960795 + 4555456 * 2 ^ 59
def prefixEnd_4555456 : Nat := 4983230072969 + 3 ^ 40 * 4555456 * 2
def baseEnd_4555456 : Nat := 779712842802744663716615

theorem tailTrace_4555456 : CollatzResearch.WordTrace tailWord_4555456 prefixEnd_4555456 779712842802744663716615 := by
  unfold tailWord_4555456
  simp only [CollatzResearch.WordTrace]
  refine ⟨83075565092184198394687111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110767420122912264526249481 83075565092184198394687111)
  ·
    refine ⟨124613347638276297592030667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83075565092184198394687111 124613347638276297592030667)
    ·
      refine ⟨186920021457414446388046001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124613347638276297592030667 186920021457414446388046001)
      ·
        refine ⟨140190016093060834791034501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186920021457414446388046001 140190016093060834791034501)
        ·
          refine ⟨26285628017448906523318969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140190016093060834791034501 26285628017448906523318969)
          ·
            refine ⟨19714221013086679892489227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26285628017448906523318969 19714221013086679892489227)
            ·
              refine ⟨29571331519630019838733841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19714221013086679892489227 29571331519630019838733841)
              ·
                refine ⟨22178498639722514879050381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29571331519630019838733841 22178498639722514879050381)
                ·
                  refine ⟨8316936989895943079643893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22178498639722514879050381 8316936989895943079643893)
                  ·
                    refine ⟨779712842802744663716615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8316936989895943079643893 779712842802744663716615)
                    ·
                      rfl

theorem cell23_4555456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 3, 5].length) (baseStart_4555456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555456 prefixEnd_4555456 := by exact prefixLift 4555456
  have htrace : WordTrace (prefixWord ++ tailWord_4555456) baseStart_4555456 baseEnd_4555456 := by
    simpa [prefixWord, tailWord_4555456, baseEnd_4555456] using wordTrace_append hprefix tailTrace_4555456
  have hstable : (prefixWord ++ tailWord_4555456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555456).length < 2 ^ (prefixWord ++ tailWord_4555456).sum := by decide
  have hdescent : baseEnd_4555456 < baseStart_4555456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555470 : List Nat := [4, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3]
def baseStart_4555470 : Nat := 118140960795 + 4555470 * 2 ^ 59
def prefixEnd_4555470 : Nat := 4983230072969 + 3 ^ 40 * 4555470 * 2
def baseEnd_4555470 : Nat := 2339145717137396936374781

theorem tailTrace_4555470 : CollatzResearch.WordTrace tailWord_4555470 prefixEnd_4555470 2339145717137396936374781 := by
  unfold tailWord_4555470
  simp only [CollatzResearch.WordTrace]
  refine ⟨20768955100789709647547983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110767760537545118120255909 20768955100789709647547983)
  ·
    refine ⟨31153432651184564471321975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20768955100789709647547983 31153432651184564471321975)
    ·
      refine ⟨46730148976776846706982963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31153432651184564471321975 46730148976776846706982963)
      ·
        refine ⟨70095223465165270060474445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46730148976776846706982963 70095223465165270060474445)
        ·
          refine ⟨26285708799436976272677917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70095223465165270060474445 26285708799436976272677917)
          ·
            refine ⟨9857140799788866102254219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26285708799436976272677917 9857140799788866102254219)
            ·
              refine ⟨14785711199683299153381329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9857140799788866102254219 14785711199683299153381329)
              ·
                refine ⟨11089283399762474365035997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14785711199683299153381329 11089283399762474365035997)
                ·
                  refine ⟨4158481274910927886888499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11089283399762474365035997 4158481274910927886888499)
                  ·
                    refine ⟨6237721912366391830332749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4158481274910927886888499 6237721912366391830332749)
                    ·
                      refine ⟨2339145717137396936374781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6237721912366391830332749 2339145717137396936374781)
                      ·
                        rfl

theorem cell23_4555470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_4555470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555470 prefixEnd_4555470 := by exact prefixLift 4555470
  have htrace : WordTrace (prefixWord ++ tailWord_4555470) baseStart_4555470 baseEnd_4555470 := by
    simpa [prefixWord, tailWord_4555470, baseEnd_4555470] using wordTrace_append hprefix tailTrace_4555470
  have hstable : (prefixWord ++ tailWord_4555470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555470).length < 2 ^ (prefixWord ++ tailWord_4555470).sum := by decide
  have hdescent : baseEnd_4555470 < baseStart_4555470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555480 : List Nat := [2, 1, 2, 2, 3, 2, 3, 1, 2, 3, 2]
def baseStart_4555480 : Nat := 118140960795 + 4555480 * 2 ^ 59
def prefixEnd_4555480 : Nat := 4983230072969 + 3 ^ 40 * 4555480 * 2
def baseEnd_4555480 : Nat := 2339150851943941897249735

theorem tailTrace_4555480 : CollatzResearch.WordTrace tailWord_4555480 prefixEnd_4555480 2339150851943941897249735 := by
  unfold tailWord_4555480
  simp only [CollatzResearch.WordTrace]
  refine ⟨83076002768140724444123947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110768003690854299258831929 83076002768140724444123947)
  ·
    refine ⟨124614004152211086666185921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83076002768140724444123947 124614004152211086666185921)
    ·
      refine ⟨93460503114158314999639441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124614004152211086666185921 93460503114158314999639441)
      ·
        refine ⟨70095377335618736249729581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93460503114158314999639441 70095377335618736249729581)
        ·
          refine ⟨26285766500857026093648593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70095377335618736249729581 26285766500857026093648593)
          ·
            refine ⟨19714324875642769570236445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26285766500857026093648593 19714324875642769570236445)
            ·
              refine ⟨7392871828366038588838667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19714324875642769570236445 7392871828366038588838667)
              ·
                refine ⟨11089307742549057883258001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7392871828366038588838667 11089307742549057883258001)
                ·
                  refine ⟨8316980806911793412443501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11089307742549057883258001 8316980806911793412443501)
                  ·
                    refine ⟨3118867802591922529666313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8316980806911793412443501 3118867802591922529666313)
                    ·
                      refine ⟨2339150851943941897249735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3118867802591922529666313 2339150851943941897249735)
                      ·
                        rfl

theorem cell23_4555480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_4555480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555480 prefixEnd_4555480 := by exact prefixLift 4555480
  have htrace : WordTrace (prefixWord ++ tailWord_4555480) baseStart_4555480 baseEnd_4555480 := by
    simpa [prefixWord, tailWord_4555480, baseEnd_4555480] using wordTrace_append hprefix tailTrace_4555480
  have hstable : (prefixWord ++ tailWord_4555480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555480).length < 2 ^ (prefixWord ++ tailWord_4555480).sum := by decide
  have hdescent : baseEnd_4555480 < baseStart_4555480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555487 : List Nat := [1, 1, 2, 3, 2, 4, 2, 3, 1, 1, 3]
def baseStart_4555487 : Nat := 118140960795 + 4555487 * 2 ^ 59
def prefixEnd_4555487 : Nat := 4983230072969 + 3 ^ 40 * 4555487 * 2
def baseEnd_4555487 : Nat := 2339154446308523369862203

theorem tailTrace_4555487 : CollatzResearch.WordTrace tailWord_4555487 prefixEnd_4555487 2339154446308523369862203 := by
  unfold tailWord_4555487
  simp only [CollatzResearch.WordTrace]
  refine ⟨166152260847256089083752715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110768173898170726055835143 166152260847256089083752715)
  ·
    refine ⟨249228391270884133625629073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166152260847256089083752715 249228391270884133625629073)
    ·
      refine ⟨186921293453163100219221805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249228391270884133625629073 186921293453163100219221805)
      ·
        refine ⟨70095485044936162582208177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186921293453163100219221805 70095485044936162582208177)
        ·
          refine ⟨52571613783702121936656133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70095485044936162582208177 52571613783702121936656133)
          ·
            refine ⟨9857177584444147863123025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52571613783702121936656133 9857177584444147863123025)
            ·
              refine ⟨7392883188333110897342269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9857177584444147863123025 7392883188333110897342269)
              ·
                refine ⟨2772331195624916586503351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7392883188333110897342269 2772331195624916586503351)
                ·
                  refine ⟨4158496793437374879755027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2772331195624916586503351 4158496793437374879755027)
                  ·
                    refine ⟨6237745190156062319632541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4158496793437374879755027 6237745190156062319632541)
                    ·
                      refine ⟨2339154446308523369862203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6237745190156062319632541 2339154446308523369862203)
                      ·
                        rfl

theorem cell23_4555487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 1, 1, 3].length) (baseStart_4555487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555487 prefixEnd_4555487 := by exact prefixLift 4555487
  have htrace : WordTrace (prefixWord ++ tailWord_4555487) baseStart_4555487 baseEnd_4555487 := by
    simpa [prefixWord, tailWord_4555487, baseEnd_4555487] using wordTrace_append hprefix tailTrace_4555487
  have hstable : (prefixWord ++ tailWord_4555487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555487).length < 2 ^ (prefixWord ++ tailWord_4555487).sum := by decide
  have hdescent : baseEnd_4555487 < baseStart_4555487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555503 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 4, 4]
def baseStart_4555503 : Nat := 118140960795 + 4555503 * 2 ^ 59
def prefixEnd_4555503 : Nat := 4983230072969 + 3 ^ 40 * 4555503 * 2
def baseEnd_4555503 : Nat := 779720887332998435754043

theorem tailTrace_4555503 : CollatzResearch.WordTrace tailWord_4555503 prefixEnd_4555503 779720887332998435754043 := by
  unfold tailWord_4555503
  simp only [CollatzResearch.WordTrace]
  refine ⟨166152844415198123816335163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110768562943465415877556775 166152844415198123816335163)
  ·
    refine ⟨249229266622797185724502745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166152844415198123816335163 249229266622797185724502745)
    ·
      refine ⟨186921949967097889293377059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249229266622797185724502745 186921949967097889293377059)
      ·
        refine ⟨280382924950646833940065589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186921949967097889293377059 280382924950646833940065589)
        ·
          refine ⟨26285899214123140681881149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 280382924950646833940065589 26285899214123140681881149)
          ·
            refine ⟨9857212205296177755705431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26285899214123140681881149 9857212205296177755705431)
            ·
              refine ⟨14785818307944266633558147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9857212205296177755705431 14785818307944266633558147)
              ·
                refine ⟨22178727461916399950337221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14785818307944266633558147 22178727461916399950337221)
                ·
                  refine ⟨4158511399109324990688229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22178727461916399950337221 4158511399109324990688229)
                  ·
                    refine ⟨779720887332998435754043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4158511399109324990688229 779720887332998435754043)
                    ·
                      rfl

theorem cell23_4555503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 4].length) (baseStart_4555503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555503 prefixEnd_4555503 := by exact prefixLift 4555503
  have htrace : WordTrace (prefixWord ++ tailWord_4555503) baseStart_4555503 baseEnd_4555503 := by
    simpa [prefixWord, tailWord_4555503, baseEnd_4555503] using wordTrace_append hprefix tailTrace_4555503
  have hstable : (prefixWord ++ tailWord_4555503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555503).length < 2 ^ (prefixWord ++ tailWord_4555503).sum := by decide
  have hdescent : baseEnd_4555503 < baseStart_4555503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555527 : List Nat := [1, 1, 4, 4, 1, 1, 2, 2, 3, 2, 2]
def baseStart_4555527 : Nat := 118140960795 + 4555527 * 2 ^ 59
def prefixEnd_4555527 : Nat := 4983230072969 + 3 ^ 40 * 4555527 * 2
def baseEnd_4555527 : Nat := 2339174985534703213362019

theorem tailTrace_4555527 : CollatzResearch.WordTrace tailWord_4555527 prefixEnd_4555527 2339174985534703213362019 := by
  unfold tailWord_4555527
  simp only [CollatzResearch.WordTrace]
  refine ⟨166153719767111175915208835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110769146511407450610139223 166153719767111175915208835)
  ·
    refine ⟨249230579650666763872813253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166153719767111175915208835 249230579650666763872813253)
    ·
      refine ⟨46730733684500018226152485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 249230579650666763872813253 46730733684500018226152485)
      ·
        refine ⟨8762012565843753417403591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46730733684500018226152485 8762012565843753417403591)
        ·
          refine ⟨13143018848765630126105387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8762012565843753417403591 13143018848765630126105387)
          ·
            refine ⟨19714528273148445189158081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13143018848765630126105387 19714528273148445189158081)
            ·
              refine ⟨14785896204861333891868561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19714528273148445189158081 14785896204861333891868561)
              ·
                refine ⟨11089422153646000418901421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14785896204861333891868561 11089422153646000418901421)
                ·
                  refine ⟨4158533307617250157088033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11089422153646000418901421 4158533307617250157088033)
                  ·
                    refine ⟨3118899980712937617816025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4158533307617250157088033 3118899980712937617816025)
                    ·
                      refine ⟨2339174985534703213362019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3118899980712937617816025 2339174985534703213362019)
                      ·
                        rfl

theorem cell23_4555527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_4555527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555527 prefixEnd_4555527 := by exact prefixLift 4555527
  have htrace : WordTrace (prefixWord ++ tailWord_4555527) baseStart_4555527 baseEnd_4555527 := by
    simpa [prefixWord, tailWord_4555527, baseEnd_4555527] using wordTrace_append hprefix tailTrace_4555527
  have hstable : (prefixWord ++ tailWord_4555527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555527).length < 2 ^ (prefixWord ++ tailWord_4555527).sum := by decide
  have hdescent : baseEnd_4555527 < baseStart_4555527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555530 : List Nat := [3, 1, 2, 2, 1, 2, 4, 2, 1, 2, 3]
def baseStart_4555530 : Nat := 118140960795 + 4555530 * 2 ^ 59
def prefixEnd_4555530 : Nat := 4983230072969 + 3 ^ 40 * 4555530 * 2
def baseEnd_4555530 : Nat := 2339176525976666701624505

theorem tailTrace_4555530 : CollatzResearch.WordTrace tailWord_4555530 prefixEnd_4555530 2339176525976666701624505 := by
  unfold tailWord_4555530
  simp only [CollatzResearch.WordTrace]
  refine ⟨41538457296525076856892011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110769219457400204951712029 41538457296525076856892011)
  ·
    refine ⟨62307685944787615285338017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41538457296525076856892011 62307685944787615285338017)
    ·
      refine ⟨46730764458590711464003513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62307685944787615285338017 46730764458590711464003513)
      ·
        refine ⟨35048073343943033598002635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46730764458590711464003513 35048073343943033598002635)
        ·
          refine ⟨52572110015914550397003953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35048073343943033598002635 52572110015914550397003953)
          ·
            refine ⟨39429082511935912797752965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52572110015914550397003953 39429082511935912797752965)
            ·
              refine ⟨7392952970987983649578681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39429082511935912797752965 7392952970987983649578681)
              ·
                refine ⟨5544714728240987737184011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7392952970987983649578681 5544714728240987737184011)
                ·
                  refine ⟨8317072092361481605776017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5544714728240987737184011 8317072092361481605776017)
                  ·
                    refine ⟨6237804069271111204332013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8317072092361481605776017 6237804069271111204332013)
                    ·
                      refine ⟨2339176525976666701624505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6237804069271111204332013 2339176525976666701624505)
                      ·
                        rfl

theorem cell23_4555530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_4555530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555530 prefixEnd_4555530 := by exact prefixLift 4555530
  have htrace : WordTrace (prefixWord ++ tailWord_4555530) baseStart_4555530 baseEnd_4555530 := by
    simpa [prefixWord, tailWord_4555530, baseEnd_4555530] using wordTrace_append hprefix tailTrace_4555530
  have hstable : (prefixWord ++ tailWord_4555530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555530).length < 2 ^ (prefixWord ++ tailWord_4555530).sum := by decide
  have hdescent : baseEnd_4555530 < baseStart_4555530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555538 : List Nat := [3, 2, 4, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_4555538 : Nat := 118140960795 + 4555538 * 2 ^ 59
def prefixEnd_4555538 : Nat := 4983230072969 + 3 ^ 40 * 4555538 * 2
def baseEnd_4555538 : Nat := 2339180633821902670324469

theorem tailTrace_4555538 : CollatzResearch.WordTrace tailWord_4555538 prefixEnd_4555538 2339180633821902670324469 := by
  unfold tailWord_4555538
  simp only [CollatzResearch.WordTrace]
  refine ⟨41538530242517831198464817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110769413980047549862572845 41538530242517831198464817)
  ·
    refine ⟨31153897681888373398848613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41538530242517831198464817 31153897681888373398848613)
    ·
      refine ⟨5841355815354070012284115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31153897681888373398848613 5841355815354070012284115)
      ·
        refine ⟨8762033723031105018426173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5841355815354070012284115 8762033723031105018426173)
        ·
          refine ⟨3285762646136664381909815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8762033723031105018426173 3285762646136664381909815)
          ·
            refine ⟨4928643969204996572864723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3285762646136664381909815 4928643969204996572864723)
            ·
              refine ⟨7392965953807494859297085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4928643969204996572864723 7392965953807494859297085)
              ·
                refine ⟨2772362232677810572236407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7392965953807494859297085 2772362232677810572236407)
                ·
                  refine ⟨4158543349016715858354611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2772362232677810572236407 4158543349016715858354611)
                  ·
                    refine ⟨6237815023525073787531917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4158543349016715858354611 6237815023525073787531917)
                    ·
                      refine ⟨2339180633821902670324469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6237815023525073787531917 2339180633821902670324469)
                      ·
                        rfl

theorem cell23_4555538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_4555538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555538 prefixEnd_4555538 := by exact prefixLift 4555538
  have htrace : WordTrace (prefixWord ++ tailWord_4555538) baseStart_4555538 baseEnd_4555538 := by
    simpa [prefixWord, tailWord_4555538, baseEnd_4555538] using wordTrace_append hprefix tailTrace_4555538
  have hstable : (prefixWord ++ tailWord_4555538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555538).length < 2 ^ (prefixWord ++ tailWord_4555538).sum := by decide
  have hdescent : baseEnd_4555538 < baseStart_4555538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555560 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_4555560 : Nat := 118140960795 + 4555560 * 2 ^ 59
def prefixEnd_4555560 : Nat := 4983230072969 + 3 ^ 40 * 4555560 * 2
def baseEnd_4555560 : Nat := 2339191930396301584249367

theorem tailTrace_4555560 : CollatzResearch.WordTrace tailWord_4555560 prefixEnd_4555560 2339191930396301584249367 := by
  unfold tailWord_4555560
  simp only [CollatzResearch.WordTrace]
  refine ⟨83077461687995811275580067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110769948917327748367440089 83077461687995811275580067)
  ·
    refine ⟨124616192531993716913370101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83077461687995811275580067 124616192531993716913370101)
    ·
      refine ⟨11682768049874410960628447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124616192531993716913370101 11682768049874410960628447)
      ·
        refine ⟨17524152074811616440942671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11682768049874410960628447 17524152074811616440942671)
        ·
          refine ⟨26286228112217424661414007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17524152074811616440942671 26286228112217424661414007)
          ·
            refine ⟨39429342168326136992121011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26286228112217424661414007 39429342168326136992121011)
            ·
              refine ⟨59144013252489205488181517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39429342168326136992121011 59144013252489205488181517)
              ·
                refine ⟨22179004969683452058068069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59144013252489205488181517 22179004969683452058068069)
                ·
                  refine ⟨4158563431815647260887763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22179004969683452058068069 4158563431815647260887763)
                  ·
                    refine ⟨6237845147723470891331645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4158563431815647260887763 6237845147723470891331645)
                    ·
                      refine ⟨2339191930396301584249367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6237845147723470891331645 2339191930396301584249367)
                      ·
                        rfl

theorem cell23_4555560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_4555560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555560 prefixEnd_4555560 := by exact prefixLift 4555560
  have htrace : WordTrace (prefixWord ++ tailWord_4555560) baseStart_4555560 baseEnd_4555560 := by
    simpa [prefixWord, tailWord_4555560, baseEnd_4555560] using wordTrace_append hprefix tailTrace_4555560
  have hstable : (prefixWord ++ tailWord_4555560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555560).length < 2 ^ (prefixWord ++ tailWord_4555560).sum := by decide
  have hdescent : baseEnd_4555560 < baseStart_4555560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555570 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2]
def baseStart_4555570 : Nat := 118140960795 + 4555570 * 2 ^ 59
def prefixEnd_4555570 : Nat := 4983230072969 + 3 ^ 40 * 4555570 * 2
def baseEnd_4555570 : Nat := 2339197065202846545124321

theorem tailTrace_4555570 : CollatzResearch.WordTrace tailWord_4555570 prefixEnd_4555570 2339197065202846545124321 := by
  unfold tailWord_4555570
  simp only [CollatzResearch.WordTrace]
  refine ⟨41538822026488848564756041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110770192070636929506016109 41538822026488848564756041)
  ·
    refine ⟨31154116519866636423567031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41538822026488848564756041 31154116519866636423567031)
    ·
      refine ⟨46731174779799954635350547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31154116519866636423567031 46731174779799954635350547)
      ·
        refine ⟨70096762169699931953025821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46731174779799954635350547 70096762169699931953025821)
        ·
          refine ⟨26286285813637474482384683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70096762169699931953025821 26286285813637474482384683)
          ·
            refine ⟨39429428720456211723577025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26286285813637474482384683 39429428720456211723577025)
            ·
              refine ⟨29572071540342158792682769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39429428720456211723577025 29572071540342158792682769)
              ·
                refine ⟨22179053655256619094512077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29572071540342158792682769 22179053655256619094512077)
                ·
                  refine ⟨8317145120721232160442029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22179053655256619094512077 8317145120721232160442029)
                  ·
                    refine ⟨3118929420270462060165761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8317145120721232160442029 3118929420270462060165761)
                    ·
                      refine ⟨2339197065202846545124321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3118929420270462060165761 2339197065202846545124321)
                      ·
                        rfl

theorem cell23_4555570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_4555570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555570 prefixEnd_4555570 := by exact prefixLift 4555570
  have htrace : WordTrace (prefixWord ++ tailWord_4555570) baseStart_4555570 baseEnd_4555570 := by
    simpa [prefixWord, tailWord_4555570, baseEnd_4555570] using wordTrace_append hprefix tailTrace_4555570
  have hstable : (prefixWord ++ tailWord_4555570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555570).length < 2 ^ (prefixWord ++ tailWord_4555570).sum := by decide
  have hdescent : baseEnd_4555570 < baseStart_4555570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555576 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 1, 8]
def baseStart_4555576 : Nat := 118140960795 + 4555576 * 2 ^ 59
def prefixEnd_4555576 : Nat := 4983230072969 + 3 ^ 40 * 4555576 * 2
def baseEnd_4555576 : Nat := 779733382028924507216431

theorem tailTrace_4555576 : CollatzResearch.WordTrace tailWord_4555576 prefixEnd_4555576 779733382028924507216431 := by
  unfold tailWord_4555576
  simp only [CollatzResearch.WordTrace]
  refine ⟨83077753471966828641871291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110770337962622438189161721 83077753471966828641871291)
  ·
    refine ⟨124616630207950242962806937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83077753471966828641871291 124616630207950242962806937)
    ·
      refine ⟨93462472655962682222105203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124616630207950242962806937 93462472655962682222105203)
      ·
        refine ⟨140193708983944023333157805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93462472655962682222105203 140193708983944023333157805)
        ·
          refine ⟨52572640868979008749934177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140193708983944023333157805 52572640868979008749934177)
          ·
            refine ⟨39429480651734256562450633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52572640868979008749934177 39429480651734256562450633)
            ·
              refine ⟨29572110488800692421837975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39429480651734256562450633 29572110488800692421837975)
              ·
                refine ⟨44358165733201038632756963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29572110488800692421837975 44358165733201038632756963)
                ·
                  refine ⟨66537248599801557949135445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44358165733201038632756963 66537248599801557949135445)
                  ·
                    refine ⟨779733382028924507216431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66537248599801557949135445 779733382028924507216431)
                    ·
                      rfl

theorem cell23_4555576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_4555576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555576 prefixEnd_4555576 := by exact prefixLift 4555576
  have htrace : WordTrace (prefixWord ++ tailWord_4555576) baseStart_4555576 baseEnd_4555576 := by
    simpa [prefixWord, tailWord_4555576, baseEnd_4555576] using wordTrace_append hprefix tailTrace_4555576
  have hstable : (prefixWord ++ tailWord_4555576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555576).length < 2 ^ (prefixWord ++ tailWord_4555576).sum := by decide
  have hdescent : baseEnd_4555576 < baseStart_4555576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555600 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 6, 2, 2]
def baseStart_4555600 : Nat := 118140960795 + 4555600 * 2 ^ 59
def prefixEnd_4555600 : Nat := 4983230072969 + 3 ^ 40 * 4555600 * 2
def baseEnd_4555600 : Nat := 2339212469622481427749183

theorem tailTrace_4555600 : CollatzResearch.WordTrace tailWord_4555600 prefixEnd_4555600 2339212469622481427749183 := by
  unfold tailWord_4555600
  simp only [CollatzResearch.WordTrace]
  refine ⟨83078191147923354691308127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110770921530564472921744169 83078191147923354691308127)
  ·
    refine ⟨124617286721885032036962191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83078191147923354691308127 124617286721885032036962191)
    ·
      refine ⟨186925930082827548055443287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124617286721885032036962191 186925930082827548055443287)
      ·
        refine ⟨280388895124241322083164931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186925930082827548055443287 280388895124241322083164931)
        ·
          refine ⟨420583342686361983124747397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280388895124241322083164931 420583342686361983124747397)
          ·
            refine ⟨78859376753692871835890137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 420583342686361983124747397 78859376753692871835890137)
            ·
              refine ⟨59144532565269653876917603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78859376753692871835890137 59144532565269653876917603)
              ·
                refine ⟨88716798847904480815376405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59144532565269653876917603 88716798847904480815376405)
                ·
                  refine ⟨4158599945995522538220769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88716798847904480815376405 4158599945995522538220769)
                  ·
                    refine ⟨3118949959496641903665577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4158599945995522538220769 3118949959496641903665577)
                    ·
                      refine ⟨2339212469622481427749183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3118949959496641903665577 2339212469622481427749183)
                      ·
                        rfl

theorem cell23_4555600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 6, 2, 2].length) (baseStart_4555600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555600 prefixEnd_4555600 := by exact prefixLift 4555600
  have htrace : WordTrace (prefixWord ++ tailWord_4555600) baseStart_4555600 baseEnd_4555600 := by
    simpa [prefixWord, tailWord_4555600, baseEnd_4555600] using wordTrace_append hprefix tailTrace_4555600
  have hstable : (prefixWord ++ tailWord_4555600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555600).length < 2 ^ (prefixWord ++ tailWord_4555600).sum := by decide
  have hdescent : baseEnd_4555600 < baseStart_4555600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555633 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 1, 5, 3]
def baseStart_4555633 : Nat := 118140960795 + 4555633 * 2 ^ 59
def prefixEnd_4555633 : Nat := 4983230072969 + 3 ^ 40 * 4555633 * 2
def baseEnd_4555633 : Nat := 2339229414484079798636531

theorem tailTrace_4555633 : CollatzResearch.WordTrace tailWord_4555633 prefixEnd_4555633 2339229414484079798636531 := by
  unfold tailWord_4555633
  simp only [CollatzResearch.WordTrace]
  refine ⟨166157585904727156018567553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110771723936484770679045035 166157585904727156018567553)
  ·
    refine ⟨124618189428545367013925665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166157585904727156018567553 124618189428545367013925665)
    ·
      refine ⟨93463642071409025260444249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124618189428545367013925665 93463642071409025260444249)
      ·
        refine ⟨70097731553556768945333187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93463642071409025260444249 70097731553556768945333187)
        ·
          refine ⟨105146597330335153417999781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70097731553556768945333187 105146597330335153417999781)
          ·
            refine ⟨19714986999437841265874959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105146597330335153417999781 19714986999437841265874959)
            ·
              refine ⟨29572480499156761898812439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19714986999437841265874959 29572480499156761898812439)
              ·
                refine ⟨44358720748735142848218659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29572480499156761898812439 44358720748735142848218659)
                ·
                  refine ⟨66538081123102714272327989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44358720748735142848218659 66538081123102714272327989)
                  ·
                    refine ⟨6237945105290879463030749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66538081123102714272327989 6237945105290879463030749)
                    ·
                      refine ⟨2339229414484079798636531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6237945105290879463030749 2339229414484079798636531)
                      ·
                        rfl

theorem cell23_4555633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_4555633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555633 prefixEnd_4555633 := by exact prefixLift 4555633
  have htrace : WordTrace (prefixWord ++ tailWord_4555633) baseStart_4555633 baseEnd_4555633 := by
    simpa [prefixWord, tailWord_4555633, baseEnd_4555633] using wordTrace_append hprefix tailTrace_4555633
  have hstable : (prefixWord ++ tailWord_4555633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555633).length < 2 ^ (prefixWord ++ tailWord_4555633).sum := by decide
  have hdescent : baseEnd_4555633 < baseStart_4555633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555653 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 1, 7]
def baseStart_4555653 : Nat := 118140960795 + 4555653 * 2 ^ 59
def prefixEnd_4555653 : Nat := 4983230072969 + 3 ^ 40 * 4555653 * 2
def baseEnd_4555653 : Nat := 779746561365723240128813

theorem tailTrace_4555653 : CollatzResearch.WordTrace tailWord_4555653 prefixEnd_4555653 779746561365723240128813 := by
  unfold tailWord_4555653
  simp only [CollatzResearch.WordTrace]
  refine ⟨166158315364654699434295613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110772210243103132956197075 166158315364654699434295613)
  ·
    refine ⟨62309368261745512287860855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166158315364654699434295613 62309368261745512287860855)
    ·
      refine ⟨93464052392618268431791283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62309368261745512287860855 93464052392618268431791283)
      ·
        refine ⟨140196078588927402647686925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93464052392618268431791283 140196078588927402647686925)
        ·
          refine ⟨52573529470847775992882597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140196078588927402647686925 52573529470847775992882597)
          ·
            refine ⟨9857536775783957998665487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52573529470847775992882597 9857536775783957998665487)
            ·
              refine ⟨14786305163675936997998231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9857536775783957998665487 14786305163675936997998231)
              ·
                refine ⟨22179457745513905496997347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14786305163675936997998231 22179457745513905496997347)
                ·
                  refine ⟨33269186618270858245496021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22179457745513905496997347 33269186618270858245496021)
                  ·
                    refine ⟨779746561365723240128813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33269186618270858245496021 779746561365723240128813)
                    ·
                      rfl

theorem cell23_4555653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_4555653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555653 prefixEnd_4555653 := by exact prefixLift 4555653
  have htrace : WordTrace (prefixWord ++ tailWord_4555653) baseStart_4555653 baseEnd_4555653 := by
    simpa [prefixWord, tailWord_4555653, baseEnd_4555653] using wordTrace_append hprefix tailTrace_4555653
  have hstable : (prefixWord ++ tailWord_4555653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555653).length < 2 ^ (prefixWord ++ tailWord_4555653).sum := by decide
  have hdescent : baseEnd_4555653 < baseStart_4555653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555673 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 4, 1, 4]
def baseStart_4555673 : Nat := 118140960795 + 4555673 * 2 ^ 59
def prefixEnd_4555673 : Nat := 4983230072969 + 3 ^ 40 * 4555673 * 2
def baseEnd_4555673 : Nat := 2339249953710259642136347

theorem tailTrace_4555673 : CollatzResearch.WordTrace tailWord_4555673 prefixEnd_4555673 2339249953710259642136347 := by
  unfold tailWord_4555673
  simp only [CollatzResearch.WordTrace]
  refine ⟨166159044824582242850023673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110772696549721495233349115 166159044824582242850023673)
  ·
    refine ⟨124619283618436682137517755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166159044824582242850023673 124619283618436682137517755)
    ·
      refine ⟨186928925427655023206276633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124619283618436682137517755 186928925427655023206276633)
      ·
        refine ⟨140196694070741267404707475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186928925427655023206276633 140196694070741267404707475)
        ·
          refine ⟨210295041106111901107061213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140196694070741267404707475 210295041106111901107061213)
          ·
            refine ⟨78860640414791962915147955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210295041106111901107061213 78860640414791962915147955)
            ·
              refine ⟨118290960622187944372721933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78860640414791962915147955 118290960622187944372721933)
              ·
                refine ⟨44359110233320479139770725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118290960622187944372721933 44359110233320479139770725)
                ·
                  refine ⟨8317333168747589838707011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44359110233320479139770725 8317333168747589838707011)
                  ·
                    refine ⟨12475999753121384758060517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8317333168747589838707011 12475999753121384758060517)
                    ·
                      refine ⟨2339249953710259642136347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12475999753121384758060517 2339249953710259642136347)
                      ·
                        rfl

theorem cell23_4555673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_4555673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555673 prefixEnd_4555673 := by exact prefixLift 4555673
  have htrace : WordTrace (prefixWord ++ tailWord_4555673) baseStart_4555673 baseEnd_4555673 := by
    simpa [prefixWord, tailWord_4555673, baseEnd_4555673] using wordTrace_append hprefix tailTrace_4555673
  have hstable : (prefixWord ++ tailWord_4555673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555673).length < 2 ^ (prefixWord ++ tailWord_4555673).sum := by decide
  have hdescent : baseEnd_4555673 < baseStart_4555673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555710 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3]
def baseStart_4555710 : Nat := 118140960795 + 4555710 * 2 ^ 59
def prefixEnd_4555710 : Nat := 4983230072969 + 3 ^ 40 * 4555710 * 2
def baseEnd_4555710 : Nat := 2339268952494475997373677

theorem tailTrace_4555710 : CollatzResearch.WordTrace tailWord_4555710 prefixEnd_4555710 2339268952494475997373677 := by
  unfold tailWord_4555710
  simp only [CollatzResearch.WordTrace]
  refine ⟨20770049290681024771140073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110773596216965465446080389 20770049290681024771140073)
  ·
    refine ⟨15577536968010768578355055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20770049290681024771140073 15577536968010768578355055)
    ·
      refine ⟨23366305452016152867532583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15577536968010768578355055 23366305452016152867532583)
      ·
        refine ⟨35049458178024229301298875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23366305452016152867532583 35049458178024229301298875)
        ·
          refine ⟨52574187267036343951948313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35049458178024229301298875 52574187267036343951948313)
          ·
            refine ⟨39430640450277257963961235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52574187267036343951948313 39430640450277257963961235)
            ·
              refine ⟨59145960675415886945941853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39430640450277257963961235 59145960675415886945941853)
              ·
                refine ⟨22179735253280957604728195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59145960675415886945941853 22179735253280957604728195)
                ·
                  refine ⟨33269602879921436407092293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22179735253280957604728195 33269602879921436407092293)
                  ·
                    refine ⟨6238050539985269326329805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33269602879921436407092293 6238050539985269326329805)
                    ·
                      refine ⟨2339268952494475997373677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6238050539985269326329805 2339268952494475997373677)
                      ·
                        rfl

theorem cell23_4555710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_4555710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555710 prefixEnd_4555710 := by exact prefixLift 4555710
  have htrace : WordTrace (prefixWord ++ tailWord_4555710) baseStart_4555710 baseEnd_4555710 := by
    simpa [prefixWord, tailWord_4555710, baseEnd_4555710] using wordTrace_append hprefix tailTrace_4555710
  have hstable : (prefixWord ++ tailWord_4555710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555710).length < 2 ^ (prefixWord ++ tailWord_4555710).sum := by decide
  have hdescent : baseEnd_4555710 < baseStart_4555710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555730 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 8]
def baseStart_4555730 : Nat := 118140960795 + 4555730 * 2 ^ 59
def prefixEnd_4555730 : Nat := 4983230072969 + 3 ^ 40 * 4555730 * 2
def baseEnd_4555730 : Nat := 259919913567507324347065

theorem tailTrace_4555730 : CollatzResearch.WordTrace tailWord_4555730 prefixEnd_4555730 259919913567507324347065 := by
  unfold tailWord_4555730
  simp only [CollatzResearch.WordTrace]
  refine ⟨41540280946343935396212161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110774082523583827723232429 41540280946343935396212161)
  ·
    refine ⟨31155210709757951547159121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41540280946343935396212161 31155210709757951547159121)
    ·
      refine ⟨23366408032318463660369341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31155210709757951547159121 23366408032318463660369341)
      ·
        refine ⟨8762403012119423872638503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23366408032318463660369341 8762403012119423872638503)
        ·
          refine ⟨13143604518179135808957755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8762403012119423872638503 13143604518179135808957755)
          ·
            refine ⟨19715406777268703713436633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13143604518179135808957755 19715406777268703713436633)
            ·
              refine ⟨14786555082951527785077475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19715406777268703713436633 14786555082951527785077475)
              ·
                refine ⟨22179832624427291677616213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14786555082951527785077475 22179832624427291677616213)
                ·
                  refine ⟨259919913567507324347065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22179832624427291677616213 259919913567507324347065)
                  ·
                    rfl

theorem cell23_4555730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_4555730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555730 prefixEnd_4555730 := by exact prefixLift 4555730
  have htrace : WordTrace (prefixWord ++ tailWord_4555730) baseStart_4555730 baseEnd_4555730 := by
    simpa [prefixWord, tailWord_4555730, baseEnd_4555730] using wordTrace_append hprefix tailTrace_4555730
  have hstable : (prefixWord ++ tailWord_4555730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555730).length < 2 ^ (prefixWord ++ tailWord_4555730).sum := by decide
  have hdescent : baseEnd_4555730 < baseStart_4555730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555734 : List Nat := [5, 2, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_4555734 : Nat := 118140960795 + 4555734 * 2 ^ 59
def prefixEnd_4555734 : Nat := 4983230072969 + 3 ^ 40 * 4555734 * 2
def baseEnd_4555734 : Nat := 779760425343394634491189

theorem tailTrace_4555734 : CollatzResearch.WordTrace tailWord_4555734 prefixEnd_4555734 779760425343394634491189 := by
  unfold tailWord_4555734
  simp only [CollatzResearch.WordTrace]
  refine ⟨10385079354835078141749641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110774179784907500178662837 10385079354835078141749641)
  ·
    refine ⟨7788809516126308606312231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10385079354835078141749641 7788809516126308606312231)
    ·
      refine ⟨11683214274189462909468347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7788809516126308606312231 11683214274189462909468347)
      ·
        refine ⟨17524821411284194364202521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11683214274189462909468347 17524821411284194364202521)
        ·
          refine ⟨13143616058463145773151891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17524821411284194364202521 13143616058463145773151891)
          ·
            refine ⟨19715424087694718659727837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13143616058463145773151891 19715424087694718659727837)
            ·
              refine ⟨7393284032885519497397939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19715424087694718659727837 7393284032885519497397939)
              ·
                refine ⟨11089926049328279246096909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7393284032885519497397939 11089926049328279246096909)
                ·
                  refine ⟨4158722268498104717286341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11089926049328279246096909 4158722268498104717286341)
                  ·
                    refine ⟨779760425343394634491189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4158722268498104717286341 779760425343394634491189)
                    ·
                      rfl

theorem cell23_4555734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_4555734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555734 prefixEnd_4555734 := by exact prefixLift 4555734
  have htrace : WordTrace (prefixWord ++ tailWord_4555734) baseStart_4555734 baseEnd_4555734 := by
    simpa [prefixWord, tailWord_4555734, baseEnd_4555734] using wordTrace_append hprefix tailTrace_4555734
  have hstable : (prefixWord ++ tailWord_4555734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555734).length < 2 ^ (prefixWord ++ tailWord_4555734).sum := by decide
  have hdescent : baseEnd_4555734 < baseStart_4555734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555793 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 6]
def baseStart_4555793 : Nat := 118140960795 + 4555793 * 2 ^ 59
def prefixEnd_4555793 : Nat := 4983230072969 + 3 ^ 40 * 4555793 * 2
def baseEnd_4555793 : Nat := 2339311571388799172635795

theorem tailTrace_4555793 : CollatzResearch.WordTrace tailWord_4555793 prefixEnd_4555793 2339311571388799172635795 := by
  unfold tailWord_4555793
  simp only [CollatzResearch.WordTrace]
  refine ⟨166163421584147503344392033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110775614389431668896261355 166163421584147503344392033)
  ·
    refine ⟨124622566188110627508294025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166163421584147503344392033 124622566188110627508294025)
    ·
      refine ⟨93466924641082970631220519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124622566188110627508294025 93466924641082970631220519)
      ·
        refine ⟨140200386961624455946830779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93466924641082970631220519 140200386961624455946830779)
        ·
          refine ⟨210300580442436683920246169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140200386961624455946830779 210300580442436683920246169)
          ·
            refine ⟨157725435331827512940184627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210300580442436683920246169 157725435331827512940184627)
            ·
              refine ⟨236588152997741269410276941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157725435331827512940184627 236588152997741269410276941)
              ·
                refine ⟨88720557374152976028853853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 236588152997741269410276941 88720557374152976028853853)
                ·
                  refine ⟨33270209015307366010820195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88720557374152976028853853 33270209015307366010820195)
                  ·
                    refine ⟨49905313522961049016230293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33270209015307366010820195 49905313522961049016230293)
                    ·
                      refine ⟨2339311571388799172635795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49905313522961049016230293 2339311571388799172635795)
                      ·
                        rfl

theorem cell23_4555793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_4555793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555793 prefixEnd_4555793 := by exact prefixLift 4555793
  have htrace : WordTrace (prefixWord ++ tailWord_4555793) baseStart_4555793 baseEnd_4555793 := by
    simpa [prefixWord, tailWord_4555793, baseEnd_4555793] using wordTrace_append hprefix tailTrace_4555793
  have hstable : (prefixWord ++ tailWord_4555793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555793).length < 2 ^ (prefixWord ++ tailWord_4555793).sum := by decide
  have hdescent : baseEnd_4555793 < baseStart_4555793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555807 : List Nat := [1, 1, 2, 4, 1, 3, 2, 3, 2, 4]
def baseStart_4555807 : Nat := 118140960795 + 4555807 * 2 ^ 59
def prefixEnd_4555807 : Nat := 4983230072969 + 3 ^ 40 * 4555807 * 2
def baseEnd_4555807 : Nat := 779772920039320705953577

theorem tailTrace_4555807 : CollatzResearch.WordTrace tailWord_4555807 prefixEnd_4555807 779772920039320705953577 := by
  unfold tailWord_4555807
  simp only [CollatzResearch.WordTrace]
  refine ⟨166163932206096783735401675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110775954804064522490267783 166163932206096783735401675)
  ·
    refine ⟨249245898309145175603102513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166163932206096783735401675 249245898309145175603102513)
    ·
      refine ⟨186934423731858881702326885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249245898309145175603102513 186934423731858881702326885)
      ·
        refine ⟨35050204449723540319186291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186934423731858881702326885 35050204449723540319186291)
        ·
          refine ⟨52575306674585310478779437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35050204449723540319186291 52575306674585310478779437)
          ·
            refine ⟨19715740002969491429542289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52575306674585310478779437 19715740002969491429542289)
            ·
              refine ⟨14786805002227118572156717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19715740002969491429542289 14786805002227118572156717)
              ·
                refine ⟨5545051875835169464558769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14786805002227118572156717 5545051875835169464558769)
                ·
                  refine ⟨4158788906876377098419077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5545051875835169464558769 4158788906876377098419077)
                  ·
                    refine ⟨779772920039320705953577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4158788906876377098419077 779772920039320705953577)
                    ·
                      rfl

theorem cell23_4555807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 4].length) (baseStart_4555807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555807 prefixEnd_4555807 := by exact prefixLift 4555807
  have htrace : WordTrace (prefixWord ++ tailWord_4555807) baseStart_4555807 baseEnd_4555807 := by
    simpa [prefixWord, tailWord_4555807, baseEnd_4555807] using wordTrace_append hprefix tailTrace_4555807
  have hstable : (prefixWord ++ tailWord_4555807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555807).length < 2 ^ (prefixWord ++ tailWord_4555807).sum := by decide
  have hdescent : baseEnd_4555807 < baseStart_4555807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555818 : List Nat := [3, 1, 4, 1, 4, 1, 1, 1, 2, 3, 2]
def baseStart_4555818 : Nat := 118140960795 + 4555818 * 2 ^ 59
def prefixEnd_4555818 : Nat := 4983230072969 + 3 ^ 40 * 4555818 * 2
def baseEnd_4555818 : Nat := 2339324408405161574823181

theorem tailTrace_4555818 : CollatzResearch.WordTrace tailWord_4555818 prefixEnd_4555818 2339324408405161574823181 := by
  unfold tailWord_4555818
  simp only [CollatzResearch.WordTrace]
  refine ⟨41541083352264233153513027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110776222272704621742701405 41541083352264233153513027)
  ·
    refine ⟨62311625028396349730269541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41541083352264233153513027 62311625028396349730269541)
    ·
      refine ⟨11683429692824315574425539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62311625028396349730269541 11683429692824315574425539)
      ·
        refine ⟨17525144539236473361638309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11683429692824315574425539 17525144539236473361638309)
        ·
          refine ⟨3285964601106838755307183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17525144539236473361638309 3285964601106838755307183)
          ·
            refine ⟨4928946901660258132960775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3285964601106838755307183 4928946901660258132960775)
            ·
              refine ⟨7393420352490387199441163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4928946901660258132960775 7393420352490387199441163)
              ·
                refine ⟨11090130528735580799161745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7393420352490387199441163 11090130528735580799161745)
                ·
                  refine ⟨8317597896551685599371309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11090130528735580799161745 8317597896551685599371309)
                  ·
                    refine ⟨3119099211206882099764241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8317597896551685599371309 3119099211206882099764241)
                    ·
                      refine ⟨2339324408405161574823181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3119099211206882099764241 2339324408405161574823181)
                      ·
                        rfl

theorem cell23_4555818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_4555818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555818 prefixEnd_4555818 := by exact prefixLift 4555818
  have htrace : WordTrace (prefixWord ++ tailWord_4555818) baseStart_4555818 baseEnd_4555818 := by
    simpa [prefixWord, tailWord_4555818, baseEnd_4555818] using wordTrace_append hprefix tailTrace_4555818
  have hstable : (prefixWord ++ tailWord_4555818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555818).length < 2 ^ (prefixWord ++ tailWord_4555818).sum := by decide
  have hdescent : baseEnd_4555818 < baseStart_4555818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555820 : List Nat := [2, 2, 1, 1, 1, 2, 7, 7]
def baseStart_4555820 : Nat := 118140960795 + 4555820 * 2 ^ 59
def prefixEnd_4555820 : Nat := 4983230072969 + 3 ^ 40 * 4555820 * 2
def baseEnd_4555820 : Nat := 86641682791350761740673

theorem tailTrace_4555820 : CollatzResearch.WordTrace tailWord_4555820 prefixEnd_4555820 86641682791350761740673 := by
  unfold tailWord_4555820
  simp only [CollatzResearch.WordTrace]
  refine ⟨83082203177524843477812457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110776270903366457970416609 83082203177524843477812457)
  ·
    refine ⟨62311652383143632608359343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83082203177524843477812457 62311652383143632608359343)
    ·
      refine ⟨93467478574715448912539015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62311652383143632608359343 93467478574715448912539015)
      ·
        refine ⟨140201217862073173368808523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93467478574715448912539015 140201217862073173368808523)
        ·
          refine ⟨210301826793109760053212785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140201217862073173368808523 210301826793109760053212785)
          ·
            refine ⟨157726370094832320039909589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210301826793109760053212785 157726370094832320039909589)
            ·
              refine ⟨3696711799097632500935381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 157726370094832320039909589 3696711799097632500935381)
              ·
                refine ⟨86641682791350761740673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3696711799097632500935381 86641682791350761740673)
                ·
                  rfl

theorem cell23_4555820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 7].length) (baseStart_4555820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555820 prefixEnd_4555820 := by exact prefixLift 4555820
  have htrace : WordTrace (prefixWord ++ tailWord_4555820) baseStart_4555820 baseEnd_4555820 := by
    simpa [prefixWord, tailWord_4555820, baseEnd_4555820] using wordTrace_append hprefix tailTrace_4555820
  have hstable : (prefixWord ++ tailWord_4555820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555820).length < 2 ^ (prefixWord ++ tailWord_4555820).sum := by decide
  have hdescent : baseEnd_4555820 < baseStart_4555820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555823 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 6]
def baseStart_4555823 : Nat := 118140960795 + 4555823 * 2 ^ 59
def prefixEnd_4555823 : Nat := 4983230072969 + 3 ^ 40 * 4555823 * 2
def baseEnd_4555823 : Nat := 2339326975808434055260657

theorem tailTrace_4555823 : CollatzResearch.WordTrace tailWord_4555823 prefixEnd_4555823 2339326975808434055260657 := by
  unfold tailWord_4555823
  simp only [CollatzResearch.WordTrace]
  refine ⟨166164515774038818467984123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110776343849359212311989415 166164515774038818467984123)
  ·
    refine ⟨249246773661058227701976185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166164515774038818467984123 249246773661058227701976185)
    ·
      refine ⟨186935080245793670776482139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249246773661058227701976185 186935080245793670776482139)
      ·
        refine ⟨280402620368690506164723209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186935080245793670776482139 280402620368690506164723209)
        ·
          refine ⟨210301965276517879623542407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280402620368690506164723209 210301965276517879623542407)
          ·
            refine ⟨315452947914776819435313611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210301965276517879623542407 315452947914776819435313611)
            ·
              refine ⟨473179421872165229152970417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315452947914776819435313611 473179421872165229152970417)
              ·
                refine ⟨354884566404123921864727813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 473179421872165229152970417 354884566404123921864727813)
                ·
                  refine ⟨66540856200773235349636465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 354884566404123921864727813 66540856200773235349636465)
                  ·
                    refine ⟨49905642150579926512227349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66540856200773235349636465 49905642150579926512227349)
                    ·
                      refine ⟨2339326975808434055260657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49905642150579926512227349 2339326975808434055260657)
                      ·
                        rfl

theorem cell23_4555823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_4555823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555823 prefixEnd_4555823 := by exact prefixLift 4555823
  have htrace : WordTrace (prefixWord ++ tailWord_4555823) baseStart_4555823 baseEnd_4555823 := by
    simpa [prefixWord, tailWord_4555823, baseEnd_4555823] using wordTrace_append hprefix tailTrace_4555823
  have hstable : (prefixWord ++ tailWord_4555823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555823).length < 2 ^ (prefixWord ++ tailWord_4555823).sum := by decide
  have hdescent : baseEnd_4555823 < baseStart_4555823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555834 : List Nat := [3, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3]
def baseStart_4555834 : Nat := 118140960795 + 4555834 * 2 ^ 59
def prefixEnd_4555834 : Nat := 4983230072969 + 3 ^ 40 * 4555834 * 2
def baseEnd_4555834 : Nat := 2339332624095633512223107

theorem tailTrace_4555834 : CollatzResearch.WordTrace tailWord_4555834 prefixEnd_4555834 2339332624095633512223107 := by
  unfold tailWord_4555834
  simp only [CollatzResearch.WordTrace]
  refine ⟨41541229244249741836658639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110776611317999311564423037 41541229244249741836658639)
  ·
    refine ⟨62311843866374612754987959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41541229244249741836658639 62311843866374612754987959)
    ·
      refine ⟨93467765799561919132481939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62311843866374612754987959 93467765799561919132481939)
      ·
        refine ⟨140201648699342878698722909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93467765799561919132481939 140201648699342878698722909)
        ·
          refine ⟨52575618262253579512021091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140201648699342878698722909 52575618262253579512021091)
          ·
            refine ⟨78863427393380369268031637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52575618262253579512021091 78863427393380369268031637)
            ·
              refine ⟨3696723159064704809438983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78863427393380369268031637 3696723159064704809438983)
              ·
                refine ⟨5545084738597057214158475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3696723159064704809438983 5545084738597057214158475)
                ·
                  refine ⟨8317627107895585821237713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5545084738597057214158475 8317627107895585821237713)
                  ·
                    refine ⟨6238220330921689365928285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8317627107895585821237713 6238220330921689365928285)
                    ·
                      refine ⟨2339332624095633512223107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6238220330921689365928285 2339332624095633512223107)
                      ·
                        rfl

theorem cell23_4555834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3].length) (baseStart_4555834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555834 prefixEnd_4555834 := by exact prefixLift 4555834
  have htrace : WordTrace (prefixWord ++ tailWord_4555834) baseStart_4555834 baseEnd_4555834 := by
    simpa [prefixWord, tailWord_4555834, baseEnd_4555834] using wordTrace_append hprefix tailTrace_4555834
  have hstable : (prefixWord ++ tailWord_4555834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555834).length < 2 ^ (prefixWord ++ tailWord_4555834).sum := by decide
  have hdescent : baseEnd_4555834 < baseStart_4555834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555841 : List Nat := [1, 2, 5, 1, 3, 2, 1, 2, 2, 4]
def baseStart_4555841 : Nat := 118140960795 + 4555841 * 2 ^ 59
def prefixEnd_4555841 : Nat := 4983230072969 + 3 ^ 40 * 4555841 * 2
def baseEnd_4555841 : Nat := 779778739486738328278525

theorem tailTrace_4555841 : CollatzResearch.WordTrace tailWord_4555841 prefixEnd_4555841 779778739486738328278525 := by
  unfold tailWord_4555841
  simp only [CollatzResearch.WordTrace]
  refine ⟨166165172287973607542139377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110776781525315738361426251 166165172287973607542139377)
  ·
    refine ⟨124623879215980205656604533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166165172287973607542139377 124623879215980205656604533)
    ·
      refine ⟨11683488676498144280306675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124623879215980205656604533 11683488676498144280306675)
      ·
        refine ⟨17525233014747216420460013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11683488676498144280306675 17525233014747216420460013)
        ·
          refine ⟨6571962380530206157672505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17525233014747216420460013 6571962380530206157672505)
          ·
            refine ⟨4928971785397654618254379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6571962380530206157672505 4928971785397654618254379)
            ·
              refine ⟨7393457678096481927381569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4928971785397654618254379 7393457678096481927381569)
              ·
                refine ⟨5545093258572361445536177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7393457678096481927381569 5545093258572361445536177)
                ·
                  refine ⟨4158819943929271084152133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5545093258572361445536177 4158819943929271084152133)
                  ·
                    refine ⟨779778739486738328278525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4158819943929271084152133 779778739486738328278525)
                    ·
                      rfl

theorem cell23_4555841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_4555841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555841 prefixEnd_4555841 := by exact prefixLift 4555841
  have htrace : WordTrace (prefixWord ++ tailWord_4555841) baseStart_4555841 baseEnd_4555841 := by
    simpa [prefixWord, tailWord_4555841, baseEnd_4555841] using wordTrace_append hprefix tailTrace_4555841
  have hstable : (prefixWord ++ tailWord_4555841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555841).length < 2 ^ (prefixWord ++ tailWord_4555841).sum := by decide
  have hdescent : baseEnd_4555841 < baseStart_4555841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555857 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 5, 3, 2]
def baseStart_4555857 : Nat := 118140960795 + 4555857 * 2 ^ 59
def prefixEnd_4555857 : Nat := 4983230072969 + 3 ^ 40 * 4555857 * 2
def baseEnd_4555857 : Nat := 2339344434150686922235501

theorem tailTrace_4555857 : CollatzResearch.WordTrace tailWord_4555857 prefixEnd_4555857 2339344434150686922235501 := by
  unfold tailWord_4555857
  simp only [CollatzResearch.WordTrace]
  refine ⟨166165755855915642274721825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110777170570610428183147883 166165755855915642274721825)
  ·
    refine ⟨124624316891936731706041369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166165755855915642274721825 124624316891936731706041369)
    ·
      refine ⟨93468237668952548779531027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124624316891936731706041369 93468237668952548779531027)
      ·
        refine ⟨140202356503428823169296541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93468237668952548779531027 140202356503428823169296541)
        ·
          refine ⟨52575883688785808688486203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140202356503428823169296541 52575883688785808688486203)
          ·
            refine ⟨78863825533178713032729305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52575883688785808688486203 78863825533178713032729305)
            ·
              refine ⟨59147869149884034774546979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78863825533178713032729305 59147869149884034774546979)
              ·
                refine ⟨88721803724826052161820469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59147869149884034774546979 88721803724826052161820469)
                ·
                  refine ⟨8317669099202442390170669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88721803724826052161820469 8317669099202442390170669)
                  ·
                    refine ⟨3119125912200915896314001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8317669099202442390170669 3119125912200915896314001)
                    ·
                      refine ⟨2339344434150686922235501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3119125912200915896314001 2339344434150686922235501)
                      ·
                        rfl

theorem cell23_4555857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 3, 2].length) (baseStart_4555857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555857 prefixEnd_4555857 := by exact prefixLift 4555857
  have htrace : WordTrace (prefixWord ++ tailWord_4555857) baseStart_4555857 baseEnd_4555857 := by
    simpa [prefixWord, tailWord_4555857, baseEnd_4555857] using wordTrace_append hprefix tailTrace_4555857
  have hstable : (prefixWord ++ tailWord_4555857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555857).length < 2 ^ (prefixWord ++ tailWord_4555857).sum := by decide
  have hdescent : baseEnd_4555857 < baseStart_4555857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555887 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 3, 4, 2]
def baseStart_4555887 : Nat := 118140960795 + 4555887 * 2 ^ 59
def prefixEnd_4555887 : Nat := 4983230072969 + 3 ^ 40 * 4555887 * 2
def baseEnd_4555887 : Nat := 2339359838570321804860363

theorem tailTrace_4555887 : CollatzResearch.WordTrace tailWord_4555887 prefixEnd_4555887 2339359838570321804860363 := by
  unfold tailWord_4555887
  simp only [CollatzResearch.WordTrace]
  refine ⟨166166850045806957398313915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110777900030537971598875943 166166850045806957398313915)
  ·
    refine ⟨249250275068710436097470873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166166850045806957398313915 249250275068710436097470873)
    ·
      refine ⟨186937706301532827073103155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249250275068710436097470873 186937706301532827073103155)
      ·
        refine ⟨280406559452299240609654733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186937706301532827073103155 280406559452299240609654733)
        ·
          refine ⟨105152459794612215228620525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 280406559452299240609654733 105152459794612215228620525)
          ·
            refine ⟨39432172422979580710732697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105152459794612215228620525 39432172422979580710732697)
            ·
              refine ⟨29574129317234685533049523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39432172422979580710732697 29574129317234685533049523)
              ·
                refine ⟨44361193975852028299574285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29574129317234685533049523 44361193975852028299574285)
                ·
                  refine ⟨16635447740944510612340357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44361193975852028299574285 16635447740944510612340357)
                  ·
                    refine ⟨3119146451427095739813817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16635447740944510612340357 3119146451427095739813817)
                    ·
                      refine ⟨2339359838570321804860363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3119146451427095739813817 2339359838570321804860363)
                      ·
                        rfl

theorem cell23_4555887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 4, 2].length) (baseStart_4555887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555887 prefixEnd_4555887 := by exact prefixLift 4555887
  have htrace : WordTrace (prefixWord ++ tailWord_4555887) baseStart_4555887 baseEnd_4555887 := by
    simpa [prefixWord, tailWord_4555887, baseEnd_4555887] using wordTrace_append hprefix tailTrace_4555887
  have hstable : (prefixWord ++ tailWord_4555887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555887).length < 2 ^ (prefixWord ++ tailWord_4555887).sum := by decide
  have hdescent : baseEnd_4555887 < baseStart_4555887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555904 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 4, 2, 2]
def baseStart_4555904 : Nat := 118140960795 + 4555904 * 2 ^ 59
def prefixEnd_4555904 : Nat := 4983230072969 + 3 ^ 40 * 4555904 * 2
def baseEnd_4555904 : Nat := 2339368567741448238347785

theorem tailTrace_4555904 : CollatzResearch.WordTrace tailWord_4555904 prefixEnd_4555904 2339368567741448238347785 := by
  unfold tailWord_4555904
  simp only [CollatzResearch.WordTrace]
  refine ⟨83083735043372684650841383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110778313391163579534455177 83083735043372684650841383)
  ·
    refine ⟨124625602565059026976262075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83083735043372684650841383 124625602565059026976262075)
    ·
      refine ⟨186938403847588540464393113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124625602565059026976262075 186938403847588540464393113)
      ·
        refine ⟨140203802885691405348294835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186938403847588540464393113 140203802885691405348294835)
        ·
          refine ⟨210305704328537108022442253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140203802885691405348294835 210305704328537108022442253)
          ·
            refine ⟨78864639123201415508415845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210305704328537108022442253 78864639123201415508415845)
            ·
              refine ⟨14787119835600265407827971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78864639123201415508415845 14787119835600265407827971)
              ·
                refine ⟨22180679753400398111741957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14787119835600265407827971 22180679753400398111741957)
                ·
                  refine ⟨4158877453762574645951617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22180679753400398111741957 4158877453762574645951617)
                  ·
                    refine ⟨3119158090321930984463713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4158877453762574645951617 3119158090321930984463713)
                    ·
                      refine ⟨2339368567741448238347785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3119158090321930984463713 2339368567741448238347785)
                      ·
                        rfl

theorem cell23_4555904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 4, 2, 2].length) (baseStart_4555904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555904 prefixEnd_4555904 := by exact prefixLift 4555904
  have htrace : WordTrace (prefixWord ++ tailWord_4555904) baseStart_4555904 baseEnd_4555904 := by
    simpa [prefixWord, tailWord_4555904, baseEnd_4555904] using wordTrace_append hprefix tailTrace_4555904
  have hstable : (prefixWord ++ tailWord_4555904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555904).length < 2 ^ (prefixWord ++ tailWord_4555904).sum := by decide
  have hdescent : baseEnd_4555904 < baseStart_4555904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555961 : List Nat := [1, 2, 1, 4, 1, 5, 2, 2, 5]
def baseStart_4555961 : Nat := 118140960795 + 4555961 * 2 ^ 59
def prefixEnd_4555961 : Nat := 4983230072969 + 3 ^ 40 * 4555961 * 2
def baseEnd_4555961 : Nat := 259933092904306057259447

theorem tailTrace_4555961 : CollatzResearch.WordTrace tailWord_4555961 prefixEnd_4555961 259933092904306057259447 := by
  unfold tailWord_4555961
  simp only [CollatzResearch.WordTrace]
  refine ⟨166169549047538868036507737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110779699365025912024338491 166169549047538868036507737)
  ·
    refine ⟨124627161785654151027380803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166169549047538868036507737 124627161785654151027380803)
    ·
      refine ⟨186940742678481226541071205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124627161785654151027380803 186940742678481226541071205)
      ·
        refine ⟨35051389252215229976450851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186940742678481226541071205 35051389252215229976450851)
        ·
          refine ⟨52577083878322844964676277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35051389252215229976450851 52577083878322844964676277)
          ·
            refine ⟨4929101613592766715438401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52577083878322844964676277 4929101613592766715438401)
            ·
              refine ⟨3696826210194575036578801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4929101613592766715438401 3696826210194575036578801)
              ·
                refine ⟨2772619657645931277434101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3696826210194575036578801 2772619657645931277434101)
                ·
                  refine ⟨259933092904306057259447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2772619657645931277434101 259933092904306057259447)
                  ·
                    rfl

theorem cell23_4555961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 5].length) (baseStart_4555961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555961 prefixEnd_4555961 := by exact prefixLift 4555961
  have htrace : WordTrace (prefixWord ++ tailWord_4555961) baseStart_4555961 baseEnd_4555961 := by
    simpa [prefixWord, tailWord_4555961, baseEnd_4555961] using wordTrace_append hprefix tailTrace_4555961
  have hstable : (prefixWord ++ tailWord_4555961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555961).length < 2 ^ (prefixWord ++ tailWord_4555961).sum := by decide
  have hdescent : baseEnd_4555961 < baseStart_4555961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555964 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 2, 5, 2]
def baseStart_4555964 : Nat := 118140960795 + 4555964 * 2 ^ 59
def prefixEnd_4555964 : Nat := 4983230072969 + 3 ^ 40 * 4555964 * 2
def baseEnd_4555964 : Nat := 2339399376580718003597509

theorem tailTrace_4555964 : CollatzResearch.WordTrace tailWord_4555964 prefixEnd_4555964 2339399376580718003597509 := by
  unfold tailWord_4555964
  simp only [CollatzResearch.WordTrace]
  refine ⟨83084829233263999774433473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110779772311018666365911297 83084829233263999774433473)
  ·
    refine ⟨62313621924947999830825105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83084829233263999774433473 62313621924947999830825105)
    ·
      refine ⟨46735216443710999873118829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62313621924947999830825105 46735216443710999873118829)
      ·
        refine ⟨17525706166391624952419561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46735216443710999873118829 17525706166391624952419561)
        ·
          refine ⟨13144279624793718714314671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17525706166391624952419561 13144279624793718714314671)
          ·
            refine ⟨19716419437190578071472007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13144279624793718714314671 19716419437190578071472007)
            ·
              refine ⟨29574629155785867107208011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19716419437190578071472007 29574629155785867107208011)
              ·
                refine ⟨44361943733678800660812017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29574629155785867107208011 44361943733678800660812017)
                ·
                  refine ⟨33271457800259100495609013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44361943733678800660812017 33271457800259100495609013)
                  ·
                    refine ⟨3119199168774290671463345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33271457800259100495609013 3119199168774290671463345)
                    ·
                      refine ⟨2339399376580718003597509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3119199168774290671463345 2339399376580718003597509)
                      ·
                        rfl

theorem cell23_4555964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_4555964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555964 prefixEnd_4555964 := by exact prefixLift 4555964
  have htrace : WordTrace (prefixWord ++ tailWord_4555964) baseStart_4555964 baseEnd_4555964 := by
    simpa [prefixWord, tailWord_4555964, baseEnd_4555964] using wordTrace_append hprefix tailTrace_4555964
  have hstable : (prefixWord ++ tailWord_4555964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555964).length < 2 ^ (prefixWord ++ tailWord_4555964).sum := by decide
  have hdescent : baseEnd_4555964 < baseStart_4555964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4555987 : List Nat := [1, 1, 1, 2, 1, 1, 1, 8, 3, 4]
def baseStart_4555987 : Nat := 118140960795 + 4555987 * 2 ^ 59
def prefixEnd_4555987 : Nat := 4983230072969 + 3 ^ 40 * 4555987 * 2
def baseEnd_4555987 : Nat := 779803728878590471203301

theorem tailTrace_4555987 : CollatzResearch.WordTrace tailWord_4555987 prefixEnd_4555987 779803728878590471203301 := by
  unfold tailWord_4555987
  simp only [CollatzResearch.WordTrace]
  refine ⟨166170497345444674476954215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110780331563629782984636143 166170497345444674476954215)
  ·
    refine ⟨249255746018167011715431323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166170497345444674476954215 249255746018167011715431323)
    ·
      refine ⟨373883619027250517573146985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249255746018167011715431323 373883619027250517573146985)
      ·
        refine ⟨280412714270437888179860239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 373883619027250517573146985 280412714270437888179860239)
        ·
          refine ⟨420619071405656832269790359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280412714270437888179860239 420619071405656832269790359)
          ·
            refine ⟨630928607108485248404685539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420619071405656832269790359 630928607108485248404685539)
            ·
              refine ⟨946392910662727872607028309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630928607108485248404685539 946392910662727872607028309)
              ·
                refine ⟨11090541921828842257113613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 946392910662727872607028309 11090541921828842257113613)
                ·
                  refine ⟨4158953220685815846417605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11090541921828842257113613 4158953220685815846417605)
                  ·
                    refine ⟨779803728878590471203301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4158953220685815846417605 779803728878590471203301)
                    ·
                      rfl

theorem cell23_4555987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 4].length) (baseStart_4555987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4555987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4555987 prefixEnd_4555987 := by exact prefixLift 4555987
  have htrace : WordTrace (prefixWord ++ tailWord_4555987) baseStart_4555987 baseEnd_4555987 := by
    simpa [prefixWord, tailWord_4555987, baseEnd_4555987] using wordTrace_append hprefix tailTrace_4555987
  have hstable : (prefixWord ++ tailWord_4555987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4555987).length < 2 ^ (prefixWord ++ tailWord_4555987).sum := by decide
  have hdescent : baseEnd_4555987 < baseStart_4555987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4555987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556014 : List Nat := [4, 1, 2, 1, 1, 1, 2, 4, 2, 2, 3]
def baseStart_4556014 : Nat := 118140960795 + 4556014 * 2 ^ 59
def prefixEnd_4556014 : Nat := 4983230072969 + 3 ^ 40 * 4556014 * 2
def baseEnd_4556014 : Nat := 2339425050613442807972279

theorem tailTrace_4556014 : CollatzResearch.WordTrace tailWord_4556014 prefixEnd_4556014 2339425050613442807972279 := by
  unfold tailWord_4556014
  simp only [CollatzResearch.WordTrace]
  refine ⟨20771435264543357261023387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110780988077564572058791397 20771435264543357261023387)
  ·
    refine ⟨31157152896815035891535081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20771435264543357261023387 31157152896815035891535081)
    ·
      refine ⟨23367864672611276918651311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31157152896815035891535081 23367864672611276918651311)
      ·
        refine ⟨35051797008916915377976967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23367864672611276918651311 35051797008916915377976967)
        ·
          refine ⟨52577695513375373066965451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35051797008916915377976967 52577695513375373066965451)
          ·
            refine ⟨78866543270063059600448177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52577695513375373066965451 78866543270063059600448177)
            ·
              refine ⟨59149907452547294700336133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78866543270063059600448177 59149907452547294700336133)
              ·
                refine ⟨11090607647352617756313025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59149907452547294700336133 11090607647352617756313025)
                ·
                  refine ⟨8317955735514463317234769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11090607647352617756313025 8317955735514463317234769)
                  ·
                    refine ⟨6238466801635847487926077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8317955735514463317234769 6238466801635847487926077)
                    ·
                      refine ⟨2339425050613442807972279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6238466801635847487926077 2339425050613442807972279)
                      ·
                        rfl

theorem cell23_4556014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_4556014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556014 prefixEnd_4556014 := by exact prefixLift 4556014
  have htrace : WordTrace (prefixWord ++ tailWord_4556014) baseStart_4556014 baseEnd_4556014 := by
    simpa [prefixWord, tailWord_4556014, baseEnd_4556014] using wordTrace_append hprefix tailTrace_4556014
  have hstable : (prefixWord ++ tailWord_4556014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556014).length < 2 ^ (prefixWord ++ tailWord_4556014).sum := by decide
  have hdescent : baseEnd_4556014 < baseStart_4556014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556087 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 3]
def baseStart_4556087 : Nat := 118140960795 + 4556087 * 2 ^ 59
def prefixEnd_4556087 : Nat := 4983230072969 + 3 ^ 40 * 4556087 * 2
def baseEnd_4556087 : Nat := 2339462534701221022359443

theorem tailTrace_4556087 : CollatzResearch.WordTrace tailWord_4556087 prefixEnd_4556087 2339462534701221022359443 := by
  unfold tailWord_4556087
  simp only [CollatzResearch.WordTrace]
  refine ⟨166174144645082391555594515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110782763096721594370396343 166174144645082391555594515)
  ·
    refine ⟨249261216967623587333391773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166174144645082391555594515 249261216967623587333391773)
    ·
      refine ⟨93472956362858845250021915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249261216967623587333391773 93472956362858845250021915)
      ·
        refine ⟨140209434544288267875032873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93472956362858845250021915 140209434544288267875032873)
        ·
          refine ⟨105157075908216200906274655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140209434544288267875032873 105157075908216200906274655)
          ·
            refine ⟨157735613862324301359411983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105157075908216200906274655 157735613862324301359411983)
            ·
              refine ⟨236603420793486452039117975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157735613862324301359411983 236603420793486452039117975)
              ·
                refine ⟨354905131190229678058676963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236603420793486452039117975 354905131190229678058676963)
                ·
                  refine ⟨532357696785344517088015445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 354905131190229678058676963 532357696785344517088015445)
                  ·
                    refine ⟨6238566759203256059625181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 532357696785344517088015445 6238566759203256059625181)
                    ·
                      refine ⟨2339462534701221022359443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6238566759203256059625181 2339462534701221022359443)
                      ·
                        rfl

theorem cell23_4556087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_4556087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556087 prefixEnd_4556087 := by exact prefixLift 4556087
  have htrace : WordTrace (prefixWord ++ tailWord_4556087) baseStart_4556087 baseEnd_4556087 := by
    simpa [prefixWord, tailWord_4556087, baseEnd_4556087] using wordTrace_append hprefix tailTrace_4556087
  have hstable : (prefixWord ++ tailWord_4556087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556087).length < 2 ^ (prefixWord ++ tailWord_4556087).sum := by decide
  have hdescent : baseEnd_4556087 < baseStart_4556087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556094 : List Nat := [4, 2, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_4556094 : Nat := 118140960795 + 4556094 * 2 ^ 59
def prefixEnd_4556094 : Nat := 4983230072969 + 3 ^ 40 * 4556094 * 2
def baseEnd_4556094 : Nat := 779822043021934164990637

theorem tailTrace_4556094 : CollatzResearch.WordTrace tailWord_4556094 prefixEnd_4556094 779822043021934164990637 := by
  unfold tailWord_4556094
  simp only [CollatzResearch.WordTrace]
  refine ⟨20771799994507128968887417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110782933304038021167399557 20771799994507128968887417)
  ·
    refine ⟨15578849995880346726665563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20771799994507128968887417 15578849995880346726665563)
    ·
      refine ⟨23368274993820520089998345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15578849995880346726665563 23368274993820520089998345)
      ·
        refine ⟨17526206245365390067498759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23368274993820520089998345 17526206245365390067498759)
        ·
          refine ⟨26289309368048085101248139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17526206245365390067498759 26289309368048085101248139)
          ·
            refine ⟨39433964052072127651872209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26289309368048085101248139 39433964052072127651872209)
            ·
              refine ⟨29575473039054095738904157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39433964052072127651872209 29575473039054095738904157)
              ·
                refine ⟨11090802389645285902089059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29575473039054095738904157 11090802389645285902089059)
                ·
                  refine ⟨16636203584467928853133589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11090802389645285902089059 16636203584467928853133589)
                  ·
                    refine ⟨779822043021934164990637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16636203584467928853133589 779822043021934164990637)
                    ·
                      rfl

theorem cell23_4556094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_4556094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556094 prefixEnd_4556094 := by exact prefixLift 4556094
  have htrace : WordTrace (prefixWord ++ tailWord_4556094) baseStart_4556094 baseEnd_4556094 := by
    simpa [prefixWord, tailWord_4556094, baseEnd_4556094] using wordTrace_append hprefix tailTrace_4556094
  have hstable : (prefixWord ++ tailWord_4556094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556094).length < 2 ^ (prefixWord ++ tailWord_4556094).sum := by decide
  have hdescent : baseEnd_4556094 < baseStart_4556094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556101 : List Nat := [1, 3, 1, 1, 1, 2, 1, 6, 3, 2, 2]
def baseStart_4556101 : Nat := 118140960795 + 4556101 * 2 ^ 59
def prefixEnd_4556101 : Nat := 4983230072969 + 3 ^ 40 * 4556101 * 2
def baseEnd_4556101 : Nat := 2339469723430383967584379

theorem tailTrace_4556101 : CollatzResearch.WordTrace tailWord_4556101 prefixEnd_4556101 2339469723430383967584379 := by
  unfold tailWord_4556101
  simp only [CollatzResearch.WordTrace]
  refine ⟨166174655267031671946604157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110783103511354447964402771 166174655267031671946604157)
  ·
    refine ⟨62315495725136876979976559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166174655267031671946604157 62315495725136876979976559)
    ·
      refine ⟨93473243587705315469964839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62315495725136876979976559 93473243587705315469964839)
      ·
        refine ⟨140209865381557973204947259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93473243587705315469964839 140209865381557973204947259)
        ·
          refine ⟨210314798072336959807420889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140209865381557973204947259 210314798072336959807420889)
          ·
            refine ⟨157736098554252719855565667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210314798072336959807420889 157736098554252719855565667)
            ·
              refine ⟨236604147831379079783348501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157736098554252719855565667 236604147831379079783348501)
              ·
                refine ⟨11090819429595894364844461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 236604147831379079783348501 11090819429595894364844461)
                ·
                  refine ⟨4159057286098460386816673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11090819429595894364844461 4159057286098460386816673)
                  ·
                    refine ⟨3119292964573845290112505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4159057286098460386816673 3119292964573845290112505)
                    ·
                      refine ⟨2339469723430383967584379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3119292964573845290112505 2339469723430383967584379)
                      ·
                        rfl

theorem cell23_4556101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 2, 2].length) (baseStart_4556101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556101 prefixEnd_4556101 := by exact prefixLift 4556101
  have htrace : WordTrace (prefixWord ++ tailWord_4556101) baseStart_4556101 baseEnd_4556101 := by
    simpa [prefixWord, tailWord_4556101, baseEnd_4556101] using wordTrace_append hprefix tailTrace_4556101
  have hstable : (prefixWord ++ tailWord_4556101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556101).length < 2 ^ (prefixWord ++ tailWord_4556101).sum := by decide
  have hdescent : baseEnd_4556101 < baseStart_4556101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556151 : List Nat := [1, 1, 3, 1, 1, 2, 3, 5, 2, 1, 3]
def baseStart_4556151 : Nat := 118140960795 + 4556151 * 2 ^ 59
def prefixEnd_4556151 : Nat := 4983230072969 + 3 ^ 40 * 4556151 * 2
def baseEnd_4556151 : Nat := 2339495397463108771959149

theorem tailTrace_4556151 : CollatzResearch.WordTrace tailWord_4556151 prefixEnd_4556151 2339495397463108771959149 := by
  unfold tailWord_4556151
  simp only [CollatzResearch.WordTrace]
  refine ⟨166176478916850530485924307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110784319277900353657282871 166176478916850530485924307)
  ·
    refine ⟨249264718375275795728886461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166176478916850530485924307 249264718375275795728886461)
    ·
      refine ⟨93474269390728423398332423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249264718375275795728886461 93474269390728423398332423)
      ·
        refine ⟨140211404086092635097498635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93474269390728423398332423 140211404086092635097498635)
        ·
          refine ⟨210317106129138952646247953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140211404086092635097498635 210317106129138952646247953)
          ·
            refine ⟨157737829596854214484685965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210317106129138952646247953 157737829596854214484685965)
            ·
              refine ⟨59151686098820330431757237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157737829596854214484685965 59151686098820330431757237)
              ·
                refine ⟨5545470571764405977977241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59151686098820330431757237 5545470571764405977977241)
                ·
                  refine ⟨4159102928823304483482931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5545470571764405977977241 4159102928823304483482931)
                  ·
                    refine ⟨6238654393234956725224397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4159102928823304483482931 6238654393234956725224397)
                    ·
                      refine ⟨2339495397463108771959149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6238654393234956725224397 2339495397463108771959149)
                      ·
                        rfl

theorem cell23_4556151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 1, 3].length) (baseStart_4556151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556151 prefixEnd_4556151 := by exact prefixLift 4556151
  have htrace : WordTrace (prefixWord ++ tailWord_4556151) baseStart_4556151 baseEnd_4556151 := by
    simpa [prefixWord, tailWord_4556151, baseEnd_4556151] using wordTrace_append hprefix tailTrace_4556151
  have hstable : (prefixWord ++ tailWord_4556151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556151).length < 2 ^ (prefixWord ++ tailWord_4556151).sum := by decide
  have hdescent : baseEnd_4556151 < baseStart_4556151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556204 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 4]
def baseStart_4556204 : Nat := 118140960795 + 4556204 * 2 ^ 59
def prefixEnd_4556204 : Nat := 4983230072969 + 3 ^ 40 * 4556204 * 2
def baseEnd_4556204 : Nat := 2339522611937797064596405

theorem tailTrace_4556204 : CollatzResearch.WordTrace tailWord_4556204 prefixEnd_4556204 2339522611937797064596405 := by
  unfold tailWord_4556204
  simp only [CollatzResearch.WordTrace]
  refine ⟨83089205992829260268801833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110785607990439013691735777 83089205992829260268801833)
  ·
    refine ⟨62316904494621945201601375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83089205992829260268801833 62316904494621945201601375)
    ·
      refine ⟨93475356741932917802402063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62316904494621945201601375 93475356741932917802402063)
      ·
        refine ⟨140213035112899376703603095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93475356741932917802402063 140213035112899376703603095)
        ·
          refine ⟨210319552669349065055404643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140213035112899376703603095 210319552669349065055404643)
          ·
            refine ⟨315479329004023597583106965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210319552669349065055404643 315479329004023597583106965)
            ·
              refine ⟨14788093547063606136708139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 315479329004023597583106965 14788093547063606136708139)
              ·
                refine ⟨22182140320595409205062209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14788093547063606136708139 22182140320595409205062209)
                ·
                  refine ⟨16636605240446556903796657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22182140320595409205062209 16636605240446556903796657)
                  ·
                    refine ⟨12477453930334917677847493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16636605240446556903796657 12477453930334917677847493)
                    ·
                      refine ⟨2339522611937797064596405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12477453930334917677847493 2339522611937797064596405)
                      ·
                        rfl

theorem cell23_4556204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_4556204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556204 prefixEnd_4556204 := by exact prefixLift 4556204
  have htrace : WordTrace (prefixWord ++ tailWord_4556204) baseStart_4556204 baseEnd_4556204 := by
    simpa [prefixWord, tailWord_4556204, baseEnd_4556204] using wordTrace_append hprefix tailTrace_4556204
  have hstable : (prefixWord ++ tailWord_4556204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556204).length < 2 ^ (prefixWord ++ tailWord_4556204).sum := by decide
  have hdescent : baseEnd_4556204 < baseStart_4556204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556207 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 9]
def baseStart_4556207 : Nat := 118140960795 + 4556207 * 2 ^ 59
def prefixEnd_4556207 : Nat := 4983230072969 + 3 ^ 40 * 4556207 * 2
def baseEnd_4556207 : Nat := 2339524152379760552858891

theorem tailTrace_4556207 : CollatzResearch.WordTrace tailWord_4556207 prefixEnd_4556207 2339524152379760552858891 := by
  unfold tailWord_4556207
  simp only [CollatzResearch.WordTrace]
  refine ⟨166178521404647652049962875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110785680936431768033308583 166178521404647652049962875)
  ·
    refine ⟨249267782106971478074944313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166178521404647652049962875 249267782106971478074944313)
    ·
      refine ⟨186950836580228608556208235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249267782106971478074944313 186950836580228608556208235)
      ·
        refine ⟨280426254870342912834312353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186950836580228608556208235 280426254870342912834312353)
        ·
          refine ⟨210319691152757184625734265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280426254870342912834312353 210319691152757184625734265)
          ·
            refine ⟨157739768364567888469300699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210319691152757184625734265 157739768364567888469300699)
            ·
              refine ⟨236609652546851832703951049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157739768364567888469300699 236609652546851832703951049)
              ·
                refine ⟨177457239410138874527963287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236609652546851832703951049 177457239410138874527963287)
                ·
                  refine ⟨266185859115208311791944931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177457239410138874527963287 266185859115208311791944931)
                  ·
                    refine ⟨399278788672812467687917397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 266185859115208311791944931 399278788672812467687917397)
                    ·
                      refine ⟨2339524152379760552858891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 399278788672812467687917397 2339524152379760552858891)
                      ·
                        rfl

theorem cell23_4556207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_4556207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556207 prefixEnd_4556207 := by exact prefixLift 4556207
  have htrace : WordTrace (prefixWord ++ tailWord_4556207) baseStart_4556207 baseEnd_4556207 := by
    simpa [prefixWord, tailWord_4556207, baseEnd_4556207] using wordTrace_append hprefix tailTrace_4556207
  have hstable : (prefixWord ++ tailWord_4556207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556207).length < 2 ^ (prefixWord ++ tailWord_4556207).sum := by decide
  have hdescent : baseEnd_4556207 < baseStart_4556207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556224 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 3]
def baseStart_4556224 : Nat := 118140960795 + 4556224 * 2 ^ 59
def prefixEnd_4556224 : Nat := 4983230072969 + 3 ^ 40 * 4556224 * 2
def baseEnd_4556224 : Nat := 2339532881550886986346313

theorem tailTrace_4556224 : CollatzResearch.WordTrace tailWord_4556224 prefixEnd_4556224 2339532881550886986346313 := by
  unfold tailWord_4556224
  simp only [CollatzResearch.WordTrace]
  refine ⟨83089570722793031976665863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110786094297057375968887817 83089570722793031976665863)
  ·
    refine ⟨124634356084189547964998795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83089570722793031976665863 124634356084189547964998795)
    ·
      refine ⟨186951534126284321947498193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124634356084189547964998795 186951534126284321947498193)
      ·
        refine ⟨140213650594713241460623645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186951534126284321947498193 140213650594713241460623645)
        ·
          refine ⟨52580118973017465547733867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140213650594713241460623645 52580118973017465547733867)
          ·
            refine ⟨78870178459526198321600801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52580118973017465547733867 78870178459526198321600801)
            ·
              refine ⟨59152633844644648741200601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78870178459526198321600801 59152633844644648741200601)
              ·
                refine ⟨44364475383483486555900451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59152633844644648741200601 44364475383483486555900451)
                ·
                  refine ⟨66546713075225229833850677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44364475383483486555900451 66546713075225229833850677)
                  ·
                    refine ⟨6238754350802365296923501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66546713075225229833850677 6238754350802365296923501)
                    ·
                      refine ⟨2339532881550886986346313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6238754350802365296923501 2339532881550886986346313)
                      ·
                        rfl

theorem cell23_4556224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 3].length) (baseStart_4556224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556224 prefixEnd_4556224 := by exact prefixLift 4556224
  have htrace : WordTrace (prefixWord ++ tailWord_4556224) baseStart_4556224 baseEnd_4556224 := by
    simpa [prefixWord, tailWord_4556224, baseEnd_4556224] using wordTrace_append hprefix tailTrace_4556224
  have hstable : (prefixWord ++ tailWord_4556224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556224).length < 2 ^ (prefixWord ++ tailWord_4556224).sum := by decide
  have hdescent : baseEnd_4556224 < baseStart_4556224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556278 : List Nat := [5, 1, 1, 1, 2, 3, 2, 1, 2, 5]
def baseStart_4556278 : Nat := 118140960795 + 4556278 * 2 ^ 59
def prefixEnd_4556278 : Nat := 4983230072969 + 3 ^ 40 * 4556278 * 2
def baseEnd_4556278 : Nat := 779853536502076591690355

theorem tailTrace_4556278 : CollatzResearch.WordTrace tailWord_4556278 prefixEnd_4556278 779853536502076591690355 := by
  unfold tailWord_4556278
  simp only [CollatzResearch.WordTrace]
  refine ⟨10386319436711901948487343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110787407324926954117198325 10386319436711901948487343)
  ·
    refine ⟨15579479155067852922731015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10386319436711901948487343 15579479155067852922731015)
    ·
      refine ⟨23369218732601779384096523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15579479155067852922731015 23369218732601779384096523)
      ·
        refine ⟨35053828098902669076144785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23369218732601779384096523 35053828098902669076144785)
        ·
          refine ⟨26290371074177001807108589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35053828098902669076144785 26290371074177001807108589)
          ·
            refine ⟨9858889152816375677665721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26290371074177001807108589 9858889152816375677665721)
            ·
              refine ⟨7394166864612281758249291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9858889152816375677665721 7394166864612281758249291)
              ·
                refine ⟨11091250296918422637373937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7394166864612281758249291 11091250296918422637373937)
                ·
                  refine ⟨8318437722688816978030453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11091250296918422637373937 8318437722688816978030453)
                  ·
                    refine ⟨779853536502076591690355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8318437722688816978030453 779853536502076591690355)
                    ·
                      rfl

theorem cell23_4556278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_4556278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556278 prefixEnd_4556278 := by exact prefixLift 4556278
  have htrace : WordTrace (prefixWord ++ tailWord_4556278) baseStart_4556278 baseEnd_4556278 := by
    simpa [prefixWord, tailWord_4556278, baseEnd_4556278] using wordTrace_append hprefix tailTrace_4556278
  have hstable : (prefixWord ++ tailWord_4556278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556278).length < 2 ^ (prefixWord ++ tailWord_4556278).sum := by decide
  have hdescent : baseEnd_4556278 < baseStart_4556278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556281 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 4, 4, 2]
def baseStart_4556281 : Nat := 118140960795 + 4556281 * 2 ^ 59
def prefixEnd_4556281 : Nat := 4983230072969 + 3 ^ 40 * 4556281 * 2
def baseEnd_4556281 : Nat := 2339562149948193263333551

theorem tailTrace_4556281 : CollatzResearch.WordTrace tailWord_4556281 prefixEnd_4556281 2339562149948193263333551 := by
  unfold tailWord_4556281
  simp only [CollatzResearch.WordTrace]
  refine ⟨166181220406379562688156697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110787480270919708458771131 166181220406379562688156697)
  ·
    refine ⟨124635915304784672016117523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166181220406379562688156697 124635915304784672016117523)
    ·
      refine ⟨186953872957177008024176285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124635915304784672016117523 186953872957177008024176285)
      ·
        refine ⟨70107702358941378009066107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186953872957177008024176285 70107702358941378009066107)
        ·
          refine ⟨105161553538412067013599161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70107702358941378009066107 105161553538412067013599161)
          ·
            refine ⟨78871165153809050260199371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105161553538412067013599161 78871165153809050260199371)
            ·
              refine ⟨118306747730713575390299057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78871165153809050260199371 118306747730713575390299057)
              ·
                refine ⟨88730060798035181542724293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118306747730713575390299057 88730060798035181542724293)
                ·
                  refine ⟨16636886399631596539260805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88730060798035181542724293 16636886399631596539260805)
                  ·
                    refine ⟨3119416199930924351111401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16636886399631596539260805 3119416199930924351111401)
                    ·
                      refine ⟨2339562149948193263333551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3119416199930924351111401 2339562149948193263333551)
                      ·
                        rfl

theorem cell23_4556281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_4556281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556281 prefixEnd_4556281 := by exact prefixLift 4556281
  have htrace : WordTrace (prefixWord ++ tailWord_4556281) baseStart_4556281 baseEnd_4556281 := by
    simpa [prefixWord, tailWord_4556281, baseEnd_4556281] using wordTrace_append hprefix tailTrace_4556281
  have hstable : (prefixWord ++ tailWord_4556281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556281).length < 2 ^ (prefixWord ++ tailWord_4556281).sum := by decide
  have hdescent : baseEnd_4556281 < baseStart_4556281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556321 : List Nat := [1, 2, 3, 2, 2, 2, 2, 3, 6]
def baseStart_4556321 : Nat := 118140960795 + 4556321 * 2 ^ 59
def prefixEnd_4556321 : Nat := 4983230072969 + 3 ^ 40 * 4556321 * 2
def baseEnd_4556321 : Nat := 259953632130485900759263

theorem tailTrace_4556321 : CollatzResearch.WordTrace tailWord_4556321 prefixEnd_4556321 259953632130485900759263 := by
  unfold tailWord_4556321
  simp only [CollatzResearch.WordTrace]
  refine ⟨166182679326234649519612817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110788452884156433013075211 166182679326234649519612817)
  ·
    refine ⟨124637009494675987139709613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166182679326234649519612817 124637009494675987139709613)
    ·
      refine ⟨46738878560503495177391105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124637009494675987139709613 46738878560503495177391105)
      ·
        refine ⟨35054158920377621383043329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46738878560503495177391105 35054158920377621383043329)
        ·
          refine ⟨26290619190283216037282497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35054158920377621383043329 26290619190283216037282497)
          ·
            refine ⟨19717964392712412027961873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26290619190283216037282497 19717964392712412027961873)
            ·
              refine ⟨14788473294534309020971405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19717964392712412027961873 14788473294534309020971405)
              ·
                refine ⟨5545677485450365882864277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14788473294534309020971405 5545677485450365882864277)
                ·
                  refine ⟨259953632130485900759263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5545677485450365882864277 259953632130485900759263)
                  ·
                    rfl

theorem cell23_4556321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 6].length) (baseStart_4556321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556321 prefixEnd_4556321 := by exact prefixLift 4556321
  have htrace : WordTrace (prefixWord ++ tailWord_4556321) baseStart_4556321 baseEnd_4556321 := by
    simpa [prefixWord, tailWord_4556321, baseEnd_4556321] using wordTrace_append hprefix tailTrace_4556321
  have hstable : (prefixWord ++ tailWord_4556321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556321).length < 2 ^ (prefixWord ++ tailWord_4556321).sum := by decide
  have hdescent : baseEnd_4556321 < baseStart_4556321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556388 : List Nat := [2, 3, 1, 1, 2, 3, 1, 4, 1, 1, 4]
def baseStart_4556388 : Nat := 118140960795 + 4556388 * 2 ^ 59
def prefixEnd_4556388 : Nat := 4983230072969 + 3 ^ 40 * 4556388 * 2
def baseEnd_4556388 : Nat := 2339617092378224344695559

theorem tailTrace_4556388 : CollatzResearch.WordTrace tailWord_4556388 prefixEnd_4556388 2339617092378224344695559 := by
  unfold tailWord_4556388
  simp only [CollatzResearch.WordTrace]
  refine ⟨83092561508495959981150909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110790082011327946641534545 83092561508495959981150909)
  ·
    refine ⟨31159710565685984992931591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83092561508495959981150909 31159710565685984992931591)
    ·
      refine ⟨46739565848528977489397387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31159710565685984992931591 46739565848528977489397387)
      ·
        refine ⟨70109348772793466234096081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46739565848528977489397387 70109348772793466234096081)
        ·
          refine ⟨52582011579595099675572061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70109348772793466234096081 52582011579595099675572061)
          ·
            refine ⟨19718254342348162378339523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52582011579595099675572061 19718254342348162378339523)
            ·
              refine ⟨29577381513522243567509285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19718254342348162378339523 29577381513522243567509285)
              ·
                refine ⟨5545759033785420668907991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29577381513522243567509285 5545759033785420668907991)
                ·
                  refine ⟨8318638550678131003361987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5545759033785420668907991 8318638550678131003361987)
                  ·
                    refine ⟨12477957826017196505042981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8318638550678131003361987 12477957826017196505042981)
                    ·
                      refine ⟨2339617092378224344695559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12477957826017196505042981 2339617092378224344695559)
                      ·
                        rfl

theorem cell23_4556388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_4556388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556388 prefixEnd_4556388 := by exact prefixLift 4556388
  have htrace : WordTrace (prefixWord ++ tailWord_4556388) baseStart_4556388 baseEnd_4556388 := by
    simpa [prefixWord, tailWord_4556388, baseEnd_4556388] using wordTrace_append hprefix tailTrace_4556388
  have hstable : (prefixWord ++ tailWord_4556388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556388).length < 2 ^ (prefixWord ++ tailWord_4556388).sum := by decide
  have hdescent : baseEnd_4556388 < baseStart_4556388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556401 : List Nat := [1, 2, 2, 2, 1, 1, 1, 6, 1, 2, 4]
def baseStart_4556401 : Nat := 118140960795 + 4556401 * 2 ^ 59
def prefixEnd_4556401 : Nat := 4983230072969 + 3 ^ 40 * 4556401 * 2
def baseEnd_4556401 : Nat := 2339623767626732793832999

theorem tailTrace_4556401 : CollatzResearch.WordTrace tailWord_4556401 prefixEnd_4556401 2339623767626732793832999 := by
  unfold tailWord_4556401
  simp only [CollatzResearch.WordTrace]
  refine ⟨166185597165944823182525057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110790398110629882121683371 166185597165944823182525057)
  ·
    refine ⟨124639197874458617386893793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166185597165944823182525057 124639197874458617386893793)
    ·
      refine ⟨93479398405843963040170345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124639197874458617386893793 93479398405843963040170345)
      ·
        refine ⟨70109548804382972280127759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93479398405843963040170345 70109548804382972280127759)
        ·
          refine ⟨105164323206574458420191639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70109548804382972280127759 105164323206574458420191639)
          ·
            refine ⟨157746484809861687630287459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105164323206574458420191639 157746484809861687630287459)
            ·
              refine ⟨236619727214792531445431189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157746484809861687630287459 236619727214792531445431189)
              ·
                refine ⟨11091549713193399911504587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 236619727214792531445431189 11091549713193399911504587)
                ·
                  refine ⟨16637324569790099867256881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11091549713193399911504587 16637324569790099867256881)
                  ·
                    refine ⟨12477993427342574900442661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16637324569790099867256881 12477993427342574900442661)
                    ·
                      refine ⟨2339623767626732793832999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12477993427342574900442661 2339623767626732793832999)
                      ·
                        rfl

theorem cell23_4556401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_4556401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556401 prefixEnd_4556401 := by exact prefixLift 4556401
  have htrace : WordTrace (prefixWord ++ tailWord_4556401) baseStart_4556401 baseEnd_4556401 := by
    simpa [prefixWord, tailWord_4556401, baseEnd_4556401] using wordTrace_append hprefix tailTrace_4556401
  have hstable : (prefixWord ++ tailWord_4556401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556401).length < 2 ^ (prefixWord ++ tailWord_4556401).sum := by decide
  have hdescent : baseEnd_4556401 < baseStart_4556401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556405 : List Nat := [1, 3, 4, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_4556405 : Nat := 118140960795 + 4556405 * 2 ^ 59
def prefixEnd_4556405 : Nat := 4983230072969 + 3 ^ 40 * 4556405 * 2
def baseEnd_4556405 : Nat := 2339625821549350778182981

theorem tailTrace_4556405 : CollatzResearch.WordTrace tailWord_4556405 prefixEnd_4556405 2339625821549350778182981 := by
  unfold tailWord_4556405
  simp only [CollatzResearch.WordTrace]
  refine ⟨166185743057930331865670669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110790495371953554577113779 166185743057930331865670669)
  ·
    refine ⟨62319653646723874449626501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166185743057930331865670669 62319653646723874449626501)
    ·
      refine ⟨11684935058760726459304969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62319653646723874449626501 11684935058760726459304969)
      ·
        refine ⟨8763701294070544844478727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11684935058760726459304969 8763701294070544844478727)
        ·
          refine ⟨13145551941105817266718091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8763701294070544844478727 13145551941105817266718091)
          ·
            refine ⟨19718327911658725900077137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13145551941105817266718091 19718327911658725900077137)
            ·
              refine ⟨14788745933744044425057853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19718327911658725900077137 14788745933744044425057853)
              ·
                refine ⟨5545779725154016659396695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14788745933744044425057853 5545779725154016659396695)
                ·
                  refine ⟨8318669587731024989095043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5545779725154016659396695 8318669587731024989095043)
                  ·
                    refine ⟨12478004381596537483642565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8318669587731024989095043 12478004381596537483642565)
                    ·
                      refine ⟨2339625821549350778182981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12478004381596537483642565 2339625821549350778182981)
                      ·
                        rfl

theorem cell23_4556405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_4556405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556405 prefixEnd_4556405 := by exact prefixLift 4556405
  have htrace : WordTrace (prefixWord ++ tailWord_4556405) baseStart_4556405 baseEnd_4556405 := by
    simpa [prefixWord, tailWord_4556405, baseEnd_4556405] using wordTrace_append hprefix tailTrace_4556405
  have hstable : (prefixWord ++ tailWord_4556405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556405).length < 2 ^ (prefixWord ++ tailWord_4556405).sum := by decide
  have hdescent : baseEnd_4556405 < baseStart_4556405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556456 : List Nat := [2, 1, 7, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_4556456 : Nat := 118140960795 + 4556456 * 2 ^ 59
def prefixEnd_4556456 : Nat := 4983230072969 + 3 ^ 40 * 4556456 * 2
def baseEnd_4556456 : Nat := 2339652009062730078645247

theorem tailTrace_4556456 : CollatzResearch.WordTrace tailWord_4556456 prefixEnd_4556456 2339652009062730078645247 := by
  unfold tailWord_4556456
  simp only [CollatzResearch.WordTrace]
  refine ⟨83093801590372783787888611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110791735453830378383851481 83093801590372783787888611)
  ·
    refine ⟨124640702385559175681832917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83093801590372783787888611 124640702385559175681832917)
    ·
      refine ⟨2921266462161543180042959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 124640702385559175681832917 2921266462161543180042959)
      ·
        refine ⟨4381899693242314770064439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2921266462161543180042959 4381899693242314770064439)
        ·
          refine ⟨6572849539863472155096659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4381899693242314770064439 6572849539863472155096659)
          ·
            refine ⟨9859274309795208232644989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6572849539863472155096659 9859274309795208232644989)
            ·
              refine ⟨3697227866173203087241871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9859274309795208232644989 3697227866173203087241871)
              ·
                refine ⟨5545841799259804630862807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3697227866173203087241871 5545841799259804630862807)
                ·
                  refine ⟨8318762698889706946294211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5545841799259804630862807 8318762698889706946294211)
                  ·
                    refine ⟨12478144048334560419441317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8318762698889706946294211 12478144048334560419441317)
                    ·
                      refine ⟨2339652009062730078645247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12478144048334560419441317 2339652009062730078645247)
                      ·
                        rfl

theorem cell23_4556456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_4556456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556456 prefixEnd_4556456 := by exact prefixLift 4556456
  have htrace : WordTrace (prefixWord ++ tailWord_4556456) baseStart_4556456 baseEnd_4556456 := by
    simpa [prefixWord, tailWord_4556456, baseEnd_4556456] using wordTrace_append hprefix tailTrace_4556456
  have hstable : (prefixWord ++ tailWord_4556456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556456).length < 2 ^ (prefixWord ++ tailWord_4556456).sum := by decide
  have hdescent : baseEnd_4556456 < baseStart_4556456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556478 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_4556478 : Nat := 118140960795 + 4556478 * 2 ^ 59
def prefixEnd_4556478 : Nat := 4983230072969 + 3 ^ 40 * 4556478 * 2
def baseEnd_4556478 : Nat := 2339663305637128992570145

theorem tailTrace_4556478 : CollatzResearch.WordTrace tailWord_4556478 prefixEnd_4556478 2339663305637128992570145 := by
  unfold tailWord_4556478
  simp only [CollatzResearch.WordTrace]
  refine ⟨20773550698333233166634761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110792270391110576888718725 20773550698333233166634761)
  ·
    refine ⟨15580163023749924874976071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20773550698333233166634761 15580163023749924874976071)
    ·
      refine ⟨23370244535624887312464107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15580163023749924874976071 23370244535624887312464107)
      ·
        refine ⟨35055366803437330968696161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23370244535624887312464107 35055366803437330968696161)
        ·
          refine ⟨26291525102577998226522121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35055366803437330968696161 26291525102577998226522121)
          ·
            refine ⟨19718643826933498669891591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26291525102577998226522121 19718643826933498669891591)
            ·
              refine ⟨29577965740400248004837387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19718643826933498669891591 29577965740400248004837387)
              ·
                refine ⟨44366948610600372007256081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29577965740400248004837387 44366948610600372007256081)
                ·
                  refine ⟨33275211457950279005442061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44366948610600372007256081 33275211457950279005442061)
                  ·
                    refine ⟨12478204296731354627040773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33275211457950279005442061 12478204296731354627040773)
                    ·
                      refine ⟨2339663305637128992570145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12478204296731354627040773 2339663305637128992570145)
                      ·
                        rfl

theorem cell23_4556478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_4556478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556478 prefixEnd_4556478 := by exact prefixLift 4556478
  have htrace : WordTrace (prefixWord ++ tailWord_4556478) baseStart_4556478 baseEnd_4556478 := by
    simpa [prefixWord, tailWord_4556478, baseEnd_4556478] using wordTrace_append hprefix tailTrace_4556478
  have hstable : (prefixWord ++ tailWord_4556478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556478).length < 2 ^ (prefixWord ++ tailWord_4556478).sum := by decide
  have hdescent : baseEnd_4556478 < baseStart_4556478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556529 : List Nat := [1, 2, 2, 2, 2, 5, 1, 2, 2, 2, 2]
def baseStart_4556529 : Nat := 118140960795 + 4556529 * 2 ^ 59
def prefixEnd_4556529 : Nat := 4983230072969 + 3 ^ 40 * 4556529 * 2
def baseEnd_4556529 : Nat := 2339689493150508293032411

theorem tailTrace_4556529 : CollatzResearch.WordTrace tailWord_4556529 prefixEnd_4556529 2339689493150508293032411 := by
  unfold tailWord_4556529
  simp only [CollatzResearch.WordTrace]
  refine ⟨166190265709481101043184641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110793510472987400695456427 166190265709481101043184641)
  ·
    refine ⟨124642699282110825782388481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166190265709481101043184641 124642699282110825782388481)
    ·
      refine ⟨93482024461583119336791361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124642699282110825782388481 93482024461583119336791361)
      ·
        refine ⟨70111518346187339502593521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93482024461583119336791361 70111518346187339502593521)
        ·
          refine ⟨52583638759640504626945141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70111518346187339502593521 52583638759640504626945141)
          ·
            refine ⟨4929716133716297308776107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52583638759640504626945141 4929716133716297308776107)
            ·
              refine ⟨7394574200574445963164161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4929716133716297308776107 7394574200574445963164161)
              ·
                refine ⟨5545930650430834472373121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7394574200574445963164161 5545930650430834472373121)
                ·
                  refine ⟨4159447987823125854279841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5545930650430834472373121 4159447987823125854279841)
                  ·
                    refine ⟨3119585990867344390709881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4159447987823125854279841 3119585990867344390709881)
                    ·
                      refine ⟨2339689493150508293032411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3119585990867344390709881 2339689493150508293032411)
                      ·
                        rfl

theorem cell23_4556529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_4556529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556529 prefixEnd_4556529 := by exact prefixLift 4556529
  have htrace : WordTrace (prefixWord ++ tailWord_4556529) baseStart_4556529 baseEnd_4556529 := by
    simpa [prefixWord, tailWord_4556529, baseEnd_4556529] using wordTrace_append hprefix tailTrace_4556529
  have hstable : (prefixWord ++ tailWord_4556529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556529).length < 2 ^ (prefixWord ++ tailWord_4556529).sum := by decide
  have hdescent : baseEnd_4556529 < baseStart_4556529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556546 : List Nat := [3, 4, 1, 1, 1, 1, 5, 1, 2, 2, 2]
def baseStart_4556546 : Nat := 118140960795 + 4556546 * 2 ^ 59
def prefixEnd_4556546 : Nat := 4983230072969 + 3 ^ 40 * 4556546 * 2
def baseEnd_4556546 : Nat := 2339698222321634726519833

theorem tailTrace_4556546 : CollatzResearch.WordTrace tailWord_4556546 prefixEnd_4556546 2339698222321634726519833 := by
  unfold tailWord_4556546
  simp only [CollatzResearch.WordTrace]
  refine ⟨41547721437604878236638373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110793923833613008631035661 41547721437604878236638373)
  ·
    refine ⟨7790197769550914669369695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41547721437604878236638373 7790197769550914669369695)
    ·
      refine ⟨11685296654326372004054543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7790197769550914669369695 11685296654326372004054543)
      ·
        refine ⟨17527944981489558006081815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11685296654326372004054543 17527944981489558006081815)
        ·
          refine ⟨26291917472234337009122723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17527944981489558006081815 26291917472234337009122723)
          ·
            refine ⟨39437876208351505513684085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26291917472234337009122723 39437876208351505513684085)
            ·
              refine ⟨3697300894532953641907883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39437876208351505513684085 3697300894532953641907883)
              ·
                refine ⟨5545951341799430462861825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3697300894532953641907883 5545951341799430462861825)
                ·
                  refine ⟨4159463506349572847146369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5545951341799430462861825 4159463506349572847146369)
                  ·
                    refine ⟨3119597629762179635359777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4159463506349572847146369 3119597629762179635359777)
                    ·
                      refine ⟨2339698222321634726519833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3119597629762179635359777 2339698222321634726519833)
                      ·
                        rfl

theorem cell23_4556546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_4556546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556546 prefixEnd_4556546 := by exact prefixLift 4556546
  have htrace : WordTrace (prefixWord ++ tailWord_4556546) baseStart_4556546 baseEnd_4556546 := by
    simpa [prefixWord, tailWord_4556546, baseEnd_4556546] using wordTrace_append hprefix tailTrace_4556546
  have hstable : (prefixWord ++ tailWord_4556546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556546).length < 2 ^ (prefixWord ++ tailWord_4556546).sum := by decide
  have hdescent : baseEnd_4556546 < baseStart_4556546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556548 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 1, 7]
def baseStart_4556548 : Nat := 118140960795 + 4556548 * 2 ^ 59
def prefixEnd_4556548 : Nat := 4983230072969 + 3 ^ 40 * 4556548 * 2
def baseEnd_4556548 : Nat := 779899749760981239564941

theorem tailTrace_4556548 : CollatzResearch.WordTrace tailWord_4556548 prefixEnd_4556548 779899749760981239564941 := by
  unfold tailWord_4556548
  simp only [CollatzResearch.WordTrace]
  refine ⟨83095479348206133644063149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110793972464274844858750865 83095479348206133644063149)
  ·
    refine ⟨31160804755577300116523681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83095479348206133644063149 31160804755577300116523681)
    ·
      refine ⟨23370603566682975087392761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31160804755577300116523681 23370603566682975087392761)
      ·
        refine ⟨17527952675012231315544571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23370603566682975087392761 17527952675012231315544571)
        ·
          refine ⟨26291929012518346973316857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17527952675012231315544571 26291929012518346973316857)
          ·
            refine ⟨19718946759388760229987643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26291929012518346973316857 19718946759388760229987643)
            ·
              refine ⟨29578420139083140344981465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19718946759388760229987643 29578420139083140344981465)
              ·
                refine ⟨22183815104312355258736099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29578420139083140344981465 22183815104312355258736099)
                ·
                  refine ⟨33275722656468532888104149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22183815104312355258736099 33275722656468532888104149)
                  ·
                    refine ⟨779899749760981239564941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33275722656468532888104149 779899749760981239564941)
                    ·
                      rfl

theorem cell23_4556548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_4556548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556548 prefixEnd_4556548 := by exact prefixLift 4556548
  have htrace : WordTrace (prefixWord ++ tailWord_4556548) baseStart_4556548 baseEnd_4556548 := by
    simpa [prefixWord, tailWord_4556548, baseEnd_4556548] using wordTrace_append hprefix tailTrace_4556548
  have hstable : (prefixWord ++ tailWord_4556548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556548).length < 2 ^ (prefixWord ++ tailWord_4556548).sum := by decide
  have hdescent : baseEnd_4556548 < baseStart_4556548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556561 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 1, 10]
def baseStart_4556561 : Nat := 118140960795 + 4556561 * 2 ^ 59
def prefixEnd_4556561 : Nat := 4983230072969 + 3 ^ 40 * 4556561 * 2
def baseEnd_4556561 : Nat := 779901974843817389277421

theorem tailTrace_4556561 : CollatzResearch.WordTrace tailWord_4556561 prefixEnd_4556561 779901974843817389277421 := by
  unfold tailWord_4556561
  simp only [CollatzResearch.WordTrace]
  refine ⟨166191432845365170508349537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110794288563576780338899691 166191432845365170508349537)
  ·
    refine ⟨124643574634023877881262153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166191432845365170508349537 124643574634023877881262153)
    ·
      refine ⟨93482680975517908410946615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124643574634023877881262153 93482680975517908410946615)
      ·
        refine ⟨140224021463276862616419923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93482680975517908410946615 140224021463276862616419923)
        ·
          refine ⟨210336032194915293924629885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140224021463276862616419923 210336032194915293924629885)
          ·
            refine ⟨78876012073093235221736207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210336032194915293924629885 78876012073093235221736207)
            ·
              refine ⟨118314018109639852832604311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78876012073093235221736207 118314018109639852832604311)
              ·
                refine ⟨177471027164459779248906467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118314018109639852832604311 177471027164459779248906467)
                ·
                  refine ⟨266206540746689668873359701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177471027164459779248906467 266206540746689668873359701)
                  ·
                    refine ⟨779901974843817389277421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 266206540746689668873359701 779901974843817389277421)
                    ·
                      rfl

theorem cell23_4556561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_4556561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556561 prefixEnd_4556561 := by exact prefixLift 4556561
  have htrace : WordTrace (prefixWord ++ tailWord_4556561) baseStart_4556561 baseEnd_4556561 := by
    simpa [prefixWord, tailWord_4556561, baseEnd_4556561] using wordTrace_append hprefix tailTrace_4556561
  have hstable : (prefixWord ++ tailWord_4556561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556561).length < 2 ^ (prefixWord ++ tailWord_4556561).sum := by decide
  have hdescent : baseEnd_4556561 < baseStart_4556561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556568 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 1, 3, 4]
def baseStart_4556568 : Nat := 118140960795 + 4556568 * 2 ^ 59
def prefixEnd_4556568 : Nat := 4983230072969 + 3 ^ 40 * 4556568 * 2
def baseEnd_4556568 : Nat := 2339709518896033640444731

theorem tailTrace_4556568 : CollatzResearch.WordTrace tailWord_4556568 prefixEnd_4556568 2339709518896033640444731 := by
  unfold tailWord_4556568
  simp only [CollatzResearch.WordTrace]
  refine ⟨83095844078169905351927179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110794458770893207135902905 83095844078169905351927179)
  ·
    refine ⟨124643766117254858027890769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83095844078169905351927179 124643766117254858027890769)
    ·
      refine ⟨93482824587941143520918077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124643766117254858027890769 93482824587941143520918077)
      ·
        refine ⟨35056059220477928820344279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93482824587941143520918077 35056059220477928820344279)
        ·
          refine ⟨52584088830716893230516419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35056059220477928820344279 52584088830716893230516419)
          ·
            refine ⟨78876133246075339845774629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52584088830716893230516419 78876133246075339845774629)
            ·
              refine ⟨14789274983639126221082743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78876133246075339845774629 14789274983639126221082743)
              ·
                refine ⟨22183912475458689331624115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14789274983639126221082743 22183912475458689331624115)
                ·
                  refine ⟨33275868713188033997436173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22183912475458689331624115 33275868713188033997436173)
                  ·
                    refine ⟨12478450767445512749038565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33275868713188033997436173 12478450767445512749038565)
                    ·
                      refine ⟨2339709518896033640444731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12478450767445512749038565 2339709518896033640444731)
                      ·
                        rfl

theorem cell23_4556568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_4556568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556568 prefixEnd_4556568 := by exact prefixLift 4556568
  have htrace : WordTrace (prefixWord ++ tailWord_4556568) baseStart_4556568 baseEnd_4556568 := by
    simpa [prefixWord, tailWord_4556568, baseEnd_4556568] using wordTrace_append hprefix tailTrace_4556568
  have hstable : (prefixWord ++ tailWord_4556568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556568).length < 2 ^ (prefixWord ++ tailWord_4556568).sum := by decide
  have hdescent : baseEnd_4556568 < baseStart_4556568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556642 : List Nat := [3, 3, 2, 1, 2, 2, 2, 2, 6]
def baseStart_4556642 : Nat := 118140960795 + 4556642 * 2 ^ 59
def prefixEnd_4556642 : Nat := 4983230072969 + 3 ^ 40 * 4556642 * 2
def baseEnd_4556642 : Nat := 259971946273829594546599

theorem tailTrace_4556642 : CollatzResearch.WordTrace tailWord_4556642 prefixEnd_4556642 259971946273829594546599 := by
  unfold tailWord_4556642
  simp only [CollatzResearch.WordTrace]
  refine ⟨41548596789517930335512045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110796258105381147561365453 41548596789517930335512045)
  ·
    refine ⟨15580723796069223875817017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41548596789517930335512045 15580723796069223875817017)
    ·
      refine ⟨11685542847051917906862763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15580723796069223875817017 11685542847051917906862763)
      ·
        refine ⟨17528314270577876860294145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11685542847051917906862763 17528314270577876860294145)
        ·
          refine ⟨13146235702933407645220609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17528314270577876860294145 13146235702933407645220609)
          ·
            refine ⟨9859676777200055733915457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13146235702933407645220609 9859676777200055733915457)
            ·
              refine ⟨7394757582900041800436593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9859676777200055733915457 7394757582900041800436593)
              ·
                refine ⟨5546068187175031350327445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7394757582900041800436593 5546068187175031350327445)
                ·
                  refine ⟨259971946273829594546599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5546068187175031350327445 259971946273829594546599)
                  ·
                    rfl

theorem cell23_4556642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_4556642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556642 prefixEnd_4556642 := by exact prefixLift 4556642
  have htrace : WordTrace (prefixWord ++ tailWord_4556642) baseStart_4556642 baseEnd_4556642 := by
    simpa [prefixWord, tailWord_4556642, baseEnd_4556642] using wordTrace_append hprefix tailTrace_4556642
  have hstable : (prefixWord ++ tailWord_4556642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556642).length < 2 ^ (prefixWord ++ tailWord_4556642).sum := by decide
  have hdescent : baseEnd_4556642 < baseStart_4556642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556645 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 3, 5, 2]
def baseStart_4556645 : Nat := 118140960795 + 4556645 * 2 ^ 59
def prefixEnd_4556645 : Nat := 4983230072969 + 3 ^ 40 * 4556645 * 2
def baseEnd_4556645 : Nat := 2339749056906429839181877

theorem tailTrace_4556645 : CollatzResearch.WordTrace tailWord_4556645 prefixEnd_4556645 2339749056906429839181877 := by
  unfold tailWord_4556645
  simp only [CollatzResearch.WordTrace]
  refine ⟨166194496577060852854407389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110796331051373901902938259 166194496577060852854407389)
  ·
    refine ⟨62322936216397819820402771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166194496577060852854407389 62322936216397819820402771)
    ·
      refine ⟨93484404324596729730604157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62322936216397819820402771 93484404324596729730604157)
      ·
        refine ⟨35056651621723773648976559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93484404324596729730604157 35056651621723773648976559)
        ·
          refine ⟨52584977432585660473464839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35056651621723773648976559 52584977432585660473464839)
          ·
            refine ⟨78877466148878490710197259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52584977432585660473464839 78877466148878490710197259)
            ·
              refine ⟨118316199223317736065295889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78877466148878490710197259 118316199223317736065295889)
              ·
                refine ⟨88737149417488302048971917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118316199223317736065295889 88737149417488302048971917)
                ·
                  refine ⟨33276431031558113268364469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88737149417488302048971917 33276431031558113268364469)
                  ·
                    refine ⟨3119665409208573118909169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33276431031558113268364469 3119665409208573118909169)
                    ·
                      refine ⟨2339749056906429839181877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3119665409208573118909169 2339749056906429839181877)
                      ·
                        rfl

theorem cell23_4556645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_4556645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556645 prefixEnd_4556645 := by exact prefixLift 4556645
  have htrace : WordTrace (prefixWord ++ tailWord_4556645) baseStart_4556645 baseEnd_4556645 := by
    simpa [prefixWord, tailWord_4556645, baseEnd_4556645] using wordTrace_append hprefix tailTrace_4556645
  have hstable : (prefixWord ++ tailWord_4556645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556645).length < 2 ^ (prefixWord ++ tailWord_4556645).sum := by decide
  have hdescent : baseEnd_4556645 < baseStart_4556645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556675 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 4]
def baseStart_4556675 : Nat := 118140960795 + 4556675 * 2 ^ 59
def prefixEnd_4556675 : Nat := 4983230072969 + 3 ^ 40 * 4556675 * 2
def baseEnd_4556675 : Nat := 2339764461326064721806739

theorem tailTrace_4556675 : CollatzResearch.WordTrace tailWord_4556675 prefixEnd_4556675 2339764461326064721806739 := by
  unfold tailWord_4556675
  simp only [CollatzResearch.WordTrace]
  refine ⟨166195590766952167977999479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110797060511301445318666319 166195590766952167977999479)
  ·
    refine ⟨249293386150428251966999219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166195590766952167977999479 249293386150428251966999219)
    ·
      refine ⟨373940079225642377950498829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249293386150428251966999219 373940079225642377950498829)
      ·
        refine ⟨140227529709615891731437061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 373940079225642377950498829 140227529709615891731437061)
        ·
          refine ⟨26292661820552979699644449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140227529709615891731437061 26292661820552979699644449)
          ·
            refine ⟨19719496365414734774733337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26292661820552979699644449 19719496365414734774733337)
            ·
              refine ⟨14789622274061051081050003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19719496365414734774733337 14789622274061051081050003)
              ·
                refine ⟨22184433411091576621575005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14789622274061051081050003 22184433411091576621575005)
                ·
                  refine ⟨8319162529159341233090627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22184433411091576621575005 8319162529159341233090627)
                  ·
                    refine ⟨12478743793739011849635941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8319162529159341233090627 12478743793739011849635941)
                    ·
                      refine ⟨2339764461326064721806739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12478743793739011849635941 2339764461326064721806739)
                      ·
                        rfl

theorem cell23_4556675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_4556675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556675 prefixEnd_4556675 := by exact prefixLift 4556675
  have htrace : WordTrace (prefixWord ++ tailWord_4556675) baseStart_4556675 baseEnd_4556675 := by
    simpa [prefixWord, tailWord_4556675, baseEnd_4556675] using wordTrace_append hprefix tailTrace_4556675
  have hstable : (prefixWord ++ tailWord_4556675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556675).length < 2 ^ (prefixWord ++ tailWord_4556675).sum := by decide
  have hdescent : baseEnd_4556675 < baseStart_4556675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556732 : List Nat := [2, 2, 2, 5, 1, 1, 1, 9]
def baseStart_4556732 : Nat := 118140960795 + 4556732 * 2 ^ 59
def prefixEnd_4556732 : Nat := 4983230072969 + 3 ^ 40 * 4556732 * 2
def baseEnd_4556732 : Nat := 86659027026791518473851

theorem tailTrace_4556732 : CollatzResearch.WordTrace tailWord_4556732 prefixEnd_4556732 86659027026791518473851 := by
  unfold tailWord_4556732
  simp only [CollatzResearch.WordTrace]
  refine ⟨83098834863872833356412225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110798446485163777808549633 83098834863872833356412225)
  ·
    refine ⟨62324126147904625017309169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83098834863872833356412225 62324126147904625017309169)
    ·
      refine ⟨46743094610928468762981877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62324126147904625017309169 46743094610928468762981877)
      ·
        refine ⟨4382165119774543946529551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46743094610928468762981877 4382165119774543946529551)
        ·
          refine ⟨6573247679661815919794327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4382165119774543946529551 6573247679661815919794327)
          ·
            refine ⟨9859871519492723879691491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6573247679661815919794327 9859871519492723879691491)
            ·
              refine ⟨14789807279239085819537237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9859871519492723879691491 14789807279239085819537237)
              ·
                refine ⟨86659027026791518473851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14789807279239085819537237 86659027026791518473851)
                ·
                  rfl

theorem cell23_4556732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 9].length) (baseStart_4556732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556732 prefixEnd_4556732 := by exact prefixLift 4556732
  have htrace : WordTrace (prefixWord ++ tailWord_4556732) baseStart_4556732 baseEnd_4556732 := by
    simpa [prefixWord, tailWord_4556732, baseEnd_4556732] using wordTrace_append hprefix tailTrace_4556732
  have hstable : (prefixWord ++ tailWord_4556732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556732).length < 2 ^ (prefixWord ++ tailWord_4556732).sum := by decide
  have hdescent : baseEnd_4556732 < baseStart_4556732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556770 : List Nat := [3, 3, 3, 1, 3, 1, 2, 1, 2, 4]
def baseStart_4556770 : Nat := 118140960795 + 4556770 * 2 ^ 59
def prefixEnd_4556770 : Nat := 4983230072969 + 3 ^ 40 * 4556770 * 2
def baseEnd_4556770 : Nat := 779937747329413950039601

theorem tailTrace_4556770 : CollatzResearch.WordTrace tailWord_4556770 prefixEnd_4556770 779937747329413950039601 := by
  unfold tailWord_4556770
  simp only [CollatzResearch.WordTrace]
  refine ⟨41549763925401999800676941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110799370467738666135138509 41549763925401999800676941)
  ·
    refine ⟨15581161472025749925253853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41549763925401999800676941 15581161472025749925253853)
    ·
      refine ⟨5842935552009656221970195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15581161472025749925253853 5842935552009656221970195)
      ·
        refine ⟨8764403328014484332955293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5842935552009656221970195 8764403328014484332955293)
        ·
          refine ⟨3286651248005431624858235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8764403328014484332955293 3286651248005431624858235)
          ·
            refine ⟨4929976872008147437287353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3286651248005431624858235 4929976872008147437287353)
            ·
              refine ⟨3697482654006110577965515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4929976872008147437287353 3697482654006110577965515)
              ·
                refine ⟨5546223981009165866948273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3697482654006110577965515 5546223981009165866948273)
                ·
                  refine ⟨4159667985756874400211205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5546223981009165866948273 4159667985756874400211205)
                  ·
                    refine ⟨779937747329413950039601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4159667985756874400211205 779937747329413950039601)
                    ·
                      rfl

theorem cell23_4556770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_4556770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556770 prefixEnd_4556770 := by exact prefixLift 4556770
  have htrace : WordTrace (prefixWord ++ tailWord_4556770) baseStart_4556770 baseEnd_4556770 := by
    simpa [prefixWord, tailWord_4556770, baseEnd_4556770] using wordTrace_append hprefix tailTrace_4556770
  have hstable : (prefixWord ++ tailWord_4556770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556770).length < 2 ^ (prefixWord ++ tailWord_4556770).sum := by decide
  have hdescent : baseEnd_4556770 < baseStart_4556770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556835 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 1, 7]
def baseStart_4556835 : Nat := 118140960795 + 4556835 * 2 ^ 59
def prefixEnd_4556835 : Nat := 4983230072969 + 3 ^ 40 * 4556835 * 2
def baseEnd_4556835 : Nat := 779948872743594698602001

theorem tailTrace_4556835 : CollatzResearch.WordTrace tailWord_4556835 prefixEnd_4556835 779948872743594698602001 := by
  unfold tailWord_4556835
  simp only [CollatzResearch.WordTrace]
  refine ⟨166201426446372515303823959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110800950964248343535882639 166201426446372515303823959)
  ·
    refine ⟨249302139669558772955735939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166201426446372515303823959 249302139669558772955735939)
    ·
      refine ⟨373953209504338159433603909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249302139669558772955735939 373953209504338159433603909)
      ·
        refine ⟨70116226782063404893800733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 373953209504338159433603909 70116226782063404893800733)
        ·
          refine ⟨26293585043273776835175275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70116226782063404893800733 26293585043273776835175275)
          ·
            refine ⟨39440377564910665252762913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26293585043273776835175275 39440377564910665252762913)
            ·
              refine ⟨29580283173682998939572185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39440377564910665252762913 29580283173682998939572185)
              ·
                refine ⟨22185212380262249204679139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29580283173682998939572185 22185212380262249204679139)
                ·
                  refine ⟨33277818570393373807018709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22185212380262249204679139 33277818570393373807018709)
                  ·
                    refine ⟨779948872743594698602001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33277818570393373807018709 779948872743594698602001)
                    ·
                      rfl

theorem cell23_4556835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 7].length) (baseStart_4556835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556835 prefixEnd_4556835 := by exact prefixLift 4556835
  have htrace : WordTrace (prefixWord ++ tailWord_4556835) baseStart_4556835 baseEnd_4556835 := by
    simpa [prefixWord, tailWord_4556835, baseEnd_4556835] using wordTrace_append hprefix tailTrace_4556835
  have hstable : (prefixWord ++ tailWord_4556835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556835).length < 2 ^ (prefixWord ++ tailWord_4556835).sum := by decide
  have hdescent : baseEnd_4556835 < baseStart_4556835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556839 : List Nat := [1, 1, 7, 1, 2, 1, 1, 2, 7]
def baseStart_4556839 : Nat := 118140960795 + 4556839 * 2 ^ 59
def prefixEnd_4556839 : Nat := 4983230072969 + 3 ^ 40 * 4556839 * 2
def baseEnd_4556839 : Nat := 259983185794822453350665

theorem tailTrace_4556839 : CollatzResearch.WordTrace tailWord_4556839 prefixEnd_4556839 259983185794822453350665 := by
  unfold tailWord_4556839
  simp only [CollatzResearch.WordTrace]
  refine ⟨166201572338358023986969571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110801048225572015991313047 166201572338358023986969571)
  ·
    refine ⟨249302358507537035980454357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166201572338358023986969571 249302358507537035980454357)
    ·
      refine ⟨5843024027520399280791899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 249302358507537035980454357 5843024027520399280791899)
      ·
        refine ⟨8764536041280598921187849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5843024027520399280791899 8764536041280598921187849)
        ·
          refine ⟨6573402030960449190890887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8764536041280598921187849 6573402030960449190890887)
          ·
            refine ⟨9860103046440673786336331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6573402030960449190890887 9860103046440673786336331)
            ·
              refine ⟨14790154569661010679504497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9860103046440673786336331 14790154569661010679504497)
              ·
                refine ⟨11092615927245758009628373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14790154569661010679504497 11092615927245758009628373)
                ·
                  refine ⟨259983185794822453350665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11092615927245758009628373 259983185794822453350665)
                  ·
                    rfl

theorem cell23_4556839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 7].length) (baseStart_4556839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556839 prefixEnd_4556839 := by exact prefixLift 4556839
  have htrace : WordTrace (prefixWord ++ tailWord_4556839) baseStart_4556839 baseEnd_4556839 := by
    simpa [prefixWord, tailWord_4556839, baseEnd_4556839] using wordTrace_append hprefix tailTrace_4556839
  have hstable : (prefixWord ++ tailWord_4556839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556839).length < 2 ^ (prefixWord ++ tailWord_4556839).sum := by decide
  have hdescent : baseEnd_4556839 < baseStart_4556839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556909 : List Nat := [1, 5, 1, 1, 2, 1, 2, 3, 2, 2, 3]
def baseStart_4556909 : Nat := 118140960795 + 4556909 * 2 ^ 59
def prefixEnd_4556909 : Nat := 4983230072969 + 3 ^ 40 * 4556909 * 2
def baseEnd_4556909 : Nat := 2339884615799216806280663

theorem tailTrace_4556909 : CollatzResearch.WordTrace tailWord_4556909 prefixEnd_4556909 2339884615799216806280663 := by
  unfold tailWord_4556909
  simp only [CollatzResearch.WordTrace]
  refine ⟨166204125448104425942017781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110802750298736283961345187 166204125448104425942017781)
  ·
    refine ⟨15581636760759789932064167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166204125448104425942017781 15581636760759789932064167)
    ·
      refine ⟨23372455141139684898096251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15581636760759789932064167 23372455141139684898096251)
      ·
        refine ⟨35058682711709527347144377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23372455141139684898096251 35058682711709527347144377)
        ·
          refine ⟨26294012033782145510358283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35058682711709527347144377 26294012033782145510358283)
          ·
            refine ⟨39441018050673218265537425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26294012033782145510358283 39441018050673218265537425)
            ·
              refine ⟨29580763538004913699153069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39441018050673218265537425 29580763538004913699153069)
              ·
                refine ⟨11092786326751842637182401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29580763538004913699153069 11092786326751842637182401)
                ·
                  refine ⟨8319589745063881977886801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11092786326751842637182401 8319589745063881977886801)
                  ·
                    refine ⟨6239692308797911483415101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8319589745063881977886801 6239692308797911483415101)
                    ·
                      refine ⟨2339884615799216806280663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6239692308797911483415101 2339884615799216806280663)
                      ·
                        rfl

theorem cell23_4556909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_4556909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556909 prefixEnd_4556909 := by exact prefixLift 4556909
  have htrace : WordTrace (prefixWord ++ tailWord_4556909) baseStart_4556909 baseEnd_4556909 := by
    simpa [prefixWord, tailWord_4556909, baseEnd_4556909] using wordTrace_append hprefix tailTrace_4556909
  have hstable : (prefixWord ++ tailWord_4556909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556909).length < 2 ^ (prefixWord ++ tailWord_4556909).sum := by decide
  have hdescent : baseEnd_4556909 < baseStart_4556909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556933 : List Nat := [1, 3, 1, 1, 5, 2, 3, 2, 1, 4]
def baseStart_4556933 : Nat := 118140960795 + 4556933 * 2 ^ 59
def prefixEnd_4556933 : Nat := 4983230072969 + 3 ^ 40 * 4556933 * 2
def baseEnd_4556933 : Nat := 779965646444974904126851

theorem tailTrace_4556933 : CollatzResearch.WordTrace tailWord_4556933 prefixEnd_4556933 779965646444974904126851 := by
  unfold tailWord_4556933
  simp only [CollatzResearch.WordTrace]
  refine ⟨166205000800017478040891453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110803333866678318693927635 166205000800017478040891453)
  ·
    refine ⟨62326875300006554265334295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166205000800017478040891453 62326875300006554265334295)
    ·
      refine ⟨93490312950009831398001443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62326875300006554265334295 93490312950009831398001443)
      ·
        refine ⟨140235469425014747097002165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93490312950009831398001443 140235469425014747097002165)
        ·
          refine ⟨13147075258595132540343953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140235469425014747097002165 13147075258595132540343953)
          ·
            refine ⟨9860306443946349405257965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13147075258595132540343953 9860306443946349405257965)
            ·
              refine ⟨3697614916479881026971737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9860306443946349405257965 3697614916479881026971737)
              ·
                refine ⟨2773211187359910770228803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3697614916479881026971737 2773211187359910770228803)
                ·
                  refine ⟨4159816781039866155343205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2773211187359910770228803 4159816781039866155343205)
                  ·
                    refine ⟨779965646444974904126851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4159816781039866155343205 779965646444974904126851)
                    ·
                      rfl

theorem cell23_4556933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 1, 4].length) (baseStart_4556933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556933 prefixEnd_4556933 := by exact prefixLift 4556933
  have htrace : WordTrace (prefixWord ++ tailWord_4556933) baseStart_4556933 baseEnd_4556933 := by
    simpa [prefixWord, tailWord_4556933, baseEnd_4556933] using wordTrace_append hprefix tailTrace_4556933
  have hstable : (prefixWord ++ tailWord_4556933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556933).length < 2 ^ (prefixWord ++ tailWord_4556933).sum := by decide
  have hdescent : baseEnd_4556933 < baseStart_4556933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556945 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 10]
def baseStart_4556945 : Nat := 118140960795 + 4556945 * 2 ^ 59
def prefixEnd_4556945 : Nat := 4983230072969 + 3 ^ 40 * 4556945 * 2
def baseEnd_4556945 : Nat := 2339903101102778665430497

theorem tailTrace_4556945 : CollatzResearch.WordTrace tailWord_4556945 prefixEnd_4556945 2339903101102778665430497 := by
  unfold tailWord_4556945
  simp only [CollatzResearch.WordTrace]
  refine ⟨166205438475974004090328289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110803625650649336060218859 166205438475974004090328289)
  ·
    refine ⟨124654078856980503067746217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166205438475974004090328289 124654078856980503067746217)
    ·
      refine ⟨93490559142735377300809663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124654078856980503067746217 93490559142735377300809663)
      ·
        refine ⟨140235838714103065951214495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93490559142735377300809663 140235838714103065951214495)
        ·
          refine ⟨210353758071154598926821743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140235838714103065951214495 210353758071154598926821743)
          ·
            refine ⟨315530637106731898390232615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210353758071154598926821743 315530637106731898390232615)
            ·
              refine ⟨473295955660097847585348923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315530637106731898390232615 473295955660097847585348923)
              ·
                refine ⟨709943933490146771378023385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 473295955660097847585348923 709943933490146771378023385)
                ·
                  refine ⟨532457950117610078533517539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 709943933490146771378023385 532457950117610078533517539)
                  ·
                    refine ⟨798686925176415117800276309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 532457950117610078533517539 798686925176415117800276309)
                    ·
                      refine ⟨2339903101102778665430497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 798686925176415117800276309 2339903101102778665430497)
                      ·
                        rfl

theorem cell23_4556945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_4556945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556945 prefixEnd_4556945 := by exact prefixLift 4556945
  have htrace : WordTrace (prefixWord ++ tailWord_4556945) baseStart_4556945 baseEnd_4556945 := by
    simpa [prefixWord, tailWord_4556945, baseEnd_4556945] using wordTrace_append hprefix tailTrace_4556945
  have hstable : (prefixWord ++ tailWord_4556945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556945).length < 2 ^ (prefixWord ++ tailWord_4556945).sum := by decide
  have hdescent : baseEnd_4556945 < baseStart_4556945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556949 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 4, 3, 2]
def baseStart_4556949 : Nat := 118140960795 + 4556949 * 2 ^ 59
def prefixEnd_4556949 : Nat := 4983230072969 + 3 ^ 40 * 4556949 * 2
def baseEnd_4556949 : Nat := 2339905155025396649780479

theorem tailTrace_4556949 : CollatzResearch.WordTrace tailWord_4556949 prefixEnd_4556949 2339905155025396649780479 := by
  unfold tailWord_4556949
  simp only [CollatzResearch.WordTrace]
  refine ⟨166205584367959512773473901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110803722911973008515649267 166205584367959512773473901)
  ·
    refine ⟨62327094137984817290052713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166205584367959512773473901 62327094137984817290052713)
    ·
      refine ⟨46745320603488612967539535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62327094137984817290052713 46745320603488612967539535)
      ·
        refine ⟨70117980905232919451309303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46745320603488612967539535 70117980905232919451309303)
        ·
          refine ⟨105176971357849379176963955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70117980905232919451309303 105176971357849379176963955)
          ·
            refine ⟨157765457036774068765445933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105176971357849379176963955 157765457036774068765445933)
            ·
              refine ⟨59162046388790275787042225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157765457036774068765445933 59162046388790275787042225)
              ·
                refine ⟨44371534791592706840281669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59162046388790275787042225 44371534791592706840281669)
                ·
                  refine ⟨8319662773423632532552813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44371534791592706840281669 8319662773423632532552813)
                  ·
                    refine ⟨3119873540033862199707305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8319662773423632532552813 3119873540033862199707305)
                    ·
                      refine ⟨2339905155025396649780479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3119873540033862199707305 2339905155025396649780479)
                      ·
                        rfl

theorem cell23_4556949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_4556949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556949 prefixEnd_4556949 := by exact prefixLift 4556949
  have htrace : WordTrace (prefixWord ++ tailWord_4556949) baseStart_4556949 baseEnd_4556949 := by
    simpa [prefixWord, tailWord_4556949, baseEnd_4556949] using wordTrace_append hprefix tailTrace_4556949
  have hstable : (prefixWord ++ tailWord_4556949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556949).length < 2 ^ (prefixWord ++ tailWord_4556949).sum := by decide
  have hdescent : baseEnd_4556949 < baseStart_4556949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556959 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 3, 5]
def baseStart_4556959 : Nat := 118140960795 + 4556959 * 2 ^ 59
def prefixEnd_4556959 : Nat := 4983230072969 + 3 ^ 40 * 4556959 * 2
def baseEnd_4556959 : Nat := 779970096610647203551811

theorem tailTrace_4556959 : CollatzResearch.WordTrace tailWord_4556959 prefixEnd_4556959 779970096610647203551811 := by
  unfold tailWord_4556959
  simp only [CollatzResearch.WordTrace]
  refine ⟨166205949097923284481337931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110803966065282189654225287 166205949097923284481337931)
  ·
    refine ⟨249308923646884926722006897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166205949097923284481337931 249308923646884926722006897)
    ·
      refine ⟨186981692735163695041505173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249308923646884926722006897 186981692735163695041505173)
      ·
        refine ⟨8764766846960798205070555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 186981692735163695041505173 8764766846960798205070555)
        ·
          refine ⟨13147150270441197307605833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8764766846960798205070555 13147150270441197307605833)
          ·
            refine ⟨9860362702830897980704375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13147150270441197307605833 9860362702830897980704375)
            ·
              refine ⟨14790544054246346971056563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9860362702830897980704375 14790544054246346971056563)
              ·
                refine ⟨22185816081369520456584845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14790544054246346971056563 22185816081369520456584845)
                ·
                  refine ⟨8319681030513570171219317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22185816081369520456584845 8319681030513570171219317)
                  ·
                    refine ⟨779970096610647203551811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8319681030513570171219317 779970096610647203551811)
                    ·
                      rfl

theorem cell23_4556959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 5].length) (baseStart_4556959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556959 prefixEnd_4556959 := by exact prefixLift 4556959
  have htrace : WordTrace (prefixWord ++ tailWord_4556959) baseStart_4556959 baseEnd_4556959 := by
    simpa [prefixWord, tailWord_4556959, baseEnd_4556959] using wordTrace_append hprefix tailTrace_4556959
  have hstable : (prefixWord ++ tailWord_4556959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556959).length < 2 ^ (prefixWord ++ tailWord_4556959).sum := by decide
  have hdescent : baseEnd_4556959 < baseStart_4556959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556980 : List Nat := [2, 5, 3, 1, 1, 1, 2, 2, 6]
def baseStart_4556980 : Nat := 118140960795 + 4556980 * 2 ^ 59
def prefixEnd_4556980 : Nat := 4983230072969 + 3 ^ 40 * 4556980 * 2
def baseEnd_4556980 : Nat := 259991230325076225388093

theorem tailTrace_4556980 : CollatzResearch.WordTrace tailWord_4556980 prefixEnd_4556980 259991230325076225388093 := by
  unfold tailWord_4556980
  simp only [CollatzResearch.WordTrace]
  refine ⟨83103357515423602533926197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110804476687231470045234929 83103357515423602533926197)
  ·
    refine ⟨7790939767070962737555581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83103357515423602533926197 7790939767070962737555581)
    ·
      refine ⟨2921602412651611026583343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7790939767070962737555581 2921602412651611026583343)
      ·
        refine ⟨4382403618977416539875015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2921602412651611026583343 4382403618977416539875015)
        ·
          refine ⟨6573605428466124809812523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4382403618977416539875015 6573605428466124809812523)
          ·
            refine ⟨9860408142699187214718785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6573605428466124809812523 9860408142699187214718785)
            ·
              refine ⟨7395306107024390411039089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9860408142699187214718785 7395306107024390411039089)
              ·
                refine ⟨5546479580268292808279317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7395306107024390411039089 5546479580268292808279317)
                ·
                  refine ⟨259991230325076225388093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5546479580268292808279317 259991230325076225388093)
                  ·
                    rfl

theorem cell23_4556980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_4556980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556980 prefixEnd_4556980 := by exact prefixLift 4556980
  have htrace : WordTrace (prefixWord ++ tailWord_4556980) baseStart_4556980 baseEnd_4556980 := by
    simpa [prefixWord, tailWord_4556980, baseEnd_4556980] using wordTrace_append hprefix tailTrace_4556980
  have hstable : (prefixWord ++ tailWord_4556980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556980).length < 2 ^ (prefixWord ++ tailWord_4556980).sum := by decide
  have hdescent : baseEnd_4556980 < baseStart_4556980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4556990 : List Nat := [4, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3]
def baseStart_4556990 : Nat := 118140960795 + 4556990 * 2 ^ 59
def prefixEnd_4556990 : Nat := 4983230072969 + 3 ^ 40 * 4556990 * 2
def baseEnd_4556990 : Nat := 2339926207732230989367791

theorem tailTrace_4556990 : CollatzResearch.WordTrace tailWord_4556990 prefixEnd_4556990 2339926207732230989367791 := by
  unfold tailWord_4556990
  simp only [CollatzResearch.WordTrace]
  refine ⟨20775884970101372096964553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110804719840540651183810949 20775884970101372096964553)
  ·
    refine ⟨15581913727576029072723415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20775884970101372096964553 15581913727576029072723415)
    ·
      refine ⟨23372870591364043609085123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15581913727576029072723415 23372870591364043609085123)
      ·
        refine ⟨35059305887046065413627685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23372870591364043609085123 35059305887046065413627685)
        ·
          refine ⟨6573619853821137265055191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35059305887046065413627685 6573619853821137265055191)
          ·
            refine ⟨9860429780731705897582787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6573619853821137265055191 9860429780731705897582787)
            ·
              refine ⟨14790644671097558846374181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9860429780731705897582787 14790644671097558846374181)
              ·
                refine ⟨2773245875830792283695159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14790644671097558846374181 2773245875830792283695159)
                ·
                  refine ⟨4159868813746188425542739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2773245875830792283695159 4159868813746188425542739)
                  ·
                    refine ⟨6239803220619282638314109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4159868813746188425542739 6239803220619282638314109)
                    ·
                      refine ⟨2339926207732230989367791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6239803220619282638314109 2339926207732230989367791)
                      ·
                        rfl

theorem cell23_4556990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_4556990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4556990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4556990 prefixEnd_4556990 := by exact prefixLift 4556990
  have htrace : WordTrace (prefixWord ++ tailWord_4556990) baseStart_4556990 baseEnd_4556990 := by
    simpa [prefixWord, tailWord_4556990, baseEnd_4556990] using wordTrace_append hprefix tailTrace_4556990
  have hstable : (prefixWord ++ tailWord_4556990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4556990).length < 2 ^ (prefixWord ++ tailWord_4556990).sum := by decide
  have hdescent : baseEnd_4556990 < baseStart_4556990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4556990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557006 : List Nat := [4, 1, 1, 1, 4, 1, 2, 3, 2, 4]
def baseStart_4557006 : Nat := 118140960795 + 4557006 * 2 ^ 59
def prefixEnd_4557006 : Nat := 4983230072969 + 3 ^ 40 * 4557006 * 2
def baseEnd_4557006 : Nat := 779978141140900975589239

theorem tailTrace_4557006 : CollatzResearch.WordTrace tailWord_4557006 prefixEnd_4557006 779978141140900975589239 := by
  unfold tailWord_4557006
  simp only [CollatzResearch.WordTrace]
  refine ⟨20775957916094126438537359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110805108885835341005532581 20775957916094126438537359)
  ·
    refine ⟨31163936874141189657806039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20775957916094126438537359 31163936874141189657806039)
    ·
      refine ⟨46745905311211784486709059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31163936874141189657806039 46745905311211784486709059)
      ·
        refine ⟨70118857966817676730063589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46745905311211784486709059 70118857966817676730063589)
        ·
          refine ⟨13147285868778314386886923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70118857966817676730063589 13147285868778314386886923)
          ·
            refine ⟨19720928803167471580330385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13147285868778314386886923 19720928803167471580330385)
            ·
              refine ⟨14790696602375603685247789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19720928803167471580330385 14790696602375603685247789)
              ·
                refine ⟨5546511225890851381967921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14790696602375603685247789 5546511225890851381967921)
                ·
                  refine ⟨4159883419418138536475941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5546511225890851381967921 4159883419418138536475941)
                  ·
                    refine ⟨779978141140900975589239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4159883419418138536475941 779978141140900975589239)
                    ·
                      rfl

theorem cell23_4557006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_4557006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557006 prefixEnd_4557006 := by exact prefixLift 4557006
  have htrace : WordTrace (prefixWord ++ tailWord_4557006) baseStart_4557006 baseEnd_4557006 := by
    simpa [prefixWord, tailWord_4557006, baseEnd_4557006] using wordTrace_append hprefix tailTrace_4557006
  have hstable : (prefixWord ++ tailWord_4557006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557006).length < 2 ^ (prefixWord ++ tailWord_4557006).sum := by decide
  have hdescent : baseEnd_4557006 < baseStart_4557006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557073 : List Nat := [1, 2, 2, 1, 1, 6, 2, 2, 1, 3, 2]
def baseStart_4557073 : Nat := 118140960795 + 4557073 * 2 ^ 59
def prefixEnd_4557073 : Nat := 4983230072969 + 3 ^ 40 * 4557073 * 2
def baseEnd_4557073 : Nat := 2339968826626554164629909

theorem tailTrace_4557073 : CollatzResearch.WordTrace tailWord_4557073 prefixEnd_4557073 2339968826626554164629909 := by
  unfold tailWord_4557073
  simp only [CollatzResearch.WordTrace]
  refine ⟨166210107019510281950987873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110806738013006854633991915 166210107019510281950987873)
  ·
    refine ⟨124657580264632711463240905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166210107019510281950987873 124657580264632711463240905)
    ·
      refine ⟨93493185198474533597430679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124657580264632711463240905 93493185198474533597430679)
      ·
        refine ⟨140239777797711800396146019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93493185198474533597430679 140239777797711800396146019)
        ·
          refine ⟨210359666696567700594219029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140239777797711800396146019 210359666696567700594219029)
          ·
            refine ⟨9860609376401610965354017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 210359666696567700594219029 9860609376401610965354017)
            ·
              refine ⟨7395457032301208224015513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9860609376401610965354017 7395457032301208224015513)
              ·
                refine ⟨5546592774225906168011635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7395457032301208224015513 5546592774225906168011635)
                ·
                  refine ⟨8319889161338859252017453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5546592774225906168011635 8319889161338859252017453)
                  ·
                    refine ⟨3119958435502072219506545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8319889161338859252017453 3119958435502072219506545)
                    ·
                      refine ⟨2339968826626554164629909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3119958435502072219506545 2339968826626554164629909)
                      ·
                        rfl

theorem cell23_4557073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 3, 2].length) (baseStart_4557073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557073 prefixEnd_4557073 := by exact prefixLift 4557073
  have htrace : WordTrace (prefixWord ++ tailWord_4557073) baseStart_4557073 baseEnd_4557073 := by
    simpa [prefixWord, tailWord_4557073, baseEnd_4557073] using wordTrace_append hprefix tailTrace_4557073
  have hstable : (prefixWord ++ tailWord_4557073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557073).length < 2 ^ (prefixWord ++ tailWord_4557073).sum := by decide
  have hdescent : baseEnd_4557073 < baseStart_4557073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557119 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 3]
def baseStart_4557119 : Nat := 118140960795 + 4557119 * 2 ^ 59
def prefixEnd_4557119 : Nat := 4983230072969 + 3 ^ 40 * 4557119 * 2
def baseEnd_4557119 : Nat := 2339992446736660984654697

theorem tailTrace_4557119 : CollatzResearch.WordTrace tailWord_4557119 prefixEnd_4557119 2339992446736660984654697 := by
  unfold tailWord_4557119
  simp only [CollatzResearch.WordTrace]
  refine ⟨166211784777343631807162411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110807856518229087871441607 166211784777343631807162411)
  ·
    refine ⟨249317677166015447710743617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166211784777343631807162411 249317677166015447710743617)
    ·
      refine ⟨186988257874511585783057713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249317677166015447710743617 186988257874511585783057713)
      ·
        refine ⟨140241193405883689337293285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186988257874511585783057713 140241193405883689337293285)
        ·
          refine ⟨26295223763603191750742491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140241193405883689337293285 26295223763603191750742491)
          ·
            refine ⟨39442835645404787626113737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26295223763603191750742491 39442835645404787626113737)
            ·
              refine ⟨29582126734053590719585303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39442835645404787626113737 29582126734053590719585303)
              ·
                refine ⟨44373190101080386079377955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29582126734053590719585303 44373190101080386079377955)
                ·
                  refine ⟨66559785151620579119066933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44373190101080386079377955 66559785151620579119066933)
                  ·
                    refine ⟨6239979857964429292412525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66559785151620579119066933 6239979857964429292412525)
                    ·
                      refine ⟨2339992446736660984654697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6239979857964429292412525 2339992446736660984654697)
                      ·
                        rfl

theorem cell23_4557119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 3].length) (baseStart_4557119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557119 prefixEnd_4557119 := by exact prefixLift 4557119
  have htrace : WordTrace (prefixWord ++ tailWord_4557119) baseStart_4557119 baseEnd_4557119 := by
    simpa [prefixWord, tailWord_4557119, baseEnd_4557119] using wordTrace_append hprefix tailTrace_4557119
  have hstable : (prefixWord ++ tailWord_4557119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557119).length < 2 ^ (prefixWord ++ tailWord_4557119).sum := by decide
  have hdescent : baseEnd_4557119 < baseStart_4557119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557124 : List Nat := [2, 3, 4, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_4557124 : Nat := 118140960795 + 4557124 * 2 ^ 59
def prefixEnd_4557124 : Nat := 4983230072969 + 3 ^ 40 * 4557124 * 2
def baseEnd_4557124 : Nat := 2339995014139933465092175

theorem tailTrace_4557124 : CollatzResearch.WordTrace tailWord_4557124 prefixEnd_4557124 2339995014139933465092175 := by
  unfold tailWord_4557124
  simp only [CollatzResearch.WordTrace]
  refine ⟨83105983571162758830547213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110807978094883678440729617 83105983571162758830547213)
  ·
    refine ⟨31164743839186034561455205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83105983571162758830547213 31164743839186034561455205)
    ·
      refine ⟨5843389469847381480272851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31164743839186034561455205 5843389469847381480272851)
      ·
        refine ⟨8765084204771072220409277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5843389469847381480272851 8765084204771072220409277)
        ·
          refine ⟨3286906576789152082653479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8765084204771072220409277 3286906576789152082653479)
          ·
            refine ⟨4930359865183728123980219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3286906576789152082653479 4930359865183728123980219)
            ·
              refine ⟨7395539797775592185970329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4930359865183728123980219 7395539797775592185970329)
              ·
                refine ⟨5546654848331694139477747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7395539797775592185970329 5546654848331694139477747)
                ·
                  refine ⟨8319982272497541209216621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5546654848331694139477747 8319982272497541209216621)
                  ·
                    refine ⟨3119993352186577953456233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8319982272497541209216621 3119993352186577953456233)
                    ·
                      refine ⟨2339995014139933465092175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3119993352186577953456233 2339995014139933465092175)
                      ·
                        rfl

theorem cell23_4557124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_4557124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557124 prefixEnd_4557124 := by exact prefixLift 4557124
  have htrace : WordTrace (prefixWord ++ tailWord_4557124) baseStart_4557124 baseEnd_4557124 := by
    simpa [prefixWord, tailWord_4557124, baseEnd_4557124] using wordTrace_append hprefix tailTrace_4557124
  have hstable : (prefixWord ++ tailWord_4557124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557124).length < 2 ^ (prefixWord ++ tailWord_4557124).sum := by decide
  have hdescent : baseEnd_4557124 < baseStart_4557124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557160 : List Nat := [2, 1, 4, 2, 2, 3, 2, 2, 5]
def baseStart_4557160 : Nat := 118140960795 + 4557160 * 2 ^ 59
def prefixEnd_4557160 : Nat := 4983230072969 + 3 ^ 40 * 4557160 * 2
def baseEnd_4557160 : Nat := 260001499938166147138001

theorem tailTrace_4557160 : CollatzResearch.WordTrace tailWord_4557160 prefixEnd_4557160 260001499938166147138001 := by
  unfold tailWord_4557160
  simp only [CollatzResearch.WordTrace]
  refine ⟨83106640085097547904702467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110808853446796730539603289 83106640085097547904702467)
  ·
    refine ⟨124659960127646321857053701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83106640085097547904702467 124659960127646321857053701)
    ·
      refine ⟨23373742523933685348197569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124659960127646321857053701 23373742523933685348197569)
      ·
        refine ⟨17530306892950264011148177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23373742523933685348197569 17530306892950264011148177)
        ·
          refine ⟨13147730169712698008361133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17530306892950264011148177 13147730169712698008361133)
          ·
            refine ⟨4930398813642261753135425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13147730169712698008361133 4930398813642261753135425)
            ·
              refine ⟨3697799110231696314851569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4930398813642261753135425 3697799110231696314851569)
              ·
                refine ⟨2773349332673772236138677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3697799110231696314851569 2773349332673772236138677)
                ·
                  refine ⟨260001499938166147138001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2773349332673772236138677 260001499938166147138001)
                  ·
                    rfl

theorem cell23_4557160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 5].length) (baseStart_4557160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557160 prefixEnd_4557160 := by exact prefixLift 4557160
  have htrace : WordTrace (prefixWord ++ tailWord_4557160) baseStart_4557160 baseEnd_4557160 := by
    simpa [prefixWord, tailWord_4557160, baseEnd_4557160] using wordTrace_append hprefix tailTrace_4557160
  have hstable : (prefixWord ++ tailWord_4557160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557160).length < 2 ^ (prefixWord ++ tailWord_4557160).sum := by decide
  have hdescent : baseEnd_4557160 < baseStart_4557160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557193 : List Nat := [1, 2, 1, 1, 6, 3, 1, 1, 2, 1, 4]
def baseStart_4557193 : Nat := 118140960795 + 4557193 * 2 ^ 59
def prefixEnd_4557193 : Nat := 4983230072969 + 3 ^ 40 * 4557193 * 2
def baseEnd_4557193 : Nat := 2340030444305093695129357

theorem tailTrace_4557193 : CollatzResearch.WordTrace tailWord_4557193 prefixEnd_4557193 2340030444305093695129357 := by
  unfold tailWord_4557193
  simp only [CollatzResearch.WordTrace]
  refine ⟨166214483779075542445356233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110809655852717028296904155 166214483779075542445356233)
  ·
    refine ⟨124660862834306656834017175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166214483779075542445356233 124660862834306656834017175)
    ·
      refine ⟨186991294251459985251025763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124660862834306656834017175 186991294251459985251025763)
      ·
        refine ⟨280486941377189977876538645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186991294251459985251025763 280486941377189977876538645)
        ·
          refine ⟨13147825377055780212962749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 280486941377189977876538645 13147825377055780212962749)
          ·
            refine ⟨4930434516395917579861031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13147825377055780212962749 4930434516395917579861031)
            ·
              refine ⟨7395651774593876369791547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4930434516395917579861031 7395651774593876369791547)
              ·
                refine ⟨11093477661890814554687321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7395651774593876369791547 11093477661890814554687321)
                ·
                  refine ⟨8320108246418110916015491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11093477661890814554687321 8320108246418110916015491)
                  ·
                    refine ⟨12480162369627166374023237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8320108246418110916015491 12480162369627166374023237)
                    ·
                      refine ⟨2340030444305093695129357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12480162369627166374023237 2340030444305093695129357)
                      ·
                        rfl

theorem cell23_4557193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 1, 4].length) (baseStart_4557193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557193 prefixEnd_4557193 := by exact prefixLift 4557193
  have htrace : WordTrace (prefixWord ++ tailWord_4557193) baseStart_4557193 baseEnd_4557193 := by
    simpa [prefixWord, tailWord_4557193, baseEnd_4557193] using wordTrace_append hprefix tailTrace_4557193
  have hstable : (prefixWord ++ tailWord_4557193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557193).length < 2 ^ (prefixWord ++ tailWord_4557193).sum := by decide
  have hdescent : baseEnd_4557193 < baseStart_4557193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557196 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 1, 4, 3]
def baseStart_4557196 : Nat := 118140960795 + 4557196 * 2 ^ 59
def prefixEnd_4557196 : Nat := 4983230072969 + 3 ^ 40 * 4557196 * 2
def baseEnd_4557196 : Nat := 2340031984747057183391843

theorem tailTrace_4557196 : CollatzResearch.WordTrace tailWord_4557196 prefixEnd_4557196 2340031984747057183391843 := by
  unfold tailWord_4557196
  simp only [CollatzResearch.WordTrace]
  refine ⟨83107296599032336978857721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110809728798709782638476961 83107296599032336978857721)
  ·
    refine ⟨62330472449274252734143291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83107296599032336978857721 62330472449274252734143291)
    ·
      refine ⟨93495708673911379101214937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62330472449274252734143291 93495708673911379101214937)
      ·
        refine ⟨70121781505433534325911203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93495708673911379101214937 70121781505433534325911203)
        ·
          refine ⟨105182672258150301488866805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70121781505433534325911203 105182672258150301488866805)
          ·
            refine ⟨9860875524201590764581263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105182672258150301488866805 9860875524201590764581263)
            ·
              refine ⟨14791313286302386146871895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9860875524201590764581263 14791313286302386146871895)
              ·
                refine ⟨22186969929453579220307843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14791313286302386146871895 22186969929453579220307843)
                ·
                  refine ⟨33280454894180368830461765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22186969929453579220307843 33280454894180368830461765)
                  ·
                    refine ⟨6240085292658819155711581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33280454894180368830461765 6240085292658819155711581)
                    ·
                      refine ⟨2340031984747057183391843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6240085292658819155711581 2340031984747057183391843)
                      ·
                        rfl

theorem cell23_4557196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_4557196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557196 prefixEnd_4557196 := by exact prefixLift 4557196
  have htrace : WordTrace (prefixWord ++ tailWord_4557196) baseStart_4557196 baseEnd_4557196 := by
    simpa [prefixWord, tailWord_4557196, baseEnd_4557196] using wordTrace_append hprefix tailTrace_4557196
  have hstable : (prefixWord ++ tailWord_4557196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557196).length < 2 ^ (prefixWord ++ tailWord_4557196).sum := by decide
  have hdescent : baseEnd_4557196 < baseStart_4557196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557216 : List Nat := [2, 1, 1, 4, 1, 3, 3, 2, 6]
def baseStart_4557216 : Nat := 118140960795 + 4557216 * 2 ^ 59
def prefixEnd_4557216 : Nat := 4983230072969 + 3 ^ 40 * 4557216 * 2
def baseEnd_4557216 : Nat := 260004694928905233904639

theorem tailTrace_4557216 : CollatzResearch.WordTrace tailWord_4557216 prefixEnd_4557216 260004694928905233904639 := by
  unfold tailWord_4557216
  simp only [CollatzResearch.WordTrace]
  refine ⟨83107661328996108686721751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110810215105328144915629001 83107661328996108686721751)
  ·
    refine ⟨124661491993494163030082627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83107661328996108686721751 124661491993494163030082627)
    ·
      refine ⟨186992237990241244545123941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124661491993494163030082627 186992237990241244545123941)
      ·
        refine ⟨35061044623170233352210739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186992237990241244545123941 35061044623170233352210739)
        ·
          refine ⟨52591566934755350028316109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35061044623170233352210739 52591566934755350028316109)
          ·
            refine ⟨19721837600533256260618541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52591566934755350028316109 19721837600533256260618541)
            ·
              refine ⟨7395689100199971097731953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19721837600533256260618541 7395689100199971097731953)
              ·
                refine ⟨5546766825149978323298965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7395689100199971097731953 5546766825149978323298965)
                ·
                  refine ⟨260004694928905233904639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5546766825149978323298965 260004694928905233904639)
                  ·
                    rfl

theorem cell23_4557216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 6].length) (baseStart_4557216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557216 prefixEnd_4557216 := by exact prefixLift 4557216
  have htrace : WordTrace (prefixWord ++ tailWord_4557216) baseStart_4557216 baseEnd_4557216 := by
    simpa [prefixWord, tailWord_4557216, baseEnd_4557216] using wordTrace_append hprefix tailTrace_4557216
  have hstable : (prefixWord ++ tailWord_4557216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557216).length < 2 ^ (prefixWord ++ tailWord_4557216).sum := by decide
  have hdescent : baseEnd_4557216 < baseStart_4557216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557219 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 6]
def baseStart_4557219 : Nat := 118140960795 + 4557219 * 2 ^ 59
def prefixEnd_4557219 : Nat := 4983230072969 + 3 ^ 40 * 4557219 * 2
def baseEnd_4557219 : Nat := 2340043794802110593404237

theorem tailTrace_4557219 : CollatzResearch.WordTrace tailWord_4557219 prefixEnd_4557219 2340043794802110593404237 := by
  unfold tailWord_4557219
  simp only [CollatzResearch.WordTrace]
  refine ⟨166215432076981348885802711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110810288051320899257201807 166215432076981348885802711)
  ·
    refine ⟨249323148115472023328704067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166215432076981348885802711 249323148115472023328704067)
    ·
      refine ⟨373984722173208034993056101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249323148115472023328704067 373984722173208034993056101)
      ·
        refine ⟨70122135407476506561198019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 373984722173208034993056101 70122135407476506561198019)
        ·
          refine ⟨105183203111214759841797029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70122135407476506561198019 105183203111214759841797029)
          ·
            refine ⟨19721850583352767470336943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105183203111214759841797029 19721850583352767470336943)
            ·
              refine ⟨29582775875029151205505415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19721850583352767470336943 29582775875029151205505415)
              ·
                refine ⟨44374163812543726808258123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29582775875029151205505415 44374163812543726808258123)
                ·
                  refine ⟨66561245718815590212387185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44374163812543726808258123 66561245718815590212387185)
                  ·
                    refine ⟨49920934289111692659290389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66561245718815590212387185 49920934289111692659290389)
                    ·
                      refine ⟨2340043794802110593404237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49920934289111692659290389 2340043794802110593404237)
                      ·
                        rfl

theorem cell23_4557219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_4557219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557219 prefixEnd_4557219 := by exact prefixLift 4557219
  have htrace : WordTrace (prefixWord ++ tailWord_4557219) baseStart_4557219 baseEnd_4557219 := by
    simpa [prefixWord, tailWord_4557219, baseEnd_4557219] using wordTrace_append hprefix tailTrace_4557219
  have hstable : (prefixWord ++ tailWord_4557219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557219).length < 2 ^ (prefixWord ++ tailWord_4557219).sum := by decide
  have hdescent : baseEnd_4557219 < baseStart_4557219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557233 : List Nat := [1, 2, 2, 4, 1, 3, 3, 1, 6]
def baseStart_4557233 : Nat := 118140960795 + 4557233 * 2 ^ 59
def prefixEnd_4557233 : Nat := 4983230072969 + 3 ^ 40 * 4557233 * 2
def baseEnd_4557233 : Nat := 260005664836808170958797

theorem tailTrace_4557233 : CollatzResearch.WordTrace tailWord_4557233 prefixEnd_4557233 260005664836808170958797 := by
  unfold tailWord_4557233
  simp only [CollatzResearch.WordTrace]
  refine ⟨166215942698930629276812353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110810628465953752851208235 166215942698930629276812353)
  ·
    refine ⟨124661957024197971957609265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166215942698930629276812353 124661957024197971957609265)
    ·
      refine ⟨93496467768148478968206949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124661957024197971957609265 93496467768148478968206949)
      ·
        refine ⟨17530587706527839806538803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93496467768148478968206949 17530587706527839806538803)
        ·
          refine ⟨26295881559791759709808205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17530587706527839806538803 26295881559791759709808205)
          ·
            refine ⟨9860955584921909891178077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26295881559791759709808205 9860955584921909891178077)
            ·
              refine ⟨3697858344345716209191779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9860955584921909891178077 3697858344345716209191779)
              ·
                refine ⟨5546787516518574313787669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3697858344345716209191779 5546787516518574313787669)
                ·
                  refine ⟨260005664836808170958797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5546787516518574313787669 260005664836808170958797)
                  ·
                    rfl

theorem cell23_4557233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 6].length) (baseStart_4557233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557233 prefixEnd_4557233 := by exact prefixLift 4557233
  have htrace : WordTrace (prefixWord ++ tailWord_4557233) baseStart_4557233 baseEnd_4557233 := by
    simpa [prefixWord, tailWord_4557233, baseEnd_4557233] using wordTrace_append hprefix tailTrace_4557233
  have hstable : (prefixWord ++ tailWord_4557233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557233).length < 2 ^ (prefixWord ++ tailWord_4557233).sum := by decide
  have hdescent : baseEnd_4557233 < baseStart_4557233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557246 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_4557246 : Nat := 118140960795 + 4557246 * 2 ^ 59
def prefixEnd_4557246 : Nat := 4983230072969 + 3 ^ 40 * 4557246 * 2
def baseEnd_4557246 : Nat := 780019219593260662588871

theorem tailTrace_4557246 : CollatzResearch.WordTrace tailWord_4557246 prefixEnd_4557246 780019219593260662588871 := by
  unfold tailWord_4557246
  simp only [CollatzResearch.WordTrace]
  refine ⟨20777052105985441562129449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110810944565255688331357061 20777052105985441562129449)
  ·
    refine ⟨15582789079489081171597087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20777052105985441562129449 15582789079489081171597087)
    ·
      refine ⟨23374183619233621757395631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15582789079489081171597087 23374183619233621757395631)
      ·
        refine ⟨35061275428850432636093447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23374183619233621757395631 35061275428850432636093447)
        ·
          refine ⟨52591913143275648954140171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35061275428850432636093447 52591913143275648954140171)
          ·
            refine ⟨78887869714913473431210257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52591913143275648954140171 78887869714913473431210257)
            ·
              refine ⟨59165902286185105073407693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78887869714913473431210257 59165902286185105073407693)
              ·
                refine ⟨22187213357319414402527885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59165902286185105073407693 22187213357319414402527885)
                ·
                  refine ⟨8320205008994780400947957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22187213357319414402527885 8320205008994780400947957)
                  ·
                    refine ⟨780019219593260662588871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8320205008994780400947957 780019219593260662588871)
                    ·
                      rfl

theorem cell23_4557246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_4557246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557246 prefixEnd_4557246 := by exact prefixLift 4557246
  have htrace : WordTrace (prefixWord ++ tailWord_4557246) baseStart_4557246 baseEnd_4557246 := by
    simpa [prefixWord, tailWord_4557246, baseEnd_4557246] using wordTrace_append hprefix tailTrace_4557246
  have hstable : (prefixWord ++ tailWord_4557246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557246).length < 2 ^ (prefixWord ++ tailWord_4557246).sum := by decide
  have hdescent : baseEnd_4557246 < baseStart_4557246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557259 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 3, 6]
def baseStart_4557259 : Nat := 118140960795 + 4557259 * 2 ^ 59
def prefixEnd_4557259 : Nat := 4983230072969 + 3 ^ 40 * 4557259 * 2
def baseEnd_4557259 : Nat := 780021444676096812301351

theorem tailTrace_4557259 : CollatzResearch.WordTrace tailWord_4557259 prefixEnd_4557259 780021444676096812301351 := by
  unfold tailWord_4557259
  simp only [CollatzResearch.WordTrace]
  refine ⟨166216890996836435717258831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110811260664557623811505887 166216890996836435717258831)
  ·
    refine ⟨249325336495254653575888247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166216890996836435717258831 249325336495254653575888247)
    ·
      refine ⟨373988004742881980363832371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249325336495254653575888247 373988004742881980363832371)
      ·
        refine ⟨560982007114322970545748557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373988004742881980363832371 560982007114322970545748557)
        ·
          refine ⟨210368252667871113954655709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 560982007114322970545748557 210368252667871113954655709)
          ·
            refine ⟨78888094750451667732995891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210368252667871113954655709 78888094750451667732995891)
            ·
              refine ⟨118332142125677501599493837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78888094750451667732995891 118332142125677501599493837)
              ·
                refine ⟨44374553297129063099810189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118332142125677501599493837 44374553297129063099810189)
                ·
                  refine ⟨16640457486423398662428821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44374553297129063099810189 16640457486423398662428821)
                  ·
                    refine ⟨780021444676096812301351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16640457486423398662428821 780021444676096812301351)
                    ·
                      rfl

theorem cell23_4557259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 6].length) (baseStart_4557259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557259 prefixEnd_4557259 := by exact prefixLift 4557259
  have htrace : WordTrace (prefixWord ++ tailWord_4557259) baseStart_4557259 baseEnd_4557259 := by
    simpa [prefixWord, tailWord_4557259, baseEnd_4557259] using wordTrace_append hprefix tailTrace_4557259
  have hstable : (prefixWord ++ tailWord_4557259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557259).length < 2 ^ (prefixWord ++ tailWord_4557259).sum := by decide
  have hdescent : baseEnd_4557259 < baseStart_4557259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557296 : List Nat := [2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 4]
def baseStart_4557296 : Nat := 118140960795 + 4557296 * 2 ^ 59
def prefixEnd_4557296 : Nat := 4983230072969 + 3 ^ 40 * 4557296 * 2
def baseEnd_4557296 : Nat := 2340083332812506792141383

theorem tailTrace_4557296 : CollatzResearch.WordTrace tailWord_4557296 prefixEnd_4557296 2340083332812506792141383 := by
  unfold tailWord_4557296
  simp only [CollatzResearch.WordTrace]
  refine ⟨83109120248851195518177871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110812160331801594024237161 83109120248851195518177871)
  ·
    refine ⟨124663680373276793277266807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83109120248851195518177871 124663680373276793277266807)
    ·
      refine ⟨186995520559915189915900211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124663680373276793277266807 186995520559915189915900211)
      ·
        refine ⟨280493280839872784873850317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186995520559915189915900211 280493280839872784873850317)
        ·
          refine ⟨105184980314952294327693869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 280493280839872784873850317 105184980314952294327693869)
          ·
            refine ⟨39444367618107110372885201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105184980314952294327693869 39444367618107110372885201)
            ·
              refine ⟨29583275713580332779663901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39444367618107110372885201 29583275713580332779663901)
              ·
                refine ⟨11093728392592624792373963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29583275713580332779663901 11093728392592624792373963)
                ·
                  refine ⟨16640592588888937188560945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11093728392592624792373963 16640592588888937188560945)
                  ·
                    refine ⟨12480444441666702891420709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16640592588888937188560945 12480444441666702891420709)
                    ·
                      refine ⟨2340083332812506792141383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12480444441666702891420709 2340083332812506792141383)
                      ·
                        rfl

theorem cell23_4557296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 4].length) (baseStart_4557296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557296 prefixEnd_4557296 := by exact prefixLift 4557296
  have htrace : WordTrace (prefixWord ++ tailWord_4557296) baseStart_4557296 baseEnd_4557296 := by
    simpa [prefixWord, tailWord_4557296, baseEnd_4557296] using wordTrace_append hprefix tailTrace_4557296
  have hstable : (prefixWord ++ tailWord_4557296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557296).length < 2 ^ (prefixWord ++ tailWord_4557296).sum := by decide
  have hdescent : baseEnd_4557296 < baseStart_4557296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557313 : List Nat := [1, 2, 4, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_4557313 : Nat := 118140960795 + 4557313 * 2 ^ 59
def prefixEnd_4557313 : Nat := 4983230072969 + 3 ^ 40 * 4557313 * 2
def baseEnd_4557313 : Nat := 2340092061983633225628805

theorem tailTrace_4557313 : CollatzResearch.WordTrace tailWord_4557313 prefixEnd_4557313 2340092061983633225628805 := by
  unfold tailWord_4557313
  simp only [CollatzResearch.WordTrace]
  refine ⟨166218860538640802939724593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110812573692427201959816395 166218860538640802939724593)
  ·
    refine ⟨124664145403980602204793445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166218860538640802939724593 124664145403980602204793445)
    ·
      refine ⟨23374527263246362913398771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124664145403980602204793445 23374527263246362913398771)
      ·
        refine ⟨35061790894869544370098157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23374527263246362913398771 35061790894869544370098157)
        ·
          refine ⟨13148171585576079138786809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35061790894869544370098157 13148171585576079138786809)
          ·
            refine ⟨9861128689182059354090107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13148171585576079138786809 9861128689182059354090107)
            ·
              refine ⟨14791693033773089031135161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9861128689182059354090107 14791693033773089031135161)
              ·
                refine ⟨11093769775329816773351371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14791693033773089031135161 11093769775329816773351371)
                ·
                  refine ⟨16640654662994725160027057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11093769775329816773351371 16640654662994725160027057)
                  ·
                    refine ⟨12480490997246043870020293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16640654662994725160027057 12480490997246043870020293)
                    ·
                      refine ⟨2340092061983633225628805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12480490997246043870020293 2340092061983633225628805)
                      ·
                        rfl

theorem cell23_4557313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_4557313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557313 prefixEnd_4557313 := by exact prefixLift 4557313
  have htrace : WordTrace (prefixWord ++ tailWord_4557313) baseStart_4557313 baseEnd_4557313 := by
    simpa [prefixWord, tailWord_4557313, baseEnd_4557313] using wordTrace_append hprefix tailTrace_4557313
  have hstable : (prefixWord ++ tailWord_4557313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557313).length < 2 ^ (prefixWord ++ tailWord_4557313).sum := by decide
  have hdescent : baseEnd_4557313 < baseStart_4557313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557336 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 2, 7]
def baseStart_4557336 : Nat := 118140960795 + 4557336 * 2 ^ 59
def prefixEnd_4557336 : Nat := 4983230072969 + 3 ^ 40 * 4557336 * 2
def baseEnd_4557336 : Nat := 780034624012895545213733

theorem tailTrace_4557336 : CollatzResearch.WordTrace tailWord_4557336 prefixEnd_4557336 780034624012895545213733 := by
  unfold tailWord_4557336
  simp only [CollatzResearch.WordTrace]
  refine ⟨83109849708778738933905931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110813132945038318578541241 83109849708778738933905931)
  ·
    refine ⟨124664774563168108400858897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83109849708778738933905931 124664774563168108400858897)
    ·
      refine ⟨93498580922376081300644173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124664774563168108400858897 93498580922376081300644173)
      ·
        refine ⟨35061967845891030487741565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93498580922376081300644173 35061967845891030487741565)
        ·
          refine ⟨13148237942209136432903087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35061967845891030487741565 13148237942209136432903087)
          ·
            refine ⟨19722356913313704649354631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13148237942209136432903087 19722356913313704649354631)
            ·
              refine ⟨29583535369970556974031947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19722356913313704649354631 29583535369970556974031947)
              ·
                refine ⟨44375303054955835461047921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29583535369970556974031947 44375303054955835461047921)
                ·
                  refine ⟨33281477291216876595785941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44375303054955835461047921 33281477291216876595785941)
                  ·
                    refine ⟨780034624012895545213733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33281477291216876595785941 780034624012895545213733)
                    ·
                      rfl

theorem cell23_4557336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_4557336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557336 prefixEnd_4557336 := by exact prefixLift 4557336
  have htrace : WordTrace (prefixWord ++ tailWord_4557336) baseStart_4557336 baseEnd_4557336 := by
    simpa [prefixWord, tailWord_4557336, baseEnd_4557336] using wordTrace_append hprefix tailTrace_4557336
  have hstable : (prefixWord ++ tailWord_4557336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557336).length < 2 ^ (prefixWord ++ tailWord_4557336).sum := by decide
  have hdescent : baseEnd_4557336 < baseStart_4557336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557346 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_4557346 : Nat := 118140960795 + 4557346 * 2 ^ 59
def prefixEnd_4557346 : Nat := 4983230072969 + 3 ^ 40 * 4557346 * 2
def baseEnd_4557346 : Nat := 2340109006845231596516153

theorem tailTrace_4557346 : CollatzResearch.WordTrace tailWord_4557346 prefixEnd_4557346 2340109006845231596516153 := by
  unfold tailWord_4557346
  simp only [CollatzResearch.WordTrace]
  refine ⟨41555016036880312393918973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110813376098347499717117261 41555016036880312393918973)
  ·
    refine ⟨15583131013830117147719615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41555016036880312393918973 15583131013830117147719615)
    ·
      refine ⟨23374696520745175721579423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15583131013830117147719615 23374696520745175721579423)
      ·
        refine ⟨35062044781117763582369135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23374696520745175721579423 35062044781117763582369135)
        ·
          refine ⟨52593067171676645373553703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35062044781117763582369135 52593067171676645373553703)
          ·
            refine ⟨78889600757514968060330555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52593067171676645373553703 78889600757514968060330555)
            ·
              refine ⟨118334401136272452090495833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78889600757514968060330555 118334401136272452090495833)
              ·
                refine ⟨88750800852204339067871875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118334401136272452090495833 88750800852204339067871875)
                ·
                  refine ⟨133126201278306508601807813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88750800852204339067871875 133126201278306508601807813)
                  ·
                    refine ⟨24961162739682470362838965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 133126201278306508601807813 24961162739682470362838965)
                    ·
                      refine ⟨2340109006845231596516153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24961162739682470362838965 2340109006845231596516153)
                      ·
                        rfl

theorem cell23_4557346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_4557346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557346 prefixEnd_4557346 := by exact prefixLift 4557346
  have htrace : WordTrace (prefixWord ++ tailWord_4557346) baseStart_4557346 baseEnd_4557346 := by
    simpa [prefixWord, tailWord_4557346, baseEnd_4557346] using wordTrace_append hprefix tailTrace_4557346
  have hstable : (prefixWord ++ tailWord_4557346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557346).length < 2 ^ (prefixWord ++ tailWord_4557346).sum := by decide
  have hdescent : baseEnd_4557346 < baseStart_4557346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557376 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 5]
def baseStart_4557376 : Nat := 118140960795 + 4557376 * 2 ^ 59
def prefixEnd_4557376 : Nat := 4983230072969 + 3 ^ 40 * 4557376 * 2
def baseEnd_4557376 : Nat := 2340124411264866479141015

theorem tailTrace_4557376 : CollatzResearch.WordTrace tailWord_4557376 prefixEnd_4557376 2340124411264866479141015 := by
  unfold tailWord_4557376
  simp only [CollatzResearch.WordTrace]
  refine ⟨83110579168706282349633991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110814105558275043132845321 83110579168706282349633991)
  ·
    refine ⟨124665868753059423524450987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83110579168706282349633991 124665868753059423524450987)
    ·
      refine ⟨186998803129589135286676481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124665868753059423524450987 186998803129589135286676481)
      ·
        refine ⟨140249102347191851465007361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186998803129589135286676481 140249102347191851465007361)
        ·
          refine ⟨105186826760393888598755521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140249102347191851465007361 105186826760393888598755521)
          ·
            refine ⟨78890120070295416449066641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105186826760393888598755521 78890120070295416449066641)
            ·
              refine ⟨59167590052721562336799981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78890120070295416449066641 59167590052721562336799981)
              ·
                refine ⟨22187846269770585876299993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59167590052721562336799981 22187846269770585876299993)
                ·
                  refine ⟨16640884702327939407224995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22187846269770585876299993 16640884702327939407224995)
                  ·
                    refine ⟨24961327053491909110837493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16640884702327939407224995 24961327053491909110837493)
                    ·
                      refine ⟨2340124411264866479141015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24961327053491909110837493 2340124411264866479141015)
                      ·
                        rfl

theorem cell23_4557376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_4557376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557376 prefixEnd_4557376 := by exact prefixLift 4557376
  have htrace : WordTrace (prefixWord ++ tailWord_4557376) baseStart_4557376 baseEnd_4557376 := by
    simpa [prefixWord, tailWord_4557376, baseEnd_4557376] using wordTrace_append hprefix tailTrace_4557376
  have hstable : (prefixWord ++ tailWord_4557376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557376).length < 2 ^ (prefixWord ++ tailWord_4557376).sum := by decide
  have hdescent : baseEnd_4557376 < baseStart_4557376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557377 : List Nat := [1, 2, 5, 1, 1, 3, 1, 3, 1, 3, 2]
def baseStart_4557377 : Nat := 118140960795 + 4557377 * 2 ^ 59
def prefixEnd_4557377 : Nat := 4983230072969 + 3 ^ 40 * 4557377 * 2
def baseEnd_4557377 : Nat := 2340124924745520975228511

theorem tailTrace_4557377 : CollatzResearch.WordTrace tailWord_4557377 prefixEnd_4557377 2340124924745520975228511 := by
  unfold tailWord_4557377
  simp only [CollatzResearch.WordTrace]
  refine ⟨166221194810408941870054385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110814129873605961246702923 166221194810408941870054385)
  ·
    refine ⟨124665896107806706402540789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166221194810408941870054385 124665896107806706402540789)
    ·
      refine ⟨11687427760106878725238199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124665896107806706402540789 11687427760106878725238199)
      ·
        refine ⟨17531141640160318087857299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11687427760106878725238199 17531141640160318087857299)
        ·
          refine ⟨26296712460240477131785949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17531141640160318087857299 26296712460240477131785949)
          ·
            refine ⟨9861267172590178924419731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26296712460240477131785949 9861267172590178924419731)
            ·
              refine ⟨14791900758885268386629597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9861267172590178924419731 14791900758885268386629597)
              ·
                refine ⟨5546962784581975644986099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14791900758885268386629597 5546962784581975644986099)
                ·
                  refine ⟨8320444176872963467479149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5546962784581975644986099 8320444176872963467479149)
                  ·
                    refine ⟨3120166566327361300304681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8320444176872963467479149 3120166566327361300304681)
                    ·
                      refine ⟨2340124924745520975228511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3120166566327361300304681 2340124924745520975228511)
                      ·
                        rfl

theorem cell23_4557377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_4557377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557377 prefixEnd_4557377 := by exact prefixLift 4557377
  have htrace : WordTrace (prefixWord ++ tailWord_4557377) baseStart_4557377 baseEnd_4557377 := by
    simpa [prefixWord, tailWord_4557377, baseEnd_4557377] using wordTrace_append hprefix tailTrace_4557377
  have hstable : (prefixWord ++ tailWord_4557377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557377).length < 2 ^ (prefixWord ++ tailWord_4557377).sum := by decide
  have hdescent : baseEnd_4557377 < baseStart_4557377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557463 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 4]
def baseStart_4557463 : Nat := 118140960795 + 4557463 * 2 ^ 59
def prefixEnd_4557463 : Nat := 4983230072969 + 3 ^ 40 * 4557463 * 2
def baseEnd_4557463 : Nat := 2340169084081807638753115

theorem tailTrace_4557463 : CollatzResearch.WordTrace tailWord_4557463 prefixEnd_4557463 2340169084081807638753115 := by
  unfold tailWord_4557463
  simp only [CollatzResearch.WordTrace]
  refine ⟨166224331488097378557685043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110816220992064919038456695 166224331488097378557685043)
  ·
    refine ⟨249336497232146067836527565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166224331488097378557685043 249336497232146067836527565)
    ·
      refine ⟨93501186462054775438697837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249336497232146067836527565 93501186462054775438697837)
      ·
        refine ⟨35062944923270540789511689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93501186462054775438697837 35062944923270540789511689)
        ·
          refine ⟨26297208692452905592133767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35062944923270540789511689 26297208692452905592133767)
          ·
            refine ⟨39445813038679358388200651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26297208692452905592133767 39445813038679358388200651)
            ·
              refine ⟨59168719558019037582300977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39445813038679358388200651 59168719558019037582300977)
              ·
                refine ⟨44376539668514278186725733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59168719558019037582300977 44376539668514278186725733)
                ·
                  refine ⟨8320601187846427160011075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44376539668514278186725733 8320601187846427160011075)
                  ·
                    refine ⟨12480901781769640740016613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8320601187846427160011075 12480901781769640740016613)
                    ·
                      refine ⟨2340169084081807638753115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12480901781769640740016613 2340169084081807638753115)
                      ·
                        rfl

theorem cell23_4557463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_4557463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557463 prefixEnd_4557463 := by exact prefixLift 4557463
  have htrace : WordTrace (prefixWord ++ tailWord_4557463) baseStart_4557463 baseEnd_4557463 := by
    simpa [prefixWord, tailWord_4557463, baseEnd_4557463] using wordTrace_append hprefix tailTrace_4557463
  have hstable : (prefixWord ++ tailWord_4557463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557463).length < 2 ^ (prefixWord ++ tailWord_4557463).sum := by decide
  have hdescent : baseEnd_4557463 < baseStart_4557463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557500 : List Nat := [2, 2, 2, 3, 1, 1, 1, 4, 2, 2, 3]
def baseStart_4557500 : Nat := 118140960795 + 4557500 * 2 ^ 59
def prefixEnd_4557500 : Nat := 4983230072969 + 3 ^ 40 * 4557500 * 2
def baseEnd_4557500 : Nat := 2340188082866023993990445

theorem tailTrace_4557500 : CollatzResearch.WordTrace tailWord_4557500 prefixEnd_4557500 2340188082866023993990445 := by
  unfold tailWord_4557500
  simp only [CollatzResearch.WordTrace]
  refine ⟨83112840494481666938390977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110817120659308889251187969 83112840494481666938390977)
  ·
    refine ⟨62334630370861250203793233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83112840494481666938390977 62334630370861250203793233)
    ·
      refine ⟨46750972778145937652844925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62334630370861250203793233 46750972778145937652844925)
      ·
        refine ⟨17531614791804726619816847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46750972778145937652844925 17531614791804726619816847)
        ·
          refine ⟨26297422187707089929725271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17531614791804726619816847 26297422187707089929725271)
          ·
            refine ⟨39446133281560634894587907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26297422187707089929725271 39446133281560634894587907)
            ·
              refine ⟨59169199922340952341881861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39446133281560634894587907 59169199922340952341881861)
              ·
                refine ⟨11094224985438928564102849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59169199922340952341881861 11094224985438928564102849)
                ·
                  refine ⟨8320668739079196423077137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11094224985438928564102849 8320668739079196423077137)
                  ·
                    refine ⟨6240501554309397317307853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8320668739079196423077137 6240501554309397317307853)
                    ·
                      refine ⟨2340188082866023993990445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6240501554309397317307853 2340188082866023993990445)
                      ·
                        rfl

theorem cell23_4557500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_4557500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557500 prefixEnd_4557500 := by exact prefixLift 4557500
  have htrace : WordTrace (prefixWord ++ tailWord_4557500) baseStart_4557500 baseEnd_4557500 := by
    simpa [prefixWord, tailWord_4557500, baseEnd_4557500] using wordTrace_append hprefix tailTrace_4557500
  have hstable : (prefixWord ++ tailWord_4557500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557500).length < 2 ^ (prefixWord ++ tailWord_4557500).sum := by decide
  have hdescent : baseEnd_4557500 < baseStart_4557500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557503 : List Nat := [1, 1, 2, 2, 2, 4, 1, 4, 6]
def baseStart_4557503 : Nat := 118140960795 + 4557503 * 2 ^ 59
def prefixEnd_4557503 : Nat := 4983230072969 + 3 ^ 40 * 4557503 * 2
def baseEnd_4557503 : Nat := 260021069256443053583659

theorem tailTrace_4557503 : CollatzResearch.WordTrace tailWord_4557503 prefixEnd_4557503 260021069256443053583659 := by
  unfold tailWord_4557503
  simp only [CollatzResearch.WordTrace]
  refine ⟨166225790407952465389141163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110817193605301643592760775 166225790407952465389141163)
  ·
    refine ⟨249338685611928698083711745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166225790407952465389141163 249338685611928698083711745)
    ·
      refine ⟨187004014208946523562783809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249338685611928698083711745 187004014208946523562783809)
      ·
        refine ⟨140253010656709892672087857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187004014208946523562783809 140253010656709892672087857)
        ·
          refine ⟨105189757992532419504065893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140253010656709892672087857 105189757992532419504065893)
          ·
            refine ⟨19723079623599828657012355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105189757992532419504065893 19723079623599828657012355)
            ·
              refine ⟨29584619435399742985518533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19723079623599828657012355 29584619435399742985518533)
              ·
                refine ⟨5547116144137451809784725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29584619435399742985518533 5547116144137451809784725)
                ·
                  refine ⟨260021069256443053583659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5547116144137451809784725 260021069256443053583659)
                  ·
                    rfl

theorem cell23_4557503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 6].length) (baseStart_4557503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557503 prefixEnd_4557503 := by exact prefixLift 4557503
  have htrace : WordTrace (prefixWord ++ tailWord_4557503) baseStart_4557503 baseEnd_4557503 := by
    simpa [prefixWord, tailWord_4557503, baseEnd_4557503] using wordTrace_append hprefix tailTrace_4557503
  have hstable : (prefixWord ++ tailWord_4557503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557503).length < 2 ^ (prefixWord ++ tailWord_4557503).sum := by decide
  have hdescent : baseEnd_4557503 < baseStart_4557503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557564 : List Nat := [2, 2, 2, 1, 3, 2, 2, 4, 1, 1, 3]
def baseStart_4557564 : Nat := 118140960795 + 4557564 * 2 ^ 59
def prefixEnd_4557564 : Nat := 4983230072969 + 3 ^ 40 * 4557564 * 2
def baseEnd_4557564 : Nat := 2340220945627911743590151

theorem tailTrace_4557564 : CollatzResearch.WordTrace tailWord_4557564 prefixEnd_4557564 2340220945627911743590151 := by
  unfold tailWord_4557564
  simp only [CollatzResearch.WordTrace]
  refine ⟨83114007630365736403555873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110818676840487648538074497 83114007630365736403555873)
  ·
    refine ⟨62335505722774302302666905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83114007630365736403555873 62335505722774302302666905)
    ·
      refine ⟨46751629292080726727000179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62335505722774302302666905 46751629292080726727000179)
      ·
        refine ⟨70127443938121090090500269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46751629292080726727000179 70127443938121090090500269)
        ·
          refine ⟨26297791476795408783937601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70127443938121090090500269 26297791476795408783937601)
          ·
            refine ⟨19723343607596556587953201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26297791476795408783937601 19723343607596556587953201)
            ·
              refine ⟨14792507705697417440964901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19723343607596556587953201 14792507705697417440964901)
              ·
                refine ⟨2773595194818265770180919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14792507705697417440964901 2773595194818265770180919)
                ·
                  refine ⟨4160392792227398655271379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2773595194818265770180919 4160392792227398655271379)
                  ·
                    refine ⟨6240589188341097982907069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4160392792227398655271379 6240589188341097982907069)
                    ·
                      refine ⟨2340220945627911743590151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6240589188341097982907069 2340220945627911743590151)
                      ·
                        rfl

theorem cell23_4557564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 1, 1, 3].length) (baseStart_4557564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557564 prefixEnd_4557564 := by exact prefixLift 4557564
  have htrace : WordTrace (prefixWord ++ tailWord_4557564) baseStart_4557564 baseEnd_4557564 := by
    simpa [prefixWord, tailWord_4557564, baseEnd_4557564] using wordTrace_append hprefix tailTrace_4557564
  have hstable : (prefixWord ++ tailWord_4557564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557564).length < 2 ^ (prefixWord ++ tailWord_4557564).sum := by decide
  have hdescent : baseEnd_4557564 < baseStart_4557564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557583 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 6]
def baseStart_4557583 : Nat := 118140960795 + 4557583 * 2 ^ 59
def prefixEnd_4557583 : Nat := 4983230072969 + 3 ^ 40 * 4557583 * 2
def baseEnd_4557583 : Nat := 2340230701760347169252563

theorem tailTrace_4557583 : CollatzResearch.WordTrace tailWord_4557583 prefixEnd_4557583 2340230701760347169252563 := by
  unfold tailWord_4557583
  simp only [CollatzResearch.WordTrace]
  refine ⟨166228708247662639052053403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110819138831775092701368935 166228708247662639052053403)
  ·
    refine ⟨249343062371493958578080105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166228708247662639052053403 249343062371493958578080105)
    ·
      refine ⟨187007296778620468933560079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249343062371493958578080105 187007296778620468933560079)
      ·
        refine ⟨280510945167930703400340119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187007296778620468933560079 280510945167930703400340119)
        ·
          refine ⟨420766417751896055100510179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280510945167930703400340119 420766417751896055100510179)
          ·
            refine ⟨631149626627844082650765269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420766417751896055100510179 631149626627844082650765269)
            ·
              refine ⟨14792569374090095687127311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 631149626627844082650765269 14792569374090095687127311)
              ·
                refine ⟨22188854061135143530690967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14792569374090095687127311 22188854061135143530690967)
                ·
                  refine ⟨33283281091702715296036451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22188854061135143530690967 33283281091702715296036451)
                  ·
                    refine ⟨49924921637554072944054677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33283281091702715296036451 49924921637554072944054677)
                    ·
                      refine ⟨2340230701760347169252563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49924921637554072944054677 2340230701760347169252563)
                      ·
                        rfl

theorem cell23_4557583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 6].length) (baseStart_4557583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557583 prefixEnd_4557583 := by exact prefixLift 4557583
  have htrace : WordTrace (prefixWord ++ tailWord_4557583) baseStart_4557583 baseEnd_4557583 := by
    simpa [prefixWord, tailWord_4557583, baseEnd_4557583] using wordTrace_append hprefix tailTrace_4557583
  have hstable : (prefixWord ++ tailWord_4557583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557583).length < 2 ^ (prefixWord ++ tailWord_4557583).sum := by decide
  have hdescent : baseEnd_4557583 < baseStart_4557583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557587 : List Nat := [1, 1, 1, 2, 1, 3, 3, 4, 3, 2, 2]
def baseStart_4557587 : Nat := 118140960795 + 4557587 * 2 ^ 59
def prefixEnd_4557587 : Nat := 4983230072969 + 3 ^ 40 * 4557587 * 2
def baseEnd_4557587 : Nat := 2340232755682965153602545

theorem tailTrace_4557587 : CollatzResearch.WordTrace tailWord_4557587 prefixEnd_4557587 2340232755682965153602545 := by
  unfold tailWord_4557587
  simp only [CollatzResearch.WordTrace]
  refine ⟨166228854139648147735199015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110819236093098765156799343 166228854139648147735199015)
  ·
    refine ⟨249343281209472221602798523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166228854139648147735199015 249343281209472221602798523)
    ·
      refine ⟨374014921814208332404197785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249343281209472221602798523 374014921814208332404197785)
      ·
        refine ⟨280511191360656249303148339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374014921814208332404197785 280511191360656249303148339)
        ·
          refine ⟨420766787040984373954722509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280511191360656249303148339 420766787040984373954722509)
          ·
            refine ⟨157787545140369140233020941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 420766787040984373954722509 157787545140369140233020941)
            ·
              refine ⟨59170329427638427587382853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157787545140369140233020941 59170329427638427587382853)
              ·
                refine ⟨11094436767682205172634285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59170329427638427587382853 11094436767682205172634285)
                ·
                  refine ⟨4160413787880826939737857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11094436767682205172634285 4160413787880826939737857)
                  ·
                    refine ⟨3120310340910620204803393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4160413787880826939737857 3120310340910620204803393)
                    ·
                      refine ⟨2340232755682965153602545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3120310340910620204803393 2340232755682965153602545)
                      ·
                        rfl

theorem cell23_4557587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 2, 2].length) (baseStart_4557587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557587 prefixEnd_4557587 := by exact prefixLift 4557587
  have htrace : WordTrace (prefixWord ++ tailWord_4557587) baseStart_4557587 baseEnd_4557587 := by
    simpa [prefixWord, tailWord_4557587, baseEnd_4557587] using wordTrace_append hprefix tailTrace_4557587
  have hstable : (prefixWord ++ tailWord_4557587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557587).length < 2 ^ (prefixWord ++ tailWord_4557587).sum := by decide
  have hdescent : baseEnd_4557587 < baseStart_4557587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557621 : List Nat := [1, 3, 3, 1, 3, 3, 1, 1, 3, 2, 2]
def baseStart_4557621 : Nat := 118140960795 + 4557621 * 2 ^ 59
def prefixEnd_4557621 : Nat := 4983230072969 + 3 ^ 40 * 4557621 * 2
def baseEnd_4557621 : Nat := 2340250214025218020577389

theorem tailTrace_4557621 : CollatzResearch.WordTrace tailWord_4557621 prefixEnd_4557621 2340250214025218020577389 := by
  unfold tailWord_4557621
  simp only [CollatzResearch.WordTrace]
  refine ⟨166230094221524971541936717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110820062814349981027957811 166230094221524971541936717)
  ·
    refine ⟨62336285333071864328226269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166230094221524971541936717 62336285333071864328226269)
    ·
      refine ⟨23376106999901949123084851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62336285333071864328226269 23376106999901949123084851)
      ·
        refine ⟨35064160499852923684627277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23376106999901949123084851 35064160499852923684627277)
        ·
          refine ⟨13149060187444846381735229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35064160499852923684627277 13149060187444846381735229)
          ·
            refine ⟨4930897570291817393150711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13149060187444846381735229 4930897570291817393150711)
            ·
              refine ⟨7396346355437726089726067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4930897570291817393150711 7396346355437726089726067)
              ·
                refine ⟨11094519533156589134589101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7396346355437726089726067 11094519533156589134589101)
                ·
                  refine ⟨4160444824933720925470913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11094519533156589134589101 4160444824933720925470913)
                  ·
                    refine ⟨3120333618700290694103185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4160444824933720925470913 3120333618700290694103185)
                    ·
                      refine ⟨2340250214025218020577389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3120333618700290694103185 2340250214025218020577389)
                      ·
                        rfl

theorem cell23_4557621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_4557621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557621 prefixEnd_4557621 := by exact prefixLift 4557621
  have htrace : WordTrace (prefixWord ++ tailWord_4557621) baseStart_4557621 baseEnd_4557621 := by
    simpa [prefixWord, tailWord_4557621, baseEnd_4557621] using wordTrace_append hprefix tailTrace_4557621
  have hstable : (prefixWord ++ tailWord_4557621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557621).length < 2 ^ (prefixWord ++ tailWord_4557621).sum := by decide
  have hdescent : baseEnd_4557621 < baseStart_4557621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557623 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 2, 7]
def baseStart_4557623 : Nat := 118140960795 + 4557623 * 2 ^ 59
def prefixEnd_4557623 : Nat := 4983230072969 + 3 ^ 40 * 4557623 * 2
def baseEnd_4557623 : Nat := 780083746995509004250793

theorem tailTrace_4557623 : CollatzResearch.WordTrace tailWord_4557623 prefixEnd_4557623 780083746995509004250793 := by
  unfold tailWord_4557623
  simp only [CollatzResearch.WordTrace]
  refine ⟨166230167167517725883509523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110820111445011817255673015 166230167167517725883509523)
  ·
    refine ⟨249345250751276588825264285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166230167167517725883509523 249345250751276588825264285)
    ·
      refine ⟨93504469031728720809474107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249345250751276588825264285 93504469031728720809474107)
      ·
        refine ⟨140256703547593081214211161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93504469031728720809474107 140256703547593081214211161)
        ·
          refine ⟨105192527660694810910658371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140256703547593081214211161 105192527660694810910658371)
          ·
            refine ⟨157788791491042216365987557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105192527660694810910658371 157788791491042216365987557)
            ·
              refine ⟨29585398404570415568622667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157788791491042216365987557 29585398404570415568622667)
              ·
                refine ⟨44378097606855623352934001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29585398404570415568622667 44378097606855623352934001)
                ·
                  refine ⟨33283573205141717514700501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44378097606855623352934001 33283573205141717514700501)
                  ·
                    refine ⟨780083746995509004250793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33283573205141717514700501 780083746995509004250793)
                    ·
                      rfl

theorem cell23_4557623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_4557623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557623 prefixEnd_4557623 := by exact prefixLift 4557623
  have htrace : WordTrace (prefixWord ++ tailWord_4557623) baseStart_4557623 baseEnd_4557623 := by
    simpa [prefixWord, tailWord_4557623, baseEnd_4557623] using wordTrace_append hprefix tailTrace_4557623
  have hstable : (prefixWord ++ tailWord_4557623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557623).length < 2 ^ (prefixWord ++ tailWord_4557623).sum := by decide
  have hdescent : baseEnd_4557623 < baseStart_4557623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557638 : List Nat := [6, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_4557638 : Nat := 118140960795 + 4557638 * 2 ^ 59
def prefixEnd_4557638 : Nat := 4983230072969 + 3 ^ 40 * 4557638 * 2
def baseEnd_4557638 : Nat := 2340258943196344454064811

theorem tailTrace_4557638 : CollatzResearch.WordTrace tailWord_4557638 prefixEnd_4557638 2340258943196344454064811 := by
  unfold tailWord_4557638
  simp only [CollatzResearch.WordTrace]
  refine ⟨5194709820701980732665799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 110820476174975588963537045 5194709820701980732665799)
  ·
    refine ⟨7792064731052971098998699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5194709820701980732665799 7792064731052971098998699)
    ·
      refine ⟨11688097096579456648498049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7792064731052971098998699 11688097096579456648498049)
      ·
        refine ⟨8766072822434592486373537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11688097096579456648498049 8766072822434592486373537)
        ·
          refine ⟨6574554616825944364780153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8766072822434592486373537 6574554616825944364780153)
          ·
            refine ⟨4930915962619458273585115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6574554616825944364780153 4930915962619458273585115)
            ·
              refine ⟨7396373943929187410377673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4930915962619458273585115 7396373943929187410377673)
              ·
                refine ⟨5547280457946890557783255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7396373943929187410377673 5547280457946890557783255)
                ·
                  refine ⟨8320920686920335836674883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5547280457946890557783255 8320920686920335836674883)
                  ·
                    refine ⟨12481381030380503755012325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8320920686920335836674883 12481381030380503755012325)
                    ·
                      refine ⟨2340258943196344454064811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12481381030380503755012325 2340258943196344454064811)
                      ·
                        rfl

theorem cell23_4557638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_4557638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557638 prefixEnd_4557638 := by exact prefixLift 4557638
  have htrace : WordTrace (prefixWord ++ tailWord_4557638) baseStart_4557638 baseEnd_4557638 := by
    simpa [prefixWord, tailWord_4557638, baseEnd_4557638] using wordTrace_append hprefix tailTrace_4557638
  have hstable : (prefixWord ++ tailWord_4557638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557638).length < 2 ^ (prefixWord ++ tailWord_4557638).sum := by decide
  have hdescent : baseEnd_4557638 < baseStart_4557638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557673 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 1, 5, 6]
def baseStart_4557673 : Nat := 118140960795 + 4557673 * 2 ^ 59
def prefixEnd_4557673 : Nat := 4983230072969 + 3 ^ 40 * 4557673 * 2
def baseEnd_4557673 : Nat := 2340276915019251817127149

theorem tailTrace_4557673 : CollatzResearch.WordTrace tailWord_4557673 prefixEnd_4557673 2340276915019251817127149 := by
  unfold tailWord_4557673
  simp only [CollatzResearch.WordTrace]
  refine ⟨166231990817336584422829673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110821327211557722948553115 166231990817336584422829673)
  ·
    refine ⟨124673993113002438317122255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166231990817336584422829673 124673993113002438317122255)
    ·
      refine ⟨187010989669503657475683383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124673993113002438317122255 187010989669503657475683383)
      ·
        refine ⟨280516484504255486213525075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187010989669503657475683383 280516484504255486213525075)
        ·
          refine ⟨420774726756383229320287613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280516484504255486213525075 420774726756383229320287613)
          ·
            refine ⟨157790522533643710995107855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 420774726756383229320287613 157790522533643710995107855)
            ·
              refine ⟨236685783800465566492661783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157790522533643710995107855 236685783800465566492661783)
              ·
                refine ⟨355028675700698349738992675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236685783800465566492661783 355028675700698349738992675)
                ·
                  refine ⟨532543013551047524608489013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 355028675700698349738992675 532543013551047524608489013)
                  ·
                    refine ⟨49925907520410705432045845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 532543013551047524608489013 49925907520410705432045845)
                    ·
                      refine ⟨2340276915019251817127149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49925907520410705432045845 2340276915019251817127149)
                      ·
                        rfl

theorem cell23_4557673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_4557673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557673 prefixEnd_4557673 := by exact prefixLift 4557673
  have htrace : WordTrace (prefixWord ++ tailWord_4557673) baseStart_4557673 baseEnd_4557673 := by
    simpa [prefixWord, tailWord_4557673, baseEnd_4557673] using wordTrace_append hprefix tailTrace_4557673
  have hstable : (prefixWord ++ tailWord_4557673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557673).length < 2 ^ (prefixWord ++ tailWord_4557673).sum := by decide
  have hdescent : baseEnd_4557673 < baseStart_4557673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557677 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 5, 4, 2]
def baseStart_4557677 : Nat := 118140960795 + 4557677 * 2 ^ 59
def prefixEnd_4557677 : Nat := 4983230072969 + 3 ^ 40 * 4557677 * 2
def baseEnd_4557677 : Nat := 2340278968941869801477131

theorem tailTrace_4557677 : CollatzResearch.WordTrace tailWord_4557677 prefixEnd_4557677 2340278968941869801477131 := by
  unfold tailWord_4557677
  simp only [CollatzResearch.WordTrace]
  refine ⟨166232136709322093105975285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110821424472881395403983523 166232136709322093105975285)
  ·
    refine ⟨15584262816498946228685183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166232136709322093105975285 15584262816498946228685183)
    ·
      refine ⟨23376394224748419343027775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15584262816498946228685183 23376394224748419343027775)
      ·
        refine ⟨35064591337122629014541663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23376394224748419343027775 35064591337122629014541663)
        ·
          refine ⟨52596887005683943521812495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35064591337122629014541663 52596887005683943521812495)
          ·
            refine ⟨78895330508525915282718743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52596887005683943521812495 78895330508525915282718743)
            ·
              refine ⟨118342995762788872924078115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78895330508525915282718743 118342995762788872924078115)
              ·
                refine ⟨177514493644183309386117173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118342995762788872924078115 177514493644183309386117173)
                ·
                  refine ⟨16641983779142185254948485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 177514493644183309386117173 16641983779142185254948485)
                  ·
                    refine ⟨3120371958589159735302841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16641983779142185254948485 3120371958589159735302841)
                    ·
                      refine ⟨2340278968941869801477131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3120371958589159735302841 2340278968941869801477131)
                      ·
                        rfl

theorem cell23_4557677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_4557677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557677 prefixEnd_4557677 := by exact prefixLift 4557677
  have htrace : WordTrace (prefixWord ++ tailWord_4557677) baseStart_4557677 baseEnd_4557677 := by
    simpa [prefixWord, tailWord_4557677, baseEnd_4557677] using wordTrace_append hprefix tailTrace_4557677
  have hstable : (prefixWord ++ tailWord_4557677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557677).length < 2 ^ (prefixWord ++ tailWord_4557677).sum := by decide
  have hdescent : baseEnd_4557677 < baseStart_4557677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557680 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 3]
def baseStart_4557680 : Nat := 118140960795 + 4557680 * 2 ^ 59
def prefixEnd_4557680 : Nat := 4983230072969 + 3 ^ 40 * 4557680 * 2
def baseEnd_4557680 : Nat := 2340280509383833289739617

theorem tailTrace_4557680 : CollatzResearch.WordTrace tailWord_4557680 prefixEnd_4557680 2340280509383833289739617 := by
  unfold tailWord_4557680
  simp only [CollatzResearch.WordTrace]
  refine ⟨83116123064155612309167247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110821497418874149745556329 83116123064155612309167247)
  ·
    refine ⟨124674184596233418463750871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83116123064155612309167247 124674184596233418463750871)
    ·
      refine ⟨187011276894350127695626307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124674184596233418463750871 187011276894350127695626307)
      ·
        refine ⟨280516915341525191543439461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187011276894350127695626307 280516915341525191543439461)
        ·
          refine ⟨52596921626535973414394899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 280516915341525191543439461 52596921626535973414394899)
          ·
            refine ⟨78895382439803960121592349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52596921626535973414394899 78895382439803960121592349)
            ·
              refine ⟨29585768414926485045597131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78895382439803960121592349 29585768414926485045597131)
              ·
                refine ⟨44378652622389727568395697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29585768414926485045597131 44378652622389727568395697)
                ·
                  refine ⟨33283989466792295676296773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44378652622389727568395697 33283989466792295676296773)
                  ·
                    refine ⟨6240748025023555439305645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33283989466792295676296773 6240748025023555439305645)
                    ·
                      refine ⟨2340280509383833289739617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6240748025023555439305645 2340280509383833289739617)
                      ·
                        rfl

theorem cell23_4557680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 3].length) (baseStart_4557680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557680 prefixEnd_4557680 := by exact prefixLift 4557680
  have htrace : WordTrace (prefixWord ++ tailWord_4557680) baseStart_4557680 baseEnd_4557680 := by
    simpa [prefixWord, tailWord_4557680, baseEnd_4557680] using wordTrace_append hprefix tailTrace_4557680
  have hstable : (prefixWord ++ tailWord_4557680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557680).length < 2 ^ (prefixWord ++ tailWord_4557680).sum := by decide
  have hdescent : baseEnd_4557680 < baseStart_4557680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557717 : List Nat := [1, 3, 2, 1, 1, 4, 1, 5, 5]
def baseStart_4557717 : Nat := 118140960795 + 4557717 * 2 ^ 59
def prefixEnd_4557717 : Nat := 4983230072969 + 3 ^ 40 * 4557717 * 2
def baseEnd_4557717 : Nat := 260033278685338849441883

theorem tailTrace_4557717 : CollatzResearch.WordTrace tailWord_4557717 prefixEnd_4557717 260033278685338849441883 := by
  unfold tailWord_4557717
  simp only [CollatzResearch.WordTrace]
  refine ⟨166233595629177179937431405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110822397086118119958287603 166233595629177179937431405)
  ·
    refine ⟨62337598360941442476536777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166233595629177179937431405 62337598360941442476536777)
    ·
      refine ⟨46753198770706081857402583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62337598360941442476536777 46753198770706081857402583)
      ·
        refine ⟨70129798156059122786103875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46753198770706081857402583 70129798156059122786103875)
        ·
          refine ⟨105194697234088684179155813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70129798156059122786103875 105194697234088684179155813)
          ·
            refine ⟨19724005731391628283591715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105194697234088684179155813 19724005731391628283591715)
            ·
              refine ⟨29586008597087442425387573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19724005731391628283591715 29586008597087442425387573)
              ·
                refine ⟨2773688305976947727380085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29586008597087442425387573 2773688305976947727380085)
                ·
                  refine ⟨260033278685338849441883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2773688305976947727380085 260033278685338849441883)
                  ·
                    rfl

theorem cell23_4557717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 5].length) (baseStart_4557717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557717 prefixEnd_4557717 := by exact prefixLift 4557717
  have htrace : WordTrace (prefixWord ++ tailWord_4557717) baseStart_4557717 baseEnd_4557717 := by
    simpa [prefixWord, tailWord_4557717, baseEnd_4557717] using wordTrace_append hprefix tailTrace_4557717
  have hstable : (prefixWord ++ tailWord_4557717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557717).length < 2 ^ (prefixWord ++ tailWord_4557717).sum := by decide
  have hdescent : baseEnd_4557717 < baseStart_4557717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557727 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 3]
def baseStart_4557727 : Nat := 118140960795 + 4557727 * 2 ^ 59
def prefixEnd_4557727 : Nat := 4983230072969 + 3 ^ 40 * 4557727 * 2
def baseEnd_4557727 : Nat := 2340304642974594605851901

theorem tailTrace_4557727 : CollatzResearch.WordTrace tailWord_4557727 prefixEnd_4557727 2340304642974594605851901 := by
  unfold tailWord_4557727
  simp only [CollatzResearch.WordTrace]
  refine ⟨166233960359140951645295435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110822640239427301096863623 166233960359140951645295435)
  ·
    refine ⟨249350940538711427467943153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166233960359140951645295435 249350940538711427467943153)
    ·
      refine ⟨187013205404033570600957365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249350940538711427467943153 187013205404033570600957365)
      ·
        refine ⟨17532488006628147243839753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 187013205404033570600957365 17532488006628147243839753)
        ·
          refine ⟨13149366004971110432879815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17532488006628147243839753 13149366004971110432879815)
          ·
            refine ⟨19724049007456665649319723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13149366004971110432879815 19724049007456665649319723)
            ·
              refine ⟨29586073511184998473979585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19724049007456665649319723 29586073511184998473979585)
              ·
                refine ⟨22189555133388748855484689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29586073511184998473979585 22189555133388748855484689)
                ·
                  refine ⟨16642166350041561641613517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22189555133388748855484689 16642166350041561641613517)
                  ·
                    refine ⟨6240812381265585615605069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16642166350041561641613517 6240812381265585615605069)
                    ·
                      refine ⟨2340304642974594605851901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6240812381265585615605069 2340304642974594605851901)
                      ·
                        rfl

theorem cell23_4557727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_4557727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557727 prefixEnd_4557727 := by exact prefixLift 4557727
  have htrace : WordTrace (prefixWord ++ tailWord_4557727) baseStart_4557727 baseEnd_4557727 := by
    simpa [prefixWord, tailWord_4557727, baseEnd_4557727] using wordTrace_append hprefix tailTrace_4557727
  have hstable : (prefixWord ++ tailWord_4557727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557727).length < 2 ^ (prefixWord ++ tailWord_4557727).sum := by decide
  have hdescent : baseEnd_4557727 < baseStart_4557727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557767 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 1, 6, 2]
def baseStart_4557767 : Nat := 118140960795 + 4557767 * 2 ^ 59
def prefixEnd_4557767 : Nat := 4983230072969 + 3 ^ 40 * 4557767 * 2
def baseEnd_4557767 : Nat := 2340325182200774449351717

theorem tailTrace_4557767 : CollatzResearch.WordTrace tailWord_4557767 prefixEnd_4557767 2340325182200774449351717 := by
  unfold tailWord_4557767
  simp only [CollatzResearch.WordTrace]
  refine ⟨166235419278996038476751555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110823612852664025651167703 166235419278996038476751555)
  ·
    refine ⟨249353128918494057715127333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166235419278996038476751555 249353128918494057715127333)
    ·
      refine ⟨46753711672217635821586375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 249353128918494057715127333 46753711672217635821586375)
      ·
        refine ⟨70130567508326453732379563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46753711672217635821586375 70130567508326453732379563)
        ·
          refine ⟨105195851262489680598569345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70130567508326453732379563 105195851262489680598569345)
          ·
            refine ⟨78896888446867260448927009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105195851262489680598569345 78896888446867260448927009)
            ·
              refine ⟨59172666335150445336695257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78896888446867260448927009 59172666335150445336695257)
              ·
                refine ⟨44379499751362834002521443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59172666335150445336695257 44379499751362834002521443)
                ·
                  refine ⟨66569249627044251003782165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44379499751362834002521443 66569249627044251003782165)
                  ·
                    refine ⟨3120433576267699265802289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66569249627044251003782165 3120433576267699265802289)
                    ·
                      refine ⟨2340325182200774449351717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3120433576267699265802289 2340325182200774449351717)
                      ·
                        rfl

theorem cell23_4557767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_4557767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557767 prefixEnd_4557767 := by exact prefixLift 4557767
  have htrace : WordTrace (prefixWord ++ tailWord_4557767) baseStart_4557767 baseEnd_4557767 := by
    simpa [prefixWord, tailWord_4557767, baseEnd_4557767] using wordTrace_append hprefix tailTrace_4557767
  have hstable : (prefixWord ++ tailWord_4557767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557767).length < 2 ^ (prefixWord ++ tailWord_4557767).sum := by decide
  have hdescent : baseEnd_4557767 < baseStart_4557767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557770 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_4557770 : Nat := 118140960795 + 4557770 * 2 ^ 59
def prefixEnd_4557770 : Nat := 4983230072969 + 3 ^ 40 * 4557770 * 2
def baseEnd_4557770 : Nat := 2340326722642737937614203

theorem tailTrace_4557770 : CollatzResearch.WordTrace tailWord_4557770 prefixEnd_4557770 2340326722642737937614203 := by
  unfold tailWord_4557770
  simp only [CollatzResearch.WordTrace]
  refine ⟨41558882174496292497277691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110823685798656779992740509 41558882174496292497277691)
  ·
    refine ⟨62338323261744438745916537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41558882174496292497277691 62338323261744438745916537)
    ·
      refine ⟨46753742446308329059437403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62338323261744438745916537 46753742446308329059437403)
      ·
        refine ⟨70130613669462493589156105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46753742446308329059437403 70130613669462493589156105)
        ·
          refine ⟨52597960252096870191867079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70130613669462493589156105 52597960252096870191867079)
          ·
            refine ⟨78896940378145305287800619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52597960252096870191867079 78896940378145305287800619)
            ·
              refine ⟨118345410567217957931700929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78896940378145305287800619 118345410567217957931700929)
              ·
                refine ⟨88759057925413468448775697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118345410567217957931700929 88759057925413468448775697)
                ·
                  refine ⟨66569293444060101336581773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88759057925413468448775697 66569293444060101336581773)
                  ·
                    refine ⟨24963485041522538001218165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66569293444060101336581773 24963485041522538001218165)
                    ·
                      refine ⟨2340326722642737937614203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24963485041522538001218165 2340326722642737937614203)
                      ·
                        rfl

theorem cell23_4557770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_4557770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557770 prefixEnd_4557770 := by exact prefixLift 4557770
  have htrace : WordTrace (prefixWord ++ tailWord_4557770) baseStart_4557770 baseEnd_4557770 := by
    simpa [prefixWord, tailWord_4557770, baseEnd_4557770] using wordTrace_append hprefix tailTrace_4557770
  have hstable : (prefixWord ++ tailWord_4557770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557770).length < 2 ^ (prefixWord ++ tailWord_4557770).sum := by decide
  have hdescent : baseEnd_4557770 < baseStart_4557770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557807 : List Nat := [1, 1, 2, 1, 4, 4, 1, 3, 6]
def baseStart_4557807 : Nat := 118140960795 + 4557807 * 2 ^ 59
def prefixEnd_4557807 : Nat := 4983230072969 + 3 ^ 40 * 4557807 * 2
def baseEnd_4557807 : Nat := 260038413491883810316837

theorem tailTrace_4557807 : CollatzResearch.WordTrace tailWord_4557807 prefixEnd_4557807 260038413491883810316837 := by
  unfold tailWord_4557807
  simp only [CollatzResearch.WordTrace]
  refine ⟨166236878198851125308207675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110824585465900750205471783 166236878198851125308207675)
  ·
    refine ⟨249355317298276687962311513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166236878198851125308207675 249355317298276687962311513)
    ·
      refine ⟨187016487973707515971733635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249355317298276687962311513 187016487973707515971733635)
      ·
        refine ⟨280524731960561273957600453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187016487973707515971733635 280524731960561273957600453)
        ·
          refine ⟨52598387242605238867050085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 280524731960561273957600453 52598387242605238867050085)
          ·
            refine ⟨9862197607988482287571891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52598387242605238867050085 9862197607988482287571891)
            ·
              refine ⟨14793296411982723431357837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9862197607988482287571891 14793296411982723431357837)
              ·
                refine ⟨5547486154493521286759189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14793296411982723431357837 5547486154493521286759189)
                ·
                  refine ⟨260038413491883810316837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5547486154493521286759189 260038413491883810316837)
                  ·
                    rfl

theorem cell23_4557807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 6].length) (baseStart_4557807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557807 prefixEnd_4557807 := by exact prefixLift 4557807
  have htrace : WordTrace (prefixWord ++ tailWord_4557807) baseStart_4557807 baseEnd_4557807 := by
    simpa [prefixWord, tailWord_4557807, baseEnd_4557807] using wordTrace_append hprefix tailTrace_4557807
  have hstable : (prefixWord ++ tailWord_4557807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557807).length < 2 ^ (prefixWord ++ tailWord_4557807).sum := by decide
  have hdescent : baseEnd_4557807 < baseStart_4557807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557867 : List Nat := [1, 1, 1, 1, 2, 1, 8, 1, 1, 6]
def baseStart_4557867 : Nat := 118140960795 + 4557867 * 2 ^ 59
def prefixEnd_4557867 : Nat := 4983230072969 + 3 ^ 40 * 4557867 * 2
def baseEnd_4557867 : Nat := 780125510088741352700419

theorem tailTrace_4557867 : CollatzResearch.WordTrace tailWord_4557867 prefixEnd_4557867 780125510088741352700419 := by
  unfold tailWord_4557867
  simp only [CollatzResearch.WordTrace]
  refine ⟨166239066578633755555391855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110826044385755837036927903 166239066578633755555391855)
  ·
    refine ⟨249358599867950633333087783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166239066578633755555391855 249358599867950633333087783)
    ·
      refine ⟨374037899801925949999631675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249358599867950633333087783 374037899801925949999631675)
      ·
        refine ⟨561056849702888924999447513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374037899801925949999631675 561056849702888924999447513)
        ·
          refine ⟨420792637277166693749585635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 561056849702888924999447513 420792637277166693749585635)
          ·
            refine ⟨631188955915750040624378453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420792637277166693749585635 631188955915750040624378453)
            ·
              refine ⟨7396745577137695788566935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 631188955915750040624378453 7396745577137695788566935)
              ·
                refine ⟨11095118365706543682850403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7396745577137695788566935 11095118365706543682850403)
                ·
                  refine ⟨16642677548559815524275605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11095118365706543682850403 16642677548559815524275605)
                  ·
                    refine ⟨780125510088741352700419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16642677548559815524275605 780125510088741352700419)
                    ·
                      rfl

theorem cell23_4557867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 6].length) (baseStart_4557867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557867 prefixEnd_4557867 := by exact prefixLift 4557867
  have htrace : WordTrace (prefixWord ++ tailWord_4557867) baseStart_4557867 baseEnd_4557867 := by
    simpa [prefixWord, tailWord_4557867, baseEnd_4557867] using wordTrace_append hprefix tailTrace_4557867
  have hstable : (prefixWord ++ tailWord_4557867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557867).length < 2 ^ (prefixWord ++ tailWord_4557867).sum := by decide
  have hdescent : baseEnd_4557867 < baseStart_4557867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557874 : List Nat := [3, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4]
def baseStart_4557874 : Nat := 118140960795 + 4557874 * 2 ^ 59
def prefixEnd_4557874 : Nat := 4983230072969 + 3 ^ 40 * 4557874 * 2
def baseEnd_4557874 : Nat := 2340380124630805530713725

theorem tailTrace_4557874 : CollatzResearch.WordTrace tailWord_4557874 prefixEnd_4557874 2340380124630805530713725 := by
  unfold tailWord_4557874
  simp only [CollatzResearch.WordTrace]
  refine ⟨41559830472402098937724169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110826214593072263833931117 41559830472402098937724169)
  ·
    refine ⟨31169872854301574203293127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41559830472402098937724169 31169872854301574203293127)
    ·
      refine ⟨46754809281452361304939691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31169872854301574203293127 46754809281452361304939691)
      ·
        refine ⟨70132213922178541957409537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46754809281452361304939691 70132213922178541957409537)
        ·
          refine ⟨52599160441633906468057153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70132213922178541957409537 52599160441633906468057153)
          ·
            refine ⟨39449370331225429851042865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52599160441633906468057153 39449370331225429851042865)
            ·
              refine ⟨29587027748419072388282149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39449370331225429851042865 29587027748419072388282149)
              ·
                refine ⟨5547567702828576072802903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29587027748419072388282149 5547567702828576072802903)
                ·
                  refine ⟨8321351554242864109204355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5547567702828576072802903 8321351554242864109204355)
                  ·
                    refine ⟨12482027331364296163806533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8321351554242864109204355 12482027331364296163806533)
                    ·
                      refine ⟨2340380124630805530713725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12482027331364296163806533 2340380124630805530713725)
                      ·
                        rfl

theorem cell23_4557874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_4557874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557874 prefixEnd_4557874 := by exact prefixLift 4557874
  have htrace : WordTrace (prefixWord ++ tailWord_4557874) baseStart_4557874 baseEnd_4557874 := by
    simpa [prefixWord, tailWord_4557874, baseEnd_4557874] using wordTrace_append hprefix tailTrace_4557874
  have hstable : (prefixWord ++ tailWord_4557874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557874).length < 2 ^ (prefixWord ++ tailWord_4557874).sum := by decide
  have hdescent : baseEnd_4557874 < baseStart_4557874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557878 : List Nat := [5, 1, 2, 1, 1, 2, 3, 1, 2, 3, 2]
def baseStart_4557878 : Nat := 118140960795 + 4557878 * 2 ^ 59
def prefixEnd_4557878 : Nat := 4983230072969 + 3 ^ 40 * 4557878 * 2
def baseEnd_4557878 : Nat := 2340382178553423515063707

theorem tailTrace_4557878 : CollatzResearch.WordTrace tailWord_4557878 prefixEnd_4557878 2340382178553423515063707 := by
  unfold tailWord_4557878
  simp only [CollatzResearch.WordTrace]
  refine ⟨10389966736349619027127643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110826311854395936289361525 10389966736349619027127643)
  ·
    refine ⟨15584950104524428540691465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10389966736349619027127643 15584950104524428540691465)
    ·
      refine ⟨11688712578393321405518599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15584950104524428540691465 11688712578393321405518599)
      ·
        refine ⟨17533068867589982108277899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11688712578393321405518599 17533068867589982108277899)
        ·
          refine ⟨26299603301384973162416849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17533068867589982108277899 26299603301384973162416849)
          ·
            refine ⟨19724702476038729871812637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26299603301384973162416849 19724702476038729871812637)
            ·
              refine ⟨7396763428514523701929739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19724702476038729871812637 7396763428514523701929739)
              ·
                refine ⟨11095145142771785552894609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7396763428514523701929739 11095145142771785552894609)
                ·
                  refine ⟨8321358857078839164670957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11095145142771785552894609 8321358857078839164670957)
                  ·
                    refine ⟨3120509571404564686751609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8321358857078839164670957 3120509571404564686751609)
                    ·
                      refine ⟨2340382178553423515063707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3120509571404564686751609 2340382178553423515063707)
                      ·
                        rfl

theorem cell23_4557878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_4557878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557878 prefixEnd_4557878 := by exact prefixLift 4557878
  have htrace : WordTrace (prefixWord ++ tailWord_4557878) baseStart_4557878 baseEnd_4557878 := by
    simpa [prefixWord, tailWord_4557878, baseEnd_4557878] using wordTrace_append hprefix tailTrace_4557878
  have hstable : (prefixWord ++ tailWord_4557878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557878).length < 2 ^ (prefixWord ++ tailWord_4557878).sum := by decide
  have hdescent : baseEnd_4557878 < baseStart_4557878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557901 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_4557901 : Nat := 118140960795 + 4557901 * 2 ^ 59
def prefixEnd_4557901 : Nat := 4983230072969 + 3 ^ 40 * 4557901 * 2
def baseEnd_4557901 : Nat := 780131329536158975025367

theorem tailTrace_4557901 : CollatzResearch.WordTrace tailWord_4557901 prefixEnd_4557901 780131329536158975025367 := by
  unfold tailWord_4557901
  simp only [CollatzResearch.WordTrace]
  refine ⟨166240306660510579362129557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110826871107007052908086371 166240306660510579362129557)
  ·
    refine ⟨7792514374711433407599823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 166240306660510579362129557 7792514374711433407599823)
    ·
      refine ⟨11688771562067150111399735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7792514374711433407599823 11688771562067150111399735)
      ·
        refine ⟨17533157343100725167099603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11688771562067150111399735 17533157343100725167099603)
        ·
          refine ⟨26299736014651087750649405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17533157343100725167099603 26299736014651087750649405)
          ·
            refine ⟨9862401005494157906493527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26299736014651087750649405 9862401005494157906493527)
            ·
              refine ⟨14793601508241236859740291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9862401005494157906493527 14793601508241236859740291)
              ·
                refine ⟨22190402262361855289610437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14793601508241236859740291 22190402262361855289610437)
                ·
                  refine ⟨4160700424192847866801957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22190402262361855289610437 4160700424192847866801957)
                  ·
                    refine ⟨780131329536158975025367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4160700424192847866801957 780131329536158975025367)
                    ·
                      rfl

theorem cell23_4557901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_4557901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557901 prefixEnd_4557901 := by exact prefixLift 4557901
  have htrace : WordTrace (prefixWord ++ tailWord_4557901) baseStart_4557901 baseEnd_4557901 := by
    simpa [prefixWord, tailWord_4557901, baseEnd_4557901] using wordTrace_append hprefix tailTrace_4557901
  have hstable : (prefixWord ++ tailWord_4557901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557901).length < 2 ^ (prefixWord ++ tailWord_4557901).sum := by decide
  have hdescent : baseEnd_4557901 < baseStart_4557901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557907 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 3]
def baseStart_4557907 : Nat := 118140960795 + 4557907 * 2 ^ 59
def prefixEnd_4557907 : Nat := 4983230072969 + 3 ^ 40 * 4557907 * 2
def baseEnd_4557907 : Nat := 2340397069492403901601073

theorem tailTrace_4557907 : CollatzResearch.WordTrace tailWord_4557907 prefixEnd_4557907 2340397069492403901601073 := by
  unfold tailWord_4557907
  simp only [CollatzResearch.WordTrace]
  refine ⟨166240525498488842386847975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110827016998992561591231983 166240525498488842386847975)
  ·
    refine ⟨249360788247733263580271963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166240525498488842386847975 249360788247733263580271963)
    ·
      refine ⟨374041182371599895370407945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249360788247733263580271963 374041182371599895370407945)
      ·
        refine ⟨280530886778699921527805959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374041182371599895370407945 280530886778699921527805959)
        ·
          refine ⟨420796330168049882291708939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280530886778699921527805959 420796330168049882291708939)
          ·
            refine ⟨631194495252074823437563409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420796330168049882291708939 631194495252074823437563409)
            ·
              refine ⟨473395871439056117578172557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 631194495252074823437563409 473395871439056117578172557)
              ·
                refine ⟨177523451789646044091814709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 473395871439056117578172557 177523451789646044091814709)
                ·
                  refine ⟨16642823605279316633607629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 177523451789646044091814709 16642823605279316633607629)
                  ·
                    refine ⟨6241058851979743737602861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16642823605279316633607629 6241058851979743737602861)
                    ·
                      refine ⟨2340397069492403901601073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6241058851979743737602861 2340397069492403901601073)
                      ·
                        rfl

theorem cell23_4557907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 3].length) (baseStart_4557907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557907 prefixEnd_4557907 := by exact prefixLift 4557907
  have htrace : WordTrace (prefixWord ++ tailWord_4557907) baseStart_4557907 baseEnd_4557907 := by
    simpa [prefixWord, tailWord_4557907, baseEnd_4557907] using wordTrace_append hprefix tailTrace_4557907
  have hstable : (prefixWord ++ tailWord_4557907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557907).length < 2 ^ (prefixWord ++ tailWord_4557907).sum := by decide
  have hdescent : baseEnd_4557907 < baseStart_4557907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557918 : List Nat := [4, 4, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_4557918 : Nat := 118140960795 + 4557918 * 2 ^ 59
def prefixEnd_4557918 : Nat := 4983230072969 + 3 ^ 40 * 4557918 * 2
def baseEnd_4557918 : Nat := 780134239259867786187841

theorem tailTrace_4557918 : CollatzResearch.WordTrace tailWord_4557918 prefixEnd_4557918 780134239259867786187841 := by
  unfold tailWord_4557918
  simp only [CollatzResearch.WordTrace]
  refine ⟨20780115837681123908187301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110827284467632660843665605 20780115837681123908187301)
  ·
    refine ⟨3896271719565210732785119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20780115837681123908187301 3896271719565210732785119)
    ·
      refine ⟨5844407579347816099177679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3896271719565210732785119 5844407579347816099177679)
      ·
        refine ⟨8766611369021724148766519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5844407579347816099177679 8766611369021724148766519)
        ·
          refine ⟨13149917053532586223149779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8766611369021724148766519 13149917053532586223149779)
          ·
            refine ⟨19724875580298879334724669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13149917053532586223149779 19724875580298879334724669)
            ·
              refine ⟨7396828342612079750521751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19724875580298879334724669 7396828342612079750521751)
              ·
                refine ⟨11095242513918119625782627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7396828342612079750521751 11095242513918119625782627)
                ·
                  refine ⟨16642863770877179438673941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11095242513918119625782627 16642863770877179438673941)
                  ·
                    refine ⟨780134239259867786187841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16642863770877179438673941 780134239259867786187841)
                    ·
                      rfl

theorem cell23_4557918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_4557918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557918 prefixEnd_4557918 := by exact prefixLift 4557918
  have htrace : WordTrace (prefixWord ++ tailWord_4557918) baseStart_4557918 baseEnd_4557918 := by
    simpa [prefixWord, tailWord_4557918, baseEnd_4557918] using wordTrace_append hprefix tailTrace_4557918
  have hstable : (prefixWord ++ tailWord_4557918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557918).length < 2 ^ (prefixWord ++ tailWord_4557918).sum := by decide
  have hdescent : baseEnd_4557918 < baseStart_4557918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557975 : List Nat := [1, 1, 3, 3, 3, 3, 2, 1, 2, 1, 3]
def baseStart_4557975 : Nat := 118140960795 + 4557975 * 2 ^ 59
def prefixEnd_4557975 : Nat := 4983230072969 + 3 ^ 40 * 4557975 * 2
def baseEnd_4557975 : Nat := 2340431986176909635550761

theorem tailTrace_4557975 : CollatzResearch.WordTrace tailWord_4557975 prefixEnd_4557975 2340431986176909635550761 := by
  unfold tailWord_4557975
  simp only [CollatzResearch.WordTrace]
  refine ⟨166243005662242490000323379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110828670441494993333548919 166243005662242490000323379)
  ·
    refine ⟨249364508493363735000485069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166243005662242490000323379 249364508493363735000485069)
    ·
      refine ⟨93511690685011400625181901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249364508493363735000485069 93511690685011400625181901)
      ·
        refine ⟨35066884006879275234443213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93511690685011400625181901 35066884006879275234443213)
        ·
          refine ⟨13150081502579728212916205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35066884006879275234443213 13150081502579728212916205)
          ·
            refine ⟨4931280563467398079843577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13150081502579728212916205 4931280563467398079843577)
            ·
              refine ⟨3698460422600548559882683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4931280563467398079843577 3698460422600548559882683)
              ·
                refine ⟨5547690633900822839824025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3698460422600548559882683 5547690633900822839824025)
                ·
                  refine ⟨4160767975425617129868019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5547690633900822839824025 4160767975425617129868019)
                  ·
                    refine ⟨6241151963138425694802029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4160767975425617129868019 6241151963138425694802029)
                    ·
                      refine ⟨2340431986176909635550761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6241151963138425694802029 2340431986176909635550761)
                      ·
                        rfl

theorem cell23_4557975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_4557975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557975 prefixEnd_4557975 := by exact prefixLift 4557975
  have htrace : WordTrace (prefixWord ++ tailWord_4557975) baseStart_4557975 baseEnd_4557975 := by
    simpa [prefixWord, tailWord_4557975, baseEnd_4557975] using wordTrace_append hprefix tailTrace_4557975
  have hstable : (prefixWord ++ tailWord_4557975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557975).length < 2 ^ (prefixWord ++ tailWord_4557975).sum := by decide
  have hdescent : baseEnd_4557975 < baseStart_4557975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557981 : List Nat := [1, 4, 2, 1, 1, 2, 2, 3, 1, 4, 2]
def baseStart_4557981 : Nat := 118140960795 + 4557981 * 2 ^ 59
def prefixEnd_4557981 : Nat := 4983230072969 + 3 ^ 40 * 4557981 * 2
def baseEnd_4557981 : Nat := 2340435067060836612075733

theorem tailTrace_4557981 : CollatzResearch.WordTrace tailWord_4557981 prefixEnd_4557981 2340435067060836612075733 := by
  unfold tailWord_4557981
  simp only [CollatzResearch.WordTrace]
  refine ⟨166243224500220753025041797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110828816333480502016694531 166243224500220753025041797)
  ·
    refine ⟨31170604593791391192195337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166243224500220753025041797 31170604593791391192195337)
    ·
      refine ⟨23377953445343543394146503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31170604593791391192195337 23377953445343543394146503)
      ·
        refine ⟨35066930168015315091219755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23377953445343543394146503 35066930168015315091219755)
        ·
          refine ⟨52600395252022972636829633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35066930168015315091219755 52600395252022972636829633)
          ·
            refine ⟨39450296439017229477622225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52600395252022972636829633 39450296439017229477622225)
            ·
              refine ⟨29587722329262922108216669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39450296439017229477622225 29587722329262922108216669)
              ·
                refine ⟨11095395873473595790581251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29587722329262922108216669 11095395873473595790581251)
                ·
                  refine ⟨16643093810210393685871877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11095395873473595790581251 16643093810210393685871877)
                  ·
                    refine ⟨3120580089414448816100977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16643093810210393685871877 3120580089414448816100977)
                    ·
                      refine ⟨2340435067060836612075733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3120580089414448816100977 2340435067060836612075733)
                      ·
                        rfl

theorem cell23_4557981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_4557981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557981 prefixEnd_4557981 := by exact prefixLift 4557981
  have htrace : WordTrace (prefixWord ++ tailWord_4557981) baseStart_4557981 baseEnd_4557981 := by
    simpa [prefixWord, tailWord_4557981, baseEnd_4557981] using wordTrace_append hprefix tailTrace_4557981
  have hstable : (prefixWord ++ tailWord_4557981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557981).length < 2 ^ (prefixWord ++ tailWord_4557981).sum := by decide
  have hdescent : baseEnd_4557981 < baseStart_4557981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4557987 : List Nat := [1, 1, 1, 4, 1, 1, 1, 6, 7]
def baseStart_4557987 : Nat := 118140960795 + 4557987 * 2 ^ 59
def prefixEnd_4557987 : Nat := 4983230072969 + 3 ^ 40 * 4557987 * 2
def baseEnd_4557987 : Nat := 260048683104973732066745

theorem tailTrace_4557987 : CollatzResearch.WordTrace tailWord_4557987 prefixEnd_4557987 260048683104973732066745 := by
  unfold tailWord_4557987
  simp only [CollatzResearch.WordTrace]
  refine ⟨166243443338199016049760215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110828962225466010699840143 166243443338199016049760215)
  ·
    refine ⟨249365165007298524074640323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166243443338199016049760215 249365165007298524074640323)
    ·
      refine ⟨374047747510947786111960485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249365165007298524074640323 374047747510947786111960485)
      ·
        refine ⟨70133952658302709895992591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 374047747510947786111960485 70133952658302709895992591)
        ·
          refine ⟨105200928987454064843988887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70133952658302709895992591 105200928987454064843988887)
          ·
            refine ⟨157801393481181097265983331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105200928987454064843988887 157801393481181097265983331)
            ·
              refine ⟨236702090221771645898974997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157801393481181097265983331 236702090221771645898974997)
              ·
                refine ⟨11095410479145545901514453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 236702090221771645898974997 11095410479145545901514453)
                ·
                  refine ⟨260048683104973732066745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11095410479145545901514453 260048683104973732066745)
                  ·
                    rfl

theorem cell23_4557987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 7].length) (baseStart_4557987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4557987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4557987 prefixEnd_4557987 := by exact prefixLift 4557987
  have htrace : WordTrace (prefixWord ++ tailWord_4557987) baseStart_4557987 baseEnd_4557987 := by
    simpa [prefixWord, tailWord_4557987, baseEnd_4557987] using wordTrace_append hprefix tailTrace_4557987
  have hstable : (prefixWord ++ tailWord_4557987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4557987).length < 2 ^ (prefixWord ++ tailWord_4557987).sum := by decide
  have hdescent : baseEnd_4557987 < baseStart_4557987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4557987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558027 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 7]
def baseStart_4558027 : Nat := 118140960795 + 4558027 * 2 ^ 59
def prefixEnd_4558027 : Nat := 4983230072969 + 3 ^ 40 * 4558027 * 2
def baseEnd_4558027 : Nat := 2340458687170943432100521

theorem tailTrace_4558027 : CollatzResearch.WordTrace tailWord_4558027 prefixEnd_4558027 2340458687170943432100521 := by
  unfold tailWord_4558027
  simp only [CollatzResearch.WordTrace]
  refine ⟨166244902258054102881216335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110829934838702735254144223 166244902258054102881216335)
  ·
    refine ⟨249367353387081154321824503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166244902258054102881216335 249367353387081154321824503)
    ·
      refine ⟨374051030080621731482736755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249367353387081154321824503 374051030080621731482736755)
      ·
        refine ⟨561076545120932597224105133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374051030080621731482736755 561076545120932597224105133)
        ·
          refine ⟨210403704420349723959039425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 561076545120932597224105133 210403704420349723959039425)
          ·
            refine ⟨157802778315262292969279569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210403704420349723959039425 157802778315262292969279569)
            ·
              refine ⟨118352083736446719726959677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157802778315262292969279569 118352083736446719726959677)
              ·
                refine ⟨44382031401167519897609879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118352083736446719726959677 44382031401167519897609879)
                ·
                  refine ⟨66573047101751279846414819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44382031401167519897609879 66573047101751279846414819)
                  ·
                    refine ⟨99859570652626919769622229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66573047101751279846414819 99859570652626919769622229)
                    ·
                      refine ⟨2340458687170943432100521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99859570652626919769622229 2340458687170943432100521)
                      ·
                        rfl

theorem cell23_4558027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 7].length) (baseStart_4558027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558027 prefixEnd_4558027 := by exact prefixLift 4558027
  have htrace : WordTrace (prefixWord ++ tailWord_4558027) baseStart_4558027 baseEnd_4558027 := by
    simpa [prefixWord, tailWord_4558027, baseEnd_4558027] using wordTrace_append hprefix tailTrace_4558027
  have hstable : (prefixWord ++ tailWord_4558027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558027).length < 2 ^ (prefixWord ++ tailWord_4558027).sum := by decide
  have hdescent : baseEnd_4558027 < baseStart_4558027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558034 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 1, 7]
def baseStart_4558034 : Nat := 118140960795 + 4558034 * 2 ^ 59
def prefixEnd_4558034 : Nat := 4983230072969 + 3 ^ 40 * 4558034 * 2
def baseEnd_4558034 : Nat := 780154093845174968237663

theorem tailTrace_4558034 : CollatzResearch.WordTrace tailWord_4558034 prefixEnd_4558034 780154093845174968237663 := by
  unfold tailWord_4558034
  simp only [CollatzResearch.WordTrace]
  refine ⟨41561289392257185769180289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110830105046019162051147437 41561289392257185769180289)
  ·
    refine ⟨31170967044192889326885217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41561289392257185769180289 31170967044192889326885217)
    ·
      refine ⟨23378225283144666995163913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31170967044192889326885217 23378225283144666995163913)
      ·
        refine ⟨17533668962358500246372935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23378225283144666995163913 17533668962358500246372935)
        ·
          refine ⟨26300503443537750369559403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17533668962358500246372935 26300503443537750369559403)
          ·
            refine ⟨39450755165306625554339105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26300503443537750369559403 39450755165306625554339105)
            ·
              refine ⟨29588066373979969165754329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39450755165306625554339105 29588066373979969165754329)
              ·
                refine ⟨22191049780484976874315747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29588066373979969165754329 22191049780484976874315747)
                ·
                  refine ⟨33286574670727465311473621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22191049780484976874315747 33286574670727465311473621)
                  ·
                    refine ⟨780154093845174968237663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33286574670727465311473621 780154093845174968237663)
                    ·
                      rfl

theorem cell23_4558034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_4558034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558034 prefixEnd_4558034 := by exact prefixLift 4558034
  have htrace : WordTrace (prefixWord ++ tailWord_4558034) baseStart_4558034 baseEnd_4558034 := by
    simpa [prefixWord, tailWord_4558034, baseEnd_4558034] using wordTrace_append hprefix tailTrace_4558034
  have hstable : (prefixWord ++ tailWord_4558034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558034).length < 2 ^ (prefixWord ++ tailWord_4558034).sum := by decide
  have hdescent : baseEnd_4558034 < baseStart_4558034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558038 : List Nat := [5, 2, 1, 2, 2, 1, 1, 2, 7]
def baseStart_4558038 : Nat := 118140960795 + 4558038 * 2 ^ 59
def prefixEnd_4558038 : Nat := 4983230072969 + 3 ^ 40 * 4558038 * 2
def baseEnd_4558038 : Nat := 260051592828682543229219

theorem tailTrace_4558038 : CollatzResearch.WordTrace tailWord_4558038 prefixEnd_4558038 260051592828682543229219 := by
  unfold tailWord_4558038
  simp only [CollatzResearch.WordTrace]
  refine ⟨10390331466313390734991673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110830202307342834506577845 10390331466313390734991673)
  ·
    refine ⟨7792748599735043051243755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10390331466313390734991673 7792748599735043051243755)
    ·
      refine ⟨11689122899602564576865633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7792748599735043051243755 11689122899602564576865633)
      ·
        refine ⟨8766842174701923432649225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11689122899602564576865633 8766842174701923432649225)
        ·
          refine ⟨6575131631026442574486919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8766842174701923432649225 6575131631026442574486919)
          ·
            refine ⟨9862697446539663861730379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6575131631026442574486919 9862697446539663861730379)
            ·
              refine ⟨14794046169809495792595569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9862697446539663861730379 14794046169809495792595569)
              ·
                refine ⟨11095534627357121844446677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14794046169809495792595569 11095534627357121844446677)
                ·
                  refine ⟨260051592828682543229219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11095534627357121844446677 260051592828682543229219)
                  ·
                    rfl

theorem cell23_4558038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_4558038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558038 prefixEnd_4558038 := by exact prefixLift 4558038
  have htrace : WordTrace (prefixWord ++ tailWord_4558038) baseStart_4558038 baseEnd_4558038 := by
    simpa [prefixWord, tailWord_4558038, baseEnd_4558038] using wordTrace_append hprefix tailTrace_4558038
  have hstable : (prefixWord ++ tailWord_4558038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558038).length < 2 ^ (prefixWord ++ tailWord_4558038).sum := by decide
  have hdescent : baseEnd_4558038 < baseStart_4558038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558057 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 9]
def baseStart_4558057 : Nat := 118140960795 + 4558057 * 2 ^ 59
def prefixEnd_4558057 : Nat := 4983230072969 + 3 ^ 40 * 4558057 * 2
def baseEnd_4558057 : Nat := 2340474091590578314725383

theorem tailTrace_4558057 : CollatzResearch.WordTrace tailWord_4558057 prefixEnd_4558057 2340474091590578314725383 := by
  unfold tailWord_4558057
  simp only [CollatzResearch.WordTrace]
  refine ⟨166245996447945418004808425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110830664298630278669872283 166245996447945418004808425)
  ·
    refine ⟨124684497335959063503606319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166245996447945418004808425 124684497335959063503606319)
    ·
      refine ⟨187026746003938595255409479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124684497335959063503606319 187026746003938595255409479)
      ·
        refine ⟨280540119005907892883114219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187026746003938595255409479 280540119005907892883114219)
        ·
          refine ⟨420810178508861839324671329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280540119005907892883114219 420810178508861839324671329)
          ·
            refine ⟨315607633881646379493503497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 420810178508861839324671329 315607633881646379493503497)
            ·
              refine ⟨236705725411234784620127623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315607633881646379493503497 236705725411234784620127623)
              ·
                refine ⟨355058588116852176930191435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236705725411234784620127623 355058588116852176930191435)
                ·
                  refine ⟨532587882175278265395287153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 355058588116852176930191435 532587882175278265395287153)
                  ·
                    refine ⟨399440911631458699046465365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 532587882175278265395287153 399440911631458699046465365)
                    ·
                      refine ⟨2340474091590578314725383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 399440911631458699046465365 2340474091590578314725383)
                      ·
                        rfl

theorem cell23_4558057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_4558057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558057 prefixEnd_4558057 := by exact prefixLift 4558057
  have htrace : WordTrace (prefixWord ++ tailWord_4558057) baseStart_4558057 baseEnd_4558057 := by
    simpa [prefixWord, tailWord_4558057, baseEnd_4558057] using wordTrace_append hprefix tailTrace_4558057
  have hstable : (prefixWord ++ tailWord_4558057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558057).length < 2 ^ (prefixWord ++ tailWord_4558057).sum := by decide
  have hdescent : baseEnd_4558057 < baseStart_4558057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558081 : List Nat := [1, 2, 4, 1, 1, 3, 1, 3, 3, 4]
def baseStart_4558081 : Nat := 118140960795 + 4558081 * 2 ^ 59
def prefixEnd_4558081 : Nat := 4983230072969 + 3 ^ 40 * 4558081 * 2
def baseEnd_4558081 : Nat := 780162138375428740275091

theorem tailTrace_4558081 : CollatzResearch.WordTrace tailWord_4558081 prefixEnd_4558081 780162138375428740275091 := by
  unfold tailWord_4558081
  simp only [CollatzResearch.WordTrace]
  refine ⟨166246871799858470103682097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110831247866572313402454731 166246871799858470103682097)
  ·
    refine ⟨124685153849893852577761573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166246871799858470103682097 124685153849893852577761573)
    ·
      refine ⟨23378466346855097358330295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124685153849893852577761573 23378466346855097358330295)
      ·
        refine ⟨35067699520282646037495443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23378466346855097358330295 35067699520282646037495443)
        ·
          refine ⟨52601549280423969056243165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35067699520282646037495443 52601549280423969056243165)
          ·
            refine ⟨19725580980158988396091187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52601549280423969056243165 19725580980158988396091187)
            ·
              refine ⟨29588371470238482594136781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19725580980158988396091187 29588371470238482594136781)
              ·
                refine ⟨11095639301339430972801293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29588371470238482594136781 11095639301339430972801293)
                ·
                  refine ⟨4160864738002286614800485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11095639301339430972801293 4160864738002286614800485)
                  ·
                    refine ⟨780162138375428740275091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4160864738002286614800485 780162138375428740275091)
                    ·
                      rfl

theorem cell23_4558081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_4558081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558081 prefixEnd_4558081 := by exact prefixLift 4558081
  have htrace : WordTrace (prefixWord ++ tailWord_4558081) baseStart_4558081 baseEnd_4558081 := by
    simpa [prefixWord, tailWord_4558081, baseEnd_4558081] using wordTrace_append hprefix tailTrace_4558081
  have hstable : (prefixWord ++ tailWord_4558081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558081).length < 2 ^ (prefixWord ++ tailWord_4558081).sum := by decide
  have hdescent : baseEnd_4558081 < baseStart_4558081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558115 : List Nat := [1, 1, 1, 4, 2, 5, 1, 3, 1, 4]
def baseStart_4558115 : Nat := 118140960795 + 4558115 * 2 ^ 59
def prefixEnd_4558115 : Nat := 4983230072969 + 3 ^ 40 * 4558115 * 2
def baseEnd_4558115 : Nat := 780167957822846362600039

theorem tailTrace_4558115 : CollatzResearch.WordTrace tailWord_4558115 prefixEnd_4558115 780167957822846362600039 := by
  unfold tailWord_4558115
  simp only [CollatzResearch.WordTrace]
  refine ⟨166248111881735293910419799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110832074587823529273613199 166248111881735293910419799)
  ·
    refine ⟨249372167822602940865629699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166248111881735293910419799 249372167822602940865629699)
    ·
      refine ⟨374058251733904411298444549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249372167822602940865629699 374058251733904411298444549)
      ·
        refine ⟨70135922200107077118458353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 374058251733904411298444549 70135922200107077118458353)
        ·
          refine ⟨52601941650080307838843765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70135922200107077118458353 52601941650080307838843765)
          ·
            refine ⟨4931432029695028859891603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52601941650080307838843765 4931432029695028859891603)
            ·
              refine ⟨7397148044542543289837405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4931432029695028859891603 7397148044542543289837405)
              ·
                refine ⟨2773930516703453733689027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7397148044542543289837405 2773930516703453733689027)
                ·
                  refine ⟨4160895775055180600533541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2773930516703453733689027 4160895775055180600533541)
                  ·
                    refine ⟨780167957822846362600039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4160895775055180600533541 780167957822846362600039)
                    ·
                      rfl

theorem cell23_4558115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 1, 4].length) (baseStart_4558115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558115 prefixEnd_4558115 := by exact prefixLift 4558115
  have htrace : WordTrace (prefixWord ++ tailWord_4558115) baseStart_4558115 baseEnd_4558115 := by
    simpa [prefixWord, tailWord_4558115, baseEnd_4558115] using wordTrace_append hprefix tailTrace_4558115
  have hstable : (prefixWord ++ tailWord_4558115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558115).length < 2 ^ (prefixWord ++ tailWord_4558115).sum := by decide
  have hdescent : baseEnd_4558115 < baseStart_4558115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558124 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 5, 5]
def baseStart_4558124 : Nat := 118140960795 + 4558124 * 2 ^ 59
def prefixEnd_4558124 : Nat := 4983230072969 + 3 ^ 40 * 4558124 * 2
def baseEnd_4558124 : Nat := 780169498264809850862525

theorem tailTrace_4558124 : CollatzResearch.WordTrace tailWord_4558124 prefixEnd_4558124 780169498264809850862525 := by
  unfold tailWord_4558124
  simp only [CollatzResearch.WordTrace]
  refine ⟨83124220069351344223748713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110832293425801792298331617 83124220069351344223748713)
  ·
    refine ⟨62343165052013508167811535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83124220069351344223748713 62343165052013508167811535)
    ·
      refine ⟨93514747578020262251717303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62343165052013508167811535 93514747578020262251717303)
      ·
        refine ⟨140272121367030393377575955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93514747578020262251717303 140272121367030393377575955)
        ·
          refine ⟨210408182050545590066363933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140272121367030393377575955 210408182050545590066363933)
          ·
            refine ⟨78903068268954596274886475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210408182050545590066363933 78903068268954596274886475)
            ·
              refine ⟨118354602403431894412329713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78903068268954596274886475 118354602403431894412329713)
              ·
                refine ⟨88765951802573920809247285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118354602403431894412329713 88765951802573920809247285)
                ·
                  refine ⟨8321807981491305075866933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88765951802573920809247285 8321807981491305075866933)
                  ·
                    refine ⟨780169498264809850862525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8321807981491305075866933 780169498264809850862525)
                    ·
                      rfl

theorem cell23_4558124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_4558124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558124 prefixEnd_4558124 := by exact prefixLift 4558124
  have htrace : WordTrace (prefixWord ++ tailWord_4558124) baseStart_4558124 baseEnd_4558124 := by
    simpa [prefixWord, tailWord_4558124, baseEnd_4558124] using wordTrace_append hprefix tailTrace_4558124
  have hstable : (prefixWord ++ tailWord_4558124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558124).length < 2 ^ (prefixWord ++ tailWord_4558124).sum := by decide
  have hdescent : baseEnd_4558124 < baseStart_4558124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558125 : List Nat := [1, 5, 3, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_4558125 : Nat := 118140960795 + 4558125 * 2 ^ 59
def prefixEnd_4558125 : Nat := 4983230072969 + 3 ^ 40 * 4558125 * 2
def baseEnd_4558125 : Nat := 2340509008275084048675071

theorem tailTrace_4558125 : CollatzResearch.WordTrace tailWord_4558125 prefixEnd_4558125 2340509008275084048675071 := by
  unfold tailWord_4558125
  simp only [CollatzResearch.WordTrace]
  refine ⟨166248476611699065618283829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110832317741132710412189219 166248476611699065618283829)
  ·
    refine ⟨15585794682346787401714109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166248476611699065618283829 15585794682346787401714109)
    ·
      refine ⟨5844673005880045275642791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15585794682346787401714109 5844673005880045275642791)
      ·
        refine ⟨8767009508820067913464187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5844673005880045275642791 8767009508820067913464187)
        ·
          refine ⟨13150514263230101870196281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8767009508820067913464187 13150514263230101870196281)
          ·
            refine ⟨9862885697422576402647211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13150514263230101870196281 9862885697422576402647211)
            ·
              refine ⟨14794328546133864603970817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9862885697422576402647211 14794328546133864603970817)
              ·
                refine ⟨11095746409600398452978113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14794328546133864603970817 11095746409600398452978113)
                ·
                  refine ⟨8321809807200298839733585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11095746409600398452978113 8321809807200298839733585)
                  ·
                    refine ⟨6241357355400224129800189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8321809807200298839733585 6241357355400224129800189)
                    ·
                      refine ⟨2340509008275084048675071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6241357355400224129800189 2340509008275084048675071)
                      ·
                        rfl

theorem cell23_4558125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_4558125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558125 prefixEnd_4558125 := by exact prefixLift 4558125
  have htrace : WordTrace (prefixWord ++ tailWord_4558125) baseStart_4558125 baseEnd_4558125 := by
    simpa [prefixWord, tailWord_4558125, baseEnd_4558125] using wordTrace_append hprefix tailTrace_4558125
  have hstable : (prefixWord ++ tailWord_4558125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558125).length < 2 ^ (prefixWord ++ tailWord_4558125).sum := by decide
  have hdescent : baseEnd_4558125 < baseStart_4558125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558132 : List Nat := [2, 5, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_4558132 : Nat := 118140960795 + 4558132 * 2 ^ 59
def prefixEnd_4558132 : Nat := 4983230072969 + 3 ^ 40 * 4558132 * 2
def baseEnd_4558132 : Nat := 780170867546555173762513

theorem tailTrace_4558132 : CollatzResearch.WordTrace tailWord_4558132 prefixEnd_4558132 780170867546555173762513 := by
  unfold tailWord_4558132
  simp only [CollatzResearch.WordTrace]
  refine ⟨83124365961336852906894325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110832487948449137209192433 83124365961336852906894325)
  ·
    refine ⟨7792909308875329960021343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83124365961336852906894325 7792909308875329960021343)
    ·
      refine ⟨11689363963312994940032015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7792909308875329960021343 11689363963312994940032015)
      ·
        refine ⟨17534045944969492410048023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11689363963312994940032015 17534045944969492410048023)
        ·
          refine ⟨26301068917454238615072035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17534045944969492410048023 26301068917454238615072035)
          ·
            refine ⟨39451603376181357922608053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26301068917454238615072035 39451603376181357922608053)
            ·
              refine ⟨3698587816517002305244505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39451603376181357922608053 3698587816517002305244505)
              ·
                refine ⟨2773940862387751728933379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3698587816517002305244505 2773940862387751728933379)
                ·
                  refine ⟨4160911293581627593400069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2773940862387751728933379 4160911293581627593400069)
                  ·
                    refine ⟨780170867546555173762513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4160911293581627593400069 780170867546555173762513)
                    ·
                      rfl

theorem cell23_4558132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_4558132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558132 prefixEnd_4558132 := by exact prefixLift 4558132
  have htrace : WordTrace (prefixWord ++ tailWord_4558132) baseStart_4558132 baseEnd_4558132 := by
    simpa [prefixWord, tailWord_4558132, baseEnd_4558132] using wordTrace_append hprefix tailTrace_4558132
  have hstable : (prefixWord ++ tailWord_4558132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558132).length < 2 ^ (prefixWord ++ tailWord_4558132).sum := by decide
  have hdescent : baseEnd_4558132 < baseStart_4558132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558145 : List Nat := [1, 2, 5, 2, 1, 3, 2, 1, 6]
def baseStart_4558145 : Nat := 118140960795 + 4558145 * 2 ^ 59
def prefixEnd_4558145 : Nat := 4983230072969 + 3 ^ 40 * 4558145 * 2
def baseEnd_4558145 : Nat := 260057697543130441158331

theorem tailTrace_4558145 : CollatzResearch.WordTrace tailWord_4558145 prefixEnd_4558145 260057697543130441158331 := by
  unfold tailWord_4558145
  simp only [CollatzResearch.WordTrace]
  refine ⟨166249206071626609034011889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110832804047751072689341259 166249206071626609034011889)
  ·
    refine ⟨124686904553719956775508917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166249206071626609034011889 124686904553719956775508917)
    ·
      refine ⟨11689397301911245947703961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124686904553719956775508917 11689397301911245947703961)
      ·
        refine ⟨8767047976433434460777971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11689397301911245947703961 8767047976433434460777971)
        ·
          refine ⟨13150571964650151691166957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8767047976433434460777971 13150571964650151691166957)
          ·
            refine ⟨4931464486743806884187609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13150571964650151691166957 4931464486743806884187609)
            ·
              refine ⟨3698598365057855163140707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4931464486743806884187609 3698598365057855163140707)
              ·
                refine ⟨5547897547586782744711061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3698598365057855163140707 5547897547586782744711061)
                ·
                  refine ⟨260057697543130441158331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5547897547586782744711061 260057697543130441158331)
                  ·
                    rfl

theorem cell23_4558145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 6].length) (baseStart_4558145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558145 prefixEnd_4558145 := by exact prefixLift 4558145
  have htrace : WordTrace (prefixWord ++ tailWord_4558145) baseStart_4558145 baseEnd_4558145 := by
    simpa [prefixWord, tailWord_4558145, baseEnd_4558145] using wordTrace_append hprefix tailTrace_4558145
  have hstable : (prefixWord ++ tailWord_4558145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558145).length < 2 ^ (prefixWord ++ tailWord_4558145).sum := by decide
  have hdescent : baseEnd_4558145 < baseStart_4558145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558154 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 5, 6]
def baseStart_4558154 : Nat := 118140960795 + 4558154 * 2 ^ 59
def prefixEnd_4558154 : Nat := 4983230072969 + 3 ^ 40 * 4558154 * 2
def baseEnd_4558154 : Nat := 780174633071354811737479

theorem tailTrace_4558154 : CollatzResearch.WordTrace tailWord_4558154 prefixEnd_4558154 780174633071354811737479 := by
  unfold tailWord_4558154
  simp only [CollatzResearch.WordTrace]
  refine ⟨41562383582148500892772379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110833022885729335714059677 41562383582148500892772379)
  ·
    refine ⟨62343575373222751339158569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41562383582148500892772379 62343575373222751339158569)
    ·
      refine ⟨46757681529917063504368927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62343575373222751339158569 46757681529917063504368927)
      ·
        refine ⟨70136522294875595256553391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46757681529917063504368927 70136522294875595256553391)
        ·
          refine ⟨105204783442313392884830087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70136522294875595256553391 105204783442313392884830087)
          ·
            refine ⟨157807175163470089327245131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105204783442313392884830087 157807175163470089327245131)
            ·
              refine ⟨236710762745205133990867697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157807175163470089327245131 236710762745205133990867697)
              ·
                refine ⟨177533072058903850493150773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236710762745205133990867697 177533072058903850493150773)
                ·
                  refine ⟨16643725505522235983732885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 177533072058903850493150773 16643725505522235983732885)
                  ·
                    refine ⟨780174633071354811737479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16643725505522235983732885 780174633071354811737479)
                    ·
                      rfl

theorem cell23_4558154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_4558154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558154 prefixEnd_4558154 := by exact prefixLift 4558154
  have htrace : WordTrace (prefixWord ++ tailWord_4558154) baseStart_4558154 baseEnd_4558154 := by
    simpa [prefixWord, tailWord_4558154, baseEnd_4558154] using wordTrace_append hprefix tailTrace_4558154
  have hstable : (prefixWord ++ tailWord_4558154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558154).length < 2 ^ (prefixWord ++ tailWord_4558154).sum := by decide
  have hdescent : baseEnd_4558154 < baseStart_4558154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558161 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 3, 1, 4]
def baseStart_4558161 : Nat := 118140960795 + 4558161 * 2 ^ 59
def prefixEnd_4558161 : Nat := 4983230072969 + 3 ^ 40 * 4558161 * 2
def baseEnd_4558161 : Nat := 2340527493578645907824905

theorem tailTrace_4558161 : CollatzResearch.WordTrace tailWord_4558161 prefixEnd_4558161 2340527493578645907824905 := by
  unfold tailWord_4558161
  simp only [CollatzResearch.WordTrace]
  refine ⟨166249789639568643766594337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110833193093045762511062891 166249789639568643766594337)
  ·
    refine ⟨124687342229676482824945753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166249789639568643766594337 124687342229676482824945753)
    ·
      refine ⟨93515506672257362118709315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124687342229676482824945753 93515506672257362118709315)
      ·
        refine ⟨140273260008386043178063973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93515506672257362118709315 140273260008386043178063973)
        ·
          refine ⟨26301236251572383095886995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140273260008386043178063973 26301236251572383095886995)
          ·
            refine ⟨39451854377358574643830493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26301236251572383095886995 39451854377358574643830493)
            ·
              refine ⟨14794445391509465491436435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39451854377358574643830493 14794445391509465491436435)
              ·
                refine ⟨22191668087264198237154653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14794445391509465491436435 22191668087264198237154653)
                ·
                  refine ⟨8321875532724074338932995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22191668087264198237154653 8321875532724074338932995)
                  ·
                    refine ⟨12482813299086111508399493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8321875532724074338932995 12482813299086111508399493)
                    ·
                      refine ⟨2340527493578645907824905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12482813299086111508399493 2340527493578645907824905)
                      ·
                        rfl

theorem cell23_4558161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_4558161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558161 prefixEnd_4558161 := by exact prefixLift 4558161
  have htrace : WordTrace (prefixWord ++ tailWord_4558161) baseStart_4558161 baseEnd_4558161 := by
    simpa [prefixWord, tailWord_4558161, baseEnd_4558161] using wordTrace_append hprefix tailTrace_4558161
  have hstable : (prefixWord ++ tailWord_4558161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558161).length < 2 ^ (prefixWord ++ tailWord_4558161).sum := by decide
  have hdescent : baseEnd_4558161 < baseStart_4558161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558165 : List Nat := [1, 3, 2, 2, 3, 2, 2, 1, 2, 3, 2]
def baseStart_4558165 : Nat := 118140960795 + 4558165 * 2 ^ 59
def prefixEnd_4558165 : Nat := 4983230072969 + 3 ^ 40 * 4558165 * 2
def baseEnd_4558165 : Nat := 2340529547501263892174887

theorem tailTrace_4558165 : CollatzResearch.WordTrace tailWord_4558165 prefixEnd_4558165 2340529547501263892174887 := by
  unfold tailWord_4558165
  simp only [CollatzResearch.WordTrace]
  refine ⟨166249935531554152449739949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110833290354369434966493299 166249935531554152449739949)
  ·
    refine ⟨62343725824332807168652481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166249935531554152449739949 62343725824332807168652481)
    ·
      refine ⟨46757794368249605376489361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62343725824332807168652481 46757794368249605376489361)
      ·
        refine ⟨35068345776187204032367021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46757794368249605376489361 35068345776187204032367021)
        ·
          refine ⟨13150629666070201512137633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35068345776187204032367021 13150629666070201512137633)
          ·
            refine ⟨9862972249552651134103225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13150629666070201512137633 9862972249552651134103225)
            ·
              refine ⟨7397229187164488350577419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9862972249552651134103225 7397229187164488350577419)
              ·
                refine ⟨11095843780746732525866129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7397229187164488350577419 11095843780746732525866129)
                ·
                  refine ⟨8321882835560049394399597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11095843780746732525866129 8321882835560049394399597)
                  ·
                    refine ⟨3120706063335018522899849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8321882835560049394399597 3120706063335018522899849)
                    ·
                      refine ⟨2340529547501263892174887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3120706063335018522899849 2340529547501263892174887)
                      ·
                        rfl

theorem cell23_4558165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_4558165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558165 prefixEnd_4558165 := by exact prefixLift 4558165
  have htrace : WordTrace (prefixWord ++ tailWord_4558165) baseStart_4558165 baseEnd_4558165 := by
    simpa [prefixWord, tailWord_4558165, baseEnd_4558165] using wordTrace_append hprefix tailTrace_4558165
  have hstable : (prefixWord ++ tailWord_4558165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558165).length < 2 ^ (prefixWord ++ tailWord_4558165).sum := by decide
  have hdescent : baseEnd_4558165 < baseStart_4558165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558184 : List Nat := [2, 1, 4, 2, 14]
def baseStart_4558184 : Nat := 118140960795 + 4558184 * 2 ^ 59
def prefixEnd_4558184 : Nat := 4983230072969 + 3 ^ 40 * 4558184 * 2
def baseEnd_4558184 : Nat := 3210616328715636924331

theorem tailTrace_4558184 : CollatzResearch.WordTrace tailWord_4558184 prefixEnd_4558184 3210616328715636924331 := by
  unfold tailWord_4558184
  simp only [CollatzResearch.WordTrace]
  refine ⟨83125314259242659347340803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110833752345656879129787737 83125314259242659347340803)
  ·
    refine ⟨124687971388863989021011205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83125314259242659347340803 124687971388863989021011205)
    ·
      refine ⟨23378994635411997941439601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124687971388863989021011205 23378994635411997941439601)
      ·
        refine ⟨17534245976558998456079701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23378994635411997941439601 17534245976558998456079701)
        ·
          refine ⟨3210616328715636924331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 17534245976558998456079701 3210616328715636924331)
          ·
            rfl

theorem cell23_4558184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 14].length) (baseStart_4558184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558184 prefixEnd_4558184 := by exact prefixLift 4558184
  have htrace : WordTrace (prefixWord ++ tailWord_4558184) baseStart_4558184 baseEnd_4558184 := by
    simpa [prefixWord, tailWord_4558184, baseEnd_4558184] using wordTrace_append hprefix tailTrace_4558184
  have hstable : (prefixWord ++ tailWord_4558184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558184).length < 2 ^ (prefixWord ++ tailWord_4558184).sum := by decide
  have hdescent : baseEnd_4558184 < baseStart_4558184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558188 : List Nat := [2, 2, 1, 1, 5, 1, 1, 4, 2, 4]
def baseStart_4558188 : Nat := 118140960795 + 4558188 * 2 ^ 59
def prefixEnd_4558188 : Nat := 4983230072969 + 3 ^ 40 * 4558188 * 2
def baseEnd_4558188 : Nat := 780180452518772434062427

theorem tailTrace_4558188 : CollatzResearch.WordTrace tailWord_4558188 prefixEnd_4558188 780180452518772434062427 := by
  unfold tailWord_4558188
  simp only [CollatzResearch.WordTrace]
  refine ⟨83125387205235413688913609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110833849606980551585218145 83125387205235413688913609)
  ·
    refine ⟨62344040403926560266685207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83125387205235413688913609 62344040403926560266685207)
    ·
      refine ⟨93516060605889840400027811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62344040403926560266685207 93516060605889840400027811)
      ·
        refine ⟨140274090908834760600041717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93516060605889840400027811 140274090908834760600041717)
        ·
          refine ⟨13150696022703258806253911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140274090908834760600041717 13150696022703258806253911)
          ·
            refine ⟨19726044034054888209380867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13150696022703258806253911 19726044034054888209380867)
            ·
              refine ⟨29589066051082332314071301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19726044034054888209380867 29589066051082332314071301)
              ·
                refine ⟨5547949884577937308888369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29589066051082332314071301 5547949884577937308888369)
                ·
                  refine ⟨4160962413433452981666277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5547949884577937308888369 4160962413433452981666277)
                  ·
                    refine ⟨780180452518772434062427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4160962413433452981666277 780180452518772434062427)
                    ·
                      rfl

theorem cell23_4558188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 4].length) (baseStart_4558188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558188 prefixEnd_4558188 := by exact prefixLift 4558188
  have htrace : WordTrace (prefixWord ++ tailWord_4558188) baseStart_4558188 baseEnd_4558188 := by
    simpa [prefixWord, tailWord_4558188, baseEnd_4558188] using wordTrace_append hprefix tailTrace_4558188
  have hstable : (prefixWord ++ tailWord_4558188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558188).length < 2 ^ (prefixWord ++ tailWord_4558188).sum := by decide
  have hdescent : baseEnd_4558188 < baseStart_4558188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558189 : List Nat := [1, 5, 1, 1, 1, 5, 2, 2, 1, 1, 3]
def baseStart_4558189 : Nat := 118140960795 + 4558189 * 2 ^ 59
def prefixEnd_4558189 : Nat := 4983230072969 + 3 ^ 40 * 4558189 * 2
def baseEnd_4558189 : Nat := 2340541871036971798274777

theorem tailTrace_4558189 : CollatzResearch.WordTrace tailWord_4558189 prefixEnd_4558189 2340541871036971798274777 := by
  unfold tailWord_4558189
  simp only [CollatzResearch.WordTrace]
  refine ⟨166250810883467204548613621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110833873922311469699075747 166250810883467204548613621)
  ·
    refine ⟨15586013520325050426432527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166250810883467204548613621 15586013520325050426432527)
    ·
      refine ⟨23379020280487575639648791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15586013520325050426432527 23379020280487575639648791)
      ·
        refine ⟨35068530420731363459473187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23379020280487575639648791 35068530420731363459473187)
        ·
          refine ⟨52602795631097045189209781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35068530420731363459473187 52602795631097045189209781)
          ·
            refine ⟨4931512090415347986488417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52602795631097045189209781 4931512090415347986488417)
            ·
              refine ⟨3698634067811510989866313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4931512090415347986488417 3698634067811510989866313)
              ·
                refine ⟨2773975550858633242399735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3698634067811510989866313 2773975550858633242399735)
                ·
                  refine ⟨4160963326287949863599603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2773975550858633242399735 4160963326287949863599603)
                  ·
                    refine ⟨6241444989431924795399405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4160963326287949863599603 6241444989431924795399405)
                    ·
                      refine ⟨2340541871036971798274777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6241444989431924795399405 2340541871036971798274777)
                      ·
                        rfl

theorem cell23_4558189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_4558189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558189 prefixEnd_4558189 := by exact prefixLift 4558189
  have htrace : WordTrace (prefixWord ++ tailWord_4558189) baseStart_4558189 baseEnd_4558189 := by
    simpa [prefixWord, tailWord_4558189, baseEnd_4558189] using wordTrace_append hprefix tailTrace_4558189
  have hstable : (prefixWord ++ tailWord_4558189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558189).length < 2 ^ (prefixWord ++ tailWord_4558189).sum := by decide
  have hdescent : baseEnd_4558189 < baseStart_4558189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558271 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 3]
def baseStart_4558271 : Nat := 118140960795 + 4558271 * 2 ^ 59
def prefixEnd_4558271 : Nat := 4983230072969 + 3 ^ 40 * 4558271 * 2
def baseEnd_4558271 : Nat := 2340583976450640477449399

theorem tailTrace_4558271 : CollatzResearch.WordTrace tailWord_4558271 prefixEnd_4558271 2340583976450640477449399 := by
  unfold tailWord_4558271
  simp only [CollatzResearch.WordTrace]
  refine ⟨166253801669170132553098667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110835867779446755035399111 166253801669170132553098667)
  ·
    refine ⟨249380702503755198829648001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166253801669170132553098667 249380702503755198829648001)
    ·
      refine ⟨187035526877816399122236001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249380702503755198829648001 187035526877816399122236001)
      ·
        refine ⟨140276645158362299341677001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187035526877816399122236001 140276645158362299341677001)
        ·
          refine ⟨105207483868771724506257751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140276645158362299341677001 105207483868771724506257751)
          ·
            refine ⟨157811225803157586759386627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105207483868771724506257751 157811225803157586759386627)
            ·
              refine ⟨236716838704736380139079941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157811225803157586759386627 236716838704736380139079941)
              ·
                refine ⟨44384407257138071276077489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 236716838704736380139079941 44384407257138071276077489)
                ·
                  refine ⟨33288305442853553457058117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44384407257138071276077489 33288305442853553457058117)
                  ·
                    refine ⟨6241557270535041273198397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33288305442853553457058117 6241557270535041273198397)
                    ·
                      refine ⟨2340583976450640477449399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6241557270535041273198397 2340583976450640477449399)
                      ·
                        rfl

theorem cell23_4558271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_4558271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558271 prefixEnd_4558271 := by exact prefixLift 4558271
  have htrace : WordTrace (prefixWord ++ tailWord_4558271) baseStart_4558271 baseEnd_4558271 := by
    simpa [prefixWord, tailWord_4558271, baseEnd_4558271] using wordTrace_append hprefix tailTrace_4558271
  have hstable : (prefixWord ++ tailWord_4558271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558271).length < 2 ^ (prefixWord ++ tailWord_4558271).sum := by decide
  have hdescent : baseEnd_4558271 < baseStart_4558271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558308 : List Nat := [2, 3, 1, 1, 1, 1, 1, 8, 5]
def baseStart_4558308 : Nat := 118140960795 + 4558308 * 2 ^ 59
def prefixEnd_4558308 : Nat := 4983230072969 + 3 ^ 40 * 4558308 * 2
def baseEnd_4558308 : Nat := 260066997248317425854081

theorem tailTrace_4558308 : CollatzResearch.WordTrace tailWord_4558308 prefixEnd_4558308 260066997248317425854081 := by
  unfold tailWord_4558308
  simp only [CollatzResearch.WordTrace]
  refine ⟨83127575585018043936097789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110836767446690725248130385 83127575585018043936097789)
  ·
    refine ⟨31172840844381766476036671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83127575585018043936097789 31172840844381766476036671)
    ·
      refine ⟨46759261266572649714055007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31172840844381766476036671 46759261266572649714055007)
      ·
        refine ⟨70138891899858974571082511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46759261266572649714055007 70138891899858974571082511)
        ·
          refine ⟨105208337849788461856623767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70138891899858974571082511 105208337849788461856623767)
          ·
            refine ⟨157812506774682692784935651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105208337849788461856623767 157812506774682692784935651)
            ·
              refine ⟨236718760162024039177403477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157812506774682692784935651 236718760162024039177403477)
              ·
                refine ⟨2774047970648719209110197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 236718760162024039177403477 2774047970648719209110197)
                ·
                  refine ⟨260066997248317425854081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2774047970648719209110197 260066997248317425854081)
                  ·
                    rfl

theorem cell23_4558308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_4558308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558308 prefixEnd_4558308 := by exact prefixLift 4558308
  have htrace : WordTrace (prefixWord ++ tailWord_4558308) baseStart_4558308 baseEnd_4558308 := by
    simpa [prefixWord, tailWord_4558308, baseEnd_4558308] using wordTrace_append hprefix tailTrace_4558308
  have hstable : (prefixWord ++ tailWord_4558308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558308).length < 2 ^ (prefixWord ++ tailWord_4558308).sum := by decide
  have hdescent : baseEnd_4558308 < baseStart_4558308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558318 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 1, 5, 3]
def baseStart_4558318 : Nat := 118140960795 + 4558318 * 2 ^ 59
def prefixEnd_4558318 : Nat := 4983230072969 + 3 ^ 40 * 4558318 * 2
def baseEnd_4558318 : Nat := 2340608110041401793561683

theorem tailTrace_4558318 : CollatzResearch.WordTrace tailWord_4558318 prefixEnd_4558318 2340608110041401793561683 := by
  unfold tailWord_4558318
  simp only [CollatzResearch.WordTrace]
  refine ⟨20781939487499982447507451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110837010599999906386706405 20781939487499982447507451)
  ·
    refine ⟨31172909231249973671261177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20781939487499982447507451 31172909231249973671261177)
    ·
      refine ⟨23379681923437480253445883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31172909231249973671261177 23379681923437480253445883)
      ·
        refine ⟨35069522885156220380168825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23379681923437480253445883 35069522885156220380168825)
        ·
          refine ⟨26302142163867165285126619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35069522885156220380168825 26302142163867165285126619)
          ·
            refine ⟨39453213245800747927689929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26302142163867165285126619 39453213245800747927689929)
            ·
              refine ⟨29589909934350560945767447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39453213245800747927689929 29589909934350560945767447)
              ·
                refine ⟨44384864901525841418651171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29589909934350560945767447 44384864901525841418651171)
                ·
                  refine ⟨66577297352288762127976757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44384864901525841418651171 66577297352288762127976757)
                  ·
                    refine ⟨6241621626777071449497821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66577297352288762127976757 6241621626777071449497821)
                    ·
                      refine ⟨2340608110041401793561683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6241621626777071449497821 2340608110041401793561683)
                      ·
                        rfl

theorem cell23_4558318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_4558318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558318 prefixEnd_4558318 := by exact prefixLift 4558318
  have htrace : WordTrace (prefixWord ++ tailWord_4558318) baseStart_4558318 baseEnd_4558318 := by
    simpa [prefixWord, tailWord_4558318, baseEnd_4558318] using wordTrace_append hprefix tailTrace_4558318
  have hstable : (prefixWord ++ tailWord_4558318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558318).length < 2 ^ (prefixWord ++ tailWord_4558318).sum := by decide
  have hdescent : baseEnd_4558318 < baseStart_4558318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558418 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_4558418 : Nat := 118140960795 + 4558418 * 2 ^ 59
def prefixEnd_4558418 : Nat := 4983230072969 + 3 ^ 40 * 4558418 * 2
def baseEnd_4558418 : Nat := 2340659458106851402311223

theorem tailTrace_4558418 : CollatzResearch.WordTrace tailWord_4558418 prefixEnd_4558418 2340659458106851402311223 := by
  unfold tailWord_4558418
  simp only [CollatzResearch.WordTrace]
  refine ⟨41564790799909394164674977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110839442133091717772466605 41564790799909394164674977)
  ·
    refine ⟨31173593099932045623506233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41564790799909394164674977 31173593099932045623506233)
    ·
      refine ⟨23380194824949034217629675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31173593099932045623506233 23380194824949034217629675)
      ·
        refine ⟨35070292237423551326444513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23380194824949034217629675 35070292237423551326444513)
        ·
          refine ⟨26302719178067663494833385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35070292237423551326444513 26302719178067663494833385)
          ·
            refine ⟨19727039383550747621125039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26302719178067663494833385 19727039383550747621125039)
            ·
              refine ⟨29590559075326121431687559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19727039383550747621125039 29590559075326121431687559)
              ·
                refine ⟨44385838612989182147531339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29590559075326121431687559 44385838612989182147531339)
                ·
                  refine ⟨66578757919483773221297009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44385838612989182147531339 66578757919483773221297009)
                  ·
                    refine ⟨49934068439612829915972757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66578757919483773221297009 49934068439612829915972757)
                    ·
                      refine ⟨2340659458106851402311223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49934068439612829915972757 2340659458106851402311223)
                      ·
                        rfl

theorem cell23_4558418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_4558418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558418 prefixEnd_4558418 := by exact prefixLift 4558418
  have htrace : WordTrace (prefixWord ++ tailWord_4558418) baseStart_4558418 baseEnd_4558418 := by
    simpa [prefixWord, tailWord_4558418, baseEnd_4558418] using wordTrace_append hprefix tailTrace_4558418
  have hstable : (prefixWord ++ tailWord_4558418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558418).length < 2 ^ (prefixWord ++ tailWord_4558418).sum := by decide
  have hdescent : baseEnd_4558418 < baseStart_4558418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558435 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 1, 5, 2]
def baseStart_4558435 : Nat := 118140960795 + 4558435 * 2 ^ 59
def prefixEnd_4558435 : Nat := 4983230072969 + 3 ^ 40 * 4558435 * 2
def baseEnd_4558435 : Nat := 2340668187277977835798645

theorem tailTrace_4558435 : CollatzResearch.WordTrace tailWord_4558435 prefixEnd_4558435 2340668187277977835798645 := by
  unfold tailWord_4558435
  simp only [CollatzResearch.WordTrace]
  refine ⟨166259783240575988562068759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110839855493717325708045839 166259783240575988562068759)
  ·
    refine ⟨249389674860863982843103139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166259783240575988562068759 249389674860863982843103139)
    ·
      refine ⟨374084512291295974264654709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249389674860863982843103139 374084512291295974264654709)
      ·
        refine ⟨35070423027308997587311379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 374084512291295974264654709 35070423027308997587311379)
        ·
          refine ⟨52605634540963496380967069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35070423027308997587311379 52605634540963496380967069)
          ·
            refine ⟨19727112952861311142862651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52605634540963496380967069 19727112952861311142862651)
            ·
              refine ⟨29590669429291966714293977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19727112952861311142862651 29590669429291966714293977)
              ·
                refine ⟨22193002071968975035720483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29590669429291966714293977 22193002071968975035720483)
                ·
                  refine ⟨33289503107953462553580725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22193002071968975035720483 33289503107953462553580725)
                  ·
                    refine ⟨3120890916370637114398193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33289503107953462553580725 3120890916370637114398193)
                    ·
                      refine ⟨2340668187277977835798645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3120890916370637114398193 2340668187277977835798645)
                      ·
                        rfl

theorem cell23_4558435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_4558435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558435 prefixEnd_4558435 := by exact prefixLift 4558435
  have htrace : WordTrace (prefixWord ++ tailWord_4558435) baseStart_4558435 baseEnd_4558435 := by
    simpa [prefixWord, tailWord_4558435, baseEnd_4558435] using wordTrace_append hprefix tailTrace_4558435
  have hstable : (prefixWord ++ tailWord_4558435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558435).length < 2 ^ (prefixWord ++ tailWord_4558435).sum := by decide
  have hdescent : baseEnd_4558435 < baseStart_4558435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558442 : List Nat := [3, 1, 3, 2, 1, 2, 2, 2, 3, 1, 3]
def baseStart_4558442 : Nat := 118140960795 + 4558442 * 2 ^ 59
def prefixEnd_4558442 : Nat := 4983230072969 + 3 ^ 40 * 4558442 * 2
def baseEnd_4558442 : Nat := 2340671781642559308411113

theorem tailTrace_4558442 : CollatzResearch.WordTrace tailWord_4558442 prefixEnd_4558442 2340671781642559308411113 := by
  unfold tailWord_4558442
  simp only [CollatzResearch.WordTrace]
  refine ⟨41565009637887657189393395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110840025701033752505049053 41565009637887657189393395)
  ·
    refine ⟨62347514456831485784090093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41565009637887657189393395 62347514456831485784090093)
    ·
      refine ⟨23380317921311807169033785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62347514456831485784090093 23380317921311807169033785)
      ·
        refine ⟨17535238440983855376775339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23380317921311807169033785 17535238440983855376775339)
        ·
          refine ⟨26302857661475783065163009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17535238440983855376775339 26302857661475783065163009)
          ·
            refine ⟨19727143246106837298872257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26302857661475783065163009 19727143246106837298872257)
            ·
              refine ⟨14795357434580127974154193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19727143246106837298872257 14795357434580127974154193)
              ·
                refine ⟨11096518075935095980615645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14795357434580127974154193 11096518075935095980615645)
                ·
                  refine ⟨4161194278475660992730867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11096518075935095980615645 4161194278475660992730867)
                  ·
                    refine ⟨6241791417713491489096301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4161194278475660992730867 6241791417713491489096301)
                    ·
                      refine ⟨2340671781642559308411113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6241791417713491489096301 2340671781642559308411113)
                      ·
                        rfl

theorem cell23_4558442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_4558442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558442 prefixEnd_4558442 := by exact prefixLift 4558442
  have htrace : WordTrace (prefixWord ++ tailWord_4558442) baseStart_4558442 baseEnd_4558442 := by
    simpa [prefixWord, tailWord_4558442, baseEnd_4558442] using wordTrace_append hprefix tailTrace_4558442
  have hstable : (prefixWord ++ tailWord_4558442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558442).length < 2 ^ (prefixWord ++ tailWord_4558442).sum := by decide
  have hdescent : baseEnd_4558442 < baseStart_4558442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558475 : List Nat := [1, 1, 1, 1, 4, 1, 4, 4, 2, 4]
def baseStart_4558475 : Nat := 118140960795 + 4558475 * 2 ^ 59
def prefixEnd_4558475 : Nat := 4983230072969 + 3 ^ 40 * 4558475 * 2
def baseEnd_4558475 : Nat := 780229575501385893099487

theorem tailTrace_4558475 : CollatzResearch.WordTrace tailWord_4558475 prefixEnd_4558475 780229575501385893099487 := by
  unfold tailWord_4558475
  simp only [CollatzResearch.WordTrace]
  refine ⟨166261242160431075393524879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110840828106954050262349919 166261242160431075393524879)
  ·
    refine ⟨249391863240646613090287319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166261242160431075393524879 249391863240646613090287319)
    ·
      refine ⟨374087794860969919635430979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249391863240646613090287319 374087794860969919635430979)
      ·
        refine ⟨561131692291454879453146469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374087794860969919635430979 561131692291454879453146469)
        ·
          refine ⟨105212192304647789897464963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 561131692291454879453146469 105212192304647789897464963)
          ·
            refine ⟨157818288456971684846197445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105212192304647789897464963 157818288456971684846197445)
            ·
              refine ⟨29590929085682190908662021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157818288456971684846197445 29590929085682190908662021)
              ·
                refine ⟨5548299203565410795374129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29590929085682190908662021 5548299203565410795374129)
                ·
                  refine ⟨4161224402674058096530597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5548299203565410795374129 4161224402674058096530597)
                  ·
                    refine ⟨780229575501385893099487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4161224402674058096530597 780229575501385893099487)
                    ·
                      rfl

theorem cell23_4558475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 4].length) (baseStart_4558475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558475 prefixEnd_4558475 := by exact prefixLift 4558475
  have htrace : WordTrace (prefixWord ++ tailWord_4558475) baseStart_4558475 baseEnd_4558475 := by
    simpa [prefixWord, tailWord_4558475, baseEnd_4558475] using wordTrace_append hprefix tailTrace_4558475
  have hstable : (prefixWord ++ tailWord_4558475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558475).length < 2 ^ (prefixWord ++ tailWord_4558475).sum := by decide
  have hdescent : baseEnd_4558475 < baseStart_4558475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558488 : List Nat := [2, 1, 2, 4, 1, 2, 1, 10]
def baseStart_4558488 : Nat := 118140960795 + 4558488 * 2 ^ 59
def prefixEnd_4558488 : Nat := 4983230072969 + 3 ^ 40 * 4558488 * 2
def baseEnd_4558488 : Nat := 86692422287135782534663

theorem tailTrace_4558488 : CollatzResearch.WordTrace tailWord_4558488 prefixEnd_4558488 86692422287135782534663 := by
  unfold tailWord_4558488
  simp only [CollatzResearch.WordTrace]
  refine ⟨83130858154691989306874059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110841144206255985742498745 83130858154691989306874059)
  ·
    refine ⟨124696287232037983960311089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83130858154691989306874059 124696287232037983960311089)
    ·
      refine ⟨93522215424028487970233317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124696287232037983960311089 93522215424028487970233317)
      ·
        refine ⟨17535415392005341494418747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93522215424028487970233317 17535415392005341494418747)
        ·
          refine ⟨26303123088008012241628121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17535415392005341494418747 26303123088008012241628121)
          ·
            refine ⟨19727342316006009181221091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26303123088008012241628121 19727342316006009181221091)
            ·
              refine ⟨29591013474009013771831637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19727342316006009181221091 29591013474009013771831637)
              ·
                refine ⟨86692422287135782534663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29591013474009013771831637 86692422287135782534663)
                ·
                  rfl

theorem cell23_4558488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 10].length) (baseStart_4558488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558488 prefixEnd_4558488 := by exact prefixLift 4558488
  have htrace : WordTrace (prefixWord ++ tailWord_4558488) baseStart_4558488 baseEnd_4558488 := by
    simpa [prefixWord, tailWord_4558488, baseEnd_4558488] using wordTrace_append hprefix tailTrace_4558488
  have hstable : (prefixWord ++ tailWord_4558488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558488).length < 2 ^ (prefixWord ++ tailWord_4558488).sum := by decide
  have hdescent : baseEnd_4558488 < baseStart_4558488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558515 : List Nat := [1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 3]
def baseStart_4558515 : Nat := 118140960795 + 4558515 * 2 ^ 59
def prefixEnd_4558515 : Nat := 4983230072969 + 3 ^ 40 * 4558515 * 2
def baseEnd_4558515 : Nat := 2340709265730337522798277

theorem tailTrace_4558515 : CollatzResearch.WordTrace tailWord_4558515 prefixEnd_4558515 2340709265730337522798277 := by
  unfold tailWord_4558515
  simp only [CollatzResearch.WordTrace]
  refine ⟨166262701080286162224980999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110841800720190774816653999 166262701080286162224980999)
  ·
    refine ⟨249394051620429243337471499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166262701080286162224980999 249394051620429243337471499)
    ·
      refine ⟨374091077430643865006207249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249394051620429243337471499 374091077430643865006207249)
      ·
        refine ⟨280568308072982898754655437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374091077430643865006207249 280568308072982898754655437)
        ·
          refine ⟨105213115527368587032995789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 280568308072982898754655437 105213115527368587032995789)
          ·
            refine ⟨39454918322763220137373421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105213115527368587032995789 39454918322763220137373421)
            ·
              refine ⟨14795594371036207551515033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39454918322763220137373421 14795594371036207551515033)
              ·
                refine ⟨11096695778277155663636275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14795594371036207551515033 11096695778277155663636275)
                ·
                  refine ⟨16645043667415733495454413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11096695778277155663636275 16645043667415733495454413)
                  ·
                    refine ⟨6241891375280900060795405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16645043667415733495454413 6241891375280900060795405)
                    ·
                      refine ⟨2340709265730337522798277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6241891375280900060795405 2340709265730337522798277)
                      ·
                        rfl

theorem cell23_4558515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 3].length) (baseStart_4558515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558515 prefixEnd_4558515 := by exact prefixLift 4558515
  have htrace : WordTrace (prefixWord ++ tailWord_4558515) baseStart_4558515 baseEnd_4558515 := by
    simpa [prefixWord, tailWord_4558515, baseEnd_4558515] using wordTrace_append hprefix tailTrace_4558515
  have hstable : (prefixWord ++ tailWord_4558515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558515).length < 2 ^ (prefixWord ++ tailWord_4558515).sum := by decide
  have hdescent : baseEnd_4558515 < baseStart_4558515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558519 : List Nat := [1, 1, 3, 1, 5, 2, 3, 1, 1, 2, 3]
def baseStart_4558519 : Nat := 118140960795 + 4558519 * 2 ^ 59
def prefixEnd_4558519 : Nat := 4983230072969 + 3 ^ 40 * 4558519 * 2
def baseEnd_4558519 : Nat := 2340711319652955507148259

theorem tailTrace_4558519 : CollatzResearch.WordTrace tailWord_4558519 prefixEnd_4558519 2340711319652955507148259 := by
  unfold tailWord_4558519
  simp only [CollatzResearch.WordTrace]
  refine ⟨166262846972271670908126611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110841897981514447272084407 166262846972271670908126611)
  ·
    refine ⟨249394270458407506362189917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166262846972271670908126611 249394270458407506362189917)
    ·
      refine ⟨93522851421902814885821219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249394270458407506362189917 93522851421902814885821219)
      ·
        refine ⟨140284277132854222328731829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93522851421902814885821219 140284277132854222328731829)
        ·
          refine ⟨13151650981205083343318609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140284277132854222328731829 13151650981205083343318609)
          ·
            refine ⟨9863738235903812507488957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13151650981205083343318609 9863738235903812507488957)
            ·
              refine ⟨3698901838463929690308359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9863738235903812507488957 3698901838463929690308359)
              ·
                refine ⟨5548352757695894535462539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3698901838463929690308359 5548352757695894535462539)
                ·
                  refine ⟨8322529136543841803193809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5548352757695894535462539 8322529136543841803193809)
                  ·
                    refine ⟨6241896852407881352395357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8322529136543841803193809 6241896852407881352395357)
                    ·
                      refine ⟨2340711319652955507148259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6241896852407881352395357 2340711319652955507148259)
                      ·
                        rfl

theorem cell23_4558519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 1, 2, 3].length) (baseStart_4558519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558519 prefixEnd_4558519 := by exact prefixLift 4558519
  have htrace : WordTrace (prefixWord ++ tailWord_4558519) baseStart_4558519 baseEnd_4558519 := by
    simpa [prefixWord, tailWord_4558519, baseEnd_4558519] using wordTrace_append hprefix tailTrace_4558519
  have hstable : (prefixWord ++ tailWord_4558519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558519).length < 2 ^ (prefixWord ++ tailWord_4558519).sum := by decide
  have hdescent : baseEnd_4558519 < baseStart_4558519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558542 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2]
def baseStart_4558542 : Nat := 118140960795 + 4558542 * 2 ^ 59
def prefixEnd_4558542 : Nat := 4983230072969 + 3 ^ 40 * 4558542 * 2
def baseEnd_4558542 : Nat := 2340723129708008917160653

theorem tailTrace_4558542 : CollatzResearch.WordTrace tailWord_4558542 prefixEnd_4558542 2340723129708008917160653 := by
  unfold tailWord_4558542
  simp only [CollatzResearch.WordTrace]
  refine ⟨20782960731398543229526735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110842457234125563890809253 20782960731398543229526735)
  ·
    refine ⟨31174441097097814844290103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20782960731398543229526735 31174441097097814844290103)
    ·
      refine ⟨46761661645646722266435155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31174441097097814844290103 46761661645646722266435155)
      ·
        refine ⟨70142492468470083399652733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46761661645646722266435155 70142492468470083399652733)
        ·
          refine ⟨26303434675676281274869775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70142492468470083399652733 26303434675676281274869775)
          ·
            refine ⟨39455152013514421912304663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26303434675676281274869775 39455152013514421912304663)
            ·
              refine ⟨59182728020271632868456995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39455152013514421912304663 59182728020271632868456995)
              ·
                refine ⟨88774092030407449302685493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59182728020271632868456995 88774092030407449302685493)
                ·
                  refine ⟨8322571127850698372126765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88774092030407449302685493 8322571127850698372126765)
                  ·
                    refine ⟨3120964172944011889547537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8322571127850698372126765 3120964172944011889547537)
                    ·
                      refine ⟨2340723129708008917160653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3120964172944011889547537 2340723129708008917160653)
                      ·
                        rfl

theorem cell23_4558542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_4558542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558542 prefixEnd_4558542 := by exact prefixLift 4558542
  have htrace : WordTrace (prefixWord ++ tailWord_4558542) baseStart_4558542 baseEnd_4558542 := by
    simpa [prefixWord, tailWord_4558542, baseEnd_4558542] using wordTrace_append hprefix tailTrace_4558542
  have hstable : (prefixWord ++ tailWord_4558542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558542).length < 2 ^ (prefixWord ++ tailWord_4558542).sum := by decide
  have hdescent : baseEnd_4558542 < baseStart_4558542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558572 : List Nat := [2, 2, 1, 1, 2, 2, 4, 2, 1, 4, 2]
def baseStart_4558572 : Nat := 118140960795 + 4558572 * 2 ^ 59
def prefixEnd_4558572 : Nat := 4983230072969 + 3 ^ 40 * 4558572 * 2
def baseEnd_4558572 : Nat := 2340738534127643799785515

theorem tailTrace_4558572 : CollatzResearch.WordTrace tailWord_4558572 prefixEnd_4558572 2340738534127643799785515 := by
  unfold tailWord_4558572
  simp only [CollatzResearch.WordTrace]
  refine ⟨83132390020539830479902985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110843186694053107306537313 83132390020539830479902985)
  ·
    refine ⟨62349292515404872859927239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83132390020539830479902985 62349292515404872859927239)
    ·
      refine ⟨93523938773107309289890859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62349292515404872859927239 93523938773107309289890859)
      ·
        refine ⟨140285908159660963934836289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93523938773107309289890859 140285908159660963934836289)
        ·
          refine ⟨105214431119745722951127217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140285908159660963934836289 105214431119745722951127217)
          ·
            refine ⟨78910823339809292213345413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105214431119745722951127217 78910823339809292213345413)
            ·
              refine ⟨14795779376214242290002265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78910823339809292213345413 14795779376214242290002265)
              ·
                refine ⟨11096834532160681717501699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14795779376214242290002265 11096834532160681717501699)
                ·
                  refine ⟨16645251798241022576252549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11096834532160681717501699 16645251798241022576252549)
                  ·
                    refine ⟨3120984712170191733047353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16645251798241022576252549 3120984712170191733047353)
                    ·
                      refine ⟨2340738534127643799785515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3120984712170191733047353 2340738534127643799785515)
                      ·
                        rfl

theorem cell23_4558572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 4, 2].length) (baseStart_4558572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558572 prefixEnd_4558572 := by exact prefixLift 4558572
  have htrace : WordTrace (prefixWord ++ tailWord_4558572) baseStart_4558572 baseEnd_4558572 := by
    simpa [prefixWord, tailWord_4558572, baseEnd_4558572] using wordTrace_append hprefix tailTrace_4558572
  have hstable : (prefixWord ++ tailWord_4558572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558572).length < 2 ^ (prefixWord ++ tailWord_4558572).sum := by decide
  have hdescent : baseEnd_4558572 < baseStart_4558572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558589 : List Nat := [1, 4, 1, 1, 1, 1, 2, 6, 2, 2, 2]
def baseStart_4558589 : Nat := 118140960795 + 4558589 * 2 ^ 59
def prefixEnd_4558589 : Nat := 4983230072969 + 3 ^ 40 * 4558589 * 2
def baseEnd_4558589 : Nat := 2340747263298770233272937

theorem tailTrace_4558589 : CollatzResearch.WordTrace tailWord_4558589 prefixEnd_4558589 2340747263298770233272937 := by
  unfold tailWord_4558589
  simp only [CollatzResearch.WordTrace]
  refine ⟨166265400082018072863174821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110843600054678715242116547 166265400082018072863174821)
  ·
    refine ⟨31174762515378388661845279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166265400082018072863174821 31174762515378388661845279)
    ·
      refine ⟨46762143773067582992767919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31174762515378388661845279 46762143773067582992767919)
      ·
        refine ⟨70143215659601374489151879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46762143773067582992767919 70143215659601374489151879)
        ·
          refine ⟨105214823489402061733727819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70143215659601374489151879 105214823489402061733727819)
          ·
            refine ⟨157822235234103092600591729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105214823489402061733727819 157822235234103092600591729)
            ·
              refine ⟨118366676425577319450443797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157822235234103092600591729 118366676425577319450443797)
              ·
                refine ⟨5548437957448936849239553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 118366676425577319450443797 5548437957448936849239553)
                ·
                  refine ⟨4161328468086702636929665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5548437957448936849239553 4161328468086702636929665)
                  ·
                    refine ⟨3120996351065026977697249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4161328468086702636929665 3120996351065026977697249)
                    ·
                      refine ⟨2340747263298770233272937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3120996351065026977697249 2340747263298770233272937)
                      ·
                        rfl

theorem cell23_4558589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_4558589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558589 prefixEnd_4558589 := by exact prefixLift 4558589
  have htrace : WordTrace (prefixWord ++ tailWord_4558589) baseStart_4558589 baseEnd_4558589 := by
    simpa [prefixWord, tailWord_4558589, baseEnd_4558589] using wordTrace_append hprefix tailTrace_4558589
  have hstable : (prefixWord ++ tailWord_4558589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558589).length < 2 ^ (prefixWord ++ tailWord_4558589).sum := by decide
  have hdescent : baseEnd_4558589 < baseStart_4558589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558625 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 1, 7]
def baseStart_4558625 : Nat := 118140960795 + 4558625 * 2 ^ 59
def prefixEnd_4558625 : Nat := 4983230072969 + 3 ^ 40 * 4558625 * 2
def baseEnd_4558625 : Nat := 780255249534110697474257

theorem tailTrace_4558625 : CollatzResearch.WordTrace tailWord_4558625 prefixEnd_4558625 780255249534110697474257 := by
  unfold tailWord_4558625
  simp only [CollatzResearch.WordTrace]
  refine ⟨166266713109887651011485329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110844475406591767340990219 166266713109887651011485329)
  ·
    refine ⟨124700034832415738258613997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166266713109887651011485329 124700034832415738258613997)
    ·
      refine ⟨46762513062155901846980249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124700034832415738258613997 46762513062155901846980249)
      ·
        refine ⟨35071884796616926385235187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46762513062155901846980249 35071884796616926385235187)
        ·
          refine ⟨52607827194925389577852781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35071884796616926385235187 52607827194925389577852781)
          ·
            refine ⟨19727935198097021091694793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52607827194925389577852781 19727935198097021091694793)
            ·
              refine ⟨14795951398572765818771095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19727935198097021091694793 14795951398572765818771095)
              ·
                refine ⟨22193927097859148728156643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14795951398572765818771095 22193927097859148728156643)
                ·
                  refine ⟨33290890646788723092234965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22193927097859148728156643 33290890646788723092234965)
                  ·
                    refine ⟨780255249534110697474257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33290890646788723092234965 780255249534110697474257)
                    ·
                      rfl

theorem cell23_4558625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_4558625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558625 prefixEnd_4558625 := by exact prefixLift 4558625
  have htrace : WordTrace (prefixWord ++ tailWord_4558625) baseStart_4558625 baseEnd_4558625 := by
    simpa [prefixWord, tailWord_4558625, baseEnd_4558625] using wordTrace_append hprefix tailTrace_4558625
  have hstable : (prefixWord ++ tailWord_4558625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558625).length < 2 ^ (prefixWord ++ tailWord_4558625).sum := by decide
  have hdescent : baseEnd_4558625 < baseStart_4558625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558629 : List Nat := [1, 3, 1, 2, 3, 4, 1, 3, 5]
def baseStart_4558629 : Nat := 118140960795 + 4558629 * 2 ^ 59
def prefixEnd_4558629 : Nat := 4983230072969 + 3 ^ 40 * 4558629 * 2
def baseEnd_4558629 : Nat := 260085311391661119641417

theorem tailTrace_4558629 : CollatzResearch.WordTrace tailWord_4558629 prefixEnd_4558629 260085311391661119641417 := by
  unfold tailWord_4558629
  simp only [CollatzResearch.WordTrace]
  refine ⟨166266859001873159694630941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110844572667915439796420627 166266859001873159694630941)
  ·
    refine ⟨62350072125702434885486603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166266859001873159694630941 62350072125702434885486603)
    ·
      refine ⟨93525108188553652328229905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62350072125702434885486603 93525108188553652328229905)
      ·
        refine ⟨70143831141415239246172429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93525108188553652328229905 70143831141415239246172429)
        ·
          refine ⟨26303936678030714717314661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70143831141415239246172429 26303936678030714717314661)
          ·
            refine ⟨4931988127130759009496499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26303936678030714717314661 4931988127130759009496499)
            ·
              refine ⟨7397982190696138514244749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4931988127130759009496499 7397982190696138514244749)
              ·
                refine ⟨2774243321511051942841781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7397982190696138514244749 2774243321511051942841781)
                ·
                  refine ⟨260085311391661119641417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2774243321511051942841781 260085311391661119641417)
                  ·
                    rfl

theorem cell23_4558629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 5].length) (baseStart_4558629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558629 prefixEnd_4558629 := by exact prefixLift 4558629
  have htrace : WordTrace (prefixWord ++ tailWord_4558629) baseStart_4558629 baseEnd_4558629 := by
    simpa [prefixWord, tailWord_4558629, baseEnd_4558629] using wordTrace_append hprefix tailTrace_4558629
  have hstable : (prefixWord ++ tailWord_4558629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558629).length < 2 ^ (prefixWord ++ tailWord_4558629).sum := by decide
  have hdescent : baseEnd_4558629 < baseStart_4558629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558642 : List Nat := [3, 2, 1, 1, 3, 3, 1, 2, 2, 5]
def baseStart_4558642 : Nat := 118140960795 + 4558642 * 2 ^ 59
def prefixEnd_4558642 : Nat := 4983230072969 + 3 ^ 40 * 4558642 * 2
def baseEnd_4558642 : Nat := 780258159257819508636731

theorem tailTrace_4558642 : CollatzResearch.WordTrace tailWord_4558642 prefixEnd_4558642 780258159257819508636731 := by
  unfold tailWord_4558642
  simp only [CollatzResearch.WordTrace]
  refine ⟨41566833287706515728713545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110844888767217375276569453 41566833287706515728713545)
  ·
    refine ⟨31175124965779886796535159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41566833287706515728713545 31175124965779886796535159)
    ·
      refine ⟨46762687448669830194802739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31175124965779886796535159 46762687448669830194802739)
      ·
        refine ⟨70144031173004745292204109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46762687448669830194802739 70144031173004745292204109)
        ·
          refine ⟨26304011689876779484576541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70144031173004745292204109 26304011689876779484576541)
          ·
            refine ⟨9864004383703792306716203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26304011689876779484576541 9864004383703792306716203)
            ·
              refine ⟨14796006575555688460074305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9864004383703792306716203 14796006575555688460074305)
              ·
                refine ⟨11097004931666766345055729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14796006575555688460074305 11097004931666766345055729)
                ·
                  refine ⟨8322753698750074758791797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11097004931666766345055729 8322753698750074758791797)
                  ·
                    refine ⟨780258159257819508636731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8322753698750074758791797 780258159257819508636731)
                    ·
                      rfl

theorem cell23_4558642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_4558642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558642 prefixEnd_4558642 := by exact prefixLift 4558642
  have htrace : WordTrace (prefixWord ++ tailWord_4558642) baseStart_4558642 baseEnd_4558642 := by
    simpa [prefixWord, tailWord_4558642, baseEnd_4558642] using wordTrace_append hprefix tailTrace_4558642
  have hstable : (prefixWord ++ tailWord_4558642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558642).length < 2 ^ (prefixWord ++ tailWord_4558642).sum := by decide
  have hdescent : baseEnd_4558642 < baseStart_4558642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558679 : List Nat := [1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 4]
def baseStart_4558679 : Nat := 118140960795 + 4558679 * 2 ^ 59
def prefixEnd_4558679 : Nat := 4983230072969 + 3 ^ 40 * 4558679 * 2
def baseEnd_4558679 : Nat := 2340793476557674881147523

theorem tailTrace_4558679 : CollatzResearch.WordTrace tailWord_4558679 prefixEnd_4558679 2340793476557674881147523 := by
  unfold tailWord_4558679
  simp only [CollatzResearch.WordTrace]
  refine ⟨166268682651692018233951091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110845788434461345489300727 166268682651692018233951091)
  ·
    refine ⟨249403023977538027350926637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166268682651692018233951091 249403023977538027350926637)
    ·
      refine ⟨93526133991576760256597489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249403023977538027350926637 93526133991576760256597489)
      ·
        refine ⟨70144600493682570192448117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93526133991576760256597489 70144600493682570192448117)
        ·
          refine ⟨6576056296282740955542011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70144600493682570192448117 6576056296282740955542011)
          ·
            refine ⟨9864084444424111433313017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6576056296282740955542011 9864084444424111433313017)
            ·
              refine ⟨7398063333318083574984763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9864084444424111433313017 7398063333318083574984763)
              ·
                refine ⟨11097094999977125362477145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7398063333318083574984763 11097094999977125362477145)
                ·
                  refine ⟨8322821249982844021857859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11097094999977125362477145 8322821249982844021857859)
                  ·
                    refine ⟨12484231874974266032786789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8322821249982844021857859 12484231874974266032786789)
                    ·
                      refine ⟨2340793476557674881147523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12484231874974266032786789 2340793476557674881147523)
                      ·
                        rfl

theorem cell23_4558679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_4558679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558679 prefixEnd_4558679 := by exact prefixLift 4558679
  have htrace : WordTrace (prefixWord ++ tailWord_4558679) baseStart_4558679 baseEnd_4558679 := by
    simpa [prefixWord, tailWord_4558679, baseEnd_4558679] using wordTrace_append hprefix tailTrace_4558679
  have hstable : (prefixWord ++ tailWord_4558679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558679).length < 2 ^ (prefixWord ++ tailWord_4558679).sum := by decide
  have hdescent : baseEnd_4558679 < baseStart_4558679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558689 : List Nat := [1, 2, 3, 1, 1, 1, 4, 5, 1, 4]
def baseStart_4558689 : Nat := 118140960795 + 4558689 * 2 ^ 59
def prefixEnd_4558689 : Nat := 4983230072969 + 3 ^ 40 * 4558689 * 2
def baseEnd_4558689 : Nat := 780266203788073280674159

theorem tailTrace_4558689 : CollatzResearch.WordTrace tailWord_4558689 prefixEnd_4558689 780266203788073280674159 := by
  unfold tailWord_4558689
  simp only [CollatzResearch.WordTrace]
  refine ⟨166269047381655789941815121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110846031587770526627876747 166269047381655789941815121)
  ·
    refine ⟨124701785536241842456361341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166269047381655789941815121 124701785536241842456361341)
    ·
      refine ⟨46763169576090690921135503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124701785536241842456361341 46763169576090690921135503)
      ·
        refine ⟨70144754364136036381703255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46763169576090690921135503 70144754364136036381703255)
        ·
          refine ⟨105217131546204054572554883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70144754364136036381703255 105217131546204054572554883)
          ·
            refine ⟨157825697319306081858832325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105217131546204054572554883 157825697319306081858832325)
            ·
              refine ⟨29592318247369890348531061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157825697319306081858832325 29592318247369890348531061)
              ·
                refine ⟨2774279835690927220174787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29592318247369890348531061 2774279835690927220174787)
                ·
                  refine ⟨4161419753536390830262181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2774279835690927220174787 4161419753536390830262181)
                  ·
                    refine ⟨780266203788073280674159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4161419753536390830262181 780266203788073280674159)
                    ·
                      rfl

theorem cell23_4558689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_4558689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558689 prefixEnd_4558689 := by exact prefixLift 4558689
  have htrace : WordTrace (prefixWord ++ tailWord_4558689) baseStart_4558689 baseEnd_4558689 := by
    simpa [prefixWord, tailWord_4558689, baseEnd_4558689] using wordTrace_append hprefix tailTrace_4558689
  have hstable : (prefixWord ++ tailWord_4558689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558689).length < 2 ^ (prefixWord ++ tailWord_4558689).sum := by decide
  have hdescent : baseEnd_4558689 < baseStart_4558689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558705 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 1, 2, 6]
def baseStart_4558705 : Nat := 118140960795 + 4558705 * 2 ^ 59
def prefixEnd_4558705 : Nat := 4983230072969 + 3 ^ 40 * 4558705 * 2
def baseEnd_4558705 : Nat := 2340806827054691779422403

theorem tailTrace_4558705 : CollatzResearch.WordTrace tailWord_4558705 prefixEnd_4558705 2340806827054691779422403 := by
  unfold tailWord_4558705
  simp only [CollatzResearch.WordTrace]
  refine ⟨166269630949597824674397569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110846420633065216449598379 166269630949597824674397569)
  ·
    refine ⟨124702223212198368505798177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166269630949597824674397569 124702223212198368505798177)
    ·
      refine ⟨93526667409148776379348633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124702223212198368505798177 93526667409148776379348633)
      ·
        refine ⟨70145000556861582284511475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93526667409148776379348633 70145000556861582284511475)
        ·
          refine ⟨105217500835292373426767213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70145000556861582284511475 105217500835292373426767213)
          ·
            refine ⟨39456562813234640035037705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105217500835292373426767213 39456562813234640035037705)
            ·
              refine ⟨29592422109925980026278279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39456562813234640035037705 29592422109925980026278279)
              ·
                refine ⟨44388633164888970039417419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29592422109925980026278279 44388633164888970039417419)
                ·
                  refine ⟨66582949747333455059126129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44388633164888970039417419 66582949747333455059126129)
                  ·
                    refine ⟨49937212310500091294344597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66582949747333455059126129 49937212310500091294344597)
                    ·
                      refine ⟨2340806827054691779422403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49937212310500091294344597 2340806827054691779422403)
                      ·
                        rfl

theorem cell23_4558705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_4558705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558705 prefixEnd_4558705 := by exact prefixLift 4558705
  have htrace : WordTrace (prefixWord ++ tailWord_4558705) baseStart_4558705 baseEnd_4558705 := by
    simpa [prefixWord, tailWord_4558705, baseEnd_4558705] using wordTrace_append hprefix tailTrace_4558705
  have hstable : (prefixWord ++ tailWord_4558705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558705).length < 2 ^ (prefixWord ++ tailWord_4558705).sum := by decide
  have hdescent : baseEnd_4558705 < baseStart_4558705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558725 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 2, 1, 7]
def baseStart_4558725 : Nat := 118140960795 + 4558725 * 2 ^ 59
def prefixEnd_4558725 : Nat := 4983230072969 + 3 ^ 40 * 4558725 * 2
def baseEnd_4558725 : Nat := 2340817096667781701172311

theorem tailTrace_4558725 : CollatzResearch.WordTrace tailWord_4558725 prefixEnd_4558725 2340817096667781701172311 := by
  unfold tailWord_4558725
  simp only [CollatzResearch.WordTrace]
  refine ⟨166270360409525368090125629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110846906939683578726750419 166270360409525368090125629)
  ·
    refine ⟨62351385153572013033797111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166270360409525368090125629 62351385153572013033797111)
    ·
      refine ⟨93527077730358019550695667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62351385153572013033797111 93527077730358019550695667)
      ·
        refine ⟨140290616595537029326043501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93527077730358019550695667 140290616595537029326043501)
        ·
          refine ⟨52608981223326385997266313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140290616595537029326043501 52608981223326385997266313)
          ·
            refine ⟨39456735917494789497949735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52608981223326385997266313 39456735917494789497949735)
            ·
              refine ⟨59185103876242184246924603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39456735917494789497949735 59185103876242184246924603)
              ·
                refine ⟨88777655814363276370386905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59185103876242184246924603 88777655814363276370386905)
                ·
                  refine ⟨66583241860772457277790179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88777655814363276370386905 66583241860772457277790179)
                  ·
                    refine ⟨99874862791158685916685269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66583241860772457277790179 99874862791158685916685269)
                    ·
                      refine ⟨2340817096667781701172311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99874862791158685916685269 2340817096667781701172311)
                      ·
                        rfl

theorem cell23_4558725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_4558725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558725 prefixEnd_4558725 := by exact prefixLift 4558725
  have htrace : WordTrace (prefixWord ++ tailWord_4558725) baseStart_4558725 baseEnd_4558725 := by
    simpa [prefixWord, tailWord_4558725, baseEnd_4558725] using wordTrace_append hprefix tailTrace_4558725
  have hstable : (prefixWord ++ tailWord_4558725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558725).length < 2 ^ (prefixWord ++ tailWord_4558725).sum := by decide
  have hdescent : baseEnd_4558725 < baseStart_4558725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558729 : List Nat := [1, 2, 1, 1, 5, 1, 3, 2, 3, 1, 3]
def baseStart_4558729 : Nat := 118140960795 + 4558729 * 2 ^ 59
def prefixEnd_4558729 : Nat := 4983230072969 + 3 ^ 40 * 4558729 * 2
def baseEnd_4558729 : Nat := 2340819150590399685522293

theorem tailTrace_4558729 : CollatzResearch.WordTrace tailWord_4558729 prefixEnd_4558729 2340819150590399685522293 := by
  unfold tailWord_4558729
  simp only [CollatzResearch.WordTrace]
  refine ⟨166270506301510876773271241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110847004201007251182180827 166270506301510876773271241)
  ·
    refine ⟨124702879726133157579953431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166270506301510876773271241 124702879726133157579953431)
    ·
      refine ⟨187054319589199736369930147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124702879726133157579953431 187054319589199736369930147)
      ·
        refine ⟨280581479383799604554895221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187054319589199736369930147 280581479383799604554895221)
        ·
          refine ⟨26304513692231212927021427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 280581479383799604554895221 26304513692231212927021427)
          ·
            refine ⟨39456770538346819390532141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26304513692231212927021427 39456770538346819390532141)
            ·
              refine ⟨14796288951880057271449553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39456770538346819390532141 14796288951880057271449553)
              ·
                refine ⟨11097216713910042953587165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14796288951880057271449553 11097216713910042953587165)
                ·
                  refine ⟨4161456267716266107595187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11097216713910042953587165 4161456267716266107595187)
                  ·
                    refine ⟨6242184401574399161392781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4161456267716266107595187 6242184401574399161392781)
                    ·
                      refine ⟨2340819150590399685522293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6242184401574399161392781 2340819150590399685522293)
                      ·
                        rfl

theorem cell23_4558729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 1, 3].length) (baseStart_4558729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558729 prefixEnd_4558729 := by exact prefixLift 4558729
  have htrace : WordTrace (prefixWord ++ tailWord_4558729) baseStart_4558729 baseEnd_4558729 := by
    simpa [prefixWord, tailWord_4558729, baseEnd_4558729] using wordTrace_append hprefix tailTrace_4558729
  have hstable : (prefixWord ++ tailWord_4558729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558729).length < 2 ^ (prefixWord ++ tailWord_4558729).sum := by decide
  have hdescent : baseEnd_4558729 < baseStart_4558729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558732 : List Nat := [2, 2, 1, 2, 1, 2, 1, 6, 1, 5]
def baseStart_4558732 : Nat := 118140960795 + 4558732 * 2 ^ 59
def prefixEnd_4558732 : Nat := 4983230072969 + 3 ^ 40 * 4558732 * 2
def baseEnd_4558732 : Nat := 780273563677454391261593

theorem tailTrace_4558732 : CollatzResearch.WordTrace tailWord_4558732 prefixEnd_4558732 780273563677454391261593 := by
  unfold tailWord_4558732
  simp only [CollatzResearch.WordTrace]
  refine ⟨83135307860250004142815225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110847077147000005523753633 83135307860250004142815225)
  ·
    refine ⟨62351480895187503107111419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83135307860250004142815225 62351480895187503107111419)
    ·
      refine ⟨93527221342781254660667129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62351480895187503107111419 93527221342781254660667129)
      ·
        refine ⟨70145416007085940995500347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93527221342781254660667129 70145416007085940995500347)
        ·
          refine ⟨105218124010628911493250521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70145416007085940995500347 105218124010628911493250521)
          ·
            refine ⟨78913593007971683619937891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105218124010628911493250521 78913593007971683619937891)
            ·
              refine ⟨118370389511957525429906837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78913593007971683619937891 118370389511957525429906837)
              ·
                refine ⟨5548612008373009004526883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 118370389511957525429906837 5548612008373009004526883)
                ·
                  refine ⟨8322918012559513506790325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5548612008373009004526883 8322918012559513506790325)
                  ·
                    refine ⟨780273563677454391261593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8322918012559513506790325 780273563677454391261593)
                    ·
                      rfl

theorem cell23_4558732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 1, 5].length) (baseStart_4558732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558732 prefixEnd_4558732 := by exact prefixLift 4558732
  have htrace : WordTrace (prefixWord ++ tailWord_4558732) baseStart_4558732 baseEnd_4558732 := by
    simpa [prefixWord, tailWord_4558732, baseEnd_4558732] using wordTrace_append hprefix tailTrace_4558732
  have hstable : (prefixWord ++ tailWord_4558732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558732).length < 2 ^ (prefixWord ++ tailWord_4558732).sum := by decide
  have hdescent : baseEnd_4558732 < baseStart_4558732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558749 : List Nat := [1, 4, 2, 1, 2, 3, 1, 3, 1, 5]
def baseStart_4558749 : Nat := 118140960795 + 4558749 * 2 ^ 59
def prefixEnd_4558749 : Nat := 4983230072969 + 3 ^ 40 * 4558749 * 2
def baseEnd_4558749 : Nat := 780276473401163202424067

theorem tailTrace_4558749 : CollatzResearch.WordTrace tailWord_4558749 prefixEnd_4558749 780276473401163202424067 := by
  unfold tailWord_4558749
  simp only [CollatzResearch.WordTrace]
  refine ⟨166271235761438420188999301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110847490507625613459332867 166271235761438420188999301)
  ·
    refine ⟨31175856705269703785437369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166271235761438420188999301 31175856705269703785437369)
    ·
      refine ⟨23381892528952277839078027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31175856705269703785437369 23381892528952277839078027)
      ·
        refine ⟨35072838793428416758617041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23381892528952277839078027 35072838793428416758617041)
        ·
          refine ⟨26304629095071312568962781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35072838793428416758617041 26304629095071312568962781)
          ·
            refine ⟨9864235910651742213361043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26304629095071312568962781 9864235910651742213361043)
            ·
              refine ⟨14796353865977613320041565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9864235910651742213361043 14796353865977613320041565)
              ·
                refine ⟨5548632699741604995015587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14796353865977613320041565 5548632699741604995015587)
                ·
                  refine ⟨8322949049612407492523381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5548632699741604995015587 8322949049612407492523381)
                  ·
                    refine ⟨780276473401163202424067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8322949049612407492523381 780276473401163202424067)
                    ·
                      rfl

theorem cell23_4558749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_4558749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558749 prefixEnd_4558749 := by exact prefixLift 4558749
  have htrace : WordTrace (prefixWord ++ tailWord_4558749) baseStart_4558749 baseEnd_4558749 := by
    simpa [prefixWord, tailWord_4558749, baseEnd_4558749] using wordTrace_append hprefix tailTrace_4558749
  have hstable : (prefixWord ++ tailWord_4558749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558749).length < 2 ^ (prefixWord ++ tailWord_4558749).sum := by decide
  have hdescent : baseEnd_4558749 < baseStart_4558749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558775 : List Nat := [1, 1, 3, 1, 3, 1, 1, 12]
def baseStart_4558775 : Nat := 118140960795 + 4558775 * 2 ^ 59
def prefixEnd_4558775 : Nat := 4983230072969 + 3 ^ 40 * 4558775 * 2
def baseEnd_4558775 : Nat := 86697880396315055761003

theorem tailTrace_4558775 : CollatzResearch.WordTrace tailWord_4558775 prefixEnd_4558775 86697880396315055761003 := by
  unfold tailWord_4558775
  simp only [CollatzResearch.WordTrace]
  refine ⟨166272184059344226629445779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110848122706229484419630519 166272184059344226629445779)
  ·
    refine ⟨249408276089016339944168669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166272184059344226629445779 249408276089016339944168669)
    ·
      refine ⟨93528103533381127479063251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249408276089016339944168669 93528103533381127479063251)
      ·
        refine ⟨140292155300071691218594877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93528103533381127479063251 140292155300071691218594877)
        ·
          refine ⟨52609558237526884206973079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140292155300071691218594877 52609558237526884206973079)
          ·
            refine ⟨78914337356290326310459619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52609558237526884206973079 78914337356290326310459619)
            ·
              refine ⟨118371506034435489465689429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78914337356290326310459619 118371506034435489465689429)
              ·
                refine ⟨86697880396315055761003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 118371506034435489465689429 86697880396315055761003)
                ·
                  rfl

theorem cell23_4558775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 12].length) (baseStart_4558775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558775 prefixEnd_4558775 := by exact prefixLift 4558775
  have htrace : WordTrace (prefixWord ++ tailWord_4558775) baseStart_4558775 baseEnd_4558775 := by
    simpa [prefixWord, tailWord_4558775, baseEnd_4558775] using wordTrace_append hprefix tailTrace_4558775
  have hstable : (prefixWord ++ tailWord_4558775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558775).length < 2 ^ (prefixWord ++ tailWord_4558775).sum := by decide
  have hdescent : baseEnd_4558775 < baseStart_4558775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558792 : List Nat := [2, 1, 3, 1, 4, 2, 1, 9]
def baseStart_4558792 : Nat := 118140960795 + 4558792 * 2 ^ 59
def prefixEnd_4558792 : Nat := 4983230072969 + 3 ^ 40 * 4558792 * 2
def baseEnd_4558792 : Nat := 86698203698949368112389

theorem tailTrace_4558792 : CollatzResearch.WordTrace tailWord_4558792 prefixEnd_4558792 86698203698949368112389 := by
  unfold tailWord_4558792
  simp only [CollatzResearch.WordTrace]
  refine ⟨83136402050141319266407315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110848536066855092355209753 83136402050141319266407315)
  ·
    refine ⟨124704603075211978899610973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83136402050141319266407315 124704603075211978899610973)
    ·
      refine ⟨46764226153204492087354115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124704603075211978899610973 46764226153204492087354115)
      ·
        refine ⟨70146339229806738131031173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46764226153204492087354115 70146339229806738131031173)
        ·
          refine ⟨13152438605588763399568345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70146339229806738131031173 13152438605588763399568345)
          ·
            refine ⟨9864328954191572549676259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13152438605588763399568345 9864328954191572549676259)
            ·
              refine ⟨14796493431287358824514389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9864328954191572549676259 14796493431287358824514389)
              ·
                refine ⟨86698203698949368112389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14796493431287358824514389 86698203698949368112389)
                ·
                  rfl

theorem cell23_4558792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 9].length) (baseStart_4558792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558792 prefixEnd_4558792 := by exact prefixLift 4558792
  have htrace : WordTrace (prefixWord ++ tailWord_4558792) baseStart_4558792 baseEnd_4558792 := by
    simpa [prefixWord, tailWord_4558792, baseEnd_4558792] using wordTrace_append hprefix tailTrace_4558792
  have hstable : (prefixWord ++ tailWord_4558792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558792).length < 2 ^ (prefixWord ++ tailWord_4558792).sum := by decide
  have hdescent : baseEnd_4558792 < baseStart_4558792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558809 : List Nat := [1, 2, 1, 2, 7, 1, 9]
def baseStart_4558809 : Nat := 118140960795 + 4558809 * 2 ^ 59
def prefixEnd_4558809 : Nat := 4983230072969 + 3 ^ 40 * 4558809 * 2
def baseEnd_4558809 : Nat := 28899509000527893487925

theorem tailTrace_4558809 : CollatzResearch.WordTrace tailWord_4558809 prefixEnd_4558809 28899509000527893487925 := by
  unfold tailWord_4558809
  simp only [CollatzResearch.WordTrace]
  refine ⟨166273424141221050436183481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110848949427480700290788987 166273424141221050436183481)
  ·
    refine ⟨124705068105915787827137611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166273424141221050436183481 124705068105915787827137611)
    ·
      refine ⟨187057602158873681740706417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124705068105915787827137611 187057602158873681740706417)
      ·
        refine ⟨140293201619155261305529813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187057602158873681740706417 140293201619155261305529813)
        ·
          refine ⟨3288121912948951436848355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 140293201619155261305529813 3288121912948951436848355)
          ·
            refine ⟨4932182869423427155272533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3288121912948951436848355 4932182869423427155272533)
            ·
              refine ⟨28899509000527893487925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4932182869423427155272533 28899509000527893487925)
              ·
                rfl

theorem cell23_4558809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 9].length) (baseStart_4558809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558809 prefixEnd_4558809 := by exact prefixLift 4558809
  have htrace : WordTrace (prefixWord ++ tailWord_4558809) baseStart_4558809 baseEnd_4558809 := by
    simpa [prefixWord, tailWord_4558809, baseEnd_4558809] using wordTrace_append hprefix tailTrace_4558809
  have hstable : (prefixWord ++ tailWord_4558809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558809).length < 2 ^ (prefixWord ++ tailWord_4558809).sum := by decide
  have hdescent : baseEnd_4558809 < baseStart_4558809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558820 : List Nat := [2, 3, 1, 1, 1, 1, 7, 2, 1, 2, 2]
def baseStart_4558820 : Nat := 118140960795 + 4558820 * 2 ^ 59
def prefixEnd_4558820 : Nat := 4983230072969 + 3 ^ 40 * 4558820 * 2
def baseEnd_4558820 : Nat := 2340865877329958829484375

theorem tailTrace_4558820 : CollatzResearch.WordTrace tailWord_4558820 prefixEnd_4558820 2340865877329958829484375 := by
  unfold tailWord_4558820
  simp only [CollatzResearch.WordTrace]
  refine ⟨83136912672090599657416957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110849216896120799543222609 83136912672090599657416957)
  ·
    refine ⟨31176342252033974871531359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83136912672090599657416957 31176342252033974871531359)
    ·
      refine ⟨46764513378050962307297039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31176342252033974871531359 46764513378050962307297039)
      ·
        refine ⟨70146770067076443460945559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46764513378050962307297039 70146770067076443460945559)
        ·
          refine ⟨105220155100614665191418339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70146770067076443460945559 105220155100614665191418339)
          ·
            refine ⟨157830232650921997787127509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105220155100614665191418339 157830232650921997787127509)
            ·
              refine ⟨3699146077755984323135801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 157830232650921997787127509 3699146077755984323135801)
              ·
                refine ⟨2774359558316988242351851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3699146077755984323135801 2774359558316988242351851)
                ·
                  refine ⟨4161539337475482363527777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2774359558316988242351851 4161539337475482363527777)
                  ·
                    refine ⟨3121154503106611772645833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4161539337475482363527777 3121154503106611772645833)
                    ·
                      refine ⟨2340865877329958829484375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3121154503106611772645833 2340865877329958829484375)
                      ·
                        rfl

theorem cell23_4558820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 1, 2, 2].length) (baseStart_4558820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558820 prefixEnd_4558820 := by exact prefixLift 4558820
  have htrace : WordTrace (prefixWord ++ tailWord_4558820) baseStart_4558820 baseEnd_4558820 := by
    simpa [prefixWord, tailWord_4558820, baseEnd_4558820] using wordTrace_append hprefix tailTrace_4558820
  have hstable : (prefixWord ++ tailWord_4558820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558820).length < 2 ^ (prefixWord ++ tailWord_4558820).sum := by decide
  have hdescent : baseEnd_4558820 < baseStart_4558820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558854 : List Nat := [6, 2, 1, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_4558854 : Nat := 118140960795 + 4558854 * 2 ^ 59
def prefixEnd_4558854 : Nat := 4983230072969 + 3 ^ 40 * 4558854 * 2
def baseEnd_4558854 : Nat := 2340883335672211696459219

theorem tailTrace_4558854 : CollatzResearch.WordTrace tailWord_4558854 prefixEnd_4558854 2340883335672211696459219 := by
  unfold tailWord_4558854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5196095794564313222549113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 110850043617372015414381077 5196095794564313222549113)
  ·
    refine ⟨3897071845923234916911835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5196095794564313222549113 3897071845923234916911835)
    ·
      refine ⟨5845607768884852375367753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3897071845923234916911835 5845607768884852375367753)
      ·
        refine ⟨4384205826663639281525815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5845607768884852375367753 4384205826663639281525815)
        ·
          refine ⟨6576308739995458922288723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4384205826663639281525815 6576308739995458922288723)
          ·
            refine ⟨9864463109993188383433085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6576308739995458922288723 9864463109993188383433085)
            ·
              refine ⟨3699173666247445643787407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9864463109993188383433085 3699173666247445643787407)
              ·
                refine ⟨5548760499371168465681111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3699173666247445643787407 5548760499371168465681111)
                ·
                  refine ⟨8323140749056752698521667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5548760499371168465681111 8323140749056752698521667)
                  ·
                    refine ⟨12484711123585129047782501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8323140749056752698521667 12484711123585129047782501)
                    ·
                      refine ⟨2340883335672211696459219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12484711123585129047782501 2340883335672211696459219)
                      ·
                        rfl

theorem cell23_4558854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_4558854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558854 prefixEnd_4558854 := by exact prefixLift 4558854
  have htrace : WordTrace (prefixWord ++ tailWord_4558854) baseStart_4558854 baseEnd_4558854 := by
    simpa [prefixWord, tailWord_4558854, baseEnd_4558854] using wordTrace_append hprefix tailTrace_4558854
  have hstable : (prefixWord ++ tailWord_4558854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558854).length < 2 ^ (prefixWord ++ tailWord_4558854).sum := by decide
  have hdescent : baseEnd_4558854 < baseStart_4558854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558909 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 1, 5, 3]
def baseStart_4558909 : Nat := 118140960795 + 4558909 * 2 ^ 59
def prefixEnd_4558909 : Nat := 4983230072969 + 3 ^ 40 * 4558909 * 2
def baseEnd_4558909 : Nat := 2340911577108208981271465

theorem tailTrace_4558909 : CollatzResearch.WordTrace tailWord_4558909 prefixEnd_4558909 2340911577108208981271465 := by
  unfold tailWord_4558909
  simp only [CollatzResearch.WordTrace]
  refine ⟨166277071440858767514823781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110851380960572511676549187 166277071440858767514823781)
  ·
    refine ⟨31176950895161018909029459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166277071440858767514823781 31176950895161018909029459)
    ·
      refine ⟨46765426342741528363544189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31176950895161018909029459 46765426342741528363544189)
      ·
        refine ⟨17537034878528073136329071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46765426342741528363544189 17537034878528073136329071)
        ·
          refine ⟨26305552317792109704493607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17537034878528073136329071 26305552317792109704493607)
          ·
            refine ⟨39458328476688164556740411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26305552317792109704493607 39458328476688164556740411)
            ·
              refine ⟨59187492715032246835110617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39458328476688164556740411 59187492715032246835110617)
              ·
                refine ⟨44390619536274185126332963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59187492715032246835110617 44390619536274185126332963)
                ·
                  refine ⟨66585929304411277689499445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44390619536274185126332963 66585929304411277689499445)
                  ·
                    refine ⟨6242430872288557283390573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66585929304411277689499445 6242430872288557283390573)
                    ·
                      refine ⟨2340911577108208981271465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6242430872288557283390573 2340911577108208981271465)
                      ·
                        rfl

theorem cell23_4558909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_4558909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558909 prefixEnd_4558909 := by exact prefixLift 4558909
  have htrace : WordTrace (prefixWord ++ tailWord_4558909) baseStart_4558909 baseEnd_4558909 := by
    simpa [prefixWord, tailWord_4558909, baseEnd_4558909] using wordTrace_append hprefix tailTrace_4558909
  have hstable : (prefixWord ++ tailWord_4558909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558909).length < 2 ^ (prefixWord ++ tailWord_4558909).sum := by decide
  have hdescent : baseEnd_4558909 < baseStart_4558909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558949 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 1, 3, 4]
def baseStart_4558949 : Nat := 118140960795 + 4558949 * 2 ^ 59
def prefixEnd_4558949 : Nat := 4983230072969 + 3 ^ 40 * 4558949 * 2
def baseEnd_4558949 : Nat := 2340932116334388824771281

theorem tailTrace_4558949 : CollatzResearch.WordTrace tailWord_4558949 prefixEnd_4558949 2340932116334388824771281 := by
  unfold tailWord_4558949
  simp only [CollatzResearch.WordTrace]
  refine ⟨166278530360713854346279901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110852353573809236230853267 166278530360713854346279901)
  ·
    refine ⟨62354448885267695379854963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166278530360713854346279901 62354448885267695379854963)
    ·
      refine ⟨93531673327901543069782445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62354448885267695379854963 93531673327901543069782445)
      ·
        refine ⟨35074377497963078651168417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93531673327901543069782445 35074377497963078651168417)
        ·
          refine ⟨26305783123472308988376313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35074377497963078651168417 26305783123472308988376313)
          ·
            refine ⟨19729337342604231741282235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26305783123472308988376313 19729337342604231741282235)
            ·
              refine ⟨29594006013906347611923353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19729337342604231741282235 29594006013906347611923353)
              ·
                refine ⟨22195504510429760708942515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29594006013906347611923353 22195504510429760708942515)
                ·
                  refine ⟨33293256765644641063413773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22195504510429760708942515 33293256765644641063413773)
                  ·
                    refine ⟨12484971287116740398780165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33293256765644641063413773 12484971287116740398780165)
                    ·
                      refine ⟨2340932116334388824771281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12484971287116740398780165 2340932116334388824771281)
                      ·
                        rfl

theorem cell23_4558949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_4558949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558949 prefixEnd_4558949 := by exact prefixLift 4558949
  have htrace : WordTrace (prefixWord ++ tailWord_4558949) baseStart_4558949 baseEnd_4558949 := by
    simpa [prefixWord, tailWord_4558949, baseEnd_4558949] using wordTrace_append hprefix tailTrace_4558949
  have hstable : (prefixWord ++ tailWord_4558949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558949).length < 2 ^ (prefixWord ++ tailWord_4558949).sum := by decide
  have hdescent : baseEnd_4558949 < baseStart_4558949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558966 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_4558966 : Nat := 118140960795 + 4558966 * 2 ^ 59
def prefixEnd_4558966 : Nat := 4983230072969 + 3 ^ 40 * 4558966 * 2
def baseEnd_4558966 : Nat := 2340940845505515258258703

theorem tailTrace_4558966 : CollatzResearch.WordTrace tailWord_4558966 prefixEnd_4558966 2340940845505515258258703 := by
  unfold tailWord_4558966
  simp only [CollatzResearch.WordTrace]
  refine ⟨10392446900103266640603047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110852766934434844166432501 10392446900103266640603047)
  ·
    refine ⟨15588670350154899960904571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10392446900103266640603047 15588670350154899960904571)
    ·
      refine ⟨23383005525232349941356857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15588670350154899960904571 23383005525232349941356857)
      ·
        refine ⟨17537254143924262456017643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23383005525232349941356857 17537254143924262456017643)
        ·
          refine ⟨26305881215886393684026465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17537254143924262456017643 26305881215886393684026465)
          ·
            refine ⟨19729410911914795263019849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26305881215886393684026465 19729410911914795263019849)
            ·
              refine ⟨14797058183936096447264887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19729410911914795263019849 14797058183936096447264887)
              ·
                refine ⟨22195587275904144670897331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14797058183936096447264887 22195587275904144670897331)
                ·
                  refine ⟨33293380913856217006345997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22195587275904144670897331 33293380913856217006345997)
                  ·
                    refine ⟨12485017842696081377379749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33293380913856217006345997 12485017842696081377379749)
                    ·
                      refine ⟨2340940845505515258258703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12485017842696081377379749 2340940845505515258258703)
                      ·
                        rfl

theorem cell23_4558966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_4558966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558966 prefixEnd_4558966 := by exact prefixLift 4558966
  have htrace : WordTrace (prefixWord ++ tailWord_4558966) baseStart_4558966 baseEnd_4558966 := by
    simpa [prefixWord, tailWord_4558966, baseEnd_4558966] using wordTrace_append hprefix tailTrace_4558966
  have hstable : (prefixWord ++ tailWord_4558966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558966).length < 2 ^ (prefixWord ++ tailWord_4558966).sum := by decide
  have hdescent : baseEnd_4558966 < baseStart_4558966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4558986 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 4, 2, 3]
def baseStart_4558986 : Nat := 118140960795 + 4558986 * 2 ^ 59
def prefixEnd_4558986 : Nat := 4983230072969 + 3 ^ 40 * 4558986 * 2
def baseEnd_4558986 : Nat := 2340951115118605180008611

theorem tailTrace_4558986 : CollatzResearch.WordTrace tailWord_4558986 prefixEnd_4558986 2340951115118605180008611 := by
  unfold tailWord_4558986
  simp only [CollatzResearch.WordTrace]
  refine ⟨41569969965394952416344203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110853253241053206443584541 41569969965394952416344203)
  ·
    refine ⟨62354954948092428624516305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41569969965394952416344203 62354954948092428624516305)
    ·
      refine ⟨46766216211069321468387229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62354954948092428624516305 46766216211069321468387229)
      ·
        refine ⟨17537331079150995550645211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46766216211069321468387229 17537331079150995550645211)
        ·
          refine ⟨26305996618726493325967817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17537331079150995550645211 26305996618726493325967817)
          ·
            refine ⟨19729497464044869994475863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26305996618726493325967817 19729497464044869994475863)
            ·
              refine ⟨29594246196067304991713795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19729497464044869994475863 29594246196067304991713795)
              ·
                refine ⟨44391369294100957487570693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29594246196067304991713795 44391369294100957487570693)
                ·
                  refine ⟨8323381742643929528919505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44391369294100957487570693 8323381742643929528919505)
                  ·
                    refine ⟨6242536306982947146689629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8323381742643929528919505 6242536306982947146689629)
                    ·
                      refine ⟨2340951115118605180008611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6242536306982947146689629 2340951115118605180008611)
                      ·
                        rfl

theorem cell23_4558986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_4558986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4558986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4558986 prefixEnd_4558986 := by exact prefixLift 4558986
  have htrace : WordTrace (prefixWord ++ tailWord_4558986) baseStart_4558986 baseEnd_4558986 := by
    simpa [prefixWord, tailWord_4558986, baseEnd_4558986] using wordTrace_append hprefix tailTrace_4558986
  have hstable : (prefixWord ++ tailWord_4558986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4558986).length < 2 ^ (prefixWord ++ tailWord_4558986).sum := by decide
  have hdescent : baseEnd_4558986 < baseStart_4558986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4558986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559050 : List Nat := [3, 1, 2, 1, 3, 1, 3, 4, 1, 1, 3]
def baseStart_4559050 : Nat := 118140960795 + 4559050 * 2 ^ 59
def prefixEnd_4559050 : Nat := 4983230072969 + 3 ^ 40 * 4559050 * 2
def baseEnd_4559050 : Nat := 2340983977880492929608317

theorem tailTrace_4559050 : CollatzResearch.WordTrace tailWord_4559050 prefixEnd_4559050 2340983977880492929608317 := by
  unfold tailWord_4559050
  simp only [CollatzResearch.WordTrace]
  refine ⟨41570553533336987148926651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110854809422231965730471069 41570553533336987148926651)
  ·
    refine ⟨62355830300005480723389977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41570553533336987148926651 62355830300005480723389977)
    ·
      refine ⟨46766872725004110542542483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62355830300005480723389977 46766872725004110542542483)
      ·
        refine ⟨70150309087506165813813725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46766872725004110542542483 70150309087506165813813725)
        ·
          refine ⟨26306365907814812180180147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70150309087506165813813725 26306365907814812180180147)
          ·
            refine ⟨39459548861722218270270221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26306365907814812180180147 39459548861722218270270221)
            ·
              refine ⟨14797330823145831851351333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39459548861722218270270221 14797330823145831851351333)
              ·
                refine ⟨2774499529339843472128375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14797330823145831851351333 2774499529339843472128375)
                ·
                  refine ⟨4161749294009765208192563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2774499529339843472128375 4161749294009765208192563)
                  ·
                    refine ⟨6242623941014647812288845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4161749294009765208192563 6242623941014647812288845)
                    ·
                      refine ⟨2340983977880492929608317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6242623941014647812288845 2340983977880492929608317)
                      ·
                        rfl

theorem cell23_4559050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 1, 1, 3].length) (baseStart_4559050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559050 prefixEnd_4559050 := by exact prefixLift 4559050
  have htrace : WordTrace (prefixWord ++ tailWord_4559050) baseStart_4559050 baseEnd_4559050 := by
    simpa [prefixWord, tailWord_4559050, baseEnd_4559050] using wordTrace_append hprefix tailTrace_4559050
  have hstable : (prefixWord ++ tailWord_4559050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559050).length < 2 ^ (prefixWord ++ tailWord_4559050).sum := by decide
  have hdescent : baseEnd_4559050 < baseStart_4559050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559059 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 3]
def baseStart_4559059 : Nat := 118140960795 + 4559059 * 2 ^ 59
def prefixEnd_4559059 : Nat := 4983230072969 + 3 ^ 40 * 4559059 * 2
def baseEnd_4559059 : Nat := 2340988599206383394395775

theorem tailTrace_4559059 : CollatzResearch.WordTrace tailWord_4559059 prefixEnd_4559059 2340988599206383394395775 := by
  unfold tailWord_4559059
  simp only [CollatzResearch.WordTrace]
  refine ⟨166282542390315343132784231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110855028260210228755189487 166282542390315343132784231)
  ·
    refine ⟨249423813585473014699176347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166282542390315343132784231 249423813585473014699176347)
    ·
      refine ⟨374135720378209522048764521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249423813585473014699176347 374135720378209522048764521)
      ·
        refine ⟨280601790283657141536573391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374135720378209522048764521 280601790283657141536573391)
        ·
          refine ⟨420902685425485712304860087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280601790283657141536573391 420902685425485712304860087)
          ·
            refine ⟨631354028138228568457290131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420902685425485712304860087 631354028138228568457290131)
            ·
              refine ⟨947031042207342852685935197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 631354028138228568457290131 947031042207342852685935197)
              ·
                refine ⟨355136640827753569757225699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 947031042207342852685935197 355136640827753569757225699)
                ·
                  refine ⟨532704961241630354635838549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 355136640827753569757225699 532704961241630354635838549)
                  ·
                    refine ⟨6242636264550355718388733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 532704961241630354635838549 6242636264550355718388733)
                    ·
                      refine ⟨2340988599206383394395775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6242636264550355718388733 2340988599206383394395775)
                      ·
                        rfl

theorem cell23_4559059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 3].length) (baseStart_4559059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559059 prefixEnd_4559059 := by exact prefixLift 4559059
  have htrace : WordTrace (prefixWord ++ tailWord_4559059) baseStart_4559059 baseEnd_4559059 := by
    simpa [prefixWord, tailWord_4559059, baseEnd_4559059] using wordTrace_append hprefix tailTrace_4559059
  have hstable : (prefixWord ++ tailWord_4559059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559059).length < 2 ^ (prefixWord ++ tailWord_4559059).sum := by decide
  have hdescent : baseEnd_4559059 < baseStart_4559059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559090 : List Nat := [3, 2, 1, 3, 2, 1, 4, 1, 1, 1, 4]
def baseStart_4559090 : Nat := 118140960795 + 4559090 * 2 ^ 59
def prefixEnd_4559090 : Nat := 4983230072969 + 3 ^ 40 * 4559090 * 2
def baseEnd_4559090 : Nat := 2341004517106672773108133

theorem tailTrace_4559090 : CollatzResearch.WordTrace tailWord_4559090 prefixEnd_4559090 2341004517106672773108133 := by
  unfold tailWord_4559090
  simp only [CollatzResearch.WordTrace]
  refine ⟨41570918263300758856790681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110855782035468690284775149 41570918263300758856790681)
  ·
    refine ⟨31178188697475569142593011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41570918263300758856790681 31178188697475569142593011)
    ·
      refine ⟨46767283046213353713889517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31178188697475569142593011 46767283046213353713889517)
      ·
        refine ⟨17537731142330007642708569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46767283046213353713889517 17537731142330007642708569)
        ·
          refine ⟨13153298356747505732031427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17537731142330007642708569 13153298356747505732031427)
          ·
            refine ⟨19729947535121258598047141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13153298356747505732031427 19729947535121258598047141)
            ·
              refine ⟨3699365162835235987133839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19729947535121258598047141 3699365162835235987133839)
              ·
                refine ⟨5549047744252853980700759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3699365162835235987133839 5549047744252853980700759)
                ·
                  refine ⟨8323571616379280971051139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5549047744252853980700759 8323571616379280971051139)
                  ·
                    refine ⟨12485357424568921456576709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8323571616379280971051139 12485357424568921456576709)
                    ·
                      refine ⟨2341004517106672773108133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12485357424568921456576709 2341004517106672773108133)
                      ·
                        rfl

theorem cell23_4559090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_4559090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559090 prefixEnd_4559090 := by exact prefixLift 4559090
  have htrace : WordTrace (prefixWord ++ tailWord_4559090) baseStart_4559090 baseEnd_4559090 := by
    simpa [prefixWord, tailWord_4559090, baseEnd_4559090] using wordTrace_append hprefix tailTrace_4559090
  have hstable : (prefixWord ++ tailWord_4559090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559090).length < 2 ^ (prefixWord ++ tailWord_4559090).sum := by decide
  have hdescent : baseEnd_4559090 < baseStart_4559090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559100 : List Nat := [2, 2, 2, 1, 4, 3, 1, 2, 2, 4]
def baseStart_4559100 : Nat := 118140960795 + 4559100 * 2 ^ 59
def prefixEnd_4559100 : Nat := 4983230072969 + 3 ^ 40 * 4559100 * 2
def baseEnd_4559100 : Nat := 780336550637739244661029

theorem tailTrace_4559100 : CollatzResearch.WordTrace tailWord_4559100 prefixEnd_4559100 780336550637739244661029 := by
  unfold tailWord_4559100
  simp only [CollatzResearch.WordTrace]
  refine ⟨83142018891583403567513377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110856025188777871423351169 83142018891583403567513377)
  ·
    refine ⟨62356514168687552675635033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83142018891583403567513377 62356514168687552675635033)
    ·
      refine ⟨46767385626515664506726275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62356514168687552675635033 46767385626515664506726275)
      ·
        refine ⟨70151078439773496760089413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46767385626515664506726275 70151078439773496760089413)
        ·
          refine ⟨13153327207457530642516765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70151078439773496760089413 13153327207457530642516765)
          ·
            refine ⟨4932497702796573990943787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13153327207457530642516765 4932497702796573990943787)
            ·
              refine ⟨7398746554194860986415681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4932497702796573990943787 7398746554194860986415681)
              ·
                refine ⟨5549059915646145739811761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7398746554194860986415681 5549059915646145739811761)
                ·
                  refine ⟨4161794936734609304858821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5549059915646145739811761 4161794936734609304858821)
                  ·
                    refine ⟨780336550637739244661029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4161794936734609304858821 780336550637739244661029)
                    ·
                      rfl

theorem cell23_4559100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_4559100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559100 prefixEnd_4559100 := by exact prefixLift 4559100
  have htrace : WordTrace (prefixWord ++ tailWord_4559100) baseStart_4559100 baseEnd_4559100 := by
    simpa [prefixWord, tailWord_4559100, baseEnd_4559100] using wordTrace_append hprefix tailTrace_4559100
  have hstable : (prefixWord ++ tailWord_4559100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559100).length < 2 ^ (prefixWord ++ tailWord_4559100).sum := by decide
  have hdescent : baseEnd_4559100 < baseStart_4559100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559109 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 2, 7]
def baseStart_4559109 : Nat := 118140960795 + 4559109 * 2 ^ 59
def prefixEnd_4559109 : Nat := 4983230072969 + 3 ^ 40 * 4559109 * 2
def baseEnd_4559109 : Nat := 780338091079702732923515

theorem tailTrace_4559109 : CollatzResearch.WordTrace tailWord_4559109 prefixEnd_4559109 780338091079702732923515 := by
  unfold tailWord_4559109
  simp only [CollatzResearch.WordTrace]
  refine ⟨166284366040134201672104381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110856244026756134448069587 166284366040134201672104381)
  ·
    refine ⟨62356637265050325627039143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166284366040134201672104381 62356637265050325627039143)
    ·
      refine ⟨93534955897575488440558715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62356637265050325627039143 93534955897575488440558715)
      ·
        refine ⟨140302433846363232660838073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93534955897575488440558715 140302433846363232660838073)
        ·
          refine ⟨105226825384772424495628555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140302433846363232660838073 105226825384772424495628555)
          ·
            refine ⟨157840238077158636743442833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105226825384772424495628555 157840238077158636743442833)
            ·
              refine ⟨118380178557868977557582125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157840238077158636743442833 118380178557868977557582125)
              ·
                refine ⟨44392566959200866584093297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118380178557868977557582125 44392566959200866584093297)
                ·
                  refine ⟨33294425219400649938069973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44392566959200866584093297 33294425219400649938069973)
                  ·
                    refine ⟨780338091079702732923515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33294425219400649938069973 780338091079702732923515)
                    ·
                      rfl

theorem cell23_4559109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_4559109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559109 prefixEnd_4559109 := by exact prefixLift 4559109
  have htrace : WordTrace (prefixWord ++ tailWord_4559109) baseStart_4559109 baseEnd_4559109 := by
    simpa [prefixWord, tailWord_4559109, baseEnd_4559109] using wordTrace_append hprefix tailTrace_4559109
  have hstable : (prefixWord ++ tailWord_4559109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559109).length < 2 ^ (prefixWord ++ tailWord_4559109).sum := by decide
  have hdescent : baseEnd_4559109 < baseStart_4559109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559119 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 5]
def baseStart_4559119 : Nat := 118140960795 + 4559119 * 2 ^ 59
def prefixEnd_4559119 : Nat := 4983230072969 + 3 ^ 40 * 4559119 * 2
def baseEnd_4559119 : Nat := 2341019408045653159645499

theorem tailTrace_4559119 : CollatzResearch.WordTrace tailWord_4559119 prefixEnd_4559119 2341019408045653159645499 := by
  unfold tailWord_4559119
  simp only [CollatzResearch.WordTrace]
  refine ⟨166284730770097973379968411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110856487180065315586645607 166284730770097973379968411)
  ·
    refine ⟨249427096155146960069952617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166284730770097973379968411 249427096155146960069952617)
    ·
      refine ⟨187070322116360220052464463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249427096155146960069952617 187070322116360220052464463)
      ·
        refine ⟨280605483174540330078696695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187070322116360220052464463 280605483174540330078696695)
        ·
          refine ⟨420908224761810495118045043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280605483174540330078696695 420908224761810495118045043)
          ·
            refine ⟨631362337142715742677067565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420908224761810495118045043 631362337142715742677067565)
            ·
              refine ⟨236760876428518403503900337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 631362337142715742677067565 236760876428518403503900337)
              ·
                refine ⟨177570657321388802627925253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236760876428518403503900337 177570657321388802627925253)
                ·
                  refine ⟨33294498247760400492735985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 177570657321388802627925253 33294498247760400492735985)
                  ·
                    refine ⟨24970873685820300369551989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33294498247760400492735985 24970873685820300369551989)
                    ·
                      refine ⟨2341019408045653159645499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24970873685820300369551989 2341019408045653159645499)
                      ·
                        rfl

theorem cell23_4559119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_4559119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559119 prefixEnd_4559119 := by exact prefixLift 4559119
  have htrace : WordTrace (prefixWord ++ tailWord_4559119) baseStart_4559119 baseEnd_4559119 := by
    simpa [prefixWord, tailWord_4559119, baseEnd_4559119] using wordTrace_append hprefix tailTrace_4559119
  have hstable : (prefixWord ++ tailWord_4559119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559119).length < 2 ^ (prefixWord ++ tailWord_4559119).sum := by decide
  have hdescent : baseEnd_4559119 < baseStart_4559119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559123 : List Nat := [1, 1, 1, 2, 1, 3, 1, 7, 2, 1, 3]
def baseStart_4559123 : Nat := 118140960795 + 4559123 * 2 ^ 59
def prefixEnd_4559123 : Nat := 4983230072969 + 3 ^ 40 * 4559123 * 2
def baseEnd_4559123 : Nat := 2341021461968271143995481

theorem tailTrace_4559123 : CollatzResearch.WordTrace tailWord_4559123 prefixEnd_4559123 2341021461968271143995481 := by
  unfold tailWord_4559123
  simp only [CollatzResearch.WordTrace]
  refine ⟨166284876662083482063114023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110856584441388988042076015 166284876662083482063114023)
  ·
    refine ⟨249427314993125223094671035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166284876662083482063114023 249427314993125223094671035)
    ·
      refine ⟨374140972489687834642006553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249427314993125223094671035 374140972489687834642006553)
      ·
        refine ⟨280605729367265875981504915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374140972489687834642006553 280605729367265875981504915)
        ·
          refine ⟨420908594050898813972257373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280605729367265875981504915 420908594050898813972257373)
          ·
            refine ⟨157840722769087055239596515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 420908594050898813972257373 157840722769087055239596515)
            ·
              refine ⟨236761084153630582859394773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157840722769087055239596515 236761084153630582859394773)
              ·
                refine ⟨5549087909850716785767065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 236761084153630582859394773 5549087909850716785767065)
                ·
                  refine ⟨4161815932388037589325299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5549087909850716785767065 4161815932388037589325299)
                  ·
                    refine ⟨6242723898582056383987949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4161815932388037589325299 6242723898582056383987949)
                    ·
                      refine ⟨2341021461968271143995481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6242723898582056383987949 2341021461968271143995481)
                      ·
                        rfl

theorem cell23_4559123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 1, 3].length) (baseStart_4559123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559123 prefixEnd_4559123 := by exact prefixLift 4559123
  have htrace : WordTrace (prefixWord ++ tailWord_4559123) baseStart_4559123 baseEnd_4559123 := by
    simpa [prefixWord, tailWord_4559123, baseEnd_4559123] using wordTrace_append hprefix tailTrace_4559123
  have hstable : (prefixWord ++ tailWord_4559123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559123).length < 2 ^ (prefixWord ++ tailWord_4559123).sum := by decide
  have hdescent : baseEnd_4559123 < baseStart_4559123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559130 : List Nat := [3, 1, 1, 3, 5, 1, 2, 7]
def baseStart_4559130 : Nat := 118140960795 + 4559130 * 2 ^ 59
def prefixEnd_4559130 : Nat := 4983230072969 + 3 ^ 40 * 4559130 * 2
def baseEnd_4559130 : Nat := 86704631716031578392887

theorem tailTrace_4559130 : CollatzResearch.WordTrace tailWord_4559130 prefixEnd_4559130 86704631716031578392887 := by
  unfold tailWord_4559130
  simp only [CollatzResearch.WordTrace]
  refine ⟨41571282993264530564654711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110856754648705414839079229 41571282993264530564654711)
  ·
    refine ⟨62356924489896795846982067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41571282993264530564654711 62356924489896795846982067)
    ·
      refine ⟨93535386734845193770473101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62356924489896795846982067 93535386734845193770473101)
      ·
        refine ⟨35075770025566947663927413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93535386734845193770473101 35075770025566947663927413)
        ·
          refine ⟨3288353439896901343493195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35075770025566947663927413 3288353439896901343493195)
          ·
            refine ⟨4932530159845352015239793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3288353439896901343493195 4932530159845352015239793)
            ·
              refine ⟨3699397619884014011429845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4932530159845352015239793 3699397619884014011429845)
              ·
                refine ⟨86704631716031578392887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3699397619884014011429845 86704631716031578392887)
                ·
                  rfl

theorem cell23_4559130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 7].length) (baseStart_4559130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559130 prefixEnd_4559130 := by exact prefixLift 4559130
  have htrace : WordTrace (prefixWord ++ tailWord_4559130) baseStart_4559130 baseEnd_4559130 := by
    simpa [prefixWord, tailWord_4559130, baseEnd_4559130] using wordTrace_append hprefix tailTrace_4559130
  have hstable : (prefixWord ++ tailWord_4559130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559130).length < 2 ^ (prefixWord ++ tailWord_4559130).sum := by decide
  have hdescent : baseEnd_4559130 < baseStart_4559130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559136 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 5]
def baseStart_4559136 : Nat := 118140960795 + 4559136 * 2 ^ 59
def prefixEnd_4559136 : Nat := 4983230072969 + 3 ^ 40 * 4559136 * 2
def baseEnd_4559136 : Nat := 2341028137216779593132921

theorem tailTrace_4559136 : CollatzResearch.WordTrace tailWord_4559136 prefixEnd_4559136 2341028137216779593132921 := by
  unfold tailWord_4559136
  simp only [CollatzResearch.WordTrace]
  refine ⟨83142675405518192641668631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110856900540690923522224841 83142675405518192641668631)
  ·
    refine ⟨124714013108277288962502947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83142675405518192641668631 124714013108277288962502947)
    ·
      refine ⟨187071019662415933443754421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124714013108277288962502947 187071019662415933443754421)
      ·
        refine ⟨17537908093351493760351977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 187071019662415933443754421 17537908093351493760351977)
        ·
          refine ⟨13153431070013620320263983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17537908093351493760351977 13153431070013620320263983)
          ·
            refine ⟨19730146605020430480395975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13153431070013620320263983 19730146605020430480395975)
            ·
              refine ⟨29595219907530645720593963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19730146605020430480395975 29595219907530645720593963)
              ·
                refine ⟨44392829861295968580890945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29595219907530645720593963 44392829861295968580890945)
                ·
                  refine ⟨33294622395971976435668209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44392829861295968580890945 33294622395971976435668209)
                  ·
                    refine ⟨24970966796978982326751157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33294622395971976435668209 24970966796978982326751157)
                    ·
                      refine ⟨2341028137216779593132921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24970966796978982326751157 2341028137216779593132921)
                      ·
                        rfl

theorem cell23_4559136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_4559136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559136 prefixEnd_4559136 := by exact prefixLift 4559136
  have htrace : WordTrace (prefixWord ++ tailWord_4559136) baseStart_4559136 baseEnd_4559136 := by
    simpa [prefixWord, tailWord_4559136, baseEnd_4559136] using wordTrace_append hprefix tailTrace_4559136
  have hstable : (prefixWord ++ tailWord_4559136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559136).length < 2 ^ (prefixWord ++ tailWord_4559136).sum := by decide
  have hdescent : baseEnd_4559136 < baseStart_4559136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559141 : List Nat := [1, 3, 1, 2, 6, 1, 1, 3, 1, 2, 2]
def baseStart_4559141 : Nat := 118140960795 + 4559141 * 2 ^ 59
def prefixEnd_4559141 : Nat := 4983230072969 + 3 ^ 40 * 4559141 * 2
def baseEnd_4559141 : Nat := 2341030704620052073570399

theorem tailTrace_4559141 : CollatzResearch.WordTrace tailWord_4559141 prefixEnd_4559141 2341030704620052073570399 := by
  unfold tailWord_4559141
  simp only [CollatzResearch.WordTrace]
  refine ⟨166285533176018271137269277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110857022117345514091512851 166285533176018271137269277)
  ·
    refine ⟨62357074941006851676475979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166285533176018271137269277 62357074941006851676475979)
    ·
      refine ⟨93535612411510277514713969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62357074941006851676475979 93535612411510277514713969)
      ·
        refine ⟨70151709308632708136035477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93535612411510277514713969 70151709308632708136035477)
        ·
          refine ⟨3288361373842158193876663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 70151709308632708136035477 3288361373842158193876663)
          ·
            refine ⟨4932542060763237290814995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3288361373842158193876663 4932542060763237290814995)
            ·
              refine ⟨7398813091144855936222493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4932542060763237290814995 7398813091144855936222493)
              ·
                refine ⟨2774554909179320976083435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7398813091144855936222493 2774554909179320976083435)
                ·
                  refine ⟨4161832363768981464125153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2774554909179320976083435 4161832363768981464125153)
                  ·
                    refine ⟨3121374272826736098093865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4161832363768981464125153 3121374272826736098093865)
                    ·
                      refine ⟨2341030704620052073570399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3121374272826736098093865 2341030704620052073570399)
                      ·
                        rfl

theorem cell23_4559141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 1, 2, 2].length) (baseStart_4559141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559141 prefixEnd_4559141 := by exact prefixLift 4559141
  have htrace : WordTrace (prefixWord ++ tailWord_4559141) baseStart_4559141 baseEnd_4559141 := by
    simpa [prefixWord, tailWord_4559141, baseEnd_4559141] using wordTrace_append hprefix tailTrace_4559141
  have hstable : (prefixWord ++ tailWord_4559141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559141).length < 2 ^ (prefixWord ++ tailWord_4559141).sum := by decide
  have hdescent : baseEnd_4559141 < baseStart_4559141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559176 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 2, 2, 4]
def baseStart_4559176 : Nat := 118140960795 + 4559176 * 2 ^ 59
def prefixEnd_4559176 : Nat := 4983230072969 + 3 ^ 40 * 4559176 * 2
def baseEnd_4559176 : Nat := 2341048676442959436632737

theorem tailTrace_4559176 : CollatzResearch.WordTrace tailWord_4559176 prefixEnd_4559176 2341048676442959436632737 := by
  unfold tailWord_4559176
  simp only [CollatzResearch.WordTrace]
  refine ⟨83143404865445736057396691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110857873153927648076528921 83143404865445736057396691)
  ·
    refine ⟨124715107298168604086095037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83143404865445736057396691 124715107298168604086095037)
    ·
      refine ⟨46768165236813226532285639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124715107298168604086095037 46768165236813226532285639)
      ·
        refine ⟨70152247855219839798428459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46768165236813226532285639 70152247855219839798428459)
        ·
          refine ⟨105228371782829759697642689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70152247855219839798428459 105228371782829759697642689)
          ·
            refine ⟨78921278837122319773232017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105228371782829759697642689 78921278837122319773232017)
            ·
              refine ⟨59190959127841739829924013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78921278837122319773232017 59190959127841739829924013)
              ·
                refine ⟨22196609672940652436221505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59190959127841739829924013 22196609672940652436221505)
                ·
                  refine ⟨16647457254705489327166129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22196609672940652436221505 16647457254705489327166129)
                  ·
                    refine ⟨12485592941029116995374597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16647457254705489327166129 12485592941029116995374597)
                    ·
                      refine ⟨2341048676442959436632737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12485592941029116995374597 2341048676442959436632737)
                      ·
                        rfl

theorem cell23_4559176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_4559176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559176 prefixEnd_4559176 := by exact prefixLift 4559176
  have htrace : WordTrace (prefixWord ++ tailWord_4559176) baseStart_4559176 baseEnd_4559176 := by
    simpa [prefixWord, tailWord_4559176, baseEnd_4559176] using wordTrace_append hprefix tailTrace_4559176
  have hstable : (prefixWord ++ tailWord_4559176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559176).length < 2 ^ (prefixWord ++ tailWord_4559176).sum := by decide
  have hdescent : baseEnd_4559176 < baseStart_4559176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559186 : List Nat := [3, 2, 2, 1, 1, 1, 2, 4, 7]
def baseStart_4559186 : Nat := 118140960795 + 4559186 * 2 ^ 59
def prefixEnd_4559186 : Nat := 4983230072969 + 3 ^ 40 * 4559186 * 2
def baseEnd_4559186 : Nat := 260117090138833821945299

theorem tailTrace_4559186 : CollatzResearch.WordTrace tailWord_4559186 prefixEnd_4559186 260117090138833821945299 := by
  unfold tailWord_4559186
  simp only [CollatzResearch.WordTrace]
  refine ⟨41571793615213810955664353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110858116307236829215104941 41571793615213810955664353)
  ·
    refine ⟨31178845211410358216748265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41571793615213810955664353 31178845211410358216748265)
    ·
      refine ⟨23384133908557768662561199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31178845211410358216748265 23384133908557768662561199)
      ·
        refine ⟨35076200862836652993841799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23384133908557768662561199 35076200862836652993841799)
        ·
          refine ⟨52614301294254979490762699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35076200862836652993841799 52614301294254979490762699)
          ·
            refine ⟨78921451941382469236144049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52614301294254979490762699 78921451941382469236144049)
            ·
              refine ⟨59191088956036851927108037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78921451941382469236144049 59191088956036851927108037)
              ·
                refine ⟨11098329179256909736332757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59191088956036851927108037 11098329179256909736332757)
                ·
                  refine ⟨260117090138833821945299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11098329179256909736332757 260117090138833821945299)
                  ·
                    rfl

theorem cell23_4559186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_4559186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559186 prefixEnd_4559186 := by exact prefixLift 4559186
  have htrace : WordTrace (prefixWord ++ tailWord_4559186) baseStart_4559186 baseEnd_4559186 := by
    simpa [prefixWord, tailWord_4559186, baseEnd_4559186] using wordTrace_append hprefix tailTrace_4559186
  have hstable : (prefixWord ++ tailWord_4559186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559186).length < 2 ^ (prefixWord ++ tailWord_4559186).sum := by decide
  have hdescent : baseEnd_4559186 < baseStart_4559186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559203 : List Nat := [1, 1, 1, 5, 2, 1, 2, 5, 5]
def baseStart_4559203 : Nat := 118140960795 + 4559203 * 2 ^ 59
def prefixEnd_4559203 : Nat := 4983230072969 + 3 ^ 40 * 4559203 * 2
def baseEnd_4559203 : Nat := 260118060046736758999457

theorem tailTrace_4559203 : CollatzResearch.WordTrace tailWord_4559203 prefixEnd_4559203 260118060046736758999457 := by
  unfold tailWord_4559203
  simp only [CollatzResearch.WordTrace]
  refine ⟨166287794501793655726026263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110858529667862437150684175 166287794501793655726026263)
  ·
    refine ⟨249431691752690483589039395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166287794501793655726026263 249431691752690483589039395)
    ·
      refine ⟨374147537629035725383559093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249431691752690483589039395 374147537629035725383559093)
      ·
        refine ⟨35076331652722099254708665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 374147537629035725383559093 35076331652722099254708665)
        ·
          refine ⟨26307248739541574441031499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35076331652722099254708665 26307248739541574441031499)
          ·
            refine ⟨39460873109312361661547249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26307248739541574441031499 39460873109312361661547249)
            ·
              refine ⟨29595654831984271246160437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39460873109312361661547249 29595654831984271246160437)
              ·
                refine ⟨2774592640498525429327541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29595654831984271246160437 2774592640498525429327541)
                ·
                  refine ⟨260118060046736758999457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2774592640498525429327541 260118060046736758999457)
                  ·
                    rfl

theorem cell23_4559203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 5].length) (baseStart_4559203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559203 prefixEnd_4559203 := by exact prefixLift 4559203
  have htrace : WordTrace (prefixWord ++ tailWord_4559203) baseStart_4559203 baseEnd_4559203 := by
    simpa [prefixWord, tailWord_4559203, baseEnd_4559203] using wordTrace_append hprefix tailTrace_4559203
  have hstable : (prefixWord ++ tailWord_4559203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559203).length < 2 ^ (prefixWord ++ tailWord_4559203).sum := by decide
  have hdescent : baseEnd_4559203 < baseStart_4559203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559213 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 2, 3, 3]
def baseStart_4559213 : Nat := 118140960795 + 4559213 * 2 ^ 59
def prefixEnd_4559213 : Nat := 4983230072969 + 3 ^ 40 * 4559213 * 2
def baseEnd_4559213 : Nat := 2341067675227175791870067

theorem tailTrace_4559213 : CollatzResearch.WordTrace tailWord_4559213 prefixEnd_4559213 2341067675227175791870067 := by
  unfold tailWord_4559213
  simp only [CollatzResearch.WordTrace]
  refine ⟨166288159231757427433890293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110858772821171618289260195 166288159231757427433890293)
  ·
    refine ⟨15589514927977258821927215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166288159231757427433890293 15589514927977258821927215)
    ·
      refine ⟨23384272391965888232890823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15589514927977258821927215 23384272391965888232890823)
      ·
        refine ⟨35076408587948832349336235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23384272391965888232890823 35076408587948832349336235)
        ·
          refine ⟨52614612881923248524004353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35076408587948832349336235 52614612881923248524004353)
          ·
            refine ⟨39460959661442436393003265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52614612881923248524004353 39460959661442436393003265)
            ·
              refine ⟨29595719746081827294752449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39460959661442436393003265 29595719746081827294752449)
              ·
                refine ⟨22196789809561370471064337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29595719746081827294752449 22196789809561370471064337)
                ·
                  refine ⟨16647592357171027853298253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22196789809561370471064337 16647592357171027853298253)
                  ·
                    refine ⟨6242847133939135444986845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16647592357171027853298253 6242847133939135444986845)
                    ·
                      refine ⟨2341067675227175791870067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6242847133939135444986845 2341067675227175791870067)
                      ·
                        rfl

theorem cell23_4559213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_4559213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559213 prefixEnd_4559213 := by exact prefixLift 4559213
  have htrace : WordTrace (prefixWord ++ tailWord_4559213) baseStart_4559213 baseEnd_4559213 := by
    simpa [prefixWord, tailWord_4559213, baseEnd_4559213] using wordTrace_append hprefix tailTrace_4559213
  have hstable : (prefixWord ++ tailWord_4559213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559213).length < 2 ^ (prefixWord ++ tailWord_4559213).sum := by decide
  have hdescent : baseEnd_4559213 < baseStart_4559213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559253 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 3, 6, 2]
def baseStart_4559253 : Nat := 118140960795 + 4559253 * 2 ^ 59
def prefixEnd_4559253 : Nat := 4983230072969 + 3 ^ 40 * 4559253 * 2
def baseEnd_4559253 : Nat := 2341088214453355635369883

theorem tailTrace_4559253 : CollatzResearch.WordTrace tailWord_4559253 prefixEnd_4559253 2341088214453355635369883 := by
  unfold tailWord_4559253
  simp only [CollatzResearch.WordTrace]
  refine ⟨166289618151612514265346413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110859745434408342843564275 166289618151612514265346413)
  ·
    refine ⟨62358606806854692849504905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166289618151612514265346413 62358606806854692849504905)
    ·
      refine ⟨46768955105141019637128679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62358606806854692849504905 46768955105141019637128679)
      ·
        refine ⟨70153432657711529455693019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46768955105141019637128679 70153432657711529455693019)
        ·
          refine ⟨105230148986567294183539529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70153432657711529455693019 105230148986567294183539529)
          ·
            refine ⟨78922611739925470637654647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105230148986567294183539529 78922611739925470637654647)
            ·
              refine ⟨118383917609888205956481971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78922611739925470637654647 118383917609888205956481971)
              ·
                refine ⟨177575876414832308934722957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118383917609888205956481971 177575876414832308934722957)
                ·
                  refine ⟨66590953655562115850521109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177575876414832308934722957 66590953655562115850521109)
                  ·
                    refine ⟨3121450952604474180493177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66590953655562115850521109 3121450952604474180493177)
                    ·
                      refine ⟨2341088214453355635369883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3121450952604474180493177 2341088214453355635369883)
                      ·
                        rfl

theorem cell23_4559253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_4559253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559253 prefixEnd_4559253 := by exact prefixLift 4559253
  have htrace : WordTrace (prefixWord ++ tailWord_4559253) baseStart_4559253 baseEnd_4559253 := by
    simpa [prefixWord, tailWord_4559253, baseEnd_4559253] using wordTrace_append hprefix tailTrace_4559253
  have hstable : (prefixWord ++ tailWord_4559253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559253).length < 2 ^ (prefixWord ++ tailWord_4559253).sum := by decide
  have hdescent : baseEnd_4559253 < baseStart_4559253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559263 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 5, 4]
def baseStart_4559263 : Nat := 118140960795 + 4559263 * 2 ^ 59
def prefixEnd_4559263 : Nat := 4983230072969 + 3 ^ 40 * 4559263 * 2
def baseEnd_4559263 : Nat := 780364449753300198748279

theorem tailTrace_4559263 : CollatzResearch.WordTrace tailWord_4559263 prefixEnd_4559263 780364449753300198748279 := by
  unfold tailWord_4559263
  simp only [CollatzResearch.WordTrace]
  refine ⟨166289982881576285973210443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110859988587717523982140295 166289982881576285973210443)
  ·
    refine ⟨249434974322364428959815665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166289982881576285973210443 249434974322364428959815665)
    ·
      refine ⟨187076230741773321719861749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249434974322364428959815665 187076230741773321719861749)
      ·
        refine ⟨17538396632041248911237039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 187076230741773321719861749 17538396632041248911237039)
        ·
          refine ⟨26307594948061873366855559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17538396632041248911237039 26307594948061873366855559)
          ·
            refine ⟨39461392422092810050283339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26307594948061873366855559 39461392422092810050283339)
            ·
              refine ⟨59192088633139215075425009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39461392422092810050283339 59192088633139215075425009)
              ·
                refine ⟨44394066474854411306568757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59192088633139215075425009 44394066474854411306568757)
                ·
                  refine ⟨4161943732017601059990821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44394066474854411306568757 4161943732017601059990821)
                  ·
                    refine ⟨780364449753300198748279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4161943732017601059990821 780364449753300198748279)
                    ·
                      rfl

theorem cell23_4559263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 4].length) (baseStart_4559263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559263 prefixEnd_4559263 := by exact prefixLift 4559263
  have htrace : WordTrace (prefixWord ++ tailWord_4559263) baseStart_4559263 baseEnd_4559263 := by
    simpa [prefixWord, tailWord_4559263, baseEnd_4559263] using wordTrace_append hprefix tailTrace_4559263
  have hstable : (prefixWord ++ tailWord_4559263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559263).length < 2 ^ (prefixWord ++ tailWord_4559263).sum := by decide
  have hdescent : baseEnd_4559263 < baseStart_4559263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559273 : List Nat := [1, 2, 1, 1, 1, 1, 3, 6, 2, 2, 3]
def baseStart_4559273 : Nat := 118140960795 + 4559273 * 2 ^ 59
def prefixEnd_4559273 : Nat := 4983230072969 + 3 ^ 40 * 4559273 * 2
def baseEnd_4559273 : Nat := 2341098484066445557119791

theorem tailTrace_4559273 : CollatzResearch.WordTrace tailWord_4559273 prefixEnd_4559273 2341098484066445557119791 := by
  unfold tailWord_4559273
  simp only [CollatzResearch.WordTrace]
  refine ⟨166290347611540057681074473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110860231741026705120716315 166290347611540057681074473)
  ·
    refine ⟨124717760708655043260805855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166290347611540057681074473 124717760708655043260805855)
    ·
      refine ⟨187076641062982564891208783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124717760708655043260805855 187076641062982564891208783)
      ·
        refine ⟨280614961594473847336813175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187076641062982564891208783 280614961594473847336813175)
        ·
          refine ⟨420922442391710771005219763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280614961594473847336813175 420922442391710771005219763)
          ·
            refine ⟨631383663587566156507829645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420922442391710771005219763 631383663587566156507829645)
            ·
              refine ⟨236768873845337308690436117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 631383663587566156507829645 236768873845337308690436117)
              ·
                refine ⟨11098540961500186344864193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 236768873845337308690436117 11098540961500186344864193)
                ·
                  refine ⟨8323905721125139758648145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11098540961500186344864193 8323905721125139758648145)
                  ·
                    refine ⟨6242929290843854818986109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8323905721125139758648145 6242929290843854818986109)
                    ·
                      refine ⟨2341098484066445557119791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6242929290843854818986109 2341098484066445557119791)
                      ·
                        rfl

theorem cell23_4559273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 2, 3].length) (baseStart_4559273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559273 prefixEnd_4559273 := by exact prefixLift 4559273
  have htrace : WordTrace (prefixWord ++ tailWord_4559273) baseStart_4559273 baseEnd_4559273 := by
    simpa [prefixWord, tailWord_4559273, baseEnd_4559273] using wordTrace_append hprefix tailTrace_4559273
  have hstable : (prefixWord ++ tailWord_4559273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559273).length < 2 ^ (prefixWord ++ tailWord_4559273).sum := by decide
  have hdescent : baseEnd_4559273 < baseStart_4559273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559296 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 6]
def baseStart_4559296 : Nat := 118140960795 + 4559296 * 2 ^ 59
def prefixEnd_4559296 : Nat := 4983230072969 + 3 ^ 40 * 4559296 * 2
def baseEnd_4559296 : Nat := 2341110294121498967132185

theorem tailTrace_4559296 : CollatzResearch.WordTrace tailWord_4559296 prefixEnd_4559296 2341110294121498967132185 := by
  unfold tailWord_4559296
  simp only [CollatzResearch.WordTrace]
  refine ⟨83145593245228366304580871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110860790993637821739441161 83145593245228366304580871)
  ·
    refine ⟨124718389867842549456871307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83145593245228366304580871 124718389867842549456871307)
    ·
      refine ⟨187077584801763824185306961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124718389867842549456871307 187077584801763824185306961)
      ·
        refine ⟨140308188601322868138980221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187077584801763824185306961 140308188601322868138980221)
        ·
          refine ⟨52615570725496075552117583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140308188601322868138980221 52615570725496075552117583)
          ·
            refine ⟨78923356088244113328176375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52615570725496075552117583 78923356088244113328176375)
            ·
              refine ⟨118385034132366169992264563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78923356088244113328176375 118385034132366169992264563)
              ·
                refine ⟨177577551198549254988396845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118385034132366169992264563 177577551198549254988396845)
                ·
                  refine ⟨66591581699455970620648817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177577551198549254988396845 66591581699455970620648817)
                  ·
                    refine ⟨49943686274591977965486613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66591581699455970620648817 49943686274591977965486613)
                    ·
                      refine ⟨2341110294121498967132185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49943686274591977965486613 2341110294121498967132185)
                      ·
                        rfl

theorem cell23_4559296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_4559296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559296 prefixEnd_4559296 := by exact prefixLift 4559296
  have htrace : WordTrace (prefixWord ++ tailWord_4559296) baseStart_4559296 baseEnd_4559296 := by
    simpa [prefixWord, tailWord_4559296, baseEnd_4559296] using wordTrace_append hprefix tailTrace_4559296
  have hstable : (prefixWord ++ tailWord_4559296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559296).length < 2 ^ (prefixWord ++ tailWord_4559296).sum := by decide
  have hdescent : baseEnd_4559296 < baseStart_4559296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559343 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 4]
def baseStart_4559343 : Nat := 118140960795 + 4559343 * 2 ^ 59
def prefixEnd_4559343 : Nat := 4983230072969 + 3 ^ 40 * 4559343 * 2
def baseEnd_4559343 : Nat := 2341134427712260283244469

theorem tailTrace_4559343 : CollatzResearch.WordTrace tailWord_4559343 prefixEnd_4559343 2341134427712260283244469 := by
  unfold tailWord_4559343
  simp only [CollatzResearch.WordTrace]
  refine ⟨166292900721286459636122683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110861933814190973090748455 166292900721286459636122683)
  ·
    refine ⟨249439351081929689454184025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166292900721286459636122683 249439351081929689454184025)
    ·
      refine ⟨187079513311447267090638019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249439351081929689454184025 187079513311447267090638019)
      ·
        refine ⟨280619269967170900635957029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187079513311447267090638019 280619269967170900635957029)
        ·
          refine ⟨52616113118844543869241943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 280619269967170900635957029 52616113118844543869241943)
          ·
            refine ⟨78924169678266815803862915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52616113118844543869241943 78924169678266815803862915)
            ·
              refine ⟨118386254517400223705794373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78924169678266815803862915 118386254517400223705794373)
              ·
                refine ⟨22197422722012541944836445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118386254517400223705794373 22197422722012541944836445)
                ·
                  refine ⟨8324033520754703229313667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22197422722012541944836445 8324033520754703229313667)
                  ·
                    refine ⟨12486050281132054843970501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8324033520754703229313667 12486050281132054843970501)
                    ·
                      refine ⟨2341134427712260283244469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12486050281132054843970501 2341134427712260283244469)
                      ·
                        rfl

theorem cell23_4559343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 4].length) (baseStart_4559343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559343 prefixEnd_4559343 := by exact prefixLift 4559343
  have htrace : WordTrace (prefixWord ++ tailWord_4559343) baseStart_4559343 baseEnd_4559343 := by
    simpa [prefixWord, tailWord_4559343, baseEnd_4559343] using wordTrace_append hprefix tailTrace_4559343
  have hstable : (prefixWord ++ tailWord_4559343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559343).length < 2 ^ (prefixWord ++ tailWord_4559343).sum := by decide
  have hdescent : baseEnd_4559343 < baseStart_4559343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559364 : List Nat := [2, 3, 2, 3, 1, 2, 2, 1, 2, 3, 2]
def baseStart_4559364 : Nat := 118140960795 + 4559364 * 2 ^ 59
def prefixEnd_4559364 : Nat := 4983230072969 + 3 ^ 40 * 4559364 * 2
def baseEnd_4559364 : Nat := 2341145210806004701081873

theorem tailTrace_4559364 : CollatzResearch.WordTrace tailWord_4559364 prefixEnd_4559364 2341145210806004701081873 := by
  unfold tailWord_4559364
  simp only [CollatzResearch.WordTrace]
  refine ⟨83146833327105190111318573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110862444436140253481758097 83146833327105190111318573)
  ·
    refine ⟨31180062497664446291744465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83146833327105190111318573 31180062497664446291744465)
    ·
      refine ⟨23385046873248334718808349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31180062497664446291744465 23385046873248334718808349)
      ·
        refine ⟨8769392577468125519553131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23385046873248334718808349 8769392577468125519553131)
        ·
          refine ⟨13154088866202188279329697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8769392577468125519553131 13154088866202188279329697)
          ·
            refine ⟨9865566649651641209497273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13154088866202188279329697 9865566649651641209497273)
            ·
              refine ⟨7399174987238730907122955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9865566649651641209497273 7399174987238730907122955)
              ·
                refine ⟨11098762480858096360684433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7399174987238730907122955 11098762480858096360684433)
                ·
                  refine ⟨8324071860643572270513325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11098762480858096360684433 8324071860643572270513325)
                  ·
                    refine ⟨3121526947741339601442497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8324071860643572270513325 3121526947741339601442497)
                    ·
                      refine ⟨2341145210806004701081873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3121526947741339601442497 2341145210806004701081873)
                      ·
                        rfl

theorem cell23_4559364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_4559364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559364 prefixEnd_4559364 := by exact prefixLift 4559364
  have htrace : WordTrace (prefixWord ++ tailWord_4559364) baseStart_4559364 baseEnd_4559364 := by
    simpa [prefixWord, tailWord_4559364, baseEnd_4559364] using wordTrace_append hprefix tailTrace_4559364
  have hstable : (prefixWord ++ tailWord_4559364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559364).length < 2 ^ (prefixWord ++ tailWord_4559364).sum := by decide
  have hdescent : baseEnd_4559364 < baseStart_4559364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559383 : List Nat := [1, 1, 3, 6, 12]
def baseStart_4559383 : Nat := 118140960795 + 4559383 * 2 ^ 59
def prefixEnd_4559383 : Nat := 4983230072969 + 3 ^ 40 * 4559383 * 2
def baseEnd_4559383 : Nat := 3211460859997860256165

theorem tailTrace_4559383 : CollatzResearch.WordTrace tailWord_4559383 prefixEnd_4559383 3211460859997860256165 := by
  unfold tailWord_4559383
  simp only [CollatzResearch.WordTrace]
  refine ⟨166294359641141546467578803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110862906427427697645052535 166294359641141546467578803)
  ·
    refine ⟨249441539461712319701368205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166294359641141546467578803 249441539461712319701368205)
    ·
      refine ⟨93540577298142119888013077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249441539461712319701368205 93540577298142119888013077)
      ·
        refine ⟨4384714560850411869750613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 93540577298142119888013077 4384714560850411869750613)
        ·
          refine ⟨3211460859997860256165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4384714560850411869750613 3211460859997860256165)
          ·
            rfl

theorem cell23_4559383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 12].length) (baseStart_4559383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559383 prefixEnd_4559383 := by exact prefixLift 4559383
  have htrace : WordTrace (prefixWord ++ tailWord_4559383) baseStart_4559383 baseEnd_4559383 := by
    simpa [prefixWord, tailWord_4559383, baseEnd_4559383] using wordTrace_append hprefix tailTrace_4559383
  have hstable : (prefixWord ++ tailWord_4559383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559383).length < 2 ^ (prefixWord ++ tailWord_4559383).sum := by decide
  have hdescent : baseEnd_4559383 < baseStart_4559383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559400 : List Nat := [2, 1, 5, 2, 1, 1, 3, 8]
def baseStart_4559400 : Nat := 118140960795 + 4559400 * 2 ^ 59
def prefixEnd_4559400 : Nat := 4983230072969 + 3 ^ 40 * 4559400 * 2
def baseEnd_4559400 : Nat := 86709766522576539267841

theorem tailTrace_4559400 : CollatzResearch.WordTrace tailWord_4559400 prefixEnd_4559400 86709766522576539267841 := by
  unfold tailWord_4559400
  simp only [CollatzResearch.WordTrace]
  refine ⟨83147489841039979185473827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110863319788053305580631769 83147489841039979185473827)
  ·
    refine ⟨124721234761559968778210741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83147489841039979185473827 124721234761559968778210741)
    ·
      refine ⟨11692615758896247072957257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124721234761559968778210741 11692615758896247072957257)
      ·
        refine ⟨8769461819172185304717943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11692615758896247072957257 8769461819172185304717943)
        ·
          refine ⟨13154192728758277957076915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8769461819172185304717943 13154192728758277957076915)
          ·
            refine ⟨19731289093137416935615373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13154192728758277957076915 19731289093137416935615373)
            ·
              refine ⟨7399233409926531350855765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19731289093137416935615373 7399233409926531350855765)
              ·
                refine ⟨86709766522576539267841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7399233409926531350855765 86709766522576539267841)
                ·
                  rfl

theorem cell23_4559400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 8].length) (baseStart_4559400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559400 prefixEnd_4559400 := by exact prefixLift 4559400
  have htrace : WordTrace (prefixWord ++ tailWord_4559400) baseStart_4559400 baseEnd_4559400 := by
    simpa [prefixWord, tailWord_4559400, baseEnd_4559400] using wordTrace_append hprefix tailTrace_4559400
  have hstable : (prefixWord ++ tailWord_4559400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559400).length < 2 ^ (prefixWord ++ tailWord_4559400).sum := by decide
  have hdescent : baseEnd_4559400 < baseStart_4559400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559410 : List Nat := [3, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3]
def baseStart_4559410 : Nat := 118140960795 + 4559410 * 2 ^ 59
def prefixEnd_4559410 : Nat := 4983230072969 + 3 ^ 40 * 4559410 * 2
def baseEnd_4559410 : Nat := 2341168830916111521106661

theorem tailTrace_4559410 : CollatzResearch.WordTrace tailWord_4559410 prefixEnd_4559410 2341168830916111521106661 := by
  unfold tailWord_4559410
  simp only [CollatzResearch.WordTrace]
  refine ⟨41573836103010932519702921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110863562941362486719207789 41573836103010932519702921)
  ·
    refine ⟨31180377077258199389777191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41573836103010932519702921 31180377077258199389777191)
    ·
      refine ⟨46770565615887299084665787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31180377077258199389777191 46770565615887299084665787)
      ·
        refine ⟨70155848423830948626998681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46770565615887299084665787 70155848423830948626998681)
        ·
          refine ⟨52616886317873211470249011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70155848423830948626998681 52616886317873211470249011)
          ·
            refine ⟨78925329476809817205373517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52616886317873211470249011 78925329476809817205373517)
            ·
              refine ⟨29596998553803681452015069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78925329476809817205373517 29596998553803681452015069)
              ·
                refine ⟨11098874457676380544505651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29596998553803681452015069 11098874457676380544505651)
                ·
                  refine ⟨16648311686514570816758477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11098874457676380544505651 16648311686514570816758477)
                  ·
                    refine ⟨6243116882442964056284429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16648311686514570816758477 6243116882442964056284429)
                    ·
                      refine ⟨2341168830916111521106661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6243116882442964056284429 2341168830916111521106661)
                      ·
                        rfl

theorem cell23_4559410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_4559410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559410 prefixEnd_4559410 := by exact prefixLift 4559410
  have htrace : WordTrace (prefixWord ++ tailWord_4559410) baseStart_4559410 baseEnd_4559410 := by
    simpa [prefixWord, tailWord_4559410, baseEnd_4559410] using wordTrace_append hprefix tailTrace_4559410
  have hstable : (prefixWord ++ tailWord_4559410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559410).length < 2 ^ (prefixWord ++ tailWord_4559410).sum := by decide
  have hdescent : baseEnd_4559410 < baseStart_4559410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559413 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 2, 7]
def baseStart_4559413 : Nat := 118140960795 + 4559413 * 2 ^ 59
def prefixEnd_4559413 : Nat := 4983230072969 + 3 ^ 40 * 4559413 * 2
def baseEnd_4559413 : Nat := 780390123786025003123049

theorem tailTrace_4559413 : CollatzResearch.WordTrace tailWord_4559413 prefixEnd_4559413 780390123786025003123049 := by
  unfold tailWord_4559413
  simp only [CollatzResearch.WordTrace]
  refine ⟨166295453831032861591170893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110863635887355241060780595 166295453831032861591170893)
  ·
    refine ⟨62360795186637323096689085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166295453831032861591170893 62360795186637323096689085)
    ·
      refine ⟨23385298194988996161258407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62360795186637323096689085 23385298194988996161258407)
      ·
        refine ⟨35077947292483494241887611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23385298194988996161258407 35077947292483494241887611)
        ·
          refine ⟨52616920938725241362831417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35077947292483494241887611 52616920938725241362831417)
          ·
            refine ⟨39462690704043931022123563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52616920938725241362831417 39462690704043931022123563)
            ·
              refine ⟨59194036056065896533185345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39462690704043931022123563 59194036056065896533185345)
              ·
                refine ⟨44395527042049422399889009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59194036056065896533185345 44395527042049422399889009)
                ·
                  refine ⟨33296645281537066799916757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44395527042049422399889009 33296645281537066799916757)
                  ·
                    refine ⟨780390123786025003123049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33296645281537066799916757 780390123786025003123049)
                    ·
                      rfl

theorem cell23_4559413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_4559413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559413 prefixEnd_4559413 := by exact prefixLift 4559413
  have htrace : WordTrace (prefixWord ++ tailWord_4559413) baseStart_4559413 baseEnd_4559413 := by
    simpa [prefixWord, tailWord_4559413, baseEnd_4559413] using wordTrace_append hprefix tailTrace_4559413
  have hstable : (prefixWord ++ tailWord_4559413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559413).length < 2 ^ (prefixWord ++ tailWord_4559413).sum := by decide
  have hdescent : baseEnd_4559413 < baseStart_4559413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559423 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 5]
def baseStart_4559423 : Nat := 118140960795 + 4559423 * 2 ^ 59
def prefixEnd_4559423 : Nat := 4983230072969 + 3 ^ 40 * 4559423 * 2
def baseEnd_4559423 : Nat := 2341175506164619970244101

theorem tailTrace_4559423 : CollatzResearch.WordTrace tailWord_4559423 prefixEnd_4559423 2341175506164619970244101 := by
  unfold tailWord_4559423
  simp only [CollatzResearch.WordTrace]
  refine ⟨166295818560996633299034923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110863879040664422199356615 166295818560996633299034923)
  ·
    refine ⟨249443727841494949948552385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166295818560996633299034923 249443727841494949948552385)
    ·
      refine ⟨187082795881121212461414289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249443727841494949948552385 187082795881121212461414289)
      ·
        refine ⟨140312096910840909346060717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187082795881121212461414289 140312096910840909346060717)
        ·
          refine ⟨52617036341565341004772769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140312096910840909346060717 52617036341565341004772769)
          ·
            refine ⟨39462777256174005753579577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52617036341565341004772769 39462777256174005753579577)
            ·
              refine ⟨29597082942130504315184683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39462777256174005753579577 29597082942130504315184683)
              ·
                refine ⟨44395624413195756472777025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29597082942130504315184683 44395624413195756472777025)
                ·
                  refine ⟨33296718309896817354582769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44395624413195756472777025 33296718309896817354582769)
                  ·
                    refine ⟨24972538732422613015937077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33296718309896817354582769 24972538732422613015937077)
                    ·
                      refine ⟨2341175506164619970244101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24972538732422613015937077 2341175506164619970244101)
                      ·
                        rfl

theorem cell23_4559423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_4559423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559423 prefixEnd_4559423 := by exact prefixLift 4559423
  have htrace : WordTrace (prefixWord ++ tailWord_4559423) baseStart_4559423 baseEnd_4559423 := by
    simpa [prefixWord, tailWord_4559423, baseEnd_4559423] using wordTrace_append hprefix tailTrace_4559423
  have hstable : (prefixWord ++ tailWord_4559423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559423).length < 2 ^ (prefixWord ++ tailWord_4559423).sum := by decide
  have hdescent : baseEnd_4559423 < baseStart_4559423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559444 : List Nat := [2, 4, 1, 1, 1, 3, 3, 2, 2, 1, 3]
def baseStart_4559444 : Nat := 118140960795 + 4559444 * 2 ^ 59
def prefixEnd_4559444 : Nat := 4983230072969 + 3 ^ 40 * 4559444 * 2
def baseEnd_4559444 : Nat := 2341186289258364388081505

theorem tailTrace_4559444 : CollatzResearch.WordTrace tailWord_4559444 prefixEnd_4559444 2341186289258364388081505 := by
  unfold tailWord_4559444
  simp only [CollatzResearch.WordTrace]
  refine ⟨83148292246960276942774693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110864389662613702590366257 83148292246960276942774693)
  ·
    refine ⟨15590304796305051926770255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83148292246960276942774693 15590304796305051926770255)
    ·
      refine ⟨23385457194457577890155383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15590304796305051926770255 23385457194457577890155383)
      ·
        refine ⟨35078185791686366835233075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23385457194457577890155383 35078185791686366835233075)
        ·
          refine ⟨52617278687529550252849613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35078185791686366835233075 52617278687529550252849613)
          ·
            refine ⟨19731479507823581344818605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52617278687529550252849613 19731479507823581344818605)
            ·
              refine ⟨7399304815433843004306977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19731479507823581344818605 7399304815433843004306977)
              ·
                refine ⟨5549478611575382253230233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7399304815433843004306977 5549478611575382253230233)
                ·
                  refine ⟨4162108958681536689922675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5549478611575382253230233 4162108958681536689922675)
                  ·
                    refine ⟨6243163438022305034884013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4162108958681536689922675 6243163438022305034884013)
                    ·
                      refine ⟨2341186289258364388081505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6243163438022305034884013 2341186289258364388081505)
                      ·
                        rfl

theorem cell23_4559444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_4559444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559444 prefixEnd_4559444 := by exact prefixLift 4559444
  have htrace : WordTrace (prefixWord ++ tailWord_4559444) baseStart_4559444 baseEnd_4559444 := by
    simpa [prefixWord, tailWord_4559444, baseEnd_4559444] using wordTrace_append hprefix tailTrace_4559444
  have hstable : (prefixWord ++ tailWord_4559444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559444).length < 2 ^ (prefixWord ++ tailWord_4559444).sum := by decide
  have hdescent : baseEnd_4559444 < baseStart_4559444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559450 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2]
def baseStart_4559450 : Nat := 118140960795 + 4559450 * 2 ^ 59
def prefixEnd_4559450 : Nat := 4983230072969 + 3 ^ 40 * 4559450 * 2
def baseEnd_4559450 : Nat := 2341189370142291364606477

theorem tailTrace_4559450 : CollatzResearch.WordTrace tailWord_4559450 prefixEnd_4559450 2341189370142291364606477 := by
  unfold tailWord_4559450
  simp only [CollatzResearch.WordTrace]
  refine ⟨41574200832974704227566951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110864535554599211273511869 41574200832974704227566951)
  ·
    refine ⟨62361301249462056341350427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41574200832974704227566951 62361301249462056341350427)
    ·
      refine ⟨93541951874193084512025641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62361301249462056341350427 93541951874193084512025641)
      ·
        refine ⟨70156463905644813384019231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93541951874193084512025641 70156463905644813384019231)
        ·
          refine ⟨105234695858467220076028847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70156463905644813384019231 105234695858467220076028847)
          ·
            refine ⟨157852043787700830114043271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105234695858467220076028847 157852043787700830114043271)
            ·
              refine ⟨236778065681551245171064907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157852043787700830114043271 236778065681551245171064907)
              ·
                refine ⟨355167098522326867756597361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236778065681551245171064907 355167098522326867756597361)
                ·
                  refine ⟨266375323891745150817448021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355167098522326867756597361 266375323891745150817448021)
                  ·
                    refine ⟨3121585826856388486141969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 266375323891745150817448021 3121585826856388486141969)
                    ·
                      refine ⟨2341189370142291364606477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3121585826856388486141969 2341189370142291364606477)
                      ·
                        rfl

theorem cell23_4559450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_4559450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559450 prefixEnd_4559450 := by exact prefixLift 4559450
  have htrace : WordTrace (prefixWord ++ tailWord_4559450) baseStart_4559450 baseEnd_4559450 := by
    simpa [prefixWord, tailWord_4559450, baseEnd_4559450] using wordTrace_append hprefix tailTrace_4559450
  have hstable : (prefixWord ++ tailWord_4559450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559450).length < 2 ^ (prefixWord ++ tailWord_4559450).sum := by decide
  have hdescent : baseEnd_4559450 < baseStart_4559450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559461 : List Nat := [1, 3, 1, 3, 4, 1, 3, 1, 2, 1, 3]
def baseStart_4559461 : Nat := 118140960795 + 4559461 * 2 ^ 59
def prefixEnd_4559461 : Nat := 4983230072969 + 3 ^ 40 * 4559461 * 2
def baseEnd_4559461 : Nat := 2341195018429490821568927

theorem tailTrace_4559461 : CollatzResearch.WordTrace tailWord_4559461 prefixEnd_4559461 2341195018429490821568927 := by
  unfold tailWord_4559461
  simp only [CollatzResearch.WordTrace]
  refine ⟨166297204534858965788918237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110864803023239310525945491 166297204534858965788918237)
  ·
    refine ⟨62361451700572112170844339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166297204534858965788918237 62361451700572112170844339)
    ·
      refine ⟨93542177550858168256266509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62361451700572112170844339 93542177550858168256266509)
      ·
        refine ⟨35078316581571813096099941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93542177550858168256266509 35078316581571813096099941)
        ·
          refine ⟨6577184359044714955518739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35078316581571813096099941 6577184359044714955518739)
          ·
            refine ⟨9865776538567072433278109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6577184359044714955518739 9865776538567072433278109)
            ·
              refine ⟨3699666201962652162479291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9865776538567072433278109 3699666201962652162479291)
              ·
                refine ⟨5549499302943978243718937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3699666201962652162479291 5549499302943978243718937)
                ·
                  refine ⟨4162124477207983682789203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5549499302943978243718937 4162124477207983682789203)
                  ·
                    refine ⟨6243186715811975524183805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4162124477207983682789203 6243186715811975524183805)
                    ·
                      refine ⟨2341195018429490821568927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6243186715811975524183805 2341195018429490821568927)
                      ·
                        rfl

theorem cell23_4559461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_4559461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559461 prefixEnd_4559461 := by exact prefixLift 4559461
  have htrace : WordTrace (prefixWord ++ tailWord_4559461) baseStart_4559461 baseEnd_4559461 := by
    simpa [prefixWord, tailWord_4559461, baseEnd_4559461] using wordTrace_append hprefix tailTrace_4559461
  have hstable : (prefixWord ++ tailWord_4559461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559461).length < 2 ^ (prefixWord ++ tailWord_4559461).sum := by decide
  have hdescent : baseEnd_4559461 < baseStart_4559461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559500 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 2, 3, 3]
def baseStart_4559500 : Nat := 118140960795 + 4559500 * 2 ^ 59
def prefixEnd_4559500 : Nat := 4983230072969 + 3 ^ 40 * 4559500 * 2
def baseEnd_4559500 : Nat := 2341215044175016168981247

theorem tailTrace_4559500 : CollatzResearch.WordTrace tailWord_4559500 prefixEnd_4559500 2341215044175016168981247 := by
  unfold tailWord_4559500
  simp only [CollatzResearch.WordTrace]
  refine ⟨83149313490858837724793977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110865751321145116966391969 83149313490858837724793977)
  ·
    refine ⟨62361985118144128293595483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83149313490858837724793977 62361985118144128293595483)
    ·
      refine ⟨93542977677216192440393225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62361985118144128293595483 93542977677216192440393225)
      ·
        refine ⟨70157233257912144330294919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93542977677216192440393225 70157233257912144330294919)
        ·
          refine ⟨105235849886868216495442379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70157233257912144330294919 105235849886868216495442379)
          ·
            refine ⟨157853774830302324743163569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105235849886868216495442379 157853774830302324743163569)
            ·
              refine ⟨118390331122726743557372677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157853774830302324743163569 118390331122726743557372677)
              ·
                refine ⟨22198187085511264417007377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118390331122726743557372677 22198187085511264417007377)
                ·
                  refine ⟨16648640314133448312755533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22198187085511264417007377 16648640314133448312755533)
                  ·
                    refine ⟨6243240117800043117283325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16648640314133448312755533 6243240117800043117283325)
                    ·
                      refine ⟨2341215044175016168981247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6243240117800043117283325 2341215044175016168981247)
                      ·
                        rfl

theorem cell23_4559500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_4559500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559500 prefixEnd_4559500 := by exact prefixLift 4559500
  have htrace : WordTrace (prefixWord ++ tailWord_4559500) baseStart_4559500 baseEnd_4559500 := by
    simpa [prefixWord, tailWord_4559500, baseEnd_4559500] using wordTrace_append hprefix tailTrace_4559500
  have hstable : (prefixWord ++ tailWord_4559500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559500).length < 2 ^ (prefixWord ++ tailWord_4559500).sum := by decide
  have hdescent : baseEnd_4559500 < baseStart_4559500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4559558 : List Nat := [6, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_4559558 : Nat := 118140960795 + 4559558 * 2 ^ 59
def prefixEnd_4559558 : Nat := 4983230072969 + 3 ^ 40 * 4559558 * 2
def baseEnd_4559558 : Nat := 260138314005886326895109

theorem tailTrace_4559558 : CollatzResearch.WordTrace tailWord_4559558 prefixEnd_4559558 260138314005886326895109 := by
  unfold tailWord_4559558
  simp only [CollatzResearch.WordTrace]
  refine ⟨5196898200484610979849979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 110867161610338367570132885 5196898200484610979849979)
  ·
    refine ⟨7795347300726916469774969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5196898200484610979849979 7795347300726916469774969)
    ·
      refine ⟨5846510475545187352331227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7795347300726916469774969 5846510475545187352331227)
      ·
        refine ⟨8769765713317781028496841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5846510475545187352331227 8769765713317781028496841)
        ·
          refine ⟨6577324284988335771372631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8769765713317781028496841 6577324284988335771372631)
          ·
            refine ⟨9865986427482503657058947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6577324284988335771372631 9865986427482503657058947)
            ·
              refine ⟨14798979641223755485588421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9865986427482503657058947 14798979641223755485588421)
              ·
                refine ⟨2774808682729454153547829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14798979641223755485588421 2774808682729454153547829)
                ·
                  refine ⟨260138314005886326895109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2774808682729454153547829 260138314005886326895109)
                  ·
                    rfl

theorem cell23_4559558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_4559558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4559558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4559558 prefixEnd_4559558 := by exact prefixLift 4559558
  have htrace : WordTrace (prefixWord ++ tailWord_4559558) baseStart_4559558 baseEnd_4559558 := by
    simpa [prefixWord, tailWord_4559558, baseEnd_4559558] using wordTrace_append hprefix tailTrace_4559558
  have hstable : (prefixWord ++ tailWord_4559558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4559558).length < 2 ^ (prefixWord ++ tailWord_4559558).sum := by decide
  have hdescent : baseEnd_4559558 < baseStart_4559558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4559558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
