import V185TrunkScan23Chunk1352

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8012423 : List Nat := [1, 1, 4, 2, 1, 2, 2, 10]
def baseStart_8012423 : Nat := 118140960795 + 8012423 * 2 ^ 59
def prefixEnd_8012423 : Nat := 4983230072969 + 3 ^ 40 * 8012423 * 2
def baseEnd_8012423 : Nat := 152378674301467040439409

theorem tailTrace_8012423 : CollatzResearch.WordTrace tailWord_8012423 prefixEnd_8012423 152378674301467040439409 := by
  unfold tailWord_8012423
  simp only [CollatzResearch.WordTrace]
  refine ⟨292237075051367358748593923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194824716700911572499062615 292237075051367358748593923)
  ·
    refine ⟨438355612577051038122890885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292237075051367358748593923 438355612577051038122890885)
    ·
      refine ⟨82191677358197069648042041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 438355612577051038122890885 82191677358197069648042041)
      ·
        refine ⟨61643758018647802236031531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82191677358197069648042041 61643758018647802236031531)
        ·
          refine ⟨92465637027971703354047297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61643758018647802236031531 92465637027971703354047297)
          ·
            refine ⟨69349227770978777515535473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92465637027971703354047297 69349227770978777515535473)
            ·
              refine ⟨52011920828234083136651605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69349227770978777515535473 52011920828234083136651605)
              ·
                refine ⟨152378674301467040439409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52011920828234083136651605 152378674301467040439409)
                ·
                  rfl

theorem cell23_8012423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 10].length) (baseStart_8012423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012423 prefixEnd_8012423 := by exact prefixLift 8012423
  have htrace : WordTrace (prefixWord ++ tailWord_8012423) baseStart_8012423 baseEnd_8012423 := by
    simpa [prefixWord, tailWord_8012423, baseEnd_8012423] using wordTrace_append hprefix tailTrace_8012423
  have hstable : (prefixWord ++ tailWord_8012423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012423).length < 2 ^ (prefixWord ++ tailWord_8012423).sum := by decide
  have hdescent : baseEnd_8012423 < baseStart_8012423 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012430 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6]
def baseStart_8012430 : Nat := 118140960795 + 8012430 * 2 ^ 59
def prefixEnd_8012430 : Nat := 4983230072969 + 3 ^ 40 * 8012430 * 2
def baseEnd_8012430 : Nat := 4114227800504191564476511

theorem tailTrace_8012430 : CollatzResearch.WordTrace tailWord_8012430 prefixEnd_8012430 4114227800504191564476511 := by
  unfold tailWord_8012430
  simp only [CollatzResearch.WordTrace]
  refine ⟨36529666295292749868012343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194824886908227999296065829 36529666295292749868012343)
  ·
    refine ⟨54794499442939124802018515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36529666295292749868012343 54794499442939124802018515)
    ·
      refine ⟨82191749164408687203027773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54794499442939124802018515 82191749164408687203027773)
      ·
        refine ⟨30821905936653257701135415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82191749164408687203027773 30821905936653257701135415)
        ·
          refine ⟨46232858904979886551703123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30821905936653257701135415 46232858904979886551703123)
          ·
            refine ⟨69349288357469829827554685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46232858904979886551703123 69349288357469829827554685)
            ·
              refine ⟨26005983134051186185333007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69349288357469829827554685 26005983134051186185333007)
              ·
                refine ⟨39008974701076779277999511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26005983134051186185333007 39008974701076779277999511)
                ·
                  refine ⟨58513462051615168916999267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39008974701076779277999511 58513462051615168916999267)
                  ·
                    refine ⟨87770193077422753375498901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58513462051615168916999267 87770193077422753375498901)
                    ·
                      refine ⟨4114227800504191564476511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87770193077422753375498901 4114227800504191564476511)
                      ·
                        rfl

theorem cell23_8012430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_8012430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012430 prefixEnd_8012430 := by exact prefixLift 8012430
  have htrace : WordTrace (prefixWord ++ tailWord_8012430) baseStart_8012430 baseEnd_8012430 := by
    simpa [prefixWord, tailWord_8012430, baseEnd_8012430] using wordTrace_append hprefix tailTrace_8012430
  have hstable : (prefixWord ++ tailWord_8012430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012430).length < 2 ^ (prefixWord ++ tailWord_8012430).sum := by decide
  have hdescent : baseEnd_8012430 < baseStart_8012430 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012434 : List Nat := [3, 2, 3, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_8012434 : Nat := 118140960795 + 8012434 * 2 ^ 59
def prefixEnd_8012434 : Nat := 4983230072969 + 3 ^ 40 * 8012434 * 2
def baseEnd_8012434 : Nat := 4114229854426809548826493

theorem tailTrace_8012434 : CollatzResearch.WordTrace tailWord_8012434 prefixEnd_8012434 4114229854426809548826493 := by
  unfold tailWord_8012434
  simp only [CollatzResearch.WordTrace]
  refine ⟨73059369063581876906811089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194824984169551671751496237 73059369063581876906811089)
  ·
    refine ⟨54794526797686407680108317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73059369063581876906811089 54794526797686407680108317)
    ·
      refine ⟨20547947549132402880040619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54794526797686407680108317 20547947549132402880040619)
      ·
        refine ⟨30821921323698604320060929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20547947549132402880040619 30821921323698604320060929)
        ·
          refine ⟨23116440992773953240045697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30821921323698604320060929 23116440992773953240045697)
          ·
            refine ⟨17337330744580464930034273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23116440992773953240045697 17337330744580464930034273)
            ·
              refine ⟨13002998058435348697525705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17337330744580464930034273 13002998058435348697525705)
              ·
                refine ⟨9752248543826511523144279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13002998058435348697525705 9752248543826511523144279)
                ·
                  refine ⟨14628372815739767284716419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9752248543826511523144279 14628372815739767284716419)
                  ·
                    refine ⟨21942559223609650927074629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14628372815739767284716419 21942559223609650927074629)
                    ·
                      refine ⟨4114229854426809548826493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21942559223609650927074629 4114229854426809548826493)
                      ·
                        rfl

theorem cell23_8012434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_8012434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012434 prefixEnd_8012434 := by exact prefixLift 8012434
  have htrace : WordTrace (prefixWord ++ tailWord_8012434) baseStart_8012434 baseEnd_8012434 := by
    simpa [prefixWord, tailWord_8012434, baseEnd_8012434] using wordTrace_append hprefix tailTrace_8012434
  have hstable : (prefixWord ++ tailWord_8012434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012434).length < 2 ^ (prefixWord ++ tailWord_8012434).sum := by decide
  have hdescent : baseEnd_8012434 < baseStart_8012434 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012453 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 1, 9]
def baseStart_8012453 : Nat := 118140960795 + 8012453 * 2 ^ 59
def prefixEnd_8012453 : Nat := 4983230072969 + 3 ^ 40 * 8012453 * 2
def baseEnd_8012453 : Nat := 1371413203519748324829635

theorem tailTrace_8012453 : CollatzResearch.WordTrace tailWord_8012453 prefixEnd_8012453 1371413203519748324829635 := by
  unfold tailWord_8012453
  simp only [CollatzResearch.WordTrace]
  refine ⟨292238169241258673872186013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194825446160839115914790675 292238169241258673872186013)
  ·
    refine ⟨109589313465472002702069755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292238169241258673872186013 109589313465472002702069755)
    ·
      refine ⟨164383970198208004053104633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109589313465472002702069755 164383970198208004053104633)
      ·
        refine ⟨123287977648656003039828475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164383970198208004053104633 123287977648656003039828475)
        ·
          refine ⟨184931966472984004559742713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123287977648656003039828475 184931966472984004559742713)
          ·
            refine ⟨138698974854738003419807035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184931966472984004559742713 138698974854738003419807035)
            ·
              refine ⟨208048462282107005129710553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138698974854738003419807035 208048462282107005129710553)
              ·
                refine ⟨156036346711580253847282915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208048462282107005129710553 156036346711580253847282915)
                ·
                  refine ⟨234054520067370380770924373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156036346711580253847282915 234054520067370380770924373)
                  ·
                    refine ⟨1371413203519748324829635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 234054520067370380770924373 1371413203519748324829635)
                    ·
                      rfl

theorem cell23_8012453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_8012453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012453 prefixEnd_8012453 := by exact prefixLift 8012453
  have htrace : WordTrace (prefixWord ++ tailWord_8012453) baseStart_8012453 baseEnd_8012453 := by
    simpa [prefixWord, tailWord_8012453, baseEnd_8012453] using wordTrace_append hprefix tailTrace_8012453
  have hstable : (prefixWord ++ tailWord_8012453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012453).length < 2 ^ (prefixWord ++ tailWord_8012453).sum := by decide
  have hdescent : baseEnd_8012453 < baseStart_8012453 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012467 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 4, 1, 3]
def baseStart_8012467 : Nat := 118140960795 + 8012467 * 2 ^ 59
def prefixEnd_8012467 : Nat := 4983230072969 + 3 ^ 40 * 8012467 * 2
def baseEnd_8012467 : Nat := 4114246799288407919713841

theorem tailTrace_8012467 : CollatzResearch.WordTrace tailWord_8012467 prefixEnd_8012467 4114246799288407919713841 := by
  unfold tailWord_8012467
  simp only [CollatzResearch.WordTrace]
  refine ⟨292238679863207954263195655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194825786575471969508797103 292238679863207954263195655)
  ·
    refine ⟨438358019794811931394793483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292238679863207954263195655 438358019794811931394793483)
    ·
      refine ⟨657537029692217897092190225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438358019794811931394793483 657537029692217897092190225)
      ·
        refine ⟨493152772269163422819142669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657537029692217897092190225 493152772269163422819142669)
        ·
          refine ⟨184932289600936283557178501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 493152772269163422819142669 184932289600936283557178501)
          ·
            refine ⟨34674804300175553166970969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184932289600936283557178501 34674804300175553166970969)
            ·
              refine ⟨26006103225131664875228227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34674804300175553166970969 26006103225131664875228227)
              ·
                refine ⟨39009154837697497312842341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26006103225131664875228227 39009154837697497312842341)
                ·
                  refine ⟨7314216532068280746157939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39009154837697497312842341 7314216532068280746157939)
                  ·
                    refine ⟨10971324798102421119236909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7314216532068280746157939 10971324798102421119236909)
                    ·
                      refine ⟨4114246799288407919713841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10971324798102421119236909 4114246799288407919713841)
                      ·
                        rfl

theorem cell23_8012467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 1, 3].length) (baseStart_8012467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012467 prefixEnd_8012467 := by exact prefixLift 8012467
  have htrace : WordTrace (prefixWord ++ tailWord_8012467) baseStart_8012467 baseEnd_8012467 := by
    simpa [prefixWord, tailWord_8012467, baseEnd_8012467] using wordTrace_append hprefix tailTrace_8012467
  have hstable : (prefixWord ++ tailWord_8012467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012467).length < 2 ^ (prefixWord ++ tailWord_8012467).sum := by decide
  have hdescent : baseEnd_8012467 < baseStart_8012467 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012494 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2]
def baseStart_8012494 : Nat := 118140960795 + 8012494 * 2 ^ 59
def prefixEnd_8012494 : Nat := 4983230072969 + 3 ^ 40 * 8012494 * 2
def baseEnd_8012494 : Nat := 4114260663266079314076217

theorem tailTrace_8012494 : CollatzResearch.WordTrace tailWord_8012494 prefixEnd_8012494 4114260663266079314076217 := by
  unfold tailWord_8012494
  simp only [CollatzResearch.WordTrace]
  refine ⟨36529958079263767234303567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194826443089406758582952357 36529958079263767234303567)
  ·
    refine ⟨54794937118895650851455351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36529958079263767234303567 54794937118895650851455351)
    ·
      refine ⟨82192405678343476277183027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54794937118895650851455351 82192405678343476277183027)
      ·
        refine ⟨123288608517515214415774541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82192405678343476277183027 123288608517515214415774541)
        ·
          refine ⟨46233228194068205405915453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123288608517515214415774541 46233228194068205405915453)
          ·
            refine ⟨17337460572775577027218295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46233228194068205405915453 17337460572775577027218295)
            ·
              refine ⟨26006190859163365540827443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17337460572775577027218295 26006190859163365540827443)
              ·
                refine ⟨39009286288745048311241165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26006190859163365540827443 39009286288745048311241165)
                ·
                  refine ⟨14628482358279393116715437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39009286288745048311241165 14628482358279393116715437)
                  ·
                    refine ⟨5485680884354772418768289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14628482358279393116715437 5485680884354772418768289)
                    ·
                      refine ⟨4114260663266079314076217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5485680884354772418768289 4114260663266079314076217)
                      ·
                        rfl

theorem cell23_8012494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_8012494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012494 prefixEnd_8012494 := by exact prefixLift 8012494
  have htrace : WordTrace (prefixWord ++ tailWord_8012494) baseStart_8012494 baseEnd_8012494 := by
    simpa [prefixWord, tailWord_8012494, baseEnd_8012494] using wordTrace_append hprefix tailTrace_8012494
  have hstable : (prefixWord ++ tailWord_8012494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012494).length < 2 ^ (prefixWord ++ tailWord_8012494).sum := by decide
  have hdescent : baseEnd_8012494 < baseStart_8012494 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012511 : List Nat := [1, 1, 2, 3, 2, 4, 3, 1, 1, 3, 2]
def baseStart_8012511 : Nat := 118140960795 + 8012511 * 2 ^ 59
def prefixEnd_8012511 : Nat := 4983230072969 + 3 ^ 40 * 8012511 * 2
def baseEnd_8012511 : Nat := 4114269392437205747563639

theorem tailTrace_8012511 : CollatzResearch.WordTrace tailWord_8012511 prefixEnd_8012511 4114269392437205747563639 := by
  unfold tailWord_8012511
  simp only [CollatzResearch.WordTrace]
  refine ⟨292240284675048549777797387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194826856450032366518531591 292240284675048549777797387)
  ·
    refine ⟨438360427012572824666696081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292240284675048549777797387 438360427012572824666696081)
    ·
      refine ⟨328770320259429618500022061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438360427012572824666696081 328770320259429618500022061)
      ·
        refine ⟨123288870097286106937508273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328770320259429618500022061 123288870097286106937508273)
        ·
          refine ⟨92466652572964580203131205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123288870097286106937508273 92466652572964580203131205)
          ·
            refine ⟨17337497357430858788087101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92466652572964580203131205 17337497357430858788087101)
            ·
              refine ⟨6501561509036572045532663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17337497357430858788087101 6501561509036572045532663)
              ·
                refine ⟨9752342263554858068298995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6501561509036572045532663 9752342263554858068298995)
                ·
                  refine ⟨14628513395332287102448493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9752342263554858068298995 14628513395332287102448493)
                  ·
                    refine ⟨5485692523249607663418185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14628513395332287102448493 5485692523249607663418185)
                    ·
                      refine ⟨4114269392437205747563639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5485692523249607663418185 4114269392437205747563639)
                      ·
                        rfl

theorem cell23_8012511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_8012511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012511 prefixEnd_8012511 := by exact prefixLift 8012511
  have htrace : WordTrace (prefixWord ++ tailWord_8012511) baseStart_8012511 baseEnd_8012511 := by
    simpa [prefixWord, tailWord_8012511, baseEnd_8012511] using wordTrace_append hprefix tailTrace_8012511
  have hstable : (prefixWord ++ tailWord_8012511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012511).length < 2 ^ (prefixWord ++ tailWord_8012511).sum := by decide
  have hdescent : baseEnd_8012511 < baseStart_8012511 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012562 : List Nat := [3, 2, 4, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_8012562 : Nat := 118140960795 + 8012562 * 2 ^ 59
def prefixEnd_8012562 : Nat := 4983230072969 + 3 ^ 40 * 8012562 * 2
def baseEnd_8012562 : Nat := 4114295579950585048025905

theorem tailTrace_8012562 : CollatzResearch.WordTrace tailWord_8012562 prefixEnd_8012562 4114295579950585048025905 := by
  unfold tailWord_8012562
  simp only [CollatzResearch.WordTrace]
  refine ⟨73060536199465946371975985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194828096531909190325269293 73060536199465946371975985)
  ·
    refine ⟨54795402149599459778981989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73060536199465946371975985 54795402149599459778981989)
    ·
      refine ⟨10274137903049898708559123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54795402149599459778981989 10274137903049898708559123)
      ·
        refine ⟨15411206854574848062838685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10274137903049898708559123 15411206854574848062838685)
        ·
          refine ⟨5779202570465568023564507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15411206854574848062838685 5779202570465568023564507)
          ·
            refine ⟨8668803855698352035346761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5779202570465568023564507 8668803855698352035346761)
            ·
              refine ⟨6501602891773764026510071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8668803855698352035346761 6501602891773764026510071)
              ·
                refine ⟨9752404337660646039765107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6501602891773764026510071 9752404337660646039765107)
                ·
                  refine ⟨14628606506490969059647661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9752404337660646039765107 14628606506490969059647661)
                  ·
                    refine ⟨5485727439934113397367873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14628606506490969059647661 5485727439934113397367873)
                    ·
                      refine ⟨4114295579950585048025905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5485727439934113397367873 4114295579950585048025905)
                      ·
                        rfl

theorem cell23_8012562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_8012562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012562 prefixEnd_8012562 := by exact prefixLift 8012562
  have htrace : WordTrace (prefixWord ++ tailWord_8012562) baseStart_8012562 baseEnd_8012562 := by
    simpa [prefixWord, tailWord_8012562, baseEnd_8012562] using wordTrace_append hprefix tailTrace_8012562
  have hstable : (prefixWord ++ tailWord_8012562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012562).length < 2 ^ (prefixWord ++ tailWord_8012562).sum := by decide
  have hdescent : baseEnd_8012562 < baseStart_8012562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012597 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_8012597 : Nat := 118140960795 + 8012597 * 2 ^ 59
def prefixEnd_8012597 : Nat := 4983230072969 + 3 ^ 40 * 8012597 * 2
def baseEnd_8012597 : Nat := 4114313551773492411088243

theorem tailTrace_8012597 : CollatzResearch.WordTrace tailWord_8012597 prefixEnd_8012597 4114313551773492411088243 := by
  unfold tailWord_8012597
  simp only [CollatzResearch.WordTrace]
  refine ⟨292243421352736986465428045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194828947568491324310285363 292243421352736986465428045)
  ·
    refine ⟨109591283007276369924535517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292243421352736986465428045 109591283007276369924535517)
    ·
      refine ⟨41096731127728638721700819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109591283007276369924535517 41096731127728638721700819)
      ·
        refine ⟨61645096691592958082551229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41096731127728638721700819 61645096691592958082551229)
        ·
          refine ⟨23116911259347359280956711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61645096691592958082551229 23116911259347359280956711)
          ·
            refine ⟨34675366889021038921435067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23116911259347359280956711 34675366889021038921435067)
            ·
              refine ⟨52013050333531558382152601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34675366889021038921435067 52013050333531558382152601)
              ·
                refine ⟨39009787750148668786614451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52013050333531558382152601 39009787750148668786614451)
                ·
                  refine ⟨58514681625223003179921677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39009787750148668786614451 58514681625223003179921677)
                  ·
                    refine ⟨21943005609458626192470629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58514681625223003179921677 21943005609458626192470629)
                    ·
                      refine ⟨4114313551773492411088243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21943005609458626192470629 4114313551773492411088243)
                      ·
                        rfl

theorem cell23_8012597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_8012597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012597 prefixEnd_8012597 := by exact prefixLift 8012597
  have htrace : WordTrace (prefixWord ++ tailWord_8012597) baseStart_8012597 baseEnd_8012597 := by
    simpa [prefixWord, tailWord_8012597, baseEnd_8012597] using wordTrace_append hprefix tailTrace_8012597
  have hstable : (prefixWord ++ tailWord_8012597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012597).length < 2 ^ (prefixWord ++ tailWord_8012597).sum := by decide
  have hdescent : baseEnd_8012597 < baseStart_8012597 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012617 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 1, 4, 3]
def baseStart_8012617 : Nat := 118140960795 + 8012617 * 2 ^ 59
def prefixEnd_8012617 : Nat := 4983230072969 + 3 ^ 40 * 8012617 * 2
def baseEnd_8012617 : Nat := 4114323821386582332838151

theorem tailTrace_8012617 : CollatzResearch.WordTrace tailWord_8012617 prefixEnd_8012617 4114323821386582332838151 := by
  unfold tailWord_8012617
  simp only [CollatzResearch.WordTrace]
  refine ⟨292244150812664529881156105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194829433875109686587437403 292244150812664529881156105)
  ·
    refine ⟨219183113109498397410867079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292244150812664529881156105 219183113109498397410867079)
    ·
      refine ⟨328774669664247596116300619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219183113109498397410867079 328774669664247596116300619)
      ·
        refine ⟨493162004496371394174450929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328774669664247596116300619 493162004496371394174450929)
        ·
          refine ⟨369871503372278545630838197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493162004496371394174450929 369871503372278545630838197)
          ·
            refine ⟨34675453441151113652891081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 369871503372278545630838197 34675453441151113652891081)
            ·
              refine ⟨26006590080863335239668311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34675453441151113652891081 26006590080863335239668311)
              ·
                refine ⟨39009885121295002859502467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26006590080863335239668311 39009885121295002859502467)
                ·
                  refine ⟨58514827681942504289253701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39009885121295002859502467 58514827681942504289253701)
                  ·
                    refine ⟨10971530190364219554235069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58514827681942504289253701 10971530190364219554235069)
                    ·
                      refine ⟨4114323821386582332838151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10971530190364219554235069 4114323821386582332838151)
                      ·
                        rfl

theorem cell23_8012617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 4, 3].length) (baseStart_8012617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012617 prefixEnd_8012617 := by exact prefixLift 8012617
  have htrace : WordTrace (prefixWord ++ tailWord_8012617) baseStart_8012617 baseEnd_8012617 := by
    simpa [prefixWord, tailWord_8012617, baseEnd_8012617] using wordTrace_append hprefix tailTrace_8012617
  have hstable : (prefixWord ++ tailWord_8012617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012617).length < 2 ^ (prefixWord ++ tailWord_8012617).sum := by decide
  have hdescent : baseEnd_8012617 < baseStart_8012617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012634 : List Nat := [3, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3]
def baseStart_8012634 : Nat := 118140960795 + 8012634 * 2 ^ 59
def prefixEnd_8012634 : Nat := 4983230072969 + 3 ^ 40 * 8012634 * 2
def baseEnd_8012634 : Nat := 4114332550557708766325573

theorem tailTrace_8012634 : CollatzResearch.WordTrace tailWord_8012634 prefixEnd_8012634 4114332550557708766325573 := by
  unfold tailWord_8012634
  simp only [CollatzResearch.WordTrace]
  refine ⟨73061192713400735446131239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194829847235735294523016637 73061192713400735446131239)
  ·
    refine ⟨109591789070101103169196859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73061192713400735446131239 109591789070101103169196859)
    ·
      refine ⟨164387683605151654753795289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109591789070101103169196859 164387683605151654753795289)
      ·
        refine ⟨123290762703863741065346467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164387683605151654753795289 123290762703863741065346467)
        ·
          refine ⟨184936144055795611598019701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123290762703863741065346467 184936144055795611598019701)
          ·
            refine ⟨17337763505230838587314347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184936144055795611598019701 17337763505230838587314347)
            ·
              refine ⟨26006645257846257880971521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17337763505230838587314347 26006645257846257880971521)
              ·
                refine ⟨19504983943384693410728641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26006645257846257880971521 19504983943384693410728641)
                ·
                  refine ⟨14628737957538520058046481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19504983943384693410728641 14628737957538520058046481)
                  ·
                    refine ⟨10971553468153890043534861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14628737957538520058046481 10971553468153890043534861)
                    ·
                      refine ⟨4114332550557708766325573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10971553468153890043534861 4114332550557708766325573)
                      ·
                        rfl

theorem cell23_8012634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_8012634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012634 prefixEnd_8012634 := by exact prefixLift 8012634
  have htrace : WordTrace (prefixWord ++ tailWord_8012634) baseStart_8012634 baseEnd_8012634 := by
    simpa [prefixWord, tailWord_8012634, baseEnd_8012634] using wordTrace_append hprefix tailTrace_8012634
  have hstable : (prefixWord ++ tailWord_8012634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012634).length < 2 ^ (prefixWord ++ tailWord_8012634).sum := by decide
  have hdescent : baseEnd_8012634 < baseStart_8012634 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012707 : List Nat := [1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 5]
def baseStart_8012707 : Nat := 118140960795 + 8012707 * 2 ^ 59
def prefixEnd_8012707 : Nat := 4983230072969 + 3 ^ 40 * 8012707 * 2
def baseEnd_8012707 : Nat := 4114370034645486980712737

theorem tailTrace_8012707 : CollatzResearch.WordTrace tailWord_8012707 prefixEnd_8012707 4114370034645486980712737 := by
  unfold tailWord_8012707
  simp only [CollatzResearch.WordTrace]
  refine ⟨292247433382338475251932375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194831622254892316834621583 292247433382338475251932375)
  ·
    refine ⟨438371150073507712877898563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292247433382338475251932375 438371150073507712877898563)
    ·
      refine ⟨657556725110261569316847845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438371150073507712877898563 657556725110261569316847845)
      ·
        refine ⟨123291885958174044246908971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 657556725110261569316847845 123291885958174044246908971)
        ·
          refine ⟨184937828937261066370363457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123291885958174044246908971 184937828937261066370363457)
          ·
            refine ⟨138703371702945799777772593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184937828937261066370363457 138703371702945799777772593)
            ·
              refine ⟨104027528777209349833329445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138703371702945799777772593 104027528777209349833329445)
              ·
                refine ⟨19505161645726753093749271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104027528777209349833329445 19505161645726753093749271)
                ·
                  refine ⟨29257742468590129640623907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19505161645726753093749271 29257742468590129640623907)
                  ·
                    refine ⟨43886613702885194460935861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29257742468590129640623907 43886613702885194460935861)
                    ·
                      refine ⟨4114370034645486980712737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43886613702885194460935861 4114370034645486980712737)
                      ·
                        rfl

theorem cell23_8012707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_8012707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012707 prefixEnd_8012707 := by exact prefixLift 8012707
  have htrace : WordTrace (prefixWord ++ tailWord_8012707) baseStart_8012707 baseEnd_8012707 := by
    simpa [prefixWord, tailWord_8012707, baseEnd_8012707] using wordTrace_append hprefix tailTrace_8012707
  have hstable : (prefixWord ++ tailWord_8012707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012707).length < 2 ^ (prefixWord ++ tailWord_8012707).sum := by decide
  have hdescent : baseEnd_8012707 < baseStart_8012707 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012734 : List Nat := [4, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_8012734 : Nat := 118140960795 + 8012734 * 2 ^ 59
def prefixEnd_8012734 : Nat := 4983230072969 + 3 ^ 40 * 8012734 * 2
def baseEnd_8012734 : Nat := 4114383898623158375075113

theorem tailTrace_8012734 : CollatzResearch.WordTrace tailWord_8012734 prefixEnd_8012734 4114383898623158375075113 := by
  unfold tailWord_8012734
  simp only [CollatzResearch.WordTrace]
  refine ⟨36531052269155082357895657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194832278768827105908776837 36531052269155082357895657)
  ·
    refine ⟨27398289201866311768421743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36531052269155082357895657 27398289201866311768421743)
    ·
      refine ⟨41097433802799467652632615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27398289201866311768421743 41097433802799467652632615)
      ·
        refine ⟨61646150704199201478948923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41097433802799467652632615 61646150704199201478948923)
        ·
          refine ⟨92469226056298802218423385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61646150704199201478948923 92469226056298802218423385)
          ·
            refine ⟨69351919542224101663817539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92469226056298802218423385 69351919542224101663817539)
            ·
              refine ⟨104027879313336152495726309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69351919542224101663817539 104027879313336152495726309)
              ·
                refine ⟨19505227371250528592948683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104027879313336152495726309 19505227371250528592948683)
                ·
                  refine ⟨29257841056875792889423025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19505227371250528592948683 29257841056875792889423025)
                  ·
                    refine ⟨21943380792656844667067269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29257841056875792889423025 21943380792656844667067269)
                    ·
                      refine ⟨4114383898623158375075113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21943380792656844667067269 4114383898623158375075113)
                      ·
                        rfl

theorem cell23_8012734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_8012734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012734 prefixEnd_8012734 := by exact prefixLift 8012734
  have htrace : WordTrace (prefixWord ++ tailWord_8012734) baseStart_8012734 baseEnd_8012734 := by
    simpa [prefixWord, tailWord_8012734, baseEnd_8012734] using wordTrace_append hprefix tailTrace_8012734
  have hstable : (prefixWord ++ tailWord_8012734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012734).length < 2 ^ (prefixWord ++ tailWord_8012734).sum := by decide
  have hdescent : baseEnd_8012734 < baseStart_8012734 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012832 : List Nat := [2, 1, 1, 7, 1, 2, 1, 2, 1, 3, 2]
def baseStart_8012832 : Nat := 118140960795 + 8012832 * 2 ^ 59
def prefixEnd_8012832 : Nat := 4983230072969 + 3 ^ 40 * 8012832 * 2
def baseEnd_8012832 : Nat := 4114434219727298991649663

theorem tailTrace_8012832 : CollatzResearch.WordTrace tailWord_8012832 prefixEnd_8012832 4114434219727298991649663 := by
  unfold tailWord_8012832
  simp only [CollatzResearch.WordTrace]
  refine ⟨146125996253442810800116375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194834661671257081066821833 146125996253442810800116375)
  ·
    refine ⟨219188994380164216200174563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146125996253442810800116375 219188994380164216200174563)
    ·
      refine ⟨328783491570246324300261845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219188994380164216200174563 328783491570246324300261845)
      ·
        refine ⟨7705863083677648225787387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 328783491570246324300261845 7705863083677648225787387)
        ·
          refine ⟨11558794625516472338681081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7705863083677648225787387 11558794625516472338681081)
          ·
            refine ⟨8669095969137354254010811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11558794625516472338681081 8669095969137354254010811)
            ·
              refine ⟨13003643953706031381016217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8669095969137354254010811 13003643953706031381016217)
              ·
                refine ⟨9752732965279523535762163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13003643953706031381016217 9752732965279523535762163)
                ·
                  refine ⟨14629099447919285303643245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9752732965279523535762163 14629099447919285303643245)
                  ·
                    refine ⟨5485912292969731988866217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14629099447919285303643245 5485912292969731988866217)
                    ·
                      refine ⟨4114434219727298991649663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5485912292969731988866217 4114434219727298991649663)
                      ·
                        rfl

theorem cell23_8012832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_8012832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012832 prefixEnd_8012832 := by exact prefixLift 8012832
  have htrace : WordTrace (prefixWord ++ tailWord_8012832) baseStart_8012832 baseEnd_8012832 := by
    simpa [prefixWord, tailWord_8012832, baseEnd_8012832] using wordTrace_append hprefix tailTrace_8012832
  have hstable : (prefixWord ++ tailWord_8012832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012832).length < 2 ^ (prefixWord ++ tailWord_8012832).sum := by decide
  have hdescent : baseEnd_8012832 < baseStart_8012832 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012847 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 5, 7]
def baseStart_8012847 : Nat := 118140960795 + 8012847 * 2 ^ 59
def prefixEnd_8012847 : Nat := 4983230072969 + 3 ^ 40 * 8012847 * 2
def baseEnd_8012847 : Nat := 1371480640645705477654031

theorem tailTrace_8012847 : CollatzResearch.WordTrace tailWord_8012847 prefixEnd_8012847 1371480640645705477654031 := by
  unfold tailWord_8012847
  simp only [CollatzResearch.WordTrace]
  refine ⟨292252539601831279162028795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194835026401220852774685863 292252539601831279162028795)
  ·
    refine ⟨438378809402746918743043193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292252539601831279162028795 438378809402746918743043193)
    ·
      refine ⟨328784107052060189057282395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438378809402746918743043193 328784107052060189057282395)
      ·
        refine ⟨493176160578090283585923593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328784107052060189057282395 493176160578090283585923593)
        ·
          refine ⟨369882120433567712689442695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493176160578090283585923593 369882120433567712689442695)
          ·
            refine ⟨554823180650351569034164043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369882120433567712689442695 554823180650351569034164043)
            ·
              refine ⟨832234770975527353551246065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554823180650351569034164043 832234770975527353551246065)
              ·
                refine ⟨624176078231645515163434549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 832234770975527353551246065 624176078231645515163434549)
                ·
                  refine ⟨58516507334216767046571989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 624176078231645515163434549 58516507334216767046571989)
                  ·
                    refine ⟨1371480640645705477654031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58516507334216767046571989 1371480640645705477654031)
                    ·
                      rfl

theorem cell23_8012847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 7].length) (baseStart_8012847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012847 prefixEnd_8012847 := by exact prefixLift 8012847
  have htrace : WordTrace (prefixWord ++ tailWord_8012847) baseStart_8012847 baseEnd_8012847 := by
    simpa [prefixWord, tailWord_8012847, baseEnd_8012847] using wordTrace_append hprefix tailTrace_8012847
  have hstable : (prefixWord ++ tailWord_8012847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012847).length < 2 ^ (prefixWord ++ tailWord_8012847).sum := by decide
  have hdescent : baseEnd_8012847 < baseStart_8012847 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012862 : List Nat := [4, 2, 1, 3, 1, 2, 2, 2, 2, 2, 2]
def baseStart_8012862 : Nat := 118140960795 + 8012862 * 2 ^ 59
def prefixEnd_8012862 : Nat := 4983230072969 + 3 ^ 40 * 8012862 * 2
def baseEnd_8012862 : Nat := 4114449624146933874274525

theorem tailTrace_8012862 : CollatzResearch.WordTrace tailWord_8012862 prefixEnd_8012862 4114449624146933874274525 := by
  unfold tailWord_8012862
  simp only [CollatzResearch.WordTrace]
  refine ⟨36531635837097117090478105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194835391131184624482549893 36531635837097117090478105)
  ·
    refine ⟨27398726877822837817858579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36531635837097117090478105 27398726877822837817858579)
    ·
      refine ⟨41098090316734256726787869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27398726877822837817858579 41098090316734256726787869)
      ·
        refine ⟨15411783868775346272545451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41098090316734256726787869 15411783868775346272545451)
        ·
          refine ⟨23117675803163019408818177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15411783868775346272545451 23117675803163019408818177)
          ·
            refine ⟨17338256852372264556613633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23117675803163019408818177 17338256852372264556613633)
            ·
              refine ⟨13003692639279198417460225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17338256852372264556613633 13003692639279198417460225)
              ·
                refine ⟨9752769479459398813095169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13003692639279198417460225 9752769479459398813095169)
                ·
                  refine ⟨7314577109594549109821377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9752769479459398813095169 7314577109594549109821377)
                  ·
                    refine ⟨5485932832195911832366033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7314577109594549109821377 5485932832195911832366033)
                    ·
                      refine ⟨4114449624146933874274525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5485932832195911832366033 4114449624146933874274525)
                      ·
                        rfl

theorem cell23_8012862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_8012862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012862 prefixEnd_8012862 := by exact prefixLift 8012862
  have htrace : WordTrace (prefixWord ++ tailWord_8012862) baseStart_8012862 baseEnd_8012862 := by
    simpa [prefixWord, tailWord_8012862, baseEnd_8012862] using wordTrace_append hprefix tailTrace_8012862
  have hstable : (prefixWord ++ tailWord_8012862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012862).length < 2 ^ (prefixWord ++ tailWord_8012862).sum := by decide
  have hdescent : baseEnd_8012862 < baseStart_8012862 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012864 : List Nat := [2, 1, 1, 2, 2, 3, 1, 4, 2, 5]
def baseStart_8012864 : Nat := 118140960795 + 8012864 * 2 ^ 59
def prefixEnd_8012864 : Nat := 4983230072969 + 3 ^ 40 * 8012864 * 2
def baseEnd_8012864 : Nat := 1371483550369414288816505

theorem tailTrace_8012864 : CollatzResearch.WordTrace tailWord_8012864 prefixEnd_8012864 1371483550369414288816505 := by
  unfold tailWord_8012864
  simp only [CollatzResearch.WordTrace]
  refine ⟨146126579821384845532698823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194835439761846460710265097 146126579821384845532698823)
  ·
    refine ⟨219189869732077268299048235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146126579821384845532698823 219189869732077268299048235)
    ·
      refine ⟨328784804598115902448572353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219189869732077268299048235 328784804598115902448572353)
      ·
        refine ⟨246588603448586926836429265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328784804598115902448572353 246588603448586926836429265)
        ·
          refine ⟨184941452586440195127321949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246588603448586926836429265 184941452586440195127321949)
          ·
            refine ⟨69353044719915073172745731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184941452586440195127321949 69353044719915073172745731)
            ·
              refine ⟨104029567079872609759118597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69353044719915073172745731 104029567079872609759118597)
              ·
                refine ⟨19505543827476114329834737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104029567079872609759118597 19505543827476114329834737)
                ·
                  refine ⟨14629157870607085747376053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19505543827476114329834737 14629157870607085747376053)
                  ·
                    refine ⟨1371483550369414288816505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14629157870607085747376053 1371483550369414288816505)
                    ·
                      rfl

theorem cell23_8012864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 2, 5].length) (baseStart_8012864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012864 prefixEnd_8012864 := by exact prefixLift 8012864
  have htrace : WordTrace (prefixWord ++ tailWord_8012864) baseStart_8012864 baseEnd_8012864 := by
    simpa [prefixWord, tailWord_8012864, baseEnd_8012864] using wordTrace_append hprefix tailTrace_8012864
  have hstable : (prefixWord ++ tailWord_8012864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012864).length < 2 ^ (prefixWord ++ tailWord_8012864).sum := by decide
  have hdescent : baseEnd_8012864 < baseStart_8012864 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012871 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 2, 5, 2]
def baseStart_8012871 : Nat := 118140960795 + 8012871 * 2 ^ 59
def prefixEnd_8012871 : Nat := 4983230072969 + 3 ^ 40 * 8012871 * 2
def baseEnd_8012871 : Nat := 4114454245472824339061983

theorem tailTrace_8012871 : CollatzResearch.WordTrace tailWord_8012871 prefixEnd_8012871 4114454245472824339061983 := by
  unfold tailWord_8012871
  simp only [CollatzResearch.WordTrace]
  refine ⟨292253414953744331260902467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194835609969162887507268311 292253414953744331260902467)
  ·
    refine ⟨438380122430616496891353701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292253414953744331260902467 438380122430616496891353701)
    ·
      refine ⟨82196272955740593167128819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 438380122430616496891353701 82196272955740593167128819)
      ·
        refine ⟨123294409433610889750693229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82196272955740593167128819 123294409433610889750693229)
        ·
          refine ⟨46235403537604083656509961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123294409433610889750693229 46235403537604083656509961)
          ·
            refine ⟨34676552653203062742382471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46235403537604083656509961 34676552653203062742382471)
            ·
              refine ⟨52014828979804594113573707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34676552653203062742382471 52014828979804594113573707)
              ·
                refine ⟨78022243469706891170360561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52014828979804594113573707 78022243469706891170360561)
                ·
                  refine ⟨58516682602280168377770421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78022243469706891170360561 58516682602280168377770421)
                  ·
                    refine ⟨5485938993963765785415977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58516682602280168377770421 5485938993963765785415977)
                    ·
                      refine ⟨4114454245472824339061983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5485938993963765785415977 4114454245472824339061983)
                      ·
                        rfl

theorem cell23_8012871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_8012871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012871 prefixEnd_8012871 := by exact prefixLift 8012871
  have htrace : WordTrace (prefixWord ++ tailWord_8012871) baseStart_8012871 baseEnd_8012871 := by
    simpa [prefixWord, tailWord_8012871, baseEnd_8012871] using wordTrace_append hprefix tailTrace_8012871
  have hstable : (prefixWord ++ tailWord_8012871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012871).length < 2 ^ (prefixWord ++ tailWord_8012871).sum := by decide
  have hdescent : baseEnd_8012871 < baseStart_8012871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012874 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 1, 2, 5]
def baseStart_8012874 : Nat := 118140960795 + 8012874 * 2 ^ 59
def prefixEnd_8012874 : Nat := 4983230072969 + 3 ^ 40 * 8012874 * 2
def baseEnd_8012874 : Nat := 4114455785914787827324469

theorem tailTrace_8012874 : CollatzResearch.WordTrace tailWord_8012874 prefixEnd_8012874 4114455785914787827324469 := by
  unfold tailWord_8012874
  simp only [CollatzResearch.WordTrace]
  refine ⟨73063381093183365693315419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194835682915155641848841117 73063381093183365693315419)
  ·
    refine ⟨109595071639775048539973129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73063381093183365693315419 109595071639775048539973129)
    ·
      refine ⟨82196303729831286404979847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109595071639775048539973129 82196303729831286404979847)
      ·
        refine ⟨123294455594746929607469771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82196303729831286404979847 123294455594746929607469771)
        ·
          refine ⟨184941683392120394411204657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123294455594746929607469771 184941683392120394411204657)
          ·
            refine ⟨138706262544090295808403493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184941683392120394411204657 138706262544090295808403493)
            ·
              refine ⟨26007424227016930464075655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138706262544090295808403493 26007424227016930464075655)
              ·
                refine ⟨39011136340525395696113483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26007424227016930464075655 39011136340525395696113483)
                ·
                  refine ⟨58516704510788093544170225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39011136340525395696113483 58516704510788093544170225)
                  ·
                    refine ⟨43887528383091070158127669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58516704510788093544170225 43887528383091070158127669)
                    ·
                      refine ⟨4114455785914787827324469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43887528383091070158127669 4114455785914787827324469)
                      ·
                        rfl

theorem cell23_8012874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_8012874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012874 prefixEnd_8012874 := by exact prefixLift 8012874
  have htrace : WordTrace (prefixWord ++ tailWord_8012874) baseStart_8012874 baseEnd_8012874 := by
    simpa [prefixWord, tailWord_8012874, baseEnd_8012874] using wordTrace_append hprefix tailTrace_8012874
  have hstable : (prefixWord ++ tailWord_8012874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012874).length < 2 ^ (prefixWord ++ tailWord_8012874).sum := by decide
  have hdescent : baseEnd_8012874 < baseStart_8012874 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012898 : List Nat := [3, 3, 2, 2, 1, 1, 3, 1, 2, 5]
def baseStart_8012898 : Nat := 118140960795 + 8012898 * 2 ^ 59
def prefixEnd_8012898 : Nat := 4983230072969 + 3 ^ 40 * 8012898 * 2
def baseEnd_8012898 : Nat := 1371489369816831911141453

theorem tailTrace_8012898 : CollatzResearch.WordTrace tailWord_8012898 prefixEnd_8012898 1371489369816831911141453 := by
  unfold tailWord_8012898
  simp only [CollatzResearch.WordTrace]
  refine ⟨73063599931161628718033837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194836266483097676581423565 73063599931161628718033837)
  ·
    refine ⟨27398849974185610769262689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73063599931161628718033837 27398849974185610769262689)
    ·
      refine ⟨20549137480639208076947017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27398849974185610769262689 20549137480639208076947017)
      ·
        refine ⟨15411853110479406057710263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20549137480639208076947017 15411853110479406057710263)
        ·
          refine ⟨23117779665719109086565395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15411853110479406057710263 23117779665719109086565395)
          ·
            refine ⟨34676669498578663629848093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23117779665719109086565395 34676669498578663629848093)
            ·
              refine ⟨13003751061966998861193035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34676669498578663629848093 13003751061966998861193035)
              ·
                refine ⟨19505626592950498291789553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13003751061966998861193035 19505626592950498291789553)
                ·
                  refine ⟨14629219944712873718842165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19505626592950498291789553 14629219944712873718842165)
                  ·
                    refine ⟨1371489369816831911141453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14629219944712873718842165 1371489369816831911141453)
                    ·
                      rfl

theorem cell23_8012898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_8012898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012898 prefixEnd_8012898 := by exact prefixLift 8012898
  have htrace : WordTrace (prefixWord ++ tailWord_8012898) baseStart_8012898 baseEnd_8012898 := by
    simpa [prefixWord, tailWord_8012898, baseEnd_8012898] using wordTrace_append hprefix tailTrace_8012898
  have hstable : (prefixWord ++ tailWord_8012898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012898).length < 2 ^ (prefixWord ++ tailWord_8012898).sum := by decide
  have hdescent : baseEnd_8012898 < baseStart_8012898 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012901 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 1, 6, 2]
def baseStart_8012901 : Nat := 118140960795 + 8012901 * 2 ^ 59
def prefixEnd_8012901 : Nat := 4983230072969 + 3 ^ 40 * 8012901 * 2
def baseEnd_8012901 : Nat := 4114469649892459221686845

theorem tailTrace_8012901 : CollatzResearch.WordTrace tailWord_8012901 prefixEnd_8012901 4114469649892459221686845 := by
  unfold tailWord_8012901
  simp only [CollatzResearch.WordTrace]
  refine ⟨292254509143635646384494557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194836339429090430922996371 292254509143635646384494557)
  ·
    refine ⟨109595440928863367394185459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292254509143635646384494557 109595440928863367394185459)
    ·
      refine ⟨164393161393295051091278189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109595440928863367394185459 164393161393295051091278189)
      ·
        refine ⟨61647435522485644159229321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164393161393295051091278189 61647435522485644159229321)
        ·
          refine ⟨46235576641864233119421991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61647435522485644159229321 46235576641864233119421991)
          ·
            refine ⟨69353364962796349679132987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46235576641864233119421991 69353364962796349679132987)
            ·
              refine ⟨104030047444194524518699481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69353364962796349679132987 104030047444194524518699481)
              ·
                refine ⟨78022535583145893389024611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104030047444194524518699481 78022535583145893389024611)
                ·
                  refine ⟨117033803374718840083536917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78022535583145893389024611 117033803374718840083536917)
                  ·
                    refine ⟨5485959533189945628915793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117033803374718840083536917 5485959533189945628915793)
                    ·
                      refine ⟨4114469649892459221686845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5485959533189945628915793 4114469649892459221686845)
                      ·
                        rfl

theorem cell23_8012901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_8012901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012901 prefixEnd_8012901 := by exact prefixLift 8012901
  have htrace : WordTrace (prefixWord ++ tailWord_8012901) baseStart_8012901 baseEnd_8012901 := by
    simpa [prefixWord, tailWord_8012901, baseEnd_8012901] using wordTrace_append hprefix tailTrace_8012901
  have hstable : (prefixWord ++ tailWord_8012901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012901).length < 2 ^ (prefixWord ++ tailWord_8012901).sum := by decide
  have hdescent : baseEnd_8012901 < baseStart_8012901 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012914 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_8012914 : Nat := 118140960795 + 8012914 * 2 ^ 59
def prefixEnd_8012914 : Nat := 4983230072969 + 3 ^ 40 * 8012914 * 2
def baseEnd_8012914 : Nat := 4114476325140967670824285

theorem tailTrace_8012914 : CollatzResearch.WordTrace tailWord_8012914 prefixEnd_8012914 4114476325140967670824285 := by
  unfold tailWord_8012914
  simp only [CollatzResearch.WordTrace]
  refine ⟨73063745823147137401179449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194836655528392366403145197 73063745823147137401179449)
  ·
    refine ⟨54797809367360353050884587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73063745823147137401179449 54797809367360353050884587)
    ·
      refine ⟨82196714051040529576326881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54797809367360353050884587 82196714051040529576326881)
      ·
        refine ⟨61647535538280397182245161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82196714051040529576326881 61647535538280397182245161)
        ·
          refine ⟨46235651653710297886683871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61647535538280397182245161 46235651653710297886683871)
          ·
            refine ⟨69353477480565446830025807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46235651653710297886683871 69353477480565446830025807)
            ·
              refine ⟨104030216220848170245038711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69353477480565446830025807 104030216220848170245038711)
              ·
                refine ⟨156045324331272255367558067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104030216220848170245038711 156045324331272255367558067)
                ·
                  refine ⟨234067986496908383051337101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156045324331272255367558067 234067986496908383051337101)
                  ·
                    refine ⟨87775494936340643644251413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 234067986496908383051337101 87775494936340643644251413)
                    ·
                      refine ⟨4114476325140967670824285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87775494936340643644251413 4114476325140967670824285)
                      ·
                        rfl

theorem cell23_8012914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_8012914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012914 prefixEnd_8012914 := by exact prefixLift 8012914
  have htrace : WordTrace (prefixWord ++ tailWord_8012914) baseStart_8012914 baseEnd_8012914 := by
    simpa [prefixWord, tailWord_8012914, baseEnd_8012914] using wordTrace_append hprefix tailTrace_8012914
  have hstable : (prefixWord ++ tailWord_8012914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012914).length < 2 ^ (prefixWord ++ tailWord_8012914).sum := by decide
  have hdescent : baseEnd_8012914 < baseStart_8012914 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012918 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2]
def baseStart_8012918 : Nat := 118140960795 + 8012918 * 2 ^ 59
def prefixEnd_8012918 : Nat := 4983230072969 + 3 ^ 40 * 8012918 * 2
def baseEnd_8012918 : Nat := 4114478379063585655174267

theorem tailTrace_8012918 : CollatzResearch.WordTrace tailWord_8012918 prefixEnd_8012918 4114478379063585655174267 := by
  unfold tailWord_8012918
  simp only [CollatzResearch.WordTrace]
  refine ⟨18265945574035878642991463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194836752789716038858575605 18265945574035878642991463)
  ·
    refine ⟨27398918361053817964487195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18265945574035878642991463 27398918361053817964487195)
    ·
      refine ⟨41098377541580726946730793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27398918361053817964487195 41098377541580726946730793)
      ·
        refine ⟨30823783156185545210048095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41098377541580726946730793 30823783156185545210048095)
        ·
          refine ⟨46235674734278317815072143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30823783156185545210048095 46235674734278317815072143)
          ·
            refine ⟨69353512101417476722608215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46235674734278317815072143 69353512101417476722608215)
            ·
              refine ⟨104030268152126215083912323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69353512101417476722608215 104030268152126215083912323)
              ·
                refine ⟨156045402228189322625868485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104030268152126215083912323 156045402228189322625868485)
                ·
                  refine ⟨29258512917785497992350341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156045402228189322625868485 29258512917785497992350341)
                  ·
                    refine ⟨5485971172084780873565689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29258512917785497992350341 5485971172084780873565689)
                    ·
                      refine ⟨4114478379063585655174267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5485971172084780873565689 4114478379063585655174267)
                      ·
                        rfl

theorem cell23_8012918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_8012918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012918 prefixEnd_8012918 := by exact prefixLift 8012918
  have htrace : WordTrace (prefixWord ++ tailWord_8012918) baseStart_8012918 baseEnd_8012918 := by
    simpa [prefixWord, tailWord_8012918, baseEnd_8012918] using wordTrace_append hprefix tailTrace_8012918
  have hstable : (prefixWord ++ tailWord_8012918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012918).length < 2 ^ (prefixWord ++ tailWord_8012918).sum := by decide
  have hdescent : baseEnd_8012918 < baseStart_8012918 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012924 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 8]
def baseStart_8012924 : Nat := 118140960795 + 8012924 * 2 ^ 59
def prefixEnd_8012924 : Nat := 4983230072969 + 3 ^ 40 * 8012924 * 2
def baseEnd_8012924 : Nat := 457164606660834736855471

theorem tailTrace_8012924 : CollatzResearch.WordTrace tailWord_8012924 prefixEnd_8012924 457164606660834736855471 := by
  unfold tailWord_8012924
  simp only [CollatzResearch.WordTrace]
  refine ⟨146127674011276160656290913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194836898681701547541721217 146127674011276160656290913)
  ·
    refine ⟨109595755508457120492218185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146127674011276160656290913 109595755508457120492218185)
    ·
      refine ⟨82196816631342840369163639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109595755508457120492218185 82196816631342840369163639)
      ·
        refine ⟨123295224947014260553745459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82196816631342840369163639 123295224947014260553745459)
        ·
          refine ⟨184942837420521390830618189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123295224947014260553745459 184942837420521390830618189)
          ·
            refine ⟨69353564032695521561481821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184942837420521390830618189 69353564032695521561481821)
            ·
              refine ⟨26007586512260820585555683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69353564032695521561481821 26007586512260820585555683)
              ·
                refine ⟨39011379768391230878333525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26007586512260820585555683 39011379768391230878333525)
                ·
                  refine ⟨457164606660834736855471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39011379768391230878333525 457164606660834736855471)
                  ·
                    rfl

theorem cell23_8012924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 8].length) (baseStart_8012924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012924 prefixEnd_8012924 := by exact prefixLift 8012924
  have htrace : WordTrace (prefixWord ++ tailWord_8012924) baseStart_8012924 baseEnd_8012924 := by
    simpa [prefixWord, tailWord_8012924, baseEnd_8012924] using wordTrace_append hprefix tailTrace_8012924
  have hstable : (prefixWord ++ tailWord_8012924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012924).length < 2 ^ (prefixWord ++ tailWord_8012924).sum := by decide
  have hdescent : baseEnd_8012924 < baseStart_8012924 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012928 : List Nat := [2, 1, 1, 2, 1, 3, 4, 4, 1, 4]
def baseStart_8012928 : Nat := 118140960795 + 8012928 * 2 ^ 59
def prefixEnd_8012928 : Nat := 4983230072969 + 3 ^ 40 * 8012928 * 2
def baseEnd_8012928 : Nat := 1371494504623376872016407

theorem tailTrace_8012928 : CollatzResearch.WordTrace tailWord_8012928 prefixEnd_8012928 1371494504623376872016407 := by
  unfold tailWord_8012928
  simp only [CollatzResearch.WordTrace]
  refine ⟨146127746957268914997863719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194836995943025219997151625 146127746957268914997863719)
  ·
    refine ⟨219191620435903372496795579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146127746957268914997863719 219191620435903372496795579)
    ·
      refine ⟨328787430653855058745193369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219191620435903372496795579 328787430653855058745193369)
      ·
        refine ⟨246590572990391294058895027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328787430653855058745193369 246590572990391294058895027)
        ·
          refine ⟨369885859485586941088342541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246590572990391294058895027 369885859485586941088342541)
          ·
            refine ⟨138707197307095102908128453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369885859485586941088342541 138707197307095102908128453)
            ·
              refine ⟨26007599495080331795274085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138707197307095102908128453 26007599495080331795274085)
              ·
                refine ⟨4876424905327562211613891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26007599495080331795274085 4876424905327562211613891)
                ·
                  refine ⟨7314637357991343317420837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4876424905327562211613891 7314637357991343317420837)
                  ·
                    refine ⟨1371494504623376872016407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7314637357991343317420837 1371494504623376872016407)
                    ·
                      rfl

theorem cell23_8012928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 1, 4].length) (baseStart_8012928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012928 prefixEnd_8012928 := by exact prefixLift 8012928
  have htrace : WordTrace (prefixWord ++ tailWord_8012928) baseStart_8012928 baseEnd_8012928 := by
    simpa [prefixWord, tailWord_8012928, baseEnd_8012928] using wordTrace_append hprefix tailTrace_8012928
  have hstable : (prefixWord ++ tailWord_8012928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012928).length < 2 ^ (prefixWord ++ tailWord_8012928).sum := by decide
  have hdescent : baseEnd_8012928 < baseStart_8012928 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012978 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2]
def baseStart_8012978 : Nat := 118140960795 + 8012978 * 2 ^ 59
def prefixEnd_8012978 : Nat := 4983230072969 + 3 ^ 40 * 8012978 * 2
def baseEnd_8012978 : Nat := 4114509187902855420423991

theorem tailTrace_8012978 : CollatzResearch.WordTrace tailWord_8012978 prefixEnd_8012978 4114509187902855420423991 := by
  unfold tailWord_8012978
  simp only [CollatzResearch.WordTrace]
  refine ⟨73064329391089172133761897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194838211709571125690031725 73064329391089172133761897)
  ·
    refine ⟨54798247043316879100321423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73064329391089172133761897 54798247043316879100321423)
    ·
      refine ⟨82197370564975318650482135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54798247043316879100321423 82197370564975318650482135)
      ·
        refine ⟨123296055847462977975723203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82197370564975318650482135 123296055847462977975723203)
        ·
          refine ⟨184944083771194466963584805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123296055847462977975723203 184944083771194466963584805)
          ·
            refine ⟨34677015707098962555672151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184944083771194466963584805 34677015707098962555672151)
            ·
              refine ⟨52015523560648443833508227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34677015707098962555672151 52015523560648443833508227)
              ·
                refine ⟨78023285340972665750262341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52015523560648443833508227 78023285340972665750262341)
                ·
                  refine ⟨14629366001432374828174189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78023285340972665750262341 14629366001432374828174189)
                  ·
                    refine ⟨5486012250537140560565321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14629366001432374828174189 5486012250537140560565321)
                    ·
                      refine ⟨4114509187902855420423991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5486012250537140560565321 4114509187902855420423991)
                      ·
                        rfl

theorem cell23_8012978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_8012978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012978 prefixEnd_8012978 := by exact prefixLift 8012978
  have htrace : WordTrace (prefixWord ++ tailWord_8012978) baseStart_8012978 baseEnd_8012978 := by
    simpa [prefixWord, tailWord_8012978, baseEnd_8012978] using wordTrace_append hprefix tailTrace_8012978
  have hstable : (prefixWord ++ tailWord_8012978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012978).length < 2 ^ (prefixWord ++ tailWord_8012978).sum := by decide
  have hdescent : baseEnd_8012978 < baseStart_8012978 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012984 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 5, 6]
def baseStart_8012984 : Nat := 118140960795 + 8012984 * 2 ^ 59
def prefixEnd_8012984 : Nat := 4983230072969 + 3 ^ 40 * 8012984 * 2
def baseEnd_8012984 : Nat := 1371504089595594132316321

theorem tailTrace_8012984 : CollatzResearch.WordTrace tailWord_8012984 prefixEnd_8012984 1371504089595594132316321 := by
  unfold tailWord_8012984
  simp only [CollatzResearch.WordTrace]
  refine ⟨146128768201167475779883003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194838357601556634373177337 146128768201167475779883003)
  ·
    refine ⟨219193152301751213669824505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146128768201167475779883003 219193152301751213669824505)
    ·
      refine ⟨164394864226313410252368379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219193152301751213669824505 164394864226313410252368379)
      ·
        refine ⟨246592296339470115378552569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164394864226313410252368379 246592296339470115378552569)
        ·
          refine ⟨184944222254602586533914427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246592296339470115378552569 184944222254602586533914427)
          ·
            refine ⟨277416333381903879800871641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184944222254602586533914427 277416333381903879800871641)
            ·
              refine ⟨208062250036427909850653731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277416333381903879800871641 208062250036427909850653731)
              ·
                refine ⟨312093375054641864775980597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208062250036427909850653731 312093375054641864775980597)
                ·
                  refine ⟨29258753911372674822748181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 312093375054641864775980597 29258753911372674822748181)
                  ·
                    refine ⟨1371504089595594132316321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29258753911372674822748181 1371504089595594132316321)
                    ·
                      rfl

theorem cell23_8012984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_8012984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012984 prefixEnd_8012984 := by exact prefixLift 8012984
  have htrace : WordTrace (prefixWord ++ tailWord_8012984) baseStart_8012984 baseEnd_8012984 := by
    simpa [prefixWord, tailWord_8012984, baseEnd_8012984] using wordTrace_append hprefix tailTrace_8012984
  have hstable : (prefixWord ++ tailWord_8012984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012984).length < 2 ^ (prefixWord ++ tailWord_8012984).sum := by decide
  have hdescent : baseEnd_8012984 < baseStart_8012984 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012985 : List Nat := [1, 2, 1, 4, 1, 5, 1, 1, 3, 1, 3]
def baseStart_8012985 : Nat := 118140960795 + 8012985 * 2 ^ 59
def prefixEnd_8012985 : Nat := 4983230072969 + 3 ^ 40 * 8012985 * 2
def baseEnd_8012985 : Nat := 4114512782267436893036459

theorem tailTrace_8012985 : CollatzResearch.WordTrace tailWord_8012985 prefixEnd_8012985 4114512782267436893036459 := by
  unfold tailWord_8012985
  simp only [CollatzResearch.WordTrace]
  refine ⟨292257572875331328730552409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194838381916887552487034939 292257572875331328730552409)
  ·
    refine ⟨219193179656498496547914307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292257572875331328730552409 219193179656498496547914307)
    ·
      refine ⟨328789769484747744821871461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219193179656498496547914307 328789769484747744821871461)
      ·
        refine ⟨61648081778390202154100899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328789769484747744821871461 61648081778390202154100899)
        ·
          refine ⟨92472122667585303231151349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61648081778390202154100899 92472122667585303231151349)
          ·
            refine ⟨8669261500086122177920439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92472122667585303231151349 8669261500086122177920439)
            ·
              refine ⟨13003892250129183266880659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8669261500086122177920439 13003892250129183266880659)
              ·
                refine ⟨19505838375193774900320989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13003892250129183266880659 19505838375193774900320989)
                ·
                  refine ⟨7314689390697665587620371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19505838375193774900320989 7314689390697665587620371)
                  ·
                    refine ⟨10972034086046498381430557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7314689390697665587620371 10972034086046498381430557)
                    ·
                      refine ⟨4114512782267436893036459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10972034086046498381430557 4114512782267436893036459)
                      ·
                        rfl

theorem cell23_8012985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_8012985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012985 prefixEnd_8012985 := by exact prefixLift 8012985
  have htrace : WordTrace (prefixWord ++ tailWord_8012985) baseStart_8012985 baseEnd_8012985 := by
    simpa [prefixWord, tailWord_8012985, baseEnd_8012985] using wordTrace_append hprefix tailTrace_8012985
  have hstable : (prefixWord ++ tailWord_8012985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012985).length < 2 ^ (prefixWord ++ tailWord_8012985).sum := by decide
  have hdescent : baseEnd_8012985 < baseStart_8012985 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013011 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 3]
def baseStart_8013011 : Nat := 118140960795 + 8013011 * 2 ^ 59
def prefixEnd_8013011 : Nat := 4983230072969 + 3 ^ 40 * 8013011 * 2
def baseEnd_8013011 : Nat := 4114526132764453791311339

theorem tailTrace_8013011 : CollatzResearch.WordTrace tailWord_8013011 prefixEnd_8013011 4114526132764453791311339 := by
  unfold tailWord_8013011
  simp only [CollatzResearch.WordTrace]
  refine ⟨292258521173237135170998887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194839014115491423447332591 292258521173237135170998887)
  ·
    refine ⟨438387781759855702756498331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292258521173237135170998887 438387781759855702756498331)
    ·
      refine ⟨657581672639783554134747497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438387781759855702756498331 657581672639783554134747497)
      ·
        refine ⟨493186254479837665601060623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657581672639783554134747497 493186254479837665601060623)
        ·
          refine ⟨739779381719756498401590935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493186254479837665601060623 739779381719756498401590935)
          ·
            refine ⟨1109669072579634747602386403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739779381719756498401590935 1109669072579634747602386403)
            ·
              refine ⟨1664503608869452121403579605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1109669072579634747602386403 1664503608869452121403579605)
              ·
                refine ⟨39011803332877784095396397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1664503608869452121403579605 39011803332877784095396397)
                ·
                  refine ⟨14629426249829169035773649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39011803332877784095396397 14629426249829169035773649)
                  ·
                    refine ⟨10972069687371876776830237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14629426249829169035773649 10972069687371876776830237)
                    ·
                      refine ⟨4114526132764453791311339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10972069687371876776830237 4114526132764453791311339)
                      ·
                        rfl

theorem cell23_8013011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 3].length) (baseStart_8013011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013011 prefixEnd_8013011 := by exact prefixLift 8013011
  have htrace : WordTrace (prefixWord ++ tailWord_8013011) baseStart_8013011 baseEnd_8013011 := by
    simpa [prefixWord, tailWord_8013011, baseEnd_8013011] using wordTrace_append hprefix tailTrace_8013011
  have hstable : (prefixWord ++ tailWord_8013011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013011).length < 2 ^ (prefixWord ++ tailWord_8013011).sum := by decide
  have hdescent : baseEnd_8013011 < baseStart_8013011 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013025 : List Nat := [1, 2, 3, 1, 3, 3, 3, 1, 1, 1, 4]
def baseStart_8013025 : Nat := 118140960795 + 8013025 * 2 ^ 59
def prefixEnd_8013025 : Nat := 4983230072969 + 3 ^ 40 * 8013025 * 2
def baseEnd_8013025 : Nat := 4114533321493616736536275

theorem tailTrace_8013025 : CollatzResearch.WordTrace tailWord_8013025 prefixEnd_8013025 4114533321493616736536275 := by
  unfold tailWord_8013025
  simp only [CollatzResearch.WordTrace]
  refine ⟨292259031795186415562008529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194839354530124277041339019 292259031795186415562008529)
  ·
    refine ⟨219194273846389811671506397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292259031795186415562008529 219194273846389811671506397)
    ·
      refine ⟨82197852692396179376814899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219194273846389811671506397 82197852692396179376814899)
      ·
        refine ⟨123296779038594269065222349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82197852692396179376814899 123296779038594269065222349)
        ·
          refine ⟨46236292139472850899458381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123296779038594269065222349 46236292139472850899458381)
          ·
            refine ⟨17338609552302319087296893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46236292139472850899458381 17338609552302319087296893)
            ·
              refine ⟨6501978582113369657736335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17338609552302319087296893 6501978582113369657736335)
              ·
                refine ⟨9752967873170054486604503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6501978582113369657736335 9752967873170054486604503)
                ·
                  refine ⟨14629451809755081729906755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9752967873170054486604503 14629451809755081729906755)
                  ·
                    refine ⟨21944177714632622594860133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14629451809755081729906755 21944177714632622594860133)
                    ·
                      refine ⟨4114533321493616736536275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21944177714632622594860133 4114533321493616736536275)
                      ·
                        rfl

theorem cell23_8013025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_8013025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013025 prefixEnd_8013025 := by exact prefixLift 8013025
  have htrace : WordTrace (prefixWord ++ tailWord_8013025) baseStart_8013025 baseEnd_8013025 := by
    simpa [prefixWord, tailWord_8013025, baseEnd_8013025] using wordTrace_append hprefix tailTrace_8013025
  have hstable : (prefixWord ++ tailWord_8013025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013025).length < 2 ^ (prefixWord ++ tailWord_8013025).sum := by decide
  have hdescent : baseEnd_8013025 < baseStart_8013025 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013028 : List Nat := [2, 3, 1, 1, 1, 2, 2, 5, 1, 2, 3]
def baseStart_8013028 : Nat := 118140960795 + 8013028 * 2 ^ 59
def prefixEnd_8013028 : Nat := 4983230072969 + 3 ^ 40 * 8013028 * 2
def baseEnd_8013028 : Nat := 4114534861935580224798761

theorem tailTrace_8013028 : CollatzResearch.WordTrace tailWord_8013028 prefixEnd_8013028 4114534861935580224798761 := by
  unfold tailWord_8013028
  simp only [CollatzResearch.WordTrace]
  refine ⟨146129570607087773537183869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194839427476117031382911825 146129570607087773537183869)
  ·
    refine ⟨54798588977657915076443951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146129570607087773537183869 54798588977657915076443951)
    ·
      refine ⟨82197883466486872614665927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54798588977657915076443951 82197883466486872614665927)
      ·
        refine ⟨123296825199730308921998891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82197883466486872614665927 123296825199730308921998891)
        ·
          refine ⟨184945237799595463382998337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123296825199730308921998891 184945237799595463382998337)
          ·
            refine ⟨138708928349696597537248753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184945237799595463382998337 138708928349696597537248753)
            ·
              refine ⟨104031696262272448152936565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138708928349696597537248753 104031696262272448152936565)
              ·
                refine ⟨9752971524588042014337803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104031696262272448152936565 9752971524588042014337803)
                ·
                  refine ⟨14629457286882063021506705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9752971524588042014337803 14629457286882063021506705)
                  ·
                    refine ⟨10972092965161547266130029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14629457286882063021506705 10972092965161547266130029)
                    ·
                      refine ⟨4114534861935580224798761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10972092965161547266130029 4114534861935580224798761)
                      ·
                        rfl

theorem cell23_8013028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_8013028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013028 prefixEnd_8013028 := by exact prefixLift 8013028
  have htrace : WordTrace (prefixWord ++ tailWord_8013028) baseStart_8013028 baseEnd_8013028 := by
    simpa [prefixWord, tailWord_8013028, baseEnd_8013028] using wordTrace_append hprefix tailTrace_8013028
  have hstable : (prefixWord ++ tailWord_8013028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013028).length < 2 ^ (prefixWord ++ tailWord_8013028).sum := by decide
  have hdescent : baseEnd_8013028 < baseStart_8013028 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013031 : List Nat := [1, 1, 5, 3, 2, 11]
def baseStart_8013031 : Nat := 118140960795 + 8013031 * 2 ^ 59
def prefixEnd_8013031 : Nat := 4983230072969 + 3 ^ 40 * 8013031 * 2
def baseEnd_8013031 : Nat := 16932248569454912399429

theorem tailTrace_8013031 : CollatzResearch.WordTrace tailWord_8013031 prefixEnd_8013031 16932248569454912399429 := by
  unfold tailWord_8013031
  simp only [CollatzResearch.WordTrace]
  refine ⟨292259250633164678586726947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194839500422109785724484631 292259250633164678586726947)
  ·
    refine ⟨438388875949747017880090421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292259250633164678586726947 438388875949747017880090421)
    ·
      refine ⟨41098957120288782926258477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 438388875949747017880090421 41098957120288782926258477)
      ·
        refine ⟨15412108920108293597346929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41098957120288782926258477 15412108920108293597346929)
        ·
          refine ⟨11559081690081220198010197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15412108920108293597346929 11559081690081220198010197)
          ·
            refine ⟨16932248569454912399429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11559081690081220198010197 16932248569454912399429)
            ·
              rfl

theorem cell23_8013031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 11].length) (baseStart_8013031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013031 prefixEnd_8013031 := by exact prefixLift 8013031
  have htrace : WordTrace (prefixWord ++ tailWord_8013031) baseStart_8013031 baseEnd_8013031 := by
    simpa [prefixWord, tailWord_8013031, baseEnd_8013031] using wordTrace_append hprefix tailTrace_8013031
  have hstable : (prefixWord ++ tailWord_8013031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013031).length < 2 ^ (prefixWord ++ tailWord_8013031).sum := by decide
  have hdescent : baseEnd_8013031 < baseStart_8013031 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013041 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 5, 3, 3]
def baseStart_8013041 : Nat := 118140960795 + 8013041 * 2 ^ 59
def prefixEnd_8013041 : Nat := 4983230072969 + 3 ^ 40 * 8013041 * 2
def baseEnd_8013041 : Nat := 4114541537184088673936201

theorem tailTrace_8013041 : CollatzResearch.WordTrace tailWord_8013041 prefixEnd_8013041 4114541537184088673936201 := by
  unfold tailWord_8013041
  simp only [CollatzResearch.WordTrace]
  refine ⟨292259615363128450294590977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194839743575418966863060651 292259615363128450294590977)
  ·
    refine ⟨219194711522346337720943233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292259615363128450294590977 219194711522346337720943233)
    ·
      refine ⟨164396033641759753290707425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219194711522346337720943233 164396033641759753290707425)
      ·
        refine ⟨123297025231319814968030569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164396033641759753290707425 123297025231319814968030569)
        ·
          refine ⟨92472768923489861226022927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123297025231319814968030569 92472768923489861226022927)
          ·
            refine ⟨138709153385234791839034391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92472768923489861226022927 138709153385234791839034391)
            ·
              refine ⟨208063730077852187758551587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138709153385234791839034391 208063730077852187758551587)
              ·
                refine ⟨312095595116778281637827381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208063730077852187758551587 312095595116778281637827381)
                ·
                  refine ⟨29258962042197963903546317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 312095595116778281637827381 29258962042197963903546317)
                  ·
                    refine ⟨10972110765824236463829869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29258962042197963903546317 10972110765824236463829869)
                    ·
                      refine ⟨4114541537184088673936201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10972110765824236463829869 4114541537184088673936201)
                      ·
                        rfl

theorem cell23_8013041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_8013041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013041 prefixEnd_8013041 := by exact prefixLift 8013041
  have htrace : WordTrace (prefixWord ++ tailWord_8013041) baseStart_8013041 baseEnd_8013041 := by
    simpa [prefixWord, tailWord_8013041, baseEnd_8013041] using wordTrace_append hprefix tailTrace_8013041
  have hstable : (prefixWord ++ tailWord_8013041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013041).length < 2 ^ (prefixWord ++ tailWord_8013041).sum := by decide
  have hdescent : baseEnd_8013041 < baseStart_8013041 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013086 : List Nat := [4, 3, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_8013086 : Nat := 118140960795 + 8013086 * 2 ^ 59
def prefixEnd_8013086 : Nat := 4983230072969 + 3 ^ 40 * 8013086 * 2
def baseEnd_8013086 : Nat := 1371521547937846999291165

theorem tailTrace_8013086 : CollatzResearch.WordTrace tailWord_8013086 prefixEnd_8013086 1371521547937846999291165 := by
  unfold tailWord_8013086
  simp only [CollatzResearch.WordTrace]
  refine ⟨36532657080995677872497389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194840837765310281986652741 36532657080995677872497389)
  ·
    refine ⟨13699746405373379202186521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36532657080995677872497389 13699746405373379202186521)
    ·
      refine ⟨10274809804030034401639891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13699746405373379202186521 10274809804030034401639891)
      ·
        refine ⟨15412214706045051602459837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10274809804030034401639891 15412214706045051602459837)
        ·
          refine ⟨5779580514766894350922439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15412214706045051602459837 5779580514766894350922439)
          ·
            refine ⟨8669370772150341526383659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5779580514766894350922439 8669370772150341526383659)
            ·
              refine ⟨13004056158225512289575489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8669370772150341526383659 13004056158225512289575489)
              ·
                refine ⟨9753042118669134217181617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13004056158225512289575489 9753042118669134217181617)
                ·
                  refine ⟨7314781589001850662886213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9753042118669134217181617 7314781589001850662886213)
                  ·
                    refine ⟨1371521547937846999291165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7314781589001850662886213 1371521547937846999291165)
                    ·
                      rfl

theorem cell23_8013086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_8013086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013086 prefixEnd_8013086 := by exact prefixLift 8013086
  have htrace : WordTrace (prefixWord ++ tailWord_8013086) baseStart_8013086 baseEnd_8013086 := by
    simpa [prefixWord, tailWord_8013086, baseEnd_8013086] using wordTrace_append hprefix tailTrace_8013086
  have hstable : (prefixWord ++ tailWord_8013086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013086).length < 2 ^ (prefixWord ++ tailWord_8013086).sum := by decide
  have hdescent : baseEnd_8013086 < baseStart_8013086 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013091 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 2, 6]
def baseStart_8013091 : Nat := 118140960795 + 8013091 * 2 ^ 59
def prefixEnd_8013091 : Nat := 4983230072969 + 3 ^ 40 * 8013091 * 2
def baseEnd_8013091 : Nat := 1371522403738937826103657

theorem tailTrace_8013091 : CollatzResearch.WordTrace tailWord_8013091 prefixEnd_8013091 1371522403738937826103657 := by
  unfold tailWord_8013091
  simp only [CollatzResearch.WordTrace]
  refine ⟨292261439012947308833911127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194840959341964872555940751 292261439012947308833911127)
  ·
    refine ⟨438392158519420963250866691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292261439012947308833911127 438392158519420963250866691)
    ·
      refine ⟨657588237779131444876300037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438392158519420963250866691 657588237779131444876300037)
      ·
        refine ⟨123297794583587145914306257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 657588237779131444876300037 123297794583587145914306257)
        ·
          refine ⟨92473345937690359435729693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123297794583587145914306257 92473345937690359435729693)
          ·
            refine ⟨34677504726633884788398635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92473345937690359435729693 34677504726633884788398635)
            ·
              refine ⟨52016257089950827182597953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34677504726633884788398635 52016257089950827182597953)
              ·
                refine ⟨39012192817463120386948465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52016257089950827182597953 39012192817463120386948465)
                ·
                  refine ⟨29259144613097340290211349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39012192817463120386948465 29259144613097340290211349)
                  ·
                    refine ⟨1371522403738937826103657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29259144613097340290211349 1371522403738937826103657)
                    ·
                      rfl

theorem cell23_8013091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 6].length) (baseStart_8013091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013091 prefixEnd_8013091 := by exact prefixLift 8013091
  have htrace : WordTrace (prefixWord ++ tailWord_8013091) baseStart_8013091 baseEnd_8013091 := by
    simpa [prefixWord, tailWord_8013091, baseEnd_8013091] using wordTrace_append hprefix tailTrace_8013091
  have hstable : (prefixWord ++ tailWord_8013091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013091).length < 2 ^ (prefixWord ++ tailWord_8013091).sum := by decide
  have hdescent : baseEnd_8013091 < baseStart_8013091 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013108 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_8013108 : Nat := 118140960795 + 8013108 * 2 ^ 59
def prefixEnd_8013108 : Nat := 4983230072969 + 3 ^ 40 * 8013108 * 2
def baseEnd_8013108 : Nat := 1371525313462646637266131

theorem tailTrace_8013108 : CollatzResearch.WordTrace tailWord_8013108 prefixEnd_8013108 1371525313462646637266131 := by
  unfold tailWord_8013108
  simp only [CollatzResearch.WordTrace]
  refine ⟨146131029526942860368639989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194841372702590480491519985 146131029526942860368639989)
  ·
    refine ⟨13699784018150893159559999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146131029526942860368639989 13699784018150893159559999)
    ·
      refine ⟨20549676027226339739339999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13699784018150893159559999 20549676027226339739339999)
      ·
        refine ⟨30824514040839509609009999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20549676027226339739339999 30824514040839509609009999)
        ·
          refine ⟨46236771061259264413514999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30824514040839509609009999 46236771061259264413514999)
          ·
            refine ⟨69355156591888896620272499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46236771061259264413514999 69355156591888896620272499)
            ·
              refine ⟨104032734887833344930408749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69355156591888896620272499 104032734887833344930408749)
              ·
                refine ⟨39012275582937504348903281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104032734887833344930408749 39012275582937504348903281)
                ·
                  refine ⟨29259206687203128261677461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39012275582937504348903281 29259206687203128261677461)
                  ·
                    refine ⟨1371525313462646637266131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29259206687203128261677461 1371525313462646637266131)
                    ·
                      rfl

theorem cell23_8013108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_8013108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013108 prefixEnd_8013108 := by exact prefixLift 8013108
  have htrace : WordTrace (prefixWord ++ tailWord_8013108) baseStart_8013108 baseEnd_8013108 := by
    simpa [prefixWord, tailWord_8013108, baseEnd_8013108] using wordTrace_append hprefix tailTrace_8013108
  have hstable : (prefixWord ++ tailWord_8013108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013108).length < 2 ^ (prefixWord ++ tailWord_8013108).sum := by decide
  have hdescent : baseEnd_8013108 < baseStart_8013108 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013118 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_8013118 : Nat := 118140960795 + 8013118 * 2 ^ 59
def prefixEnd_8013118 : Nat := 4983230072969 + 3 ^ 40 * 8013118 * 2
def baseEnd_8013118 : Nat := 4114581075194484872673347

theorem tailTrace_8013118 : CollatzResearch.WordTrace tailWord_8013118 prefixEnd_8013118 4114581075194484872673347 := by
  unfold tailWord_8013118
  simp only [CollatzResearch.WordTrace]
  refine ⟨36532802972981186555643001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194841615855899661630096005 36532802972981186555643001)
  ·
    refine ⟨27399602229735889916732251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36532802972981186555643001 27399602229735889916732251)
    ·
      refine ⟨41099403344603834875098377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27399602229735889916732251 41099403344603834875098377)
      ·
        refine ⟨30824552508452876156323783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41099403344603834875098377 30824552508452876156323783)
        ·
          refine ⟨46236828762679314234485675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30824552508452876156323783 46236828762679314234485675)
          ·
            refine ⟨69355243144018971351728513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46236828762679314234485675 69355243144018971351728513)
            ·
              refine ⟨52016432358014228513796385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69355243144018971351728513 52016432358014228513796385)
              ·
                refine ⟨39012324268510671385347289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52016432358014228513796385 39012324268510671385347289)
                ·
                  refine ⟨29259243201383003539010467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39012324268510671385347289 29259243201383003539010467)
                  ·
                    refine ⟨43888864802074505308515701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29259243201383003539010467 43888864802074505308515701)
                    ·
                      refine ⟨4114581075194484872673347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43888864802074505308515701 4114581075194484872673347)
                      ·
                        rfl

theorem cell23_8013118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_8013118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013118 prefixEnd_8013118 := by exact prefixLift 8013118
  have htrace : WordTrace (prefixWord ++ tailWord_8013118) baseStart_8013118 baseEnd_8013118 := by
    simpa [prefixWord, tailWord_8013118, baseEnd_8013118] using wordTrace_append hprefix tailTrace_8013118
  have hstable : (prefixWord ++ tailWord_8013118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013118).length < 2 ^ (prefixWord ++ tailWord_8013118).sum := by decide
  have hdescent : baseEnd_8013118 < baseStart_8013118 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013166 : List Nat := [4, 1, 2, 4, 1, 1, 1, 3, 2, 2, 2]
def baseStart_8013166 : Nat := 118140960795 + 8013166 * 2 ^ 59
def prefixEnd_8013166 : Nat := 4983230072969 + 3 ^ 40 * 8013166 * 2
def baseEnd_8013166 : Nat := 4114605722265900684873127

theorem tailTrace_8013166 : CollatzResearch.WordTrace tailWord_8013166 prefixEnd_8013166 4114605722265900684873127 := by
  unfold tailWord_8013166
  simp only [CollatzResearch.WordTrace]
  refine ⟨36533021810959449580361419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194842782991783731095260901 36533021810959449580361419)
  ·
    refine ⟨54799532716439174370542129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36533021810959449580361419 54799532716439174370542129)
    ·
      refine ⟨41099649537329380777906597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54799532716439174370542129 41099649537329380777906597)
      ·
        refine ⟨7706184288249258895857487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41099649537329380777906597 7706184288249258895857487)
        ·
          refine ⟨11559276432373888343786231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7706184288249258895857487 11559276432373888343786231)
          ·
            refine ⟨17338914648560832515679347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11559276432373888343786231 17338914648560832515679347)
            ·
              refine ⟨26008371972841248773519021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17338914648560832515679347 26008371972841248773519021)
              ·
                refine ⟨9753139489815468290069633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26008371972841248773519021 9753139489815468290069633)
                ·
                  refine ⟨7314854617361601217552225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9753139489815468290069633 7314854617361601217552225)
                  ·
                    refine ⟨5486140963021200913164169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7314854617361601217552225 5486140963021200913164169)
                    ·
                      refine ⟨4114605722265900684873127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5486140963021200913164169 4114605722265900684873127)
                      ·
                        rfl

theorem cell23_8013166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_8013166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013166 prefixEnd_8013166 := by exact prefixLift 8013166
  have htrace : WordTrace (prefixWord ++ tailWord_8013166) baseStart_8013166 baseEnd_8013166 := by
    simpa [prefixWord, tailWord_8013166, baseEnd_8013166] using wordTrace_append hprefix tailTrace_8013166
  have hstable : (prefixWord ++ tailWord_8013166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013166).length < 2 ^ (prefixWord ++ tailWord_8013166).sum := by decide
  have hdescent : baseEnd_8013166 < baseStart_8013166 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013201 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 6]
def baseStart_8013201 : Nat := 118140960795 + 8013201 * 2 ^ 59
def prefixEnd_8013201 : Nat := 4983230072969 + 3 ^ 40 * 8013201 * 2
def baseEnd_8013201 : Nat := 4114623694088808047935465

theorem tailTrace_8013201 : CollatzResearch.WordTrace tailWord_8013201 prefixEnd_8013201 4114623694088808047935465 := by
  unfold tailWord_8013201
  simp only [CollatzResearch.WordTrace]
  refine ⟨292265451042548797620415457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194843634028365865080276971 292265451042548797620415457)
  ·
    refine ⟨219199088281911598215311593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292265451042548797620415457 219199088281911598215311593)
    ·
      refine ⟨164399316211433698661483695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219199088281911598215311593 164399316211433698661483695)
      ·
        refine ⟨246598974317150547992225543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164399316211433698661483695 246598974317150547992225543)
        ·
          refine ⟨369898461475725821988338315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246598974317150547992225543 369898461475725821988338315)
          ·
            refine ⟨554847692213588732982507473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369898461475725821988338315 554847692213588732982507473)
            ·
              refine ⟨416135769160191549736880605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554847692213588732982507473 416135769160191549736880605)
              ·
                refine ⟨156050913435071831151330227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 416135769160191549736880605 156050913435071831151330227)
                ·
                  refine ⟨234076370152607746726995341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156050913435071831151330227 234076370152607746726995341)
                  ·
                    refine ⟨87778638807227905022623253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 234076370152607746726995341 87778638807227905022623253)
                    ·
                      refine ⟨4114623694088808047935465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87778638807227905022623253 4114623694088808047935465)
                      ·
                        rfl

theorem cell23_8013201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_8013201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013201 prefixEnd_8013201 := by exact prefixLift 8013201
  have htrace : WordTrace (prefixWord ++ tailWord_8013201) baseStart_8013201 baseEnd_8013201 := by
    simpa [prefixWord, tailWord_8013201, baseEnd_8013201] using wordTrace_append hprefix tailTrace_8013201
  have hstable : (prefixWord ++ tailWord_8013201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013201).length < 2 ^ (prefixWord ++ tailWord_8013201).sum := by decide
  have hdescent : baseEnd_8013201 < baseStart_8013201 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013228 : List Nat := [2, 2, 1, 1, 1, 1, 6, 3, 6]
def baseStart_8013228 : Nat := 118140960795 + 8013228 * 2 ^ 59
def prefixEnd_8013228 : Nat := 4983230072969 + 3 ^ 40 * 8013228 * 2
def baseEnd_8013228 : Nat := 457181950896275493588649

theorem tailTrace_8013228 : CollatzResearch.WordTrace tailWord_8013228 prefixEnd_8013228 457181950896275493588649 := by
  unfold tailWord_8013228
  simp only [CollatzResearch.WordTrace]
  refine ⟨146133217906725490615824169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194844290542300654154432225 146133217906725490615824169)
  ·
    refine ⟨109599913430044117961868127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146133217906725490615824169 109599913430044117961868127)
    ·
      refine ⟨164399870145066176942802191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109599913430044117961868127 164399870145066176942802191)
      ·
        refine ⟨246599805217599265414203287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164399870145066176942802191 246599805217599265414203287)
        ·
          refine ⟨369899707826398898121304931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246599805217599265414203287 369899707826398898121304931)
          ·
            refine ⟨554849561739598347181957397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369899707826398898121304931 554849561739598347181957397)
            ·
              refine ⟨26008573206543672524154253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 554849561739598347181957397 26008573206543672524154253)
              ·
                refine ⟨9753214952453877196557845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26008573206543672524154253 9753214952453877196557845)
                ·
                  refine ⟨457181950896275493588649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9753214952453877196557845 457181950896275493588649)
                  ·
                    rfl

theorem cell23_8013228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 6].length) (baseStart_8013228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013228 prefixEnd_8013228 := by exact prefixLift 8013228
  have htrace : WordTrace (prefixWord ++ tailWord_8013228) baseStart_8013228 baseEnd_8013228 := by
    simpa [prefixWord, tailWord_8013228, baseEnd_8013228] using wordTrace_append hprefix tailTrace_8013228
  have hstable : (prefixWord ++ tailWord_8013228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013228).length < 2 ^ (prefixWord ++ tailWord_8013228).sum := by decide
  have hdescent : baseEnd_8013228 < baseStart_8013228 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013255 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 5, 1, 3]
def baseStart_8013255 : Nat := 118140960795 + 8013255 * 2 ^ 59
def prefixEnd_8013255 : Nat := 4983230072969 + 3 ^ 40 * 8013255 * 2
def baseEnd_8013255 : Nat := 4114651422044150836660217

theorem tailTrace_8013255 : CollatzResearch.WordTrace tailWord_8013255 prefixEnd_8013255 4114651422044150836660217 := by
  unfold tailWord_8013255
  simp only [CollatzResearch.WordTrace]
  refine ⟨292267420584353164842881219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194844947056235443228587479 292267420584353164842881219)
  ·
    refine ⟨438401130876529747264321829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292267420584353164842881219 438401130876529747264321829)
    ·
      refine ⟨82200212039349327612060343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 438401130876529747264321829 82200212039349327612060343)
      ·
        refine ⟨123300318059023991418090515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82200212039349327612060343 123300318059023991418090515)
        ·
          refine ⟨184950477088535987127135773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123300318059023991418090515 184950477088535987127135773)
          ·
            refine ⟨69356428908200995172675915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184950477088535987127135773 69356428908200995172675915)
            ·
              refine ⟨104034643362301492759013873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69356428908200995172675915 104034643362301492759013873)
              ·
                refine ⟨78025982521726119569260405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104034643362301492759013873 78025982521726119569260405)
                ·
                  refine ⟨7314935861411823709618163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78025982521726119569260405 7314935861411823709618163)
                  ·
                    refine ⟨10972403792117735564427245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7314935861411823709618163 10972403792117735564427245)
                    ·
                      refine ⟨4114651422044150836660217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10972403792117735564427245 4114651422044150836660217)
                      ·
                        rfl

theorem cell23_8013255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_8013255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013255 prefixEnd_8013255 := by exact prefixLift 8013255
  have htrace : WordTrace (prefixWord ++ tailWord_8013255) baseStart_8013255 baseEnd_8013255 := by
    simpa [prefixWord, tailWord_8013255, baseEnd_8013255] using wordTrace_append hprefix tailTrace_8013255
  have hstable : (prefixWord ++ tailWord_8013255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013255).length < 2 ^ (prefixWord ++ tailWord_8013255).sum := by decide
  have hdescent : baseEnd_8013255 < baseStart_8013255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013295 : List Nat := [1, 1, 2, 1, 4, 1, 3, 4, 1, 1, 4]
def baseStart_8013295 : Nat := 118140960795 + 8013295 * 2 ^ 59
def prefixEnd_8013295 : Nat := 4983230072969 + 3 ^ 40 * 8013295 * 2
def baseEnd_8013295 : Nat := 4114671961270330680160033

theorem tailTrace_8013295 : CollatzResearch.WordTrace tailWord_8013295 prefixEnd_8013295 4114671961270330680160033 := by
  unfold tailWord_8013295
  simp only [CollatzResearch.WordTrace]
  refine ⟨292268879504208251674337339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194845919669472167782891559 292268879504208251674337339)
  ·
    refine ⟨438403319256312377511506009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292268879504208251674337339 438403319256312377511506009)
    ·
      refine ⟨328802489442234283133629507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438403319256312377511506009 328802489442234283133629507)
      ·
        refine ⟨493203734163351424700444261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328802489442234283133629507 493203734163351424700444261)
        ·
          refine ⟨92475700155628392131333299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 493203734163351424700444261 92475700155628392131333299)
          ·
            refine ⟨138713550233442588196999949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92475700155628392131333299 138713550233442588196999949)
            ·
              refine ⟨52017581337540970573874981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138713550233442588196999949 52017581337540970573874981)
              ·
                refine ⟨9753296500788931982601559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52017581337540970573874981 9753296500788931982601559)
                ·
                  refine ⟨14629944751183397973902339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9753296500788931982601559 14629944751183397973902339)
                  ·
                    refine ⟨21944917126775096960853509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14629944751183397973902339 21944917126775096960853509)
                    ·
                      refine ⟨4114671961270330680160033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21944917126775096960853509 4114671961270330680160033)
                      ·
                        rfl

theorem cell23_8013295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 1, 4].length) (baseStart_8013295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013295 prefixEnd_8013295 := by exact prefixLift 8013295
  have htrace : WordTrace (prefixWord ++ tailWord_8013295) baseStart_8013295 baseEnd_8013295 := by
    simpa [prefixWord, tailWord_8013295, baseEnd_8013295] using wordTrace_append hprefix tailTrace_8013295
  have hstable : (prefixWord ++ tailWord_8013295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013295).length < 2 ^ (prefixWord ++ tailWord_8013295).sum := by decide
  have hdescent : baseEnd_8013295 < baseStart_8013295 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013338 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6]
def baseStart_8013338 : Nat := 118140960795 + 8013338 * 2 ^ 59
def prefixEnd_8013338 : Nat := 4983230072969 + 3 ^ 40 * 8013338 * 2
def baseEnd_8013338 : Nat := 4114694040938474011922335

theorem tailTrace_8013338 : CollatzResearch.WordTrace tailWord_8013338 prefixEnd_8013338 4114694040938474011922335 := by
  unfold tailWord_8013338
  simp only [CollatzResearch.WordTrace]
  refine ⟨73067611960763117504538167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194846965228701646678768445 73067611960763117504538167)
  ·
    refine ⟨109601417941144676256807251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73067611960763117504538167 109601417941144676256807251)
    ·
      refine ⟨164402126911717014385210877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109601417941144676256807251 164402126911717014385210877)
      ·
        refine ⟨61650797591893880394454079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164402126911717014385210877 61650797591893880394454079)
        ·
          refine ⟨92476196387840820591681119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61650797591893880394454079 92476196387840820591681119)
          ·
            refine ⟨138714294581761230887521679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92476196387840820591681119 138714294581761230887521679)
            ·
              refine ⟨208071441872641846331282519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138714294581761230887521679 208071441872641846331282519)
              ·
                refine ⟨312107162808962769496923779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208071441872641846331282519 312107162808962769496923779)
                ·
                  refine ⟨468160744213444154245385669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312107162808962769496923779 468160744213444154245385669)
                  ·
                    refine ⟨87780139540020778921009813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 468160744213444154245385669 87780139540020778921009813)
                    ·
                      refine ⟨4114694040938474011922335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87780139540020778921009813 4114694040938474011922335)
                      ·
                        rfl

theorem cell23_8013338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_8013338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013338 prefixEnd_8013338 := by exact prefixLift 8013338
  have htrace : WordTrace (prefixWord ++ tailWord_8013338) baseStart_8013338 baseEnd_8013338 := by
    simpa [prefixWord, tailWord_8013338, baseEnd_8013338] using wordTrace_append hprefix tailTrace_8013338
  have hstable : (prefixWord ++ tailWord_8013338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013338).length < 2 ^ (prefixWord ++ tailWord_8013338).sum := by decide
  have hdescent : baseEnd_8013338 < baseStart_8013338 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013366 : List Nat := [5, 1, 2, 1, 4, 1, 1, 1, 1, 1, 5]
def baseStart_8013366 : Nat := 118140960795 + 8013366 * 2 ^ 59
def prefixEnd_8013366 : Nat := 4983230072969 + 3 ^ 40 * 8013366 * 2
def baseEnd_8013366 : Nat := 4114708418396799902372207

theorem tailTrace_8013366 : CollatzResearch.WordTrace tailWord_8013366 prefixEnd_8013366 4114708418396799902372207 := by
  unfold tailWord_8013366
  simp only [CollatzResearch.WordTrace]
  refine ⟨18266966817934439425010747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194847646057967353866781301 18266966817934439425010747)
  ·
    refine ⟨27400450226901659137516121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18266966817934439425010747 27400450226901659137516121)
    ·
      refine ⟨20550337670176244353137091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27400450226901659137516121 20550337670176244353137091)
      ·
        refine ⟨30825506505264366529705637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20550337670176244353137091 30825506505264366529705637)
        ·
          refine ⟨5779782469737068724319807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30825506505264366529705637 5779782469737068724319807)
          ·
            refine ⟨8669673704605603086479711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5779782469737068724319807 8669673704605603086479711)
            ·
              refine ⟨13004510556908404629719567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8669673704605603086479711 13004510556908404629719567)
              ·
                refine ⟨19506765835362606944579351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13004510556908404629719567 19506765835362606944579351)
                ·
                  refine ⟨29260148753043910416869027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19506765835362606944579351 29260148753043910416869027)
                  ·
                    refine ⟨43890223129565865625303541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29260148753043910416869027 43890223129565865625303541)
                    ·
                      refine ⟨4114708418396799902372207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43890223129565865625303541 4114708418396799902372207)
                      ·
                        rfl

theorem cell23_8013366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_8013366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013366 prefixEnd_8013366 := by exact prefixLift 8013366
  have htrace : WordTrace (prefixWord ++ tailWord_8013366) baseStart_8013366 baseEnd_8013366 := by
    simpa [prefixWord, tailWord_8013366, baseEnd_8013366] using wordTrace_append hprefix tailTrace_8013366
  have hstable : (prefixWord ++ tailWord_8013366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013366).length < 2 ^ (prefixWord ++ tailWord_8013366).sum := by decide
  have hdescent : baseEnd_8013366 < baseStart_8013366 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013435 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 3]
def baseStart_8013435 : Nat := 118140960795 + 8013435 * 2 ^ 59
def prefixEnd_8013435 : Nat := 4983230072969 + 3 ^ 40 * 8013435 * 2
def baseEnd_8013435 : Nat := 4114743848561960132409389

theorem tailTrace_8013435 : CollatzResearch.WordTrace tailWord_8013435 prefixEnd_8013435 4114743848561960132409389 := by
  unfold tailWord_8013435
  simp only [CollatzResearch.WordTrace]
  refine ⟨292273985723701055584433759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194849323815800703722955839 292273985723701055584433759)
  ·
    refine ⟨438410978585551583376650639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292273985723701055584433759 438410978585551583376650639)
    ·
      refine ⟨657616467878327375064975959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438410978585551583376650639 657616467878327375064975959)
      ·
        refine ⟨986424701817491062597463939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657616467878327375064975959 986424701817491062597463939)
        ·
          refine ⟨1479637052726236593896195909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 986424701817491062597463939 1479637052726236593896195909)
          ·
            refine ⟨277431947386169361355536733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1479637052726236593896195909 277431947386169361355536733)
            ·
              refine ⟨104036980269813510508326275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277431947386169361355536733 104036980269813510508326275)
              ·
                refine ⟨156055470404720265762489413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104036980269813510508326275 156055470404720265762489413)
                ·
                  refine ⟨29260400700885049830466765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156055470404720265762489413 29260400700885049830466765)
                  ·
                    refine ⟨10972650262831893686425037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29260400700885049830466765 10972650262831893686425037)
                    ·
                      refine ⟨4114743848561960132409389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10972650262831893686425037 4114743848561960132409389)
                      ·
                        rfl

theorem cell23_8013435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 3].length) (baseStart_8013435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013435 prefixEnd_8013435 := by exact prefixLift 8013435
  have htrace : WordTrace (prefixWord ++ tailWord_8013435) baseStart_8013435 baseEnd_8013435 := by
    simpa [prefixWord, tailWord_8013435, baseEnd_8013435] using wordTrace_append hprefix tailTrace_8013435
  have hstable : (prefixWord ++ tailWord_8013435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013435).length < 2 ^ (prefixWord ++ tailWord_8013435).sum := by decide
  have hdescent : baseEnd_8013435 < baseStart_8013435 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013475 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 4]
def baseStart_8013475 : Nat := 118140960795 + 8013475 * 2 ^ 59
def prefixEnd_8013475 : Nat := 4983230072969 + 3 ^ 40 * 8013475 * 2
def baseEnd_8013475 : Nat := 4114764387788139975909205

theorem tailTrace_8013475 : CollatzResearch.WordTrace tailWord_8013475 prefixEnd_8013475 4114764387788139975909205 := by
  unfold tailWord_8013475
  simp only [CollatzResearch.WordTrace]
  refine ⟨292275444643556142415889879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194850296429037428277259919 292275444643556142415889879)
  ·
    refine ⟨438413166965334213623834819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292275444643556142415889879 438413166965334213623834819)
    ·
      refine ⟨657619750448001320435752229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438413166965334213623834819 657619750448001320435752229)
      ·
        refine ⟨123303703209000247581703543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 657619750448001320435752229 123303703209000247581703543)
        ·
          refine ⟨184955554813500371372555315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123303703209000247581703543 184955554813500371372555315)
          ·
            refine ⟨277433332220250557058832973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184955554813500371372555315 277433332220250557058832973)
            ·
              refine ⟨104037499582593958897062365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277433332220250557058832973 104037499582593958897062365)
              ·
                refine ⟨39014062343472734586398387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104037499582593958897062365 39014062343472734586398387)
                ·
                  refine ⟨58521093515209101879597581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39014062343472734586398387 58521093515209101879597581)
                  ·
                    refine ⟨21945410068203413204849093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58521093515209101879597581 21945410068203413204849093)
                    ·
                      refine ⟨4114764387788139975909205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21945410068203413204849093 4114764387788139975909205)
                      ·
                        rfl

theorem cell23_8013475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_8013475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013475 prefixEnd_8013475 := by exact prefixLift 8013475
  have htrace : WordTrace (prefixWord ++ tailWord_8013475) baseStart_8013475 baseEnd_8013475 := by
    simpa [prefixWord, tailWord_8013475, baseEnd_8013475] using wordTrace_append hprefix tailTrace_8013475
  have hstable : (prefixWord ++ tailWord_8013475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013475).length < 2 ^ (prefixWord ++ tailWord_8013475).sum := by decide
  have hdescent : baseEnd_8013475 < baseStart_8013475 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013512 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 4, 2, 3]
def baseStart_8013512 : Nat := 118140960795 + 8013512 * 2 ^ 59
def prefixEnd_8013512 : Nat := 4983230072969 + 3 ^ 40 * 8013512 * 2
def baseEnd_8013512 : Nat := 4114783386572356331146535

theorem tailTrace_8013512 : CollatzResearch.WordTrace tailWord_8013512 prefixEnd_8013512 4114783386572356331146535 := by
  unfold tailWord_8013512
  simp only [CollatzResearch.WordTrace]
  refine ⟨146138397072211048867493395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194851196096281398489991193 146138397072211048867493395)
  ·
    refine ⟨219207595608316573301240093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146138397072211048867493395 219207595608316573301240093)
    ·
      refine ⟨82202848353118714987965035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219207595608316573301240093 82202848353118714987965035)
      ·
        refine ⟨123304272529678072481947553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82202848353118714987965035 123304272529678072481947553)
        ·
          refine ⟨92478204397258554361460665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123304272529678072481947553 92478204397258554361460665)
          ·
            refine ⟨69358653297943915771095499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92478204397258554361460665 69358653297943915771095499)
            ·
              refine ⟨104037979946915873656643249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69358653297943915771095499 104037979946915873656643249)
              ·
                refine ⟨78028484960186905242482437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104037979946915873656643249 78028484960186905242482437)
                ·
                  refine ⟨14630340930035044732965457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78028484960186905242482437 14630340930035044732965457)
                  ·
                    refine ⟨10972755697526283549724093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14630340930035044732965457 10972755697526283549724093)
                    ·
                      refine ⟨4114783386572356331146535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10972755697526283549724093 4114783386572356331146535)
                      ·
                        rfl

theorem cell23_8013512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_8013512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013512 prefixEnd_8013512 := by exact prefixLift 8013512
  have htrace : WordTrace (prefixWord ++ tailWord_8013512) baseStart_8013512 baseEnd_8013512 := by
    simpa [prefixWord, tailWord_8013512, baseEnd_8013512] using wordTrace_append hprefix tailTrace_8013512
  have hstable : (prefixWord ++ tailWord_8013512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013512).length < 2 ^ (prefixWord ++ tailWord_8013512).sum := by decide
  have hdescent : baseEnd_8013512 < baseStart_8013512 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013529 : List Nat := [1, 2, 1, 2, 3, 4, 2, 1, 2, 2, 3]
def baseStart_8013529 : Nat := 118140960795 + 8013529 * 2 ^ 59
def prefixEnd_8013529 : Nat := 4983230072969 + 3 ^ 40 * 8013529 * 2
def baseEnd_8013529 : Nat := 4114792115743482764633957

theorem tailTrace_8013529 : CollatzResearch.WordTrace tailWord_8013529 prefixEnd_8013529 4114792115743482764633957 := by
  unfold tailWord_8013529
  simp only [CollatzResearch.WordTrace]
  refine ⟨292277414185360509638355641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194851609456907006425570427 292277414185360509638355641)
  ·
    refine ⟨219208060639020382228766731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292277414185360509638355641 219208060639020382228766731)
    ·
      refine ⟨328812090958530573343150097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219208060639020382228766731 328812090958530573343150097)
      ·
        refine ⟨246609068218897930007362573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328812090958530573343150097 246609068218897930007362573)
        ·
          refine ⟨92478400582086723752760965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246609068218897930007362573 92478400582086723752760965)
          ·
            refine ⟨17339700109141260703642681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92478400582086723752760965 17339700109141260703642681)
            ·
              refine ⟨13004775081855945527732011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17339700109141260703642681 13004775081855945527732011)
              ·
                refine ⟨19507162622783918291598017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13004775081855945527732011 19507162622783918291598017)
                ·
                  refine ⟨14630371967087938718698513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19507162622783918291598017 14630371967087938718698513)
                  ·
                    refine ⟨10972778975315954039023885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14630371967087938718698513 10972778975315954039023885)
                    ·
                      refine ⟨4114792115743482764633957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10972778975315954039023885 4114792115743482764633957)
                      ·
                        rfl

theorem cell23_8013529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 2, 3].length) (baseStart_8013529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013529 prefixEnd_8013529 := by exact prefixLift 8013529
  have htrace : WordTrace (prefixWord ++ tailWord_8013529) baseStart_8013529 baseEnd_8013529 := by
    simpa [prefixWord, tailWord_8013529, baseEnd_8013529] using wordTrace_append hprefix tailTrace_8013529
  have hstable : (prefixWord ++ tailWord_8013529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013529).length < 2 ^ (prefixWord ++ tailWord_8013529).sum := by decide
  have hdescent : baseEnd_8013529 < baseStart_8013529 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013549 : List Nat := [1, 5, 1, 2, 1, 3, 2, 2, 6]
def baseStart_8013549 : Nat := 118140960795 + 8013549 * 2 ^ 59
def prefixEnd_8013549 : Nat := 4983230072969 + 3 ^ 40 * 8013549 * 2
def baseEnd_8013549 : Nat := 457200265039619187375985

theorem tailTrace_8013549 : CollatzResearch.WordTrace tailWord_8013549 prefixEnd_8013549 457200265039619187375985 := by
  unfold tailWord_8013549
  simp only [CollatzResearch.WordTrace]
  refine ⟨292278143645288053054083701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194852095763525368702722467 292278143645288053054083701)
  ·
    refine ⟨27401075966745754973820347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 292278143645288053054083701 27401075966745754973820347)
    ·
      refine ⟨41101613950118632460730521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27401075966745754973820347 41101613950118632460730521)
      ·
        refine ⟨30826210462588974345547891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41101613950118632460730521 30826210462588974345547891)
        ·
          refine ⟨46239315693883461518321837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30826210462588974345547891 46239315693883461518321837)
          ·
            refine ⟨17339743385206298069370689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46239315693883461518321837 17339743385206298069370689)
            ·
              refine ⟨13004807538904723552028017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17339743385206298069370689 13004807538904723552028017)
              ·
                refine ⟨9753605654178542664021013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13004807538904723552028017 9753605654178542664021013)
                ·
                  refine ⟨457200265039619187375985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9753605654178542664021013 457200265039619187375985)
                  ·
                    rfl

theorem cell23_8013549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_8013549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013549 prefixEnd_8013549 := by exact prefixLift 8013549
  have htrace : WordTrace (prefixWord ++ tailWord_8013549) baseStart_8013549 baseEnd_8013549 := by
    simpa [prefixWord, tailWord_8013549, baseEnd_8013549] using wordTrace_append hprefix tailTrace_8013549
  have hstable : (prefixWord ++ tailWord_8013549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013549).length < 2 ^ (prefixWord ++ tailWord_8013549).sum := by decide
  have hdescent : baseEnd_8013549 < baseStart_8013549 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013553 : List Nat := [1, 2, 2, 2, 2, 5, 2, 2, 1, 4]
def baseStart_8013553 : Nat := 118140960795 + 8013553 * 2 ^ 59
def prefixEnd_8013553 : Nat := 4983230072969 + 3 ^ 40 * 8013553 * 2
def baseEnd_8013553 : Nat := 1371601479759730223577949

theorem tailTrace_8013553 : CollatzResearch.WordTrace tailWord_8013553 prefixEnd_8013553 1371601479759730223577949 := by
  unfold tailWord_8013553
  simp only [CollatzResearch.WordTrace]
  refine ⟨292278289537273561737229313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194852193024849041158152875 292278289537273561737229313)
  ·
    refine ⟨219208717152955171302921985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292278289537273561737229313 219208717152955171302921985)
    ·
      refine ⟨164406537864716378477191489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219208717152955171302921985 164406537864716378477191489)
      ·
        refine ⟨123304903398537283857893617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164406537864716378477191489 123304903398537283857893617)
        ·
          refine ⟨92478677548902962893420213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123304903398537283857893617 92478677548902962893420213)
          ·
            refine ⟨8669876020209652771258145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92478677548902962893420213 8669876020209652771258145)
            ·
              refine ⟨6502407015157239578443609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8669876020209652771258145 6502407015157239578443609)
              ·
                refine ⟨4876805261367929683832707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6502407015157239578443609 4876805261367929683832707)
                ·
                  refine ⟨7315207892051894525749061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4876805261367929683832707 7315207892051894525749061)
                  ·
                    refine ⟨1371601479759730223577949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7315207892051894525749061 1371601479759730223577949)
                    ·
                      rfl

theorem cell23_8013553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 1, 4].length) (baseStart_8013553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013553 prefixEnd_8013553 := by exact prefixLift 8013553
  have htrace : WordTrace (prefixWord ++ tailWord_8013553) baseStart_8013553 baseEnd_8013553 := by
    simpa [prefixWord, tailWord_8013553, baseEnd_8013553] using wordTrace_append hprefix tailTrace_8013553
  have hstable : (prefixWord ++ tailWord_8013553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013553).length < 2 ^ (prefixWord ++ tailWord_8013553).sum := by decide
  have hdescent : baseEnd_8013553 < baseStart_8013553 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013569 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 4, 3, 2]
def baseStart_8013569 : Nat := 118140960795 + 8013569 * 2 ^ 59
def prefixEnd_8013569 : Nat := 4983230072969 + 3 ^ 40 * 8013569 * 2
def baseEnd_8013569 : Nat := 4114812654969662608133773

theorem tailTrace_8013569 : CollatzResearch.WordTrace tailWord_8013569 prefixEnd_8013569 4114812654969662608133773 := by
  unfold tailWord_8013569
  simp only [CollatzResearch.WordTrace]
  refine ⟨292278873105215596469811761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194852582070143730979874507 292278873105215596469811761)
  ·
    refine ⟨219209154828911697352358821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292278873105215596469811761 219209154828911697352358821)
    ·
      refine ⟨41101716530420943253567279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219209154828911697352358821 41101716530420943253567279)
      ·
        refine ⟨61652574795631414880350919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41101716530420943253567279 61652574795631414880350919)
        ·
          refine ⟨92478862193447122320526379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61652574795631414880350919 92478862193447122320526379)
          ·
            refine ⟨138718293290170683480789569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92478862193447122320526379 138718293290170683480789569)
            ·
              refine ⟨104038719967628012610592177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138718293290170683480789569 104038719967628012610592177)
              ·
                refine ⟨78029039975721009457944133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104038719967628012610592177 78029039975721009457944133)
                ·
                  refine ⟨14630444995447689273364525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78029039975721009457944133 14630444995447689273364525)
                  ·
                    refine ⟨5486416873292883477511697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14630444995447689273364525 5486416873292883477511697)
                    ·
                      refine ⟨4114812654969662608133773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5486416873292883477511697 4114812654969662608133773)
                      ·
                        rfl

theorem cell23_8013569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_8013569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013569 prefixEnd_8013569 := by exact prefixLift 8013569
  have htrace : WordTrace (prefixWord ++ tailWord_8013569) baseStart_8013569 baseEnd_8013569 := by
    simpa [prefixWord, tailWord_8013569, baseEnd_8013569] using wordTrace_append hprefix tailTrace_8013569
  have hstable : (prefixWord ++ tailWord_8013569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013569).length < 2 ^ (prefixWord ++ tailWord_8013569).sum := by decide
  have hdescent : baseEnd_8013569 < baseStart_8013569 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013574 : List Nat := [6, 2, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_8013574 : Nat := 118140960795 + 8013574 * 2 ^ 59
def prefixEnd_8013574 : Nat := 4983230072969 + 3 ^ 40 * 8013574 * 2
def baseEnd_8013574 : Nat := 1371605074124311696190417

theorem tailTrace_8013574 : CollatzResearch.WordTrace tailWord_8013574 prefixEnd_8013574 1371605074124311696190417 := by
  unfold tailWord_8013574
  simp only [CollatzResearch.WordTrace]
  refine ⟨9133720483443671322616993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 194852703646798321549162517 9133720483443671322616993)
  ·
    refine ⟨6850290362582753491962745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9133720483443671322616993 6850290362582753491962745)
    ·
      refine ⟨5137717771937065118972059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6850290362582753491962745 5137717771937065118972059)
      ·
        refine ⟨7706576657905597678458089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5137717771937065118972059 7706576657905597678458089)
        ·
          refine ⟨5779932493429198258843567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7706576657905597678458089 5779932493429198258843567)
          ·
            refine ⟨8669898740143797388265351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5779932493429198258843567 8669898740143797388265351)
            ·
              refine ⟨13004848110215696082398027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8669898740143797388265351 13004848110215696082398027)
              ·
                refine ⟨19507272165323544123597041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13004848110215696082398027 19507272165323544123597041)
                ·
                  refine ⟨14630454123992658092697781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19507272165323544123597041 14630454123992658092697781)
                  ·
                    refine ⟨1371605074124311696190417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14630454123992658092697781 1371605074124311696190417)
                    ·
                      rfl

theorem cell23_8013574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_8013574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013574 prefixEnd_8013574 := by exact prefixLift 8013574
  have htrace : WordTrace (prefixWord ++ tailWord_8013574) baseStart_8013574 baseEnd_8013574 := by
    simpa [prefixWord, tailWord_8013574, baseEnd_8013574] using wordTrace_append hprefix tailTrace_8013574
  have hstable : (prefixWord ++ tailWord_8013574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013574).length < 2 ^ (prefixWord ++ tailWord_8013574).sum := by decide
  have hdescent : baseEnd_8013574 < baseStart_8013574 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013592 : List Nat := [2, 1, 2, 3, 1, 1, 4, 2, 1, 6]
def baseStart_8013592 : Nat := 118140960795 + 8013592 * 2 ^ 59
def prefixEnd_8013592 : Nat := 4983230072969 + 3 ^ 40 * 8013592 * 2
def baseEnd_8013592 : Nat := 1371608155008238672715389

theorem tailTrace_8013592 : CollatzResearch.WordTrace tailWord_8013592 prefixEnd_8013592 1371608155008238672715389 := by
  unfold tailWord_8013592
  simp only [CollatzResearch.WordTrace]
  refine ⟨146139855992066135698949515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194853141322754847598599353 146139855992066135698949515)
  ·
    refine ⟨219209783988099203548424273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146139855992066135698949515 219209783988099203548424273)
    ·
      refine ⟨164407337991074402661318205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219209783988099203548424273 164407337991074402661318205)
      ·
        refine ⟨61652751746652900997994327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164407337991074402661318205 61652751746652900997994327)
        ·
          refine ⟨92479127619979351496991491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61652751746652900997994327 92479127619979351496991491)
          ·
            refine ⟨138718691429969027245487237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92479127619979351496991491 138718691429969027245487237)
            ·
              refine ⟨26009754643119192608528857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138718691429969027245487237 26009754643119192608528857)
              ·
                refine ⟨19507315982339394456396643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26009754643119192608528857 19507315982339394456396643)
                ·
                  refine ⟨29260973973509091684594965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19507315982339394456396643 29260973973509091684594965)
                  ·
                    refine ⟨1371608155008238672715389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29260973973509091684594965 1371608155008238672715389)
                    ·
                      rfl

theorem cell23_8013592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_8013592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013592 prefixEnd_8013592 := by exact prefixLift 8013592
  have htrace : WordTrace (prefixWord ++ tailWord_8013592) baseStart_8013592 baseEnd_8013592 := by
    simpa [prefixWord, tailWord_8013592, baseEnd_8013592] using wordTrace_append hprefix tailTrace_8013592
  have hstable : (prefixWord ++ tailWord_8013592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013592).length < 2 ^ (prefixWord ++ tailWord_8013592).sum := by decide
  have hdescent : baseEnd_8013592 < baseStart_8013592 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013599 : List Nat := [1, 1, 2, 4, 2, 1, 3, 3, 1, 1, 4]
def baseStart_8013599 : Nat := 118140960795 + 8013599 * 2 ^ 59
def prefixEnd_8013599 : Nat := 4983230072969 + 3 ^ 40 * 8013599 * 2
def baseEnd_8013599 : Nat := 4114828059389297490758635

theorem tailTrace_8013599 : CollatzResearch.WordTrace tailWord_8013599 prefixEnd_8013599 4114828059389297490758635 := by
  unfold tailWord_8013599
  simp only [CollatzResearch.WordTrace]
  refine ⟨292279967295106911593403851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194853311530071274395602567 292279967295106911593403851)
  ·
    refine ⟨438419950942660367390105777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292279967295106911593403851 438419950942660367390105777)
    ·
      refine ⟨328814963206995275542579333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438419950942660367390105777 328814963206995275542579333)
      ·
        refine ⟨61652805601311614164233625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328814963206995275542579333 61652805601311614164233625)
        ·
          refine ⟨46239604200983710623175219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61652805601311614164233625 46239604200983710623175219)
          ·
            refine ⟨69359406301475565934762829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46239604200983710623175219 69359406301475565934762829)
            ·
              refine ⟨26009777363053337225536061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69359406301475565934762829 26009777363053337225536061)
              ·
                refine ⟨9753666511145001459576023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26009777363053337225536061 9753666511145001459576023)
                ·
                  refine ⟨14630499766717502189364035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9753666511145001459576023 14630499766717502189364035)
                  ·
                    refine ⟨21945749650076253284046053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14630499766717502189364035 21945749650076253284046053)
                    ·
                      refine ⟨4114828059389297490758635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21945749650076253284046053 4114828059389297490758635)
                      ·
                        rfl

theorem cell23_8013599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_8013599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013599 prefixEnd_8013599 := by exact prefixLift 8013599
  have htrace : WordTrace (prefixWord ++ tailWord_8013599) baseStart_8013599 baseEnd_8013599 := by
    simpa [prefixWord, tailWord_8013599, baseEnd_8013599] using wordTrace_append hprefix tailTrace_8013599
  have hstable : (prefixWord ++ tailWord_8013599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013599).length < 2 ^ (prefixWord ++ tailWord_8013599).sum := by decide
  have hdescent : baseEnd_8013599 < baseStart_8013599 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013619 : List Nat := [1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 5]
def baseStart_8013619 : Nat := 118140960795 + 8013619 * 2 ^ 59
def prefixEnd_8013619 : Nat := 4983230072969 + 3 ^ 40 * 8013619 * 2
def baseEnd_8013619 : Nat := 4114838329002387412508543

theorem tailTrace_8013619 : CollatzResearch.WordTrace tailWord_8013619 prefixEnd_8013619 4114838329002387412508543 := by
  unfold tailWord_8013619
  simp only [CollatzResearch.WordTrace]
  refine ⟨292280696755034455009131911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194853797836689636672754607 292280696755034455009131911)
  ·
    refine ⟨438421045132551682513697867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292280696755034455009131911 438421045132551682513697867)
    ·
      refine ⟨657631567698827523770546801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438421045132551682513697867 657631567698827523770546801)
      ·
        refine ⟨493223675774120642827910101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657631567698827523770546801 493223675774120642827910101)
        ·
          refine ⟨11559929900955952566279143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 493223675774120642827910101 11559929900955952566279143)
          ·
            refine ⟨17339894851433928849418715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11559929900955952566279143 17339894851433928849418715)
            ·
              refine ⟨26009842277150893274128073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17339894851433928849418715 26009842277150893274128073)
              ·
                refine ⟨19507381707863169955596055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26009842277150893274128073 19507381707863169955596055)
                ·
                  refine ⟨29261072561794754933394083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19507381707863169955596055 29261072561794754933394083)
                  ·
                    refine ⟨43891608842692132400091125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29261072561794754933394083 43891608842692132400091125)
                    ·
                      refine ⟨4114838329002387412508543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43891608842692132400091125 4114838329002387412508543)
                      ·
                        rfl

theorem cell23_8013619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 5].length) (baseStart_8013619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013619 prefixEnd_8013619 := by exact prefixLift 8013619
  have htrace : WordTrace (prefixWord ++ tailWord_8013619) baseStart_8013619 baseEnd_8013619 := by
    simpa [prefixWord, tailWord_8013619, baseEnd_8013619] using wordTrace_append hprefix tailTrace_8013619
  have hstable : (prefixWord ++ tailWord_8013619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013619).length < 2 ^ (prefixWord ++ tailWord_8013619).sum := by decide
  have hdescent : baseEnd_8013619 < baseStart_8013619 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013629 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 1, 1, 6]
def baseStart_8013629 : Nat := 118140960795 + 8013629 * 2 ^ 59
def prefixEnd_8013629 : Nat := 4983230072969 + 3 ^ 40 * 8013629 * 2
def baseEnd_8013629 : Nat := 4114843463808932373383497

theorem tailTrace_8013629 : CollatzResearch.WordTrace tailWord_8013629 prefixEnd_8013629 4114843463808932373383497 := by
  unfold tailWord_8013629
  simp only [CollatzResearch.WordTrace]
  refine ⟨292281061484998226716995941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194854040989998817811330627 292281061484998226716995941)
  ·
    refine ⟨54802699028437167509436739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292281061484998226716995941 54802699028437167509436739)
    ·
      refine ⟨82204048542655751264155109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54802699028437167509436739 82204048542655751264155109)
      ·
        refine ⟨15413259101747953362029083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82204048542655751264155109 15413259101747953362029083)
        ·
          refine ⟨23119888652621930043043625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15413259101747953362029083 23119888652621930043043625)
          ·
            refine ⟨17339916489466447532282719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23119888652621930043043625 17339916489466447532282719)
            ·
              refine ⟨26009874734199671298424079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17339916489466447532282719 26009874734199671298424079)
              ·
                refine ⟨39014812101299506947636119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26009874734199671298424079 39014812101299506947636119)
                ·
                  refine ⟨58522218151949260421454179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39014812101299506947636119 58522218151949260421454179)
                  ·
                    refine ⟨87783327227923890632181269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58522218151949260421454179 87783327227923890632181269)
                    ·
                      refine ⟨4114843463808932373383497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87783327227923890632181269 4114843463808932373383497)
                      ·
                        rfl

theorem cell23_8013629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_8013629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013629 prefixEnd_8013629 := by exact prefixLift 8013629
  have htrace : WordTrace (prefixWord ++ tailWord_8013629) baseStart_8013629 baseEnd_8013629 := by
    simpa [prefixWord, tailWord_8013629, baseEnd_8013629] using wordTrace_append hprefix tailTrace_8013629
  have hstable : (prefixWord ++ tailWord_8013629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013629).length < 2 ^ (prefixWord ++ tailWord_8013629).sum := by decide
  have hdescent : baseEnd_8013629 < baseStart_8013629 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013650 : List Nat := [3, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2]
def baseStart_8013650 : Nat := 118140960795 + 8013650 * 2 ^ 59
def prefixEnd_8013650 : Nat := 4983230072969 + 3 ^ 40 * 8013650 * 2
def baseEnd_8013650 : Nat := 4114854246902676791220901

theorem tailTrace_8013650 : CollatzResearch.WordTrace tailWord_8013650 prefixEnd_8013650 4114854246902676791220901 := by
  unfold tailWord_8013650
  simp only [CollatzResearch.WordTrace]
  refine ⟨73070456854480536825877601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194854551611948098202340269 73070456854480536825877601)
  ·
    refine ⟨54802842640860402619408201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73070456854480536825877601 54802842640860402619408201)
    ·
      refine ⟨41102131980645301964556151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54802842640860402619408201 41102131980645301964556151)
      ·
        refine ⟨61653197970967952946834227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41102131980645301964556151 61653197970967952946834227)
        ·
          refine ⟨92479796956451929420251341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61653197970967952946834227 92479796956451929420251341)
          ·
            refine ⟨34679923858669473532594253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92479796956451929420251341 34679923858669473532594253)
            ·
              refine ⟨13004971447001052574722845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34679923858669473532594253 13004971447001052574722845)
              ·
                refine ⟨4876864292625394715521067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13004971447001052574722845 4876864292625394715521067)
                ·
                  refine ⟨7315296438938092073281601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4876864292625394715521067 7315296438938092073281601)
                  ·
                    refine ⟨5486472329203569054961201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7315296438938092073281601 5486472329203569054961201)
                    ·
                      refine ⟨4114854246902676791220901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5486472329203569054961201 4114854246902676791220901)
                      ·
                        rfl

theorem cell23_8013650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_8013650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013650 prefixEnd_8013650 := by exact prefixLift 8013650
  have htrace : WordTrace (prefixWord ++ tailWord_8013650) baseStart_8013650 baseEnd_8013650 := by
    simpa [prefixWord, tailWord_8013650, baseEnd_8013650] using wordTrace_append hprefix tailTrace_8013650
  have hstable : (prefixWord ++ tailWord_8013650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013650).length < 2 ^ (prefixWord ++ tailWord_8013650).sum := by decide
  have hdescent : baseEnd_8013650 < baseStart_8013650 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013667 : List Nat := [1, 1, 1, 5, 4, 1, 3, 2, 1, 2, 2]
def baseStart_8013667 : Nat := 118140960795 + 8013667 * 2 ^ 59
def prefixEnd_8013667 : Nat := 4983230072969 + 3 ^ 40 * 8013667 * 2
def baseEnd_8013667 : Nat := 4114862976073803224708323

theorem tailTrace_8013667 : CollatzResearch.WordTrace tailWord_8013667 prefixEnd_8013667 4114862976073803224708323 := by
  unfold tailWord_8013667
  simp only [CollatzResearch.WordTrace]
  refine ⟨292282447458860559206879255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194854964972573706137919503 292282447458860559206879255)
  ·
    refine ⟨438423671188290838810318883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292282447458860559206879255 438423671188290838810318883)
    ·
      refine ⟨657635506782436258215478325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438423671188290838810318883 657635506782436258215478325)
      ·
        refine ⟨61653328760853399207701093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 657635506782436258215478325 61653328760853399207701093)
        ·
          refine ⟨11559999142660012351443955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61653328760853399207701093 11559999142660012351443955)
          ·
            refine ⟨17339998713990018527165933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11559999142660012351443955 17339998713990018527165933)
            ·
              refine ⟨6502499517746256947687225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17339998713990018527165933 6502499517746256947687225)
              ·
                refine ⟨4876874638309692710765419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6502499517746256947687225 4876874638309692710765419)
                ·
                  refine ⟨7315311957464539066148129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4876874638309692710765419 7315311957464539066148129)
                  ·
                    refine ⟨5486483968098404299611097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7315311957464539066148129 5486483968098404299611097)
                    ·
                      refine ⟨4114862976073803224708323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5486483968098404299611097 4114862976073803224708323)
                      ·
                        rfl

theorem cell23_8013667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_8013667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013667 prefixEnd_8013667 := by exact prefixLift 8013667
  have htrace : WordTrace (prefixWord ++ tailWord_8013667) baseStart_8013667 baseEnd_8013667 := by
    simpa [prefixWord, tailWord_8013667, baseEnd_8013667] using wordTrace_append hprefix tailTrace_8013667
  have hstable : (prefixWord ++ tailWord_8013667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013667).length < 2 ^ (prefixWord ++ tailWord_8013667).sum := by decide
  have hdescent : baseEnd_8013667 < baseStart_8013667 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013682 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 1, 8]
def baseStart_8013682 : Nat := 118140960795 + 8013682 * 2 ^ 59
def prefixEnd_8013682 : Nat := 4983230072969 + 3 ^ 40 * 8013682 * 2
def baseEnd_8013682 : Nat := 1371623559427873555340251

theorem tailTrace_8013682 : CollatzResearch.WordTrace tailWord_8013682 prefixEnd_8013682 1371623559427873555340251 := by
  unfold tailWord_8013682
  simp only [CollatzResearch.WordTrace]
  refine ⟨73070748638451554192168825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194855329702537477845783533 73070748638451554192168825)
  ·
    refine ⟨54803061478838665644126619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73070748638451554192168825 54803061478838665644126619)
    ·
      refine ⟨82204592218257998466189929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54803061478838665644126619 82204592218257998466189929)
      ·
        refine ⟨61653444163693498849642447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82204592218257998466189929 61653444163693498849642447)
        ·
          refine ⟨92480166245540248274463671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61653444163693498849642447 92480166245540248274463671)
          ·
            refine ⟨138720249368310372411695507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92480166245540248274463671 138720249368310372411695507)
            ·
              refine ⟨208080374052465558617543261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138720249368310372411695507 208080374052465558617543261)
              ·
                refine ⟨78030140269674584481578723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208080374052465558617543261 78030140269674584481578723)
                ·
                  refine ⟨117045210404511876722368085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78030140269674584481578723 117045210404511876722368085)
                  ·
                    refine ⟨1371623559427873555340251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117045210404511876722368085 1371623559427873555340251)
                    ·
                      rfl

theorem cell23_8013682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_8013682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013682 prefixEnd_8013682 := by exact prefixLift 8013682
  have htrace : WordTrace (prefixWord ++ tailWord_8013682) baseStart_8013682 baseEnd_8013682 := by
    simpa [prefixWord, tailWord_8013682, baseEnd_8013682] using wordTrace_append hprefix tailTrace_8013682
  have hstable : (prefixWord ++ tailWord_8013682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013682).length < 2 ^ (prefixWord ++ tailWord_8013682).sum := by decide
  have hdescent : baseEnd_8013682 < baseStart_8013682 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013718 : List Nat := [5, 3, 1, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_8013718 : Nat := 118140960795 + 8013718 * 2 ^ 59
def prefixEnd_8013718 : Nat := 4983230072969 + 3 ^ 40 * 8013718 * 2
def baseEnd_8013718 : Nat := 4114889163587182525170589

theorem tailTrace_8013718 : CollatzResearch.WordTrace tailWord_8013718 prefixEnd_8013718 4114889163587182525170589 := by
  unfold tailWord_8013718
  simp only [CollatzResearch.WordTrace]
  refine ⟨18267769223854737182311613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194856205054450529944657205 18267769223854737182311613)
  ·
    refine ⟨6850413458945526443366855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18267769223854737182311613 6850413458945526443366855)
    ·
      refine ⟨10275620188418289665050283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6850413458945526443366855 10275620188418289665050283)
      ·
        refine ⟨15413430282627434497575425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10275620188418289665050283 15413430282627434497575425)
        ·
          refine ⟨11560072711970575873181569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15413430282627434497575425 11560072711970575873181569)
          ·
            refine ⟨8670054533977931904886177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11560072711970575873181569 8670054533977931904886177)
            ·
              refine ⟨6502540900483448928664633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8670054533977931904886177 6502540900483448928664633)
              ·
                refine ⟨4876905675362586696498475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6502540900483448928664633 4876905675362586696498475)
                ·
                  refine ⟨7315358513043880044747713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4876905675362586696498475 7315358513043880044747713)
                  ·
                    refine ⟨5486518884782910033560785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7315358513043880044747713 5486518884782910033560785)
                    ·
                      refine ⟨4114889163587182525170589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5486518884782910033560785 4114889163587182525170589)
                      ·
                        rfl

theorem cell23_8013718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_8013718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013718 prefixEnd_8013718 := by exact prefixLift 8013718
  have htrace : WordTrace (prefixWord ++ tailWord_8013718) baseStart_8013718 baseEnd_8013718 := by
    simpa [prefixWord, tailWord_8013718, baseEnd_8013718] using wordTrace_append hprefix tailTrace_8013718
  have hstable : (prefixWord ++ tailWord_8013718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013718).length < 2 ^ (prefixWord ++ tailWord_8013718).sum := by decide
  have hdescent : baseEnd_8013718 < baseStart_8013718 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013796 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 2, 4, 2]
def baseStart_8013796 : Nat := 118140960795 + 8013796 * 2 ^ 59
def prefixEnd_8013796 : Nat := 4983230072969 + 3 ^ 40 * 8013796 * 2
def baseEnd_8013796 : Nat := 4114929215078233219995229

theorem tailTrace_8013796 : CollatzResearch.WordTrace tailWord_8013796 prefixEnd_8013796 4114929215078233219995229 := by
  unfold tailWord_8013796
  simp only [CollatzResearch.WordTrace]
  refine ⟨146143576237696607119162621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194858101650262142825550161 146143576237696607119162621)
  ·
    refine ⟨54803841089136227669685983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146143576237696607119162621 54803841089136227669685983)
    ·
      refine ⟨82205761633704341504528975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54803841089136227669685983 82205761633704341504528975)
      ·
        refine ⟨123308642450556512256793463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82205761633704341504528975 123308642450556512256793463)
        ·
          refine ⟨184962963675834768385190195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123308642450556512256793463 184962963675834768385190195)
          ·
            refine ⟨277444445513752152577785293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184962963675834768385190195 277444445513752152577785293)
            ·
              refine ⟨104041667067657057216669485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277444445513752152577785293 104041667067657057216669485)
              ·
                refine ⟨39015625150371396456251057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104041667067657057216669485 39015625150371396456251057)
                ·
                  refine ⟨29261718862778547342188293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39015625150371396456251057 29261718862778547342188293)
                  ·
                    refine ⟨5486572286770977626660305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29261718862778547342188293 5486572286770977626660305)
                    ·
                      refine ⟨4114929215078233219995229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5486572286770977626660305 4114929215078233219995229)
                      ·
                        rfl

theorem cell23_8013796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_8013796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013796 prefixEnd_8013796 := by exact prefixLift 8013796
  have htrace : WordTrace (prefixWord ++ tailWord_8013796) baseStart_8013796 baseEnd_8013796 := by
    simpa [prefixWord, tailWord_8013796, baseEnd_8013796] using wordTrace_append hprefix tailTrace_8013796
  have hstable : (prefixWord ++ tailWord_8013796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013796).length < 2 ^ (prefixWord ++ tailWord_8013796).sum := by decide
  have hdescent : baseEnd_8013796 < baseStart_8013796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013849 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 3, 5]
def baseStart_8013849 : Nat := 118140960795 + 8013849 * 2 ^ 59
def prefixEnd_8013849 : Nat := 4983230072969 + 3 ^ 40 * 8013849 * 2
def baseEnd_8013849 : Nat := 1371652143184307170877495

theorem tailTrace_8013849 : CollatzResearch.WordTrace tailWord_8013849 prefixEnd_8013849 1371652143184307170877495 := by
  unfold tailWord_8013849
  simp only [CollatzResearch.WordTrace]
  refine ⟨292289085544201204290004601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194859390362800802860003067 292289085544201204290004601)
  ·
    refine ⟨219216814158150903217503451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292289085544201204290004601 219216814158150903217503451)
    ·
      refine ⟨328825221237226354826255177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219216814158150903217503451 328825221237226354826255177)
      ·
        refine ⟨246618915927919766119691383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328825221237226354826255177 246618915927919766119691383)
        ·
          refine ⟨369928373891879649179537075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246618915927919766119691383 369928373891879649179537075)
          ·
            refine ⟨554892560837819473769305613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369928373891879649179537075 554892560837819473769305613)
            ·
              refine ⟨208084710314182302663489605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 554892560837819473769305613 208084710314182302663489605)
              ·
                refine ⟨39015883183909181749404301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208084710314182302663489605 39015883183909181749404301)
                ·
                  refine ⟨14630956193965943156026613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39015883183909181749404301 14630956193965943156026613)
                  ·
                    refine ⟨1371652143184307170877495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14630956193965943156026613 1371652143184307170877495)
                    ·
                      rfl

theorem cell23_8013849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 5].length) (baseStart_8013849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013849 prefixEnd_8013849 := by exact prefixLift 8013849
  have htrace : WordTrace (prefixWord ++ tailWord_8013849) baseStart_8013849 baseEnd_8013849 := by
    simpa [prefixWord, tailWord_8013849, baseEnd_8013849] using wordTrace_append hprefix tailTrace_8013849
  have hstable : (prefixWord ++ tailWord_8013849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013849).length < 2 ^ (prefixWord ++ tailWord_8013849).sum := by decide
  have hdescent : baseEnd_8013849 < baseStart_8013849 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013853 : List Nat := [1, 4, 2, 2, 2, 1, 4, 1, 6]
def baseStart_8013853 : Nat := 118140960795 + 8013853 * 2 ^ 59
def prefixEnd_8013853 : Nat := 4983230072969 + 3 ^ 40 * 8013853 * 2
def baseEnd_8013853 : Nat := 457217609275059944109163

theorem tailTrace_8013853 : CollatzResearch.WordTrace tailWord_8013853 prefixEnd_8013853 457217609275059944109163 := by
  unfold tailWord_8013853
  simp only [CollatzResearch.WordTrace]
  refine ⟨292289231436186712973150213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194859487624124475315433475 292289231436186712973150213)
  ·
    refine ⟨54804230894285008682465665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292289231436186712973150213 54804230894285008682465665)
    ·
      refine ⟨41103173170713756511849249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54804230894285008682465665 41103173170713756511849249)
      ·
        refine ⟨30827379878035317383886937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41103173170713756511849249 30827379878035317383886937)
        ·
          refine ⟨23120534908526488037915203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30827379878035317383886937 23120534908526488037915203)
          ·
            refine ⟨34680802362789732056872805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23120534908526488037915203 34680802362789732056872805)
            ·
              refine ⟨6502650443023074760663651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34680802362789732056872805 6502650443023074760663651)
              ·
                refine ⟨9753975664534612140995477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6502650443023074760663651 9753975664534612140995477)
                ·
                  refine ⟨457217609275059944109163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9753975664534612140995477 457217609275059944109163)
                  ·
                    rfl

theorem cell23_8013853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_8013853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013853 prefixEnd_8013853 := by exact prefixLift 8013853
  have htrace : WordTrace (prefixWord ++ tailWord_8013853) baseStart_8013853 baseEnd_8013853 := by
    simpa [prefixWord, tailWord_8013853, baseEnd_8013853] using wordTrace_append hprefix tailTrace_8013853
  have hstable : (prefixWord ++ tailWord_8013853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013853).length < 2 ^ (prefixWord ++ tailWord_8013853).sum := by decide
  have hdescent : baseEnd_8013853 < baseStart_8013853 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013873 : List Nat := [1, 2, 2, 3, 1, 3, 1, 3, 2, 3, 2]
def baseStart_8013873 : Nat := 118140960795 + 8013873 * 2 ^ 59
def prefixEnd_8013873 : Nat := 4983230072969 + 3 ^ 40 * 8013873 * 2
def baseEnd_8013873 : Nat := 4114968753088629418732375

theorem tailTrace_8013873 : CollatzResearch.WordTrace tailWord_8013873 prefixEnd_8013873 4114968753088629418732375 := by
  unfold tailWord_8013873
  simp only [CollatzResearch.WordTrace]
  refine ⟨292289960896114256388878273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194859973930742837592585515 292289960896114256388878273)
  ·
    refine ⟨219217470672085692291658705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292289960896114256388878273 219217470672085692291658705)
    ·
      refine ⟨164413103004064269218744029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219217470672085692291658705 164413103004064269218744029)
      ·
        refine ⟨61654913626524100957029011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164413103004064269218744029 61654913626524100957029011)
        ·
          refine ⟨92482370439786151435543517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61654913626524100957029011 92482370439786151435543517)
          ·
            refine ⟨34680888914919806788328819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92482370439786151435543517 34680888914919806788328819)
            ·
              refine ⟨52021333372379710182493229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34680888914919806788328819 52021333372379710182493229)
              ·
                refine ⟨19508000014642391318434961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52021333372379710182493229 19508000014642391318434961)
                ·
                  refine ⟨14631000010981793488826221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19508000014642391318434961 14631000010981793488826221)
                  ·
                    refine ⟨5486625004118172558309833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14631000010981793488826221 5486625004118172558309833)
                    ·
                      refine ⟨4114968753088629418732375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5486625004118172558309833 4114968753088629418732375)
                      ·
                        rfl

theorem cell23_8013873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_8013873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013873 prefixEnd_8013873 := by exact prefixLift 8013873
  have htrace : WordTrace (prefixWord ++ tailWord_8013873) baseStart_8013873 baseEnd_8013873 := by
    simpa [prefixWord, tailWord_8013873, baseEnd_8013873] using wordTrace_append hprefix tailTrace_8013873
  have hstable : (prefixWord ++ tailWord_8013873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013873).length < 2 ^ (prefixWord ++ tailWord_8013873).sum := by decide
  have hdescent : baseEnd_8013873 < baseStart_8013873 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013879 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 3, 6]
def baseStart_8013879 : Nat := 118140960795 + 8013879 * 2 ^ 59
def prefixEnd_8013879 : Nat := 4983230072969 + 3 ^ 40 * 8013879 * 2
def baseEnd_8013879 : Nat := 1371657277990852131752449

theorem tailTrace_8013879 : CollatzResearch.WordTrace tailWord_8013879 prefixEnd_8013879 1371657277990852131752449 := by
  unfold tailWord_8013879
  simp only [CollatzResearch.WordTrace]
  refine ⟨292290179734092519413596691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194860119822728346275731127 292290179734092519413596691)
  ·
    refine ⟨438435269601138779120395037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292290179734092519413596691 438435269601138779120395037)
    ·
      refine ⟨164413226100427042170148139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438435269601138779120395037 164413226100427042170148139)
      ·
        refine ⟨246619839150640563255222209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164413226100427042170148139 246619839150640563255222209)
        ·
          refine ⟨184964879362980422441416657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246619839150640563255222209 184964879362980422441416657)
          ·
            refine ⟨138723659522235316831062493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184964879362980422441416657 138723659522235316831062493)
            ·
              refine ⟨52021372320838243811648435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138723659522235316831062493 52021372320838243811648435)
              ·
                refine ⟨78032058481257365717472653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52021372320838243811648435 78032058481257365717472653)
                ·
                  refine ⟨29262021930471512144052245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78032058481257365717472653 29262021930471512144052245)
                  ·
                    refine ⟨1371657277990852131752449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29262021930471512144052245 1371657277990852131752449)
                    ·
                      rfl

theorem cell23_8013879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_8013879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013879 prefixEnd_8013879 := by exact prefixLift 8013879
  have htrace : WordTrace (prefixWord ++ tailWord_8013879) baseStart_8013879 baseEnd_8013879 := by
    simpa [prefixWord, tailWord_8013879, baseEnd_8013879] using wordTrace_append hprefix tailTrace_8013879
  have hstable : (prefixWord ++ tailWord_8013879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013879).length < 2 ^ (prefixWord ++ tailWord_8013879).sum := by decide
  have hdescent : baseEnd_8013879 < baseStart_8013879 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013920 : List Nat := [2, 1, 1, 3, 2, 4, 1, 2, 3, 2, 2]
def baseStart_8013920 : Nat := 118140960795 + 8013920 * 2 ^ 59
def prefixEnd_8013920 : Nat := 4983230072969 + 3 ^ 40 * 8013920 * 2
def baseEnd_8013920 : Nat := 4114992886679390734844659

theorem tailTrace_8013920 : CollatzResearch.WordTrace tailWord_8013920 prefixEnd_8013920 4114992886679390734844659 := by
  unfold tailWord_8013920
  simp only [CollatzResearch.WordTrace]
  refine ⟨146145837563471991707919607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194861116751295988943892809 146145837563471991707919607)
  ·
    refine ⟨219218756345207987561879411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146145837563471991707919607 219218756345207987561879411)
    ·
      refine ⟨328828134517811981342819117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219218756345207987561879411 328828134517811981342819117)
      ·
        refine ⟨123310550444179493003557169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328828134517811981342819117 123310550444179493003557169)
        ·
          refine ⟨92482912833134619752667877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123310550444179493003557169 92482912833134619752667877)
          ·
            refine ⟨17340546156212741203625227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92482912833134619752667877 17340546156212741203625227)
            ·
              refine ⟨26010819234319111805437841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17340546156212741203625227 26010819234319111805437841)
              ·
                refine ⟨19508114425739333854078381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26010819234319111805437841 19508114425739333854078381)
                ·
                  refine ⟨7315542909652250195279393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19508114425739333854078381 7315542909652250195279393)
                  ·
                    refine ⟨5486657182239187646459545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7315542909652250195279393 5486657182239187646459545)
                    ·
                      refine ⟨4114992886679390734844659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5486657182239187646459545 4114992886679390734844659)
                      ·
                        rfl

theorem cell23_8013920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_8013920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013920 prefixEnd_8013920 := by exact prefixLift 8013920
  have htrace : WordTrace (prefixWord ++ tailWord_8013920) baseStart_8013920 baseEnd_8013920 := by
    simpa [prefixWord, tailWord_8013920, baseEnd_8013920] using wordTrace_append hprefix tailTrace_8013920
  have hstable : (prefixWord ++ tailWord_8013920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013920).length < 2 ^ (prefixWord ++ tailWord_8013920).sum := by decide
  have hdescent : baseEnd_8013920 < baseStart_8013920 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013937 : List Nat := [1, 2, 2, 2, 1, 1, 6, 3, 1, 2, 2]
def baseStart_8013937 : Nat := 118140960795 + 8013937 * 2 ^ 59
def prefixEnd_8013937 : Nat := 4983230072969 + 3 ^ 40 * 8013937 * 2
def baseEnd_8013937 : Nat := 4115001615850517168332081

theorem tailTrace_8013937 : CollatzResearch.WordTrace tailWord_8013937 prefixEnd_8013937 4115001615850517168332081 := by
  unfold tailWord_8013937
  simp only [CollatzResearch.WordTrace]
  refine ⟨292292295167882395319208065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194861530111921596879472043 292292295167882395319208065)
  ·
    refine ⟨219219221375911796489406049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292292295167882395319208065 219219221375911796489406049)
    ·
      refine ⟨164414416031933847367054537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219219221375911796489406049 164414416031933847367054537)
      ·
        refine ⟨123310812023950385525290903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164414416031933847367054537 123310812023950385525290903)
        ·
          refine ⟨184966218035925578287936355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123310812023950385525290903 184966218035925578287936355)
          ·
            refine ⟨277449327053888367431904533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184966218035925578287936355 277449327053888367431904533)
            ·
              refine ⟨13005437205651017223370525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 277449327053888367431904533 13005437205651017223370525)
              ·
                refine ⟨4877038952119131458763947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13005437205651017223370525 4877038952119131458763947)
                ·
                  refine ⟨7315558428178697188145921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4877038952119131458763947 7315558428178697188145921)
                  ·
                    refine ⟨5486668821134022891109441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7315558428178697188145921 5486668821134022891109441)
                    ·
                      refine ⟨4115001615850517168332081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5486668821134022891109441 4115001615850517168332081)
                      ·
                        rfl

theorem cell23_8013937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 1, 2, 2].length) (baseStart_8013937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013937 prefixEnd_8013937 := by exact prefixLift 8013937
  have htrace : WordTrace (prefixWord ++ tailWord_8013937) baseStart_8013937 baseEnd_8013937 := by
    simpa [prefixWord, tailWord_8013937, baseEnd_8013937] using wordTrace_append hprefix tailTrace_8013937
  have hstable : (prefixWord ++ tailWord_8013937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013937).length < 2 ^ (prefixWord ++ tailWord_8013937).sum := by decide
  have hdescent : baseEnd_8013937 < baseStart_8013937 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8013997 : List Nat := [1, 5, 2, 1, 2, 1, 2, 3, 1, 3, 2]
def baseStart_8013997 : Nat := 118140960795 + 8013997 * 2 ^ 59
def prefixEnd_8013997 : Nat := 4983230072969 + 3 ^ 40 * 8013997 * 2
def baseEnd_8013997 : Nat := 4115032424689786933581805

theorem tailTrace_8013997 : CollatzResearch.WordTrace tailWord_8013997 prefixEnd_8013997 4115032424689786933581805 := by
  unfold tailWord_8013997
  simp only [CollatzResearch.WordTrace]
  refine ⟨292294483547665025566392245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194862989031776683710928163 292294483547665025566392245)
  ·
    refine ⟨27402607832593596146849273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 292294483547665025566392245 27402607832593596146849273)
    ·
      refine ⟨20551955874445197110136955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27402607832593596146849273 20551955874445197110136955)
      ·
        refine ⟨30827933811667795665205433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20551955874445197110136955 30827933811667795665205433)
        ·
          refine ⟨23120950358750846748904075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30827933811667795665205433 23120950358750846748904075)
          ·
            refine ⟨34681425538126270123356113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23120950358750846748904075 34681425538126270123356113)
            ·
              refine ⟨26011069153594702592517085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34681425538126270123356113 26011069153594702592517085)
              ·
                refine ⟨9754150932598013472193907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26011069153594702592517085 9754150932598013472193907)
                ·
                  refine ⟨14631226398897020208290861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9754150932598013472193907 14631226398897020208290861)
                  ·
                    refine ⟨5486709899586382578109073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14631226398897020208290861 5486709899586382578109073)
                    ·
                      refine ⟨4115032424689786933581805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5486709899586382578109073 4115032424689786933581805)
                      ·
                        rfl

theorem cell23_8013997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_8013997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8013997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8013997 prefixEnd_8013997 := by exact prefixLift 8013997
  have htrace : WordTrace (prefixWord ++ tailWord_8013997) baseStart_8013997 baseEnd_8013997 := by
    simpa [prefixWord, tailWord_8013997, baseEnd_8013997] using wordTrace_append hprefix tailTrace_8013997
  have hstable : (prefixWord ++ tailWord_8013997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8013997).length < 2 ^ (prefixWord ++ tailWord_8013997).sum := by decide
  have hdescent : baseEnd_8013997 < baseStart_8013997 := by decide
  rcases family_descends (prefixWord ++ tailWord_8013997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014010 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2]
def baseStart_8014010 : Nat := 118140960795 + 8014010 * 2 ^ 59
def prefixEnd_8014010 : Nat := 4983230072969 + 3 ^ 40 * 8014010 * 2
def baseEnd_8014010 : Nat := 4115039099938295382719245

theorem tailTrace_8014010 : CollatzResearch.WordTrace tailWord_8014010 prefixEnd_8014010 4115039099938295382719245 := by
  unfold tailWord_8014010
  simp only [CollatzResearch.WordTrace]
  refine ⟨73073739424154482196653871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194863305131078619191076989 73073739424154482196653871)
  ·
    refine ⟨109610609136231723294980807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73073739424154482196653871 109610609136231723294980807)
    ·
      refine ⟨164415913704347584942471211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109610609136231723294980807 164415913704347584942471211)
      ·
        refine ⟨246623870556521377413706817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164415913704347584942471211 246623870556521377413706817)
        ·
          refine ⟨184967902917391033060280113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246623870556521377413706817 184967902917391033060280113)
          ·
            refine ⟨138725927188043274795210085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184967902917391033060280113 138725927188043274795210085)
            ·
              refine ⟨26011111347758114024101891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138725927188043274795210085 26011111347758114024101891)
              ·
                refine ⟨39016667021637171036152837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26011111347758114024101891 39016667021637171036152837)
                ·
                  refine ⟨7315625066556969569278657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39016667021637171036152837 7315625066556969569278657)
                  ·
                    refine ⟨5486718799917727176958993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7315625066556969569278657 5486718799917727176958993)
                    ·
                      refine ⟨4115039099938295382719245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5486718799917727176958993 4115039099938295382719245)
                      ·
                        rfl

theorem cell23_8014010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2].length) (baseStart_8014010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014010 prefixEnd_8014010 := by exact prefixLift 8014010
  have htrace : WordTrace (prefixWord ++ tailWord_8014010) baseStart_8014010 baseEnd_8014010 := by
    simpa [prefixWord, tailWord_8014010, baseEnd_8014010] using wordTrace_append hprefix tailTrace_8014010
  have hstable : (prefixWord ++ tailWord_8014010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014010).length < 2 ^ (prefixWord ++ tailWord_8014010).sum := by decide
  have hdescent : baseEnd_8014010 < baseStart_8014010 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014044 : List Nat := [2, 2, 5, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_8014044 : Nat := 118140960795 + 8014044 * 2 ^ 59
def prefixEnd_8014044 : Nat := 4983230072969 + 3 ^ 40 * 8014044 * 2
def baseEnd_8014044 : Nat := 4115056558280548249694089

theorem tailTrace_8014044 : CollatzResearch.WordTrace tailWord_8014044 prefixEnd_8014044 4115056558280548249694089 := by
  unfold tailWord_8014044
  simp only [CollatzResearch.WordTrace]
  refine ⟨146148098889247376296676593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194864131852329835062235457 146148098889247376296676593)
  ·
    refine ⟨109611074166935532222507445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146148098889247376296676593 109611074166935532222507445)
    ·
      refine ⟨10276038203150206145860073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109611074166935532222507445 10276038203150206145860073)
      ·
        refine ⟨7707028652362654609395055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10276038203150206145860073 7707028652362654609395055)
        ·
          refine ⟨11560542978543981914092583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7707028652362654609395055 11560542978543981914092583)
          ·
            refine ⟨17340814467815972871138875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11560542978543981914092583 17340814467815972871138875)
            ·
              refine ⟨26011221701723959306708313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17340814467815972871138875 26011221701723959306708313)
              ·
                refine ⟨19508416276292969480031235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26011221701723959306708313 19508416276292969480031235)
                ·
                  refine ⟨29262624414439454220046853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19508416276292969480031235 29262624414439454220046853)
                  ·
                    refine ⟨5486742077707397666258785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29262624414439454220046853 5486742077707397666258785)
                    ·
                      refine ⟨4115056558280548249694089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5486742077707397666258785 4115056558280548249694089)
                      ·
                        rfl

theorem cell23_8014044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_8014044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014044 prefixEnd_8014044 := by exact prefixLift 8014044
  have htrace : WordTrace (prefixWord ++ tailWord_8014044) baseStart_8014044 baseEnd_8014044 := by
    simpa [prefixWord, tailWord_8014044, baseEnd_8014044] using wordTrace_append hprefix tailTrace_8014044
  have hstable : (prefixWord ++ tailWord_8014044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014044).length < 2 ^ (prefixWord ++ tailWord_8014044).sum := by decide
  have hdescent : baseEnd_8014044 < baseStart_8014044 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014063 : List Nat := [1, 1, 2, 1, 6, 1, 2, 2, 2, 5]
def baseStart_8014063 : Nat := 118140960795 + 8014063 * 2 ^ 59
def prefixEnd_8014063 : Nat := 4983230072969 + 3 ^ 40 * 8014063 * 2
def baseEnd_8014063 : Nat := 1371688771470994558452167

theorem tailTrace_8014063 : CollatzResearch.WordTrace tailWord_8014063 prefixEnd_8014063 1371688771470994558452167 := by
  unfold tailWord_8014063
  simp only [CollatzResearch.WordTrace]
  refine ⟨292296890765425918838294843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194864593843617279225529895 292296890765425918838294843)
  ·
    refine ⟨438445336148138878257442265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292296890765425918838294843 438445336148138878257442265)
    ·
      refine ⟨328834002111104158693081699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438445336148138878257442265 328834002111104158693081699)
      ·
        refine ⟨493251003166656238039622549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328834002111104158693081699 493251003166656238039622549)
        ·
          refine ⟨23121140773437011158107307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 493251003166656238039622549 23121140773437011158107307)
          ·
            refine ⟨34681711160155516737160961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23121140773437011158107307 34681711160155516737160961)
            ·
              refine ⟨26011283370116637552870721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34681711160155516737160961 26011283370116637552870721)
              ·
                refine ⟨19508462527587478164653041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26011283370116637552870721 19508462527587478164653041)
                ·
                  refine ⟨14631346895690608623489781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19508462527587478164653041 14631346895690608623489781)
                  ·
                    refine ⟨1371688771470994558452167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14631346895690608623489781 1371688771470994558452167)
                    ·
                      rfl

theorem cell23_8014063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 5].length) (baseStart_8014063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014063 prefixEnd_8014063 := by exact prefixLift 8014063
  have htrace : WordTrace (prefixWord ++ tailWord_8014063) baseStart_8014063 baseEnd_8014063 := by
    simpa [prefixWord, tailWord_8014063, baseEnd_8014063] using wordTrace_append hprefix tailTrace_8014063
  have hstable : (prefixWord ++ tailWord_8014063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014063).length < 2 ^ (prefixWord ++ tailWord_8014063).sum := by decide
  have hdescent : baseEnd_8014063 < baseStart_8014063 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014070 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2]
def baseStart_8014070 : Nat := 118140960795 + 8014070 * 2 ^ 59
def prefixEnd_8014070 : Nat := 4983230072969 + 3 ^ 40 * 8014070 * 2
def baseEnd_8014070 : Nat := 4115069908777565147968969

theorem tailTrace_8014070 : CollatzResearch.WordTrace tailWord_8014070 prefixEnd_8014070 4115069908777565147968969 := by
  unfold tailWord_8014070
  simp only [CollatzResearch.WordTrace]
  refine ⟨18268571629775034939612479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194864764050933706022533109 18268571629775034939612479)
  ·
    refine ⟨27402857444662552409418719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18268571629775034939612479 27402857444662552409418719)
    ·
      refine ⟨41104286166993828614128079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27402857444662552409418719 41104286166993828614128079)
      ·
        refine ⟨61656429250490742921192119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41104286166993828614128079 61656429250490742921192119)
        ·
          refine ⟨92484643875736114381788179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61656429250490742921192119 92484643875736114381788179)
          ·
            refine ⟨138726965813604171572682269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92484643875736114381788179 138726965813604171572682269)
            ·
              refine ⟨52022612180101564339755851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138726965813604171572682269 52022612180101564339755851)
              ·
                refine ⟨78033918270152346509633777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52022612180101564339755851 78033918270152346509633777)
                ·
                  refine ⟨58525438702614259882225333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78033918270152346509633777 58525438702614259882225333)
                  ·
                    refine ⟨5486759878370086863958625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58525438702614259882225333 5486759878370086863958625)
                    ·
                      refine ⟨4115069908777565147968969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5486759878370086863958625 4115069908777565147968969)
                      ·
                        rfl

theorem cell23_8014070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_8014070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014070 prefixEnd_8014070 := by exact prefixLift 8014070
  have htrace : WordTrace (prefixWord ++ tailWord_8014070) baseStart_8014070 baseEnd_8014070 := by
    simpa [prefixWord, tailWord_8014070, baseEnd_8014070] using wordTrace_append hprefix tailTrace_8014070
  have hstable : (prefixWord ++ tailWord_8014070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014070).length < 2 ^ (prefixWord ++ tailWord_8014070).sum := by decide
  have hdescent : baseEnd_8014070 < baseStart_8014070 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014140 : List Nat := [2, 2, 2, 2, 1, 2, 5, 1, 6]
def baseStart_8014140 : Nat := 118140960795 + 8014140 * 2 ^ 59
def prefixEnd_8014140 : Nat := 4983230072969 + 3 ^ 40 * 8014140 * 2
def baseEnd_8014140 : Nat := 457233983602597763788183

theorem tailTrace_8014140 : CollatzResearch.WordTrace tailWord_8014140 prefixEnd_8014140 457233983602597763788183 := by
  unfold tailWord_8014140
  simp only [CollatzResearch.WordTrace]
  refine ⟨146149849593073480494423937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194866466124097973992565249 146149849593073480494423937)
  ·
    refine ⟨109612387194805110370817953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146149849593073480494423937 109612387194805110370817953)
    ·
      refine ⟨82209290396103832778113465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109612387194805110370817953 82209290396103832778113465)
      ·
        refine ⟨61656967797077874583585099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82209290396103832778113465 61656967797077874583585099)
        ·
          refine ⟨92485451695616811875377649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61656967797077874583585099 92485451695616811875377649)
          ·
            refine ⟨69364088771712608906533237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92485451695616811875377649 69364088771712608906533237)
            ·
              refine ⟨6502883322348057084987491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69364088771712608906533237 6502883322348057084987491)
              ·
                refine ⟨9754324983522085627481237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6502883322348057084987491 9754324983522085627481237)
                ·
                  refine ⟨457233983602597763788183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9754324983522085627481237 457233983602597763788183)
                  ·
                    rfl

theorem cell23_8014140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 6].length) (baseStart_8014140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014140 prefixEnd_8014140 := by exact prefixLift 8014140
  have htrace : WordTrace (prefixWord ++ tailWord_8014140) baseStart_8014140 baseEnd_8014140 := by
    simpa [prefixWord, tailWord_8014140, baseEnd_8014140] using wordTrace_append hprefix tailTrace_8014140
  have hstable : (prefixWord ++ tailWord_8014140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014140).length < 2 ^ (prefixWord ++ tailWord_8014140).sum := by decide
  have hdescent : baseEnd_8014140 < baseStart_8014140 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014160 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 1, 5, 2]
def baseStart_8014160 : Nat := 118140960795 + 8014160 * 2 ^ 59
def prefixEnd_8014160 : Nat := 4983230072969 + 3 ^ 40 * 8014160 * 2
def baseEnd_8014160 : Nat := 4115116122036469795843555

theorem tailTrace_8014160 : CollatzResearch.WordTrace tailWord_8014160 prefixEnd_8014160 4115116122036469795843555 := by
  unfold tailWord_8014160
  simp only [CollatzResearch.WordTrace]
  refine ⟨146150214323037252202287967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194866952430716336269717289 146150214323037252202287967)
  ·
    refine ⟨219225321484555878303431951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146150214323037252202287967 219225321484555878303431951)
    ·
      refine ⟨328837982226833817455147927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219225321484555878303431951 328837982226833817455147927)
      ·
        refine ⟨493256973340250726182721891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328837982226833817455147927 493256973340250726182721891)
        ·
          refine ⟨739885460010376089274082837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493256973340250726182721891 739885460010376089274082837)
          ·
            refine ⟨34682130937986379184722633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 739885460010376089274082837 34682130937986379184722633)
            ·
              refine ⟨26011598203489784388541975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34682130937986379184722633 26011598203489784388541975)
              ·
                refine ⟨39017397305234676582812963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26011598203489784388541975 39017397305234676582812963)
                ·
                  refine ⟨58526095957852014874219445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39017397305234676582812963 58526095957852014874219445)
                  ·
                    refine ⟨5486821496048626394458073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58526095957852014874219445 5486821496048626394458073)
                    ·
                      refine ⟨4115116122036469795843555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5486821496048626394458073 4115116122036469795843555)
                      ·
                        rfl

theorem cell23_8014160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 1, 5, 2].length) (baseStart_8014160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014160 prefixEnd_8014160 := by exact prefixLift 8014160
  have htrace : WordTrace (prefixWord ++ tailWord_8014160) baseStart_8014160 baseEnd_8014160 := by
    simpa [prefixWord, tailWord_8014160, baseEnd_8014160] using wordTrace_append hprefix tailTrace_8014160
  have hstable : (prefixWord ++ tailWord_8014160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014160).length < 2 ^ (prefixWord ++ tailWord_8014160).sum := by decide
  have hdescent : baseEnd_8014160 < baseStart_8014160 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014184 : List Nat := [2, 1, 4, 2, 2, 3, 1, 1, 3, 1, 3]
def baseStart_8014184 : Nat := 118140960795 + 8014184 * 2 ^ 59
def prefixEnd_8014184 : Nat := 4983230072969 + 3 ^ 40 * 8014184 * 2
def baseEnd_8014184 : Nat := 4115128445572177701943445

theorem tailTrace_8014184 : CollatzResearch.WordTrace tailWord_8014184 prefixEnd_8014184 4115128445572177701943445 := by
  unfold tailWord_8014184
  simp only [CollatzResearch.WordTrace]
  refine ⟨146150651998993778251724803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194867535998658371002299737 146150651998993778251724803)
  ·
    refine ⟨219225977998490667377587205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146150651998993778251724803 219225977998490667377587205)
    ·
      refine ⟨41104870874717000133297601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219225977998490667377587205 41104870874717000133297601)
      ·
        refine ⟨30828653156037750099973201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41104870874717000133297601 30828653156037750099973201)
        ·
          refine ⟨23121489867028312574979901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30828653156037750099973201 23121489867028312574979901)
          ·
            refine ⟨8670558700135617215617463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23121489867028312574979901 8670558700135617215617463)
            ·
              refine ⟨13005838050203425823426195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8670558700135617215617463 13005838050203425823426195)
              ·
                refine ⟨19508757075305138735139293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13005838050203425823426195 19508757075305138735139293)
                ·
                  refine ⟨7315783903239427025677235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19508757075305138735139293 7315783903239427025677235)
                  ·
                    refine ⟨10973675854859140538515853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7315783903239427025677235 10973675854859140538515853)
                    ·
                      refine ⟨4115128445572177701943445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10973675854859140538515853 4115128445572177701943445)
                      ·
                        rfl

theorem cell23_8014184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_8014184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014184 prefixEnd_8014184 := by exact prefixLift 8014184
  have htrace : WordTrace (prefixWord ++ tailWord_8014184) baseStart_8014184 baseEnd_8014184 := by
    simpa [prefixWord, tailWord_8014184, baseEnd_8014184] using wordTrace_append hprefix tailTrace_8014184
  have hstable : (prefixWord ++ tailWord_8014184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014184).length < 2 ^ (prefixWord ++ tailWord_8014184).sum := by decide
  have hdescent : baseEnd_8014184 < baseStart_8014184 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014193 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 2, 6, 3]
def baseStart_8014193 : Nat := 118140960795 + 8014193 * 2 ^ 59
def prefixEnd_8014193 : Nat := 4983230072969 + 3 ^ 40 * 8014193 * 2
def baseEnd_8014193 : Nat := 4115133066898068166730903

theorem tailTrace_8014193 : CollatzResearch.WordTrace tailWord_8014193 prefixEnd_8014193 4115133066898068166730903 := by
  unfold tailWord_8014193
  simp only [CollatzResearch.WordTrace]
  refine ⟨292301632254954951040527233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194867754836636634027018155 292301632254954951040527233)
  ·
    refine ⟨219226224191216213280395425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292301632254954951040527233 219226224191216213280395425)
    ·
      refine ⟨164419668143412159960296569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219226224191216213280395425 164419668143412159960296569)
      ·
        refine ⟨123314751107559119970222427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164419668143412159960296569 123314751107559119970222427)
        ·
          refine ⟨184972126661338679955333641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123314751107559119970222427 184972126661338679955333641)
          ·
            refine ⟨138729094996004009966500231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184972126661338679955333641 138729094996004009966500231)
            ·
              refine ⟨208093642494006014949750347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138729094996004009966500231 208093642494006014949750347)
              ·
                refine ⟨312140463741009022424625521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208093642494006014949750347 312140463741009022424625521)
                ·
                  refine ⟨234105347805756766818469141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312140463741009022424625521 234105347805756766818469141)
                  ·
                    refine ⟨10973688178394848444615741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 234105347805756766818469141 10973688178394848444615741)
                    ·
                      refine ⟨4115133066898068166730903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10973688178394848444615741 4115133066898068166730903)
                      ·
                        rfl

theorem cell23_8014193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_8014193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014193 prefixEnd_8014193 := by exact prefixLift 8014193
  have htrace : WordTrace (prefixWord ++ tailWord_8014193) baseStart_8014193 baseEnd_8014193 := by
    simpa [prefixWord, tailWord_8014193, baseEnd_8014193] using wordTrace_append hprefix tailTrace_8014193
  have hstable : (prefixWord ++ tailWord_8014193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014193).length < 2 ^ (prefixWord ++ tailWord_8014193).sum := by decide
  have hdescent : baseEnd_8014193 < baseStart_8014193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014203 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 6]
def baseStart_8014203 : Nat := 118140960795 + 8014203 * 2 ^ 59
def prefixEnd_8014203 : Nat := 4983230072969 + 3 ^ 40 * 8014203 * 2
def baseEnd_8014203 : Nat := 4115138201704613127605857

theorem tailTrace_8014203 : CollatzResearch.WordTrace tailWord_8014203 prefixEnd_8014203 4115138201704613127605857 := by
  unfold tailWord_8014203
  simp only [CollatzResearch.WordTrace]
  refine ⟨292301996984918722748391263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194867997989945815165594175 292301996984918722748391263)
  ·
    refine ⟨438452995477378084122586895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292301996984918722748391263 438452995477378084122586895)
    ·
      refine ⟨657679493216067126183880343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438452995477378084122586895 657679493216067126183880343)
      ·
        refine ⟨986519239824100689275820515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657679493216067126183880343 986519239824100689275820515)
        ·
          refine ⟨1479778859736151033913730773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 986519239824100689275820515 1479778859736151033913730773)
          ·
            refine ⟨34682317025066039857353065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1479778859736151033913730773 34682317025066039857353065)
            ·
              refine ⟨26011737768799529893014799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34682317025066039857353065 26011737768799529893014799)
              ·
                refine ⟨39017606653199294839522199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26011737768799529893014799 39017606653199294839522199)
                ·
                  refine ⟨58526409979798942259283299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39017606653199294839522199 58526409979798942259283299)
                  ·
                    refine ⟨87789614969698413388924949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58526409979798942259283299 87789614969698413388924949)
                    ·
                      refine ⟨4115138201704613127605857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87789614969698413388924949 4115138201704613127605857)
                      ·
                        rfl

theorem cell23_8014203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 6].length) (baseStart_8014203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014203 prefixEnd_8014203 := by exact prefixLift 8014203
  have htrace : WordTrace (prefixWord ++ tailWord_8014203) baseStart_8014203 baseEnd_8014203 := by
    simpa [prefixWord, tailWord_8014203, baseEnd_8014203] using wordTrace_append hprefix tailTrace_8014203
  have hstable : (prefixWord ++ tailWord_8014203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014203).length < 2 ^ (prefixWord ++ tailWord_8014203).sum := by decide
  have hdescent : baseEnd_8014203 < baseStart_8014203 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014220 : List Nat := [2, 2, 1, 2, 1, 5, 1, 2, 1, 2, 4]
def baseStart_8014220 : Nat := 118140960795 + 8014220 * 2 ^ 59
def prefixEnd_8014220 : Nat := 4983230072969 + 3 ^ 40 * 8014220 * 2
def baseEnd_8014220 : Nat := 4115146930875739561093279

theorem tailTrace_8014220 : CollatzResearch.WordTrace tailWord_8014220 prefixEnd_8014220 4115146930875739561093279 := by
  unfold tailWord_8014220
  simp only [CollatzResearch.WordTrace]
  refine ⟨146151308512928567325880057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194868411350571423101173409 146151308512928567325880057)
  ·
    refine ⟨109613481384696425494410043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146151308512928567325880057 109613481384696425494410043)
    ·
      refine ⟨164420222077044638241615065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109613481384696425494410043 164420222077044638241615065)
      ·
        refine ⟨123315166557783478681211299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164420222077044638241615065 123315166557783478681211299)
        ·
          refine ⟨184972749836675218021816949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123315166557783478681211299 184972749836675218021816949)
          ·
            refine ⟨17341195297188301689545339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184972749836675218021816949 17341195297188301689545339)
            ·
              refine ⟨26011792945782452534318009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17341195297188301689545339 26011792945782452534318009)
              ·
                refine ⟨19508844709336839400738507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26011792945782452534318009 19508844709336839400738507)
                ·
                  refine ⟨29263267064005259101107761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19508844709336839400738507 29263267064005259101107761)
                  ·
                    refine ⟨21947450298003944325830821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29263267064005259101107761 21947450298003944325830821)
                    ·
                      refine ⟨4115146930875739561093279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21947450298003944325830821 4115146930875739561093279)
                      ·
                        rfl

theorem cell23_8014220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_8014220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014220 prefixEnd_8014220 := by exact prefixLift 8014220
  have htrace : WordTrace (prefixWord ++ tailWord_8014220) baseStart_8014220 baseEnd_8014220 := by
    simpa [prefixWord, tailWord_8014220, baseEnd_8014220] using wordTrace_append hprefix tailTrace_8014220
  have hstable : (prefixWord ++ tailWord_8014220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014220).length < 2 ^ (prefixWord ++ tailWord_8014220).sum := by decide
  have hdescent : baseEnd_8014220 < baseStart_8014220 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014243 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 2, 7]
def baseStart_8014243 : Nat := 118140960795 + 8014243 * 2 ^ 59
def prefixEnd_8014243 : Nat := 4983230072969 + 3 ^ 40 * 8014243 * 2
def baseEnd_8014243 : Nat := 1371719580310264323701891

theorem tailTrace_8014243 : CollatzResearch.WordTrace tailWord_8014243 prefixEnd_8014243 1371719580310264323701891 := by
  unfold tailWord_8014243
  simp only [CollatzResearch.WordTrace]
  refine ⟨292303455904773809579847383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194868970603182539719898255 292303455904773809579847383)
  ·
    refine ⟨438455183857160714369771075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292303455904773809579847383 438455183857160714369771075)
    ·
      refine ⟨657682775785741071554656613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438455183857160714369771075 657682775785741071554656613)
      ·
        refine ⟨123315520459826450916498115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 657682775785741071554656613 123315520459826450916498115)
        ·
          refine ⟨184973280689739676374747173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123315520459826450916498115 184973280689739676374747173)
          ·
            refine ⟨34682490129326189320265095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184973280689739676374747173 34682490129326189320265095)
            ·
              refine ⟨52023735193989283980397643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34682490129326189320265095 52023735193989283980397643)
              ·
                refine ⟨78035602790983925970596465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52023735193989283980397643 78035602790983925970596465)
                ·
                  refine ⟨58526702093237944477947349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78035602790983925970596465 58526702093237944477947349)
                  ·
                    refine ⟨1371719580310264323701891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58526702093237944477947349 1371719580310264323701891)
                    ·
                      rfl

theorem cell23_8014243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 7].length) (baseStart_8014243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014243 prefixEnd_8014243 := by exact prefixLift 8014243
  have htrace : WordTrace (prefixWord ++ tailWord_8014243) baseStart_8014243 baseEnd_8014243 := by
    simpa [prefixWord, tailWord_8014243, baseEnd_8014243] using wordTrace_append hprefix tailTrace_8014243
  have hstable : (prefixWord ++ tailWord_8014243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014243).length < 2 ^ (prefixWord ++ tailWord_8014243).sum := by decide
  have hdescent : baseEnd_8014243 < baseStart_8014243 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014257 : List Nat := [1, 2, 2, 4, 1, 3, 2, 1, 1, 3, 3]
def baseStart_8014257 : Nat := 118140960795 + 8014257 * 2 ^ 59
def prefixEnd_8014257 : Nat := 4983230072969 + 3 ^ 40 * 8014257 * 2
def baseEnd_8014257 : Nat := 4115165929659955916330609

theorem tailTrace_8014257 : CollatzResearch.WordTrace tailWord_8014257 prefixEnd_8014257 4115165929659955916330609 := by
  unfold tailWord_8014257
  simp only [CollatzResearch.WordTrace]
  refine ⟨292303966526723089970857025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194869311017815393313904683 292303966526723089970857025)
  ·
    refine ⟨219227974895042317478142769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292303966526723089970857025 219227974895042317478142769)
    ·
      refine ⟨164420981171281738108607077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219227974895042317478142769 164420981171281738108607077)
      ·
        refine ⟨30828933969615325895363827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164420981171281738108607077 30828933969615325895363827)
        ·
          refine ⟨46243400954422988843045741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30828933969615325895363827 46243400954422988843045741)
          ·
            refine ⟨17341275357908620816142153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46243400954422988843045741 17341275357908620816142153)
            ·
              refine ⟨13005956518431465612106615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17341275357908620816142153 13005956518431465612106615)
              ·
                refine ⟨19508934777647198418159923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13005956518431465612106615 19508934777647198418159923)
                ·
                  refine ⟨29263402166470797627239885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19508934777647198418159923 29263402166470797627239885)
                  ·
                    refine ⟨10973775812426549110214957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29263402166470797627239885 10973775812426549110214957)
                    ·
                      refine ⟨4115165929659955916330609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10973775812426549110214957 4115165929659955916330609)
                      ·
                        rfl

theorem cell23_8014257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_8014257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014257 prefixEnd_8014257 := by exact prefixLift 8014257
  have htrace : WordTrace (prefixWord ++ tailWord_8014257) baseStart_8014257 baseEnd_8014257 := by
    simpa [prefixWord, tailWord_8014257, baseEnd_8014257] using wordTrace_append hprefix tailTrace_8014257
  have hstable : (prefixWord ++ tailWord_8014257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014257).length < 2 ^ (prefixWord ++ tailWord_8014257).sum := by decide
  have hdescent : baseEnd_8014257 < baseStart_8014257 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014283 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 5]
def baseStart_8014283 : Nat := 118140960795 + 8014283 * 2 ^ 59
def prefixEnd_8014283 : Nat := 4983230072969 + 3 ^ 40 * 8014283 * 2
def baseEnd_8014283 : Nat := 4115179280156972814605489

theorem tailTrace_8014283 : CollatzResearch.WordTrace tailWord_8014283 prefixEnd_8014283 4115179280156972814605489 := by
  unfold tailWord_8014283
  simp only [CollatzResearch.WordTrace]
  refine ⟨292304914824628896411303503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194869943216419264274202335 292304914824628896411303503)
  ·
    refine ⟨438457372236943344616955255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292304914824628896411303503 438457372236943344616955255)
    ·
      refine ⟨657686058355415016925432883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438457372236943344616955255 657686058355415016925432883)
      ·
        refine ⟨986529087533122525388149325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657686058355415016925432883 986529087533122525388149325)
        ·
          refine ⟨369948407824920947020555997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 986529087533122525388149325 369948407824920947020555997)
          ·
            refine ⟨138730652934345355132708499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369948407824920947020555997 138730652934345355132708499)
            ·
              refine ⟨208095979401518032699062749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138730652934345355132708499 208095979401518032699062749)
              ·
                refine ⟨78035992275569262262148531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208095979401518032699062749 78035992275569262262148531)
                ·
                  refine ⟨117053988413353893393222797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78035992275569262262148531 117053988413353893393222797)
                  ·
                    refine ⟨43895245655007710022458549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117053988413353893393222797 43895245655007710022458549)
                    ·
                      refine ⟨4115179280156972814605489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43895245655007710022458549 4115179280156972814605489)
                      ·
                        rfl

theorem cell23_8014283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 5].length) (baseStart_8014283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014283 prefixEnd_8014283 := by exact prefixLift 8014283
  have htrace : WordTrace (prefixWord ++ tailWord_8014283) baseStart_8014283 baseEnd_8014283 := by
    simpa [prefixWord, tailWord_8014283, baseEnd_8014283] using wordTrace_append hprefix tailTrace_8014283
  have hstable : (prefixWord ++ tailWord_8014283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014283).length < 2 ^ (prefixWord ++ tailWord_8014283).sum := by decide
  have hdescent : baseEnd_8014283 < baseStart_8014283 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014314 : List Nat := [3, 1, 3, 1, 3, 1, 3, 1, 1, 4, 2]
def baseStart_8014314 : Nat := 118140960795 + 8014314 * 2 ^ 59
def prefixEnd_8014314 : Nat := 4983230072969 + 3 ^ 40 * 8014314 * 2
def baseEnd_8014314 : Nat := 4115195198057262193317847

theorem tailTrace_8014314 : CollatzResearch.WordTrace tailWord_8014314 prefixEnd_8014314 4115195198057262193317847 := by
  unfold tailWord_8014314
  simp only [CollatzResearch.WordTrace]
  refine ⟨73076511371879147176420499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194870696991677725803787997 73076511371879147176420499)
  ·
    refine ⟨109614767057818720764630749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73076511371879147176420499 109614767057818720764630749)
    ·
      refine ⟨41105537646682020286736531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109614767057818720764630749 41105537646682020286736531)
      ·
        refine ⟨61658306470023030430104797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41105537646682020286736531 61658306470023030430104797)
        ·
          refine ⟨23121864926258636411289299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61658306470023030430104797 23121864926258636411289299)
          ·
            refine ⟨34682797389387954616933949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23121864926258636411289299 34682797389387954616933949)
            ·
              refine ⟨13006049021020482981350231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34682797389387954616933949 13006049021020482981350231)
              ·
                refine ⟨19509073531530724472025347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13006049021020482981350231 19509073531530724472025347)
                ·
                  refine ⟨29263610297296086708038021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19509073531530724472025347 29263610297296086708038021)
                  ·
                    refine ⟨5486926930743016257757129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29263610297296086708038021 5486926930743016257757129)
                    ·
                      refine ⟨4115195198057262193317847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5486926930743016257757129 4115195198057262193317847)
                      ·
                        rfl

theorem cell23_8014314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_8014314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014314 prefixEnd_8014314 := by exact prefixLift 8014314
  have htrace : WordTrace (prefixWord ++ tailWord_8014314) baseStart_8014314 baseEnd_8014314 := by
    simpa [prefixWord, tailWord_8014314, baseEnd_8014314] using wordTrace_append hprefix tailTrace_8014314
  have hstable : (prefixWord ++ tailWord_8014314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014314).length < 2 ^ (prefixWord ++ tailWord_8014314).sum := by decide
  have hdescent : baseEnd_8014314 < baseStart_8014314 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014330 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3]
def baseStart_8014330 : Nat := 118140960795 + 8014330 * 2 ^ 59
def prefixEnd_8014330 : Nat := 4983230072969 + 3 ^ 40 * 8014330 * 2
def baseEnd_8014330 : Nat := 4115203413747734130717773

theorem tailTrace_8014330 : CollatzResearch.WordTrace tailWord_8014330 prefixEnd_8014330 4115203413747734130717773 := by
  unfold tailWord_8014330
  simp only [CollatzResearch.WordTrace]
  refine ⟨73076657263864655859566111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194871086036972415625509629 73076657263864655859566111)
  ·
    refine ⟨109614985895796983789349167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73076657263864655859566111 109614985895796983789349167)
    ·
      refine ⟨164422478843695475684023751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109614985895796983789349167 164422478843695475684023751)
      ·
        refine ⟨246633718265543213526035627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164422478843695475684023751 246633718265543213526035627)
        ·
          refine ⟨369950577398314820289053441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246633718265543213526035627 369950577398314820289053441)
          ·
            refine ⟨277462933048736115216790081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369950577398314820289053441 277462933048736115216790081)
            ·
              refine ⟨208097199786552086412592561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277462933048736115216790081 208097199786552086412592561)
              ·
                refine ⟨156072899839914064809444421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208097199786552086412592561 156072899839914064809444421)
                ·
                  refine ⟨29263668719983887151770829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156072899839914064809444421 29263668719983887151770829)
                  ·
                    refine ⟨10973875769993957681914061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29263668719983887151770829 10973875769993957681914061)
                    ·
                      refine ⟨4115203413747734130717773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10973875769993957681914061 4115203413747734130717773)
                      ·
                        rfl

theorem cell23_8014330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3].length) (baseStart_8014330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014330 prefixEnd_8014330 := by exact prefixLift 8014330
  have htrace : WordTrace (prefixWord ++ tailWord_8014330) baseStart_8014330 baseEnd_8014330 := by
    simpa [prefixWord, tailWord_8014330, baseEnd_8014330] using wordTrace_append hprefix tailTrace_8014330
  have hstable : (prefixWord ++ tailWord_8014330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014330).length < 2 ^ (prefixWord ++ tailWord_8014330).sum := by decide
  have hdescent : baseEnd_8014330 < baseStart_8014330 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014357 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 2, 5, 2]
def baseStart_8014357 : Nat := 118140960795 + 8014357 * 2 ^ 59
def prefixEnd_8014357 : Nat := 4983230072969 + 3 ^ 40 * 8014357 * 2
def baseEnd_8014357 : Nat := 4115217277725405525080149

theorem tailTrace_8014357 : CollatzResearch.WordTrace tailWord_8014357 prefixEnd_8014357 4115217277725405525080149 := by
  unfold tailWord_8014357
  simp only [CollatzResearch.WordTrace]
  refine ⟨292307613826360807049497325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194871742550907204699664883 292307613826360807049497325)
  ·
    refine ⟨109615355184885302643561497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292307613826360807049497325 109615355184885302643561497)
    ·
      refine ⟨82211516388663976982671123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109615355184885302643561497 82211516388663976982671123)
      ·
        refine ⟨123317274582995965474006685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82211516388663976982671123 123317274582995965474006685)
        ·
          refine ⟨46243977968623487052752507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123317274582995965474006685 46243977968623487052752507)
          ·
            refine ⟨69365966952935230579128761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46243977968623487052752507 69365966952935230579128761)
            ·
              refine ⟨52024475214701422934346571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69365966952935230579128761 52024475214701422934346571)
              ·
                refine ⟨78036712822052134401519857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52024475214701422934346571 78036712822052134401519857)
                ·
                  refine ⟨58527534616539100801139893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78036712822052134401519857 58527534616539100801139893)
                  ·
                    refine ⟨5486956370300540700106865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58527534616539100801139893 5486956370300540700106865)
                    ·
                      refine ⟨4115217277725405525080149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5486956370300540700106865 4115217277725405525080149)
                      ·
                        rfl

theorem cell23_8014357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_8014357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014357 prefixEnd_8014357 := by exact prefixLift 8014357
  have htrace : WordTrace (prefixWord ++ tailWord_8014357) baseStart_8014357 baseEnd_8014357 := by
    simpa [prefixWord, tailWord_8014357, baseEnd_8014357] using wordTrace_append hprefix tailTrace_8014357
  have hstable : (prefixWord ++ tailWord_8014357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014357).length < 2 ^ (prefixWord ++ tailWord_8014357).sum := by decide
  have hdescent : baseEnd_8014357 < baseStart_8014357 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014360 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 1, 1, 7]
def baseStart_8014360 : Nat := 118140960795 + 8014360 * 2 ^ 59
def prefixEnd_8014360 : Nat := 4983230072969 + 3 ^ 40 * 8014360 * 2
def baseEnd_8014360 : Nat := 4115218818167369013342635

theorem tailTrace_8014360 : CollatzResearch.WordTrace tailWord_8014360 prefixEnd_8014360 4115218818167369013342635 := by
  unfold tailWord_8014360
  simp only [CollatzResearch.WordTrace]
  refine ⟨146153861622674969280928267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194871815496899959041237689 146153861622674969280928267)
  ·
    refine ⟨219230792434012453921392401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146153861622674969280928267 219230792434012453921392401)
    ·
      refine ⟨164423094325509340441044301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219230792434012453921392401 164423094325509340441044301)
      ·
        refine ⟨61658660372066002665391613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164423094325509340441044301 61658660372066002665391613)
        ·
          refine ⟨23121997639524750999521855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61658660372066002665391613 23121997639524750999521855)
          ·
            refine ⟨34682996459287126499282783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23121997639524750999521855 34682996459287126499282783)
            ·
              refine ⟨52024494688930689748924175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34682996459287126499282783 52024494688930689748924175)
              ·
                refine ⟨78036742033396034623386263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52024494688930689748924175 78036742033396034623386263)
                ·
                  refine ⟨117055113050094051935079395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78036742033396034623386263 117055113050094051935079395)
                  ·
                    refine ⟨175582669575141077902619093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117055113050094051935079395 175582669575141077902619093)
                    ·
                      refine ⟨4115218818167369013342635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175582669575141077902619093 4115218818167369013342635)
                      ·
                        rfl

theorem cell23_8014360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_8014360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014360 prefixEnd_8014360 := by exact prefixLift 8014360
  have htrace : WordTrace (prefixWord ++ tailWord_8014360) baseStart_8014360 baseEnd_8014360 := by
    simpa [prefixWord, tailWord_8014360, baseEnd_8014360] using wordTrace_append hprefix tailTrace_8014360
  have hstable : (prefixWord ++ tailWord_8014360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014360).length < 2 ^ (prefixWord ++ tailWord_8014360).sum := by decide
  have hdescent : baseEnd_8014360 < baseStart_8014360 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014387 : List Nat := [1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 4]
def baseStart_8014387 : Nat := 118140960795 + 8014387 * 2 ^ 59
def prefixEnd_8014387 : Nat := 4983230072969 + 3 ^ 40 * 8014387 * 2
def baseEnd_8014387 : Nat := 4115232682145040407705011

theorem tailTrace_8014387 : CollatzResearch.WordTrace tailWord_8014387 prefixEnd_8014387 4115232682145040407705011 := by
  unfold tailWord_8014387
  simp only [CollatzResearch.WordTrace]
  refine ⟨292308708016252122173089415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194872472010834748115392943 292308708016252122173089415)
  ·
    refine ⟨438463062024378183259634123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292308708016252122173089415 438463062024378183259634123)
    ·
      refine ⟨657694593036567274889451185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438463062024378183259634123 657694593036567274889451185)
      ·
        refine ⟨493270944777425456167088389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657694593036567274889451185 493270944777425456167088389)
        ·
          refine ⟨92488302145767273031329073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 493270944777425456167088389 92488302145767273031329073)
          ·
            refine ⟨69366226609325454773496805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92488302145767273031329073 69366226609325454773496805)
            ·
              refine ⟨13006167489248522770030651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69366226609325454773496805 13006167489248522770030651)
              ·
                refine ⟨19509251233872784155045977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13006167489248522770030651 19509251233872784155045977)
                ·
                  refine ⟨14631938425404588116284483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19509251233872784155045977 14631938425404588116284483)
                  ·
                    refine ⟨21947907638106882174426725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14631938425404588116284483 21947907638106882174426725)
                    ·
                      refine ⟨4115232682145040407705011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21947907638106882174426725 4115232682145040407705011)
                      ·
                        rfl

theorem cell23_8014387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 4].length) (baseStart_8014387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014387 prefixEnd_8014387 := by exact prefixLift 8014387
  have htrace : WordTrace (prefixWord ++ tailWord_8014387) baseStart_8014387 baseEnd_8014387 := by
    simpa [prefixWord, tailWord_8014387, baseEnd_8014387] using wordTrace_append hprefix tailTrace_8014387
  have hstable : (prefixWord ++ tailWord_8014387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014387).length < 2 ^ (prefixWord ++ tailWord_8014387).sum := by decide
  have hdescent : baseEnd_8014387 < baseStart_8014387 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014461 : List Nat := [1, 4, 1, 1, 6, 1, 1, 2, 6]
def baseStart_8014461 : Nat := 118140960795 + 8014461 * 2 ^ 59
def prefixEnd_8014461 : Nat := 4983230072969 + 3 ^ 40 * 8014461 * 2
def baseEnd_8014461 : Nat := 457252297745941457575519

theorem tailTrace_8014461 : CollatzResearch.WordTrace tailWord_8014461 prefixEnd_8014461 457252297745941457575519 := by
  unfold tailWord_8014461
  simp only [CollatzResearch.WordTrace]
  refine ⟨292311407017984032811283237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194874271345322688540855491 292311407017984032811283237)
  ·
    refine ⟨54808388815872006152115607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292311407017984032811283237 54808388815872006152115607)
    ·
      refine ⟨82212583223808009228173411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54808388815872006152115607 82212583223808009228173411)
      ·
        refine ⟨123318874835712013842260117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82212583223808009228173411 123318874835712013842260117)
        ·
          refine ⟨5780572257924000648855943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 123318874835712013842260117 5780572257924000648855943)
          ·
            refine ⟨8670858386886000973283915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5780572257924000648855943 8670858386886000973283915)
            ·
              refine ⟨13006287580329001459925873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8670858386886000973283915 13006287580329001459925873)
              ·
                refine ⟨9754715685246751094944405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13006287580329001459925873 9754715685246751094944405)
                ·
                  refine ⟨457252297745941457575519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9754715685246751094944405 457252297745941457575519)
                  ·
                    rfl

theorem cell23_8014461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_8014461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014461 prefixEnd_8014461 := by exact prefixLift 8014461
  have htrace : WordTrace (prefixWord ++ tailWord_8014461) baseStart_8014461 baseEnd_8014461 := by
    simpa [prefixWord, tailWord_8014461, baseEnd_8014461] using wordTrace_append hprefix tailTrace_8014461
  have hstable : (prefixWord ++ tailWord_8014461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014461).length < 2 ^ (prefixWord ++ tailWord_8014461).sum := by decide
  have hdescent : baseEnd_8014461 < baseStart_8014461 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014471 : List Nat := [1, 1, 4, 2, 1, 2, 1, 6, 1, 1, 3]
def baseStart_8014471 : Nat := 118140960795 + 8014471 * 2 ^ 59
def prefixEnd_8014471 : Nat := 4983230072969 + 3 ^ 40 * 8014471 * 2
def baseEnd_8014471 : Nat := 4115275814520018079054625

theorem tailTrace_8014471 : CollatzResearch.WordTrace tailWord_8014471 prefixEnd_8014471 4115275814520018079054625 := by
  unfold tailWord_8014471
  simp only [CollatzResearch.WordTrace]
  refine ⟨292311771747947804519147267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194874514498631869679431511 292311771747947804519147267)
  ·
    refine ⟨438467657621921706778720901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292311771747947804519147267 438467657621921706778720901)
    ·
      refine ⟨82212685804110320021010169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 438467657621921706778720901 82212685804110320021010169)
      ·
        refine ⟨61659514353082740015757627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82212685804110320021010169 61659514353082740015757627)
        ·
          refine ⟨92489271529624110023636441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61659514353082740015757627 92489271529624110023636441)
          ·
            refine ⟨69366953647218082517727331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92489271529624110023636441 69366953647218082517727331)
            ·
              refine ⟨104050430470827123776590997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69366953647218082517727331 104050430470827123776590997)
              ·
                refine ⟨4877363928320021427027703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104050430470827123776590997 4877363928320021427027703)
                ·
                  refine ⟨7316045892480032140541555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4877363928320021427027703 7316045892480032140541555)
                  ·
                    refine ⟨10974068838720048210812333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7316045892480032140541555 10974068838720048210812333)
                    ·
                      refine ⟨4115275814520018079054625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10974068838720048210812333 4115275814520018079054625)
                      ·
                        rfl

theorem cell23_8014471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_8014471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014471 prefixEnd_8014471 := by exact prefixLift 8014471
  have htrace : WordTrace (prefixWord ++ tailWord_8014471) baseStart_8014471 baseEnd_8014471 := by
    simpa [prefixWord, tailWord_8014471, baseEnd_8014471] using wordTrace_append hprefix tailTrace_8014471
  have hstable : (prefixWord ++ tailWord_8014471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014471).length < 2 ^ (prefixWord ++ tailWord_8014471).sum := by decide
  have hdescent : baseEnd_8014471 < baseStart_8014471 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014517 : List Nat := [1, 3, 3, 3, 1, 1, 11]
def baseStart_8014517 : Nat := 118140960795 + 8014517 * 2 ^ 59
def prefixEnd_8014517 : Nat := 4983230072969 + 3 ^ 40 * 8014517 * 2
def baseEnd_8014517 : Nat := 50806165859631171593573

theorem tailTrace_8014517 : CollatzResearch.WordTrace tailWord_8014517 prefixEnd_8014517 50806165859631171593573 := by
  unfold tailWord_8014517
  simp only [CollatzResearch.WordTrace]
  refine ⟨292313449505781154375321805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194875633003854102916881203 292313449505781154375321805)
  ·
    refine ⟨109617543564667932890745677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292313449505781154375321805 109617543564667932890745677)
    ·
      refine ⟨41106578836750474834029629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109617543564667932890745677 41106578836750474834029629)
      ·
        refine ⟨15414967063781428062761111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41106578836750474834029629 15414967063781428062761111)
        ·
          refine ⟨23122450595672142094141667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15414967063781428062761111 23122450595672142094141667)
          ·
            refine ⟨34683675893508213141212501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23122450595672142094141667 34683675893508213141212501)
            ·
              refine ⟨50806165859631171593573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34683675893508213141212501 50806165859631171593573)
              ·
                rfl

theorem cell23_8014517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 11].length) (baseStart_8014517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014517 prefixEnd_8014517 := by exact prefixLift 8014517
  have htrace : WordTrace (prefixWord ++ tailWord_8014517) baseStart_8014517 baseEnd_8014517 := by
    simpa [prefixWord, tailWord_8014517, baseEnd_8014517] using wordTrace_append hprefix tailTrace_8014517
  have hstable : (prefixWord ++ tailWord_8014517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014517).length < 2 ^ (prefixWord ++ tailWord_8014517).sum := by decide
  have hdescent : baseEnd_8014517 < baseStart_8014517 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014528 : List Nat := [2, 1, 1, 2, 4, 4, 1, 1, 3, 2, 2]
def baseStart_8014528 : Nat := 118140960795 + 8014528 * 2 ^ 59
def prefixEnd_8014528 : Nat := 4983230072969 + 3 ^ 40 * 8014528 * 2
def baseEnd_8014528 : Nat := 4115305082917324356041863

theorem tailTrace_8014528 : CollatzResearch.WordTrace tailWord_8014528 prefixEnd_8014528 4115305082917324356041863 := by
  unfold tailWord_8014528
  simp only [CollatzResearch.WordTrace]
  refine ⟨146156925354370651626986119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194875900472494202169314825 146156925354370651626986119)
  ·
    refine ⟨219235388031555977440479179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146156925354370651626986119 219235388031555977440479179)
    ·
      refine ⟨328853082047333966160718769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219235388031555977440479179 328853082047333966160718769)
      ·
        refine ⟨246639811535500474620539077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328853082047333966160718769 246639811535500474620539077)
        ·
          refine ⟨46244964662906338991351077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246639811535500474620539077 46244964662906338991351077)
          ·
            refine ⟨8670930874294938560878327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46244964662906338991351077 8670930874294938560878327)
            ·
              refine ⟨13006396311442407841317491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8670930874294938560878327 13006396311442407841317491)
              ·
                refine ⟨19509594467163611761976237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13006396311442407841317491 19509594467163611761976237)
                ·
                  refine ⟨7316097925186354410741089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19509594467163611761976237 7316097925186354410741089)
                  ·
                    refine ⟨5487073443889765808055817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7316097925186354410741089 5487073443889765808055817)
                    ·
                      refine ⟨4115305082917324356041863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5487073443889765808055817 4115305082917324356041863)
                      ·
                        rfl

theorem cell23_8014528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 3, 2, 2].length) (baseStart_8014528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014528 prefixEnd_8014528 := by exact prefixLift 8014528
  have htrace : WordTrace (prefixWord ++ tailWord_8014528) baseStart_8014528 baseEnd_8014528 := by
    simpa [prefixWord, tailWord_8014528, baseEnd_8014528] using wordTrace_append hprefix tailTrace_8014528
  have hstable : (prefixWord ++ tailWord_8014528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014528).length < 2 ^ (prefixWord ++ tailWord_8014528).sum := by decide
  have hdescent : baseEnd_8014528 < baseStart_8014528 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014538 : List Nat := [3, 1, 2, 1, 4, 3, 2, 1, 2, 4]
def baseStart_8014538 : Nat := 118140960795 + 8014538 * 2 ^ 59
def prefixEnd_8014538 : Nat := 4983230072969 + 3 ^ 40 * 8014538 * 2
def baseEnd_8014538 : Nat := 1371770072574623105638939

theorem tailTrace_8014538 : CollatzResearch.WordTrace tailWord_8014538 prefixEnd_8014538 1371770072574623105638939 := by
  unfold tailWord_8014538
  simp only [CollatzResearch.WordTrace]
  refine ⟨73078553859676268740459067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194876143625803383307890845 73078553859676268740459067)
  ·
    refine ⟨109617830789514403110688601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73078553859676268740459067 109617830789514403110688601)
    ·
      refine ⟨82213373092135802333016451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109617830789514403110688601 82213373092135802333016451)
      ·
        refine ⟨123320059638203703499524677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82213373092135802333016451 123320059638203703499524677)
        ·
          refine ⟨23122511182163194406160877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123320059638203703499524677 23122511182163194406160877)
          ·
            refine ⟨8670941693311197902310329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23122511182163194406160877 8670941693311197902310329)
            ·
              refine ⟨6503206269983398426732747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8670941693311197902310329 6503206269983398426732747)
              ·
                refine ⟨9754809404975097640099121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6503206269983398426732747 9754809404975097640099121)
                ·
                  refine ⟨7316107053731323230074341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9754809404975097640099121 7316107053731323230074341)
                  ·
                    refine ⟨1371770072574623105638939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7316107053731323230074341 1371770072574623105638939)
                    ·
                      rfl

theorem cell23_8014538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_8014538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014538 prefixEnd_8014538 := by exact prefixLift 8014538
  have htrace : WordTrace (prefixWord ++ tailWord_8014538) baseStart_8014538 baseEnd_8014538 := by
    simpa [prefixWord, tailWord_8014538, baseEnd_8014538] using wordTrace_append hprefix tailTrace_8014538
  have hstable : (prefixWord ++ tailWord_8014538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014538).length < 2 ^ (prefixWord ++ tailWord_8014538).sum := by decide
  have hdescent : baseEnd_8014538 < baseStart_8014538 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014577 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 2, 6]
def baseStart_8014577 : Nat := 118140960795 + 8014577 * 2 ^ 59
def prefixEnd_8014577 : Nat := 4983230072969 + 3 ^ 40 * 8014577 * 2
def baseEnd_8014577 : Nat := 1371776747823131554776379

theorem tailTrace_8014577 : CollatzResearch.WordTrace tailWord_8014577 prefixEnd_8014577 1371776747823131554776379 := by
  unfold tailWord_8014577
  simp only [CollatzResearch.WordTrace]
  refine ⟨292315637885563784622505985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194877091923709189748337323 292315637885563784622505985)
  ·
    refine ⟨219236728414172838466879489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292315637885563784622505985 219236728414172838466879489)
    ·
      refine ⟨164427546310629628850159617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219236728414172838466879489 164427546310629628850159617)
      ·
        refine ⟨123320659732972221637619713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164427546310629628850159617 123320659732972221637619713)
        ·
          refine ⟨92490494799729166228214785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123320659732972221637619713 92490494799729166228214785)
          ·
            refine ⟨69367871099796874671161089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92490494799729166228214785 69367871099796874671161089)
            ·
              refine ⟨52025903324847656003370817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69367871099796874671161089 52025903324847656003370817)
              ·
                refine ⟨39019427493635742002528113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52025903324847656003370817 39019427493635742002528113)
                ·
                  refine ⟨29264570620226806501896085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39019427493635742002528113 29264570620226806501896085)
                  ·
                    refine ⟨1371776747823131554776379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29264570620226806501896085 1371776747823131554776379)
                    ·
                      rfl

theorem cell23_8014577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_8014577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014577 prefixEnd_8014577 := by exact prefixLift 8014577
  have htrace : WordTrace (prefixWord ++ tailWord_8014577) baseStart_8014577 baseEnd_8014577 := by
    simpa [prefixWord, tailWord_8014577, baseEnd_8014577] using wordTrace_append hprefix tailTrace_8014577
  have hstable : (prefixWord ++ tailWord_8014577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014577).length < 2 ^ (prefixWord ++ tailWord_8014577).sum := by decide
  have hdescent : baseEnd_8014577 < baseStart_8014577 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014578 : List Nat := [3, 2, 1, 3, 1, 3, 2, 2, 2, 1, 3]
def baseStart_8014578 : Nat := 118140960795 + 8014578 * 2 ^ 59
def prefixEnd_8014578 : Nat := 4983230072969 + 3 ^ 40 * 8014578 * 2
def baseEnd_8014578 : Nat := 4115330756950049160416633

theorem tailTrace_8014578 : CollatzResearch.WordTrace tailWord_8014578 prefixEnd_8014578 4115330756950049160416633 := by
  unfold tailWord_8014578
  simp only [CollatzResearch.WordTrace]
  refine ⟨73078918589640040448323097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194877116239040107862194925 73078918589640040448323097)
  ·
    refine ⟨54809188942230030336242323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73078918589640040448323097 54809188942230030336242323)
    ·
      refine ⟨82213783413345045504363485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54809188942230030336242323 82213783413345045504363485)
      ·
        refine ⟨30830168780004392064136307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82213783413345045504363485 30830168780004392064136307)
        ·
          refine ⟨46245253170006588096204461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30830168780004392064136307 46245253170006588096204461)
          ·
            refine ⟨17341969938752470536076673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46245253170006588096204461 17341969938752470536076673)
            ·
              refine ⟨13006477454064352902057505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17341969938752470536076673 13006477454064352902057505)
              ·
                refine ⟨9754858090548264676543129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13006477454064352902057505 9754858090548264676543129)
                ·
                  refine ⟨7316143567911198507407347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9754858090548264676543129 7316143567911198507407347)
                  ·
                    refine ⟨10974215351866797761111021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7316143567911198507407347 10974215351866797761111021)
                    ·
                      refine ⟨4115330756950049160416633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10974215351866797761111021 4115330756950049160416633)
                      ·
                        rfl

theorem cell23_8014578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_8014578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014578 prefixEnd_8014578 := by exact prefixLift 8014578
  have htrace : WordTrace (prefixWord ++ tailWord_8014578) baseStart_8014578 baseEnd_8014578 := by
    simpa [prefixWord, tailWord_8014578, baseEnd_8014578] using wordTrace_append hprefix tailTrace_8014578
  have hstable : (prefixWord ++ tailWord_8014578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014578).length < 2 ^ (prefixWord ++ tailWord_8014578).sum := by decide
  have hdescent : baseEnd_8014578 < baseStart_8014578 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014584 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 3, 4, 2]
def baseStart_8014584 : Nat := 118140960795 + 8014584 * 2 ^ 59
def prefixEnd_8014584 : Nat := 4983230072969 + 3 ^ 40 * 8014584 * 2
def baseEnd_8014584 : Nat := 4115333837833976136941605

theorem tailTrace_8014584 : CollatzResearch.WordTrace tailWord_8014584 prefixEnd_8014584 4115333837833976136941605 := by
  unfold tailWord_8014584
  simp only [CollatzResearch.WordTrace]
  refine ⟨146157946598269212409005403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194877262131025616545340537 146157946598269212409005403)
  ·
    refine ⟨219236919897403818613508105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146157946598269212409005403 219236919897403818613508105)
    ·
      refine ⟨164427689923052863960131079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219236919897403818613508105 164427689923052863960131079)
      ·
        refine ⟨246641534884579295940196619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164427689923052863960131079 246641534884579295940196619)
        ·
          refine ⟨369962302326868943910294929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246641534884579295940196619 369962302326868943910294929)
          ·
            refine ⟨277471726745151707932721197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369962302326868943910294929 277471726745151707932721197)
            ·
              refine ⟨104051897529431890474770449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277471726745151707932721197 104051897529431890474770449)
              ·
                refine ⟨78038923147073917856077837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104051897529431890474770449 78038923147073917856077837)
                ·
                  refine ⟨29264596180152719196029189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78038923147073917856077837 29264596180152719196029189)
                  ·
                    refine ⟨5487111783778634849255473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29264596180152719196029189 5487111783778634849255473)
                    ·
                      refine ⟨4115333837833976136941605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5487111783778634849255473 4115333837833976136941605)
                      ·
                        rfl

theorem cell23_8014584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 3, 4, 2].length) (baseStart_8014584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014584 prefixEnd_8014584 := by exact prefixLift 8014584
  have htrace : WordTrace (prefixWord ++ tailWord_8014584) baseStart_8014584 baseEnd_8014584 := by
    simpa [prefixWord, tailWord_8014584, baseEnd_8014584] using wordTrace_append hprefix tailTrace_8014584
  have hstable : (prefixWord ++ tailWord_8014584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014584).length < 2 ^ (prefixWord ++ tailWord_8014584).sum := by decide
  have hdescent : baseEnd_8014584 < baseStart_8014584 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014594 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_8014594 : Nat := 118140960795 + 8014594 * 2 ^ 59
def prefixEnd_8014594 : Nat := 4983230072969 + 3 ^ 40 * 8014594 * 2
def baseEnd_8014594 : Nat := 1371779657546840365938853

theorem tailTrace_8014594 : CollatzResearch.WordTrace tailWord_8014594 prefixEnd_8014594 1371779657546840365938853 := by
  unfold tailWord_8014594
  simp only [CollatzResearch.WordTrace]
  refine ⟨73079064481625549131468709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194877505284334797683916557 73079064481625549131468709)
  ·
    refine ⟨13702324590304790462150383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73079064481625549131468709 13702324590304790462150383)
    ·
      refine ⟨20553486885457185693225575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13702324590304790462150383 20553486885457185693225575)
      ·
        refine ⟨30830230328185778539838363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20553486885457185693225575 30830230328185778539838363)
        ·
          refine ⟨46245345492278667809757545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30830230328185778539838363 46245345492278667809757545)
          ·
            refine ⟨34684009119209000857318159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46245345492278667809757545 34684009119209000857318159)
            ·
              refine ⟨52026013678813501285977239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34684009119209000857318159 52026013678813501285977239)
              ·
                refine ⟨78039020518220251928965859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52026013678813501285977239 78039020518220251928965859)
                ·
                  refine ⟨117058530777330377893448789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78039020518220251928965859 117058530777330377893448789)
                  ·
                    refine ⟨1371779657546840365938853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117058530777330377893448789 1371779657546840365938853)
                    ·
                      rfl

theorem cell23_8014594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_8014594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014594 prefixEnd_8014594 := by exact prefixLift 8014594
  have htrace : WordTrace (prefixWord ++ tailWord_8014594) baseStart_8014594 baseEnd_8014594 := by
    simpa [prefixWord, tailWord_8014594, baseEnd_8014594] using wordTrace_append hprefix tailTrace_8014594
  have hstable : (prefixWord ++ tailWord_8014594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014594).length < 2 ^ (prefixWord ++ tailWord_8014594).sum := by decide
  have hdescent : baseEnd_8014594 < baseStart_8014594 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014607 : List Nat := [1, 1, 2, 1, 1, 1, 7, 2, 7]
def baseStart_8014607 : Nat := 118140960795 + 8014607 * 2 ^ 59
def prefixEnd_8014607 : Nat := 4983230072969 + 3 ^ 40 * 8014607 * 2
def baseEnd_8014607 : Nat := 457260627543225505217111

theorem tailTrace_8014607 : CollatzResearch.WordTrace tailWord_8014607 prefixEnd_8014607 457260627543225505217111 := by
  unfold tailWord_8014607
  simp only [CollatzResearch.WordTrace]
  refine ⟨292316732075455099746098075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194877821383636733164065383 292316732075455099746098075)
  ·
    refine ⟨438475098113182649619147113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292316732075455099746098075 438475098113182649619147113)
    ·
      refine ⟨328856323584886987214360335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438475098113182649619147113 328856323584886987214360335)
      ·
        refine ⟨493284485377330480821540503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328856323584886987214360335 493284485377330480821540503)
        ·
          refine ⟨739926728065995721232310755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493284485377330480821540503 739926728065995721232310755)
          ·
            refine ⟨1109890092098993581848466133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739926728065995721232310755 1109890092098993581848466133)
            ·
              refine ⟨26013049033570162074573425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1109890092098993581848466133 26013049033570162074573425)
              ·
                refine ⟨19509786775177621555930069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26013049033570162074573425 19509786775177621555930069)
                ·
                  refine ⟨457260627543225505217111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19509786775177621555930069 457260627543225505217111)
                  ·
                    rfl

theorem cell23_8014607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 7].length) (baseStart_8014607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014607 prefixEnd_8014607 := by exact prefixLift 8014607
  have htrace : WordTrace (prefixWord ++ tailWord_8014607) baseStart_8014607 baseEnd_8014607 := by
    simpa [prefixWord, tailWord_8014607, baseEnd_8014607] using wordTrace_append hprefix tailTrace_8014607
  have hstable : (prefixWord ++ tailWord_8014607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014607).length < 2 ^ (prefixWord ++ tailWord_8014607).sum := by decide
  have hdescent : baseEnd_8014607 < baseStart_8014607 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014647 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 7]
def baseStart_8014647 : Nat := 118140960795 + 8014647 * 2 ^ 59
def prefixEnd_8014647 : Nat := 4983230072969 + 3 ^ 40 * 8014647 * 2
def baseEnd_8014647 : Nat := 4115366187115209390453815

theorem tailTrace_8014647 : CollatzResearch.WordTrace tailWord_8014647 prefixEnd_8014647 4115366187115209390453815 := by
  unfold tailWord_8014647
  simp only [CollatzResearch.WordTrace]
  refine ⟨292318190995310186577554195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194878793996873457718369463 292318190995310186577554195)
  ·
    refine ⟨438477286492965279866331293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292318190995310186577554195 438477286492965279866331293)
    ·
      refine ⟨164428982434861979949874235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438477286492965279866331293 164428982434861979949874235)
      ·
        refine ⟨246643473652292969924811353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164428982434861979949874235 246643473652292969924811353)
        ·
          refine ⟨184982605239219727443608515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246643473652292969924811353 184982605239219727443608515)
          ·
            refine ⟨277473907858829591165412773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184982605239219727443608515 277473907858829591165412773)
            ·
              refine ⟨52026357723530548343514895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 277473907858829591165412773 52026357723530548343514895)
              ·
                refine ⟨78039536585295822515272343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52026357723530548343514895 78039536585295822515272343)
                ·
                  refine ⟨117059304877943733772908515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78039536585295822515272343 117059304877943733772908515)
                  ·
                    refine ⟨175588957316915600659362773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117059304877943733772908515 175588957316915600659362773)
                    ·
                      refine ⟨4115366187115209390453815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175588957316915600659362773 4115366187115209390453815)
                      ·
                        rfl

theorem cell23_8014647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_8014647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014647 prefixEnd_8014647 := by exact prefixLift 8014647
  have htrace : WordTrace (prefixWord ++ tailWord_8014647) baseStart_8014647 baseEnd_8014647 := by
    simpa [prefixWord, tailWord_8014647, baseEnd_8014647] using wordTrace_append hprefix tailTrace_8014647
  have hstable : (prefixWord ++ tailWord_8014647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014647).length < 2 ^ (prefixWord ++ tailWord_8014647).sum := by decide
  have hdescent : baseEnd_8014647 < baseStart_8014647 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014674 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_8014674 : Nat := 118140960795 + 8014674 * 2 ^ 59
def prefixEnd_8014674 : Nat := 4983230072969 + 3 ^ 40 * 8014674 * 2
def baseEnd_8014674 : Nat := 4115380051092880784816191

theorem tailTrace_8014674 : CollatzResearch.WordTrace tailWord_8014674 prefixEnd_8014674 4115380051092880784816191 := by
  unfold tailWord_8014674
  simp only [CollatzResearch.WordTrace]
  refine ⟨73079793941553092547196769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194879450510808246792524717 73079793941553092547196769)
  ·
    refine ⟨54809845456164819410397577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73079793941553092547196769 54809845456164819410397577)
    ·
      refine ⟨41107384092123614557798183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54809845456164819410397577 41107384092123614557798183)
      ·
        refine ⟨61661076138185421836697275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41107384092123614557798183 61661076138185421836697275)
        ·
          refine ⟨92491614207278132755045913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61661076138185421836697275 92491614207278132755045913)
          ·
            refine ⟨69368710655458599566284435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92491614207278132755045913 69368710655458599566284435)
            ·
              refine ⟨104053065983187899349426653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69368710655458599566284435 104053065983187899349426653)
              ·
                refine ⟨39019899743695462256034995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104053065983187899349426653 39019899743695462256034995)
                ·
                  refine ⟨58529849615543193384052493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39019899743695462256034995 58529849615543193384052493)
                  ·
                    refine ⟨21948693605828697519019685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58529849615543193384052493 21948693605828697519019685)
                    ·
                      refine ⟨4115380051092880784816191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21948693605828697519019685 4115380051092880784816191)
                      ·
                        rfl

theorem cell23_8014674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_8014674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014674 prefixEnd_8014674 := by exact prefixLift 8014674
  have htrace : WordTrace (prefixWord ++ tailWord_8014674) baseStart_8014674 baseEnd_8014674 := by
    simpa [prefixWord, tailWord_8014674, baseEnd_8014674] using wordTrace_append hprefix tailTrace_8014674
  have hstable : (prefixWord ++ tailWord_8014674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014674).length < 2 ^ (prefixWord ++ tailWord_8014674).sum := by decide
  have hdescent : baseEnd_8014674 < baseStart_8014674 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014691 : List Nat := [1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 4]
def baseStart_8014691 : Nat := 118140960795 + 8014691 * 2 ^ 59
def prefixEnd_8014691 : Nat := 4983230072969 + 3 ^ 40 * 8014691 * 2
def baseEnd_8014691 : Nat := 4115388780264007218303613

theorem tailTrace_8014691 : CollatzResearch.WordTrace tailWord_8014691 prefixEnd_8014691 4115388780264007218303613 := by
  unfold tailWord_8014691
  simp only [CollatzResearch.WordTrace]
  refine ⟨292319795807150782092155927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194879863871433854728103951 292319795807150782092155927)
  ·
    refine ⟨438479693710726173138233891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292319795807150782092155927 438479693710726173138233891)
    ·
      refine ⟨657719540566089259707350837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438479693710726173138233891 657719540566089259707350837)
      ·
        refine ⟨61661206928070868097564141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 657719540566089259707350837 61661206928070868097564141)
        ·
          refine ⟨23122952598026575536586553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61661206928070868097564141 23122952598026575536586553)
          ·
            refine ⟨17342214448519931652439915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23122952598026575536586553 17342214448519931652439915)
            ·
              refine ⟨26013321672779897478659873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17342214448519931652439915 26013321672779897478659873)
              ·
                refine ⟨19509991254584923108994905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26013321672779897478659873 19509991254584923108994905)
                ·
                  refine ⟨14632493440938692331746179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19509991254584923108994905 14632493440938692331746179)
                  ·
                    refine ⟨21948740161408038497619269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14632493440938692331746179 21948740161408038497619269)
                    ·
                      refine ⟨4115388780264007218303613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21948740161408038497619269 4115388780264007218303613)
                      ·
                        rfl

theorem cell23_8014691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_8014691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014691 prefixEnd_8014691 := by exact prefixLift 8014691
  have htrace : WordTrace (prefixWord ++ tailWord_8014691) baseStart_8014691 baseEnd_8014691 := by
    simpa [prefixWord, tailWord_8014691, baseEnd_8014691] using wordTrace_append hprefix tailTrace_8014691
  have hstable : (prefixWord ++ tailWord_8014691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014691).length < 2 ^ (prefixWord ++ tailWord_8014691).sum := by decide
  have hdescent : baseEnd_8014691 < baseStart_8014691 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014728 : List Nat := [2, 1, 3, 3, 2, 2, 2, 1, 2, 2, 3]
def baseStart_8014728 : Nat := 118140960795 + 8014728 * 2 ^ 59
def prefixEnd_8014728 : Nat := 4983230072969 + 3 ^ 40 * 8014728 * 2
def baseEnd_8014728 : Nat := 4115407779048223573540943

theorem tailTrace_8014728 : CollatzResearch.WordTrace tailWord_8014728 prefixEnd_8014728 4115407779048223573540943 := by
  unfold tailWord_8014728
  simp only [CollatzResearch.WordTrace]
  refine ⟨146160572654008368705626419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194880763538677824940835225 146160572654008368705626419)
  ·
    refine ⟨219240858981012553058439629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146160572654008368705626419 219240858981012553058439629)
    ·
      refine ⟨82215322117879707396914861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219240858981012553058439629 82215322117879707396914861)
      ·
        refine ⟨30830745794204890273843073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82215322117879707396914861 30830745794204890273843073)
        ·
          refine ⟨23123059345653667705382305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30830745794204890273843073 23123059345653667705382305)
          ·
            refine ⟨17342294509240250779036729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23123059345653667705382305 17342294509240250779036729)
            ·
              refine ⟨13006720881930188084277547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17342294509240250779036729 13006720881930188084277547)
              ·
                refine ⟨19510081322895282126416321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13006720881930188084277547 19510081322895282126416321)
                ·
                  refine ⟨14632560992171461594812241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19510081322895282126416321 14632560992171461594812241)
                  ·
                    refine ⟨10974420744128596196109181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14632560992171461594812241 10974420744128596196109181)
                    ·
                      refine ⟨4115407779048223573540943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10974420744128596196109181 4115407779048223573540943)
                      ·
                        rfl

theorem cell23_8014728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_8014728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014728 prefixEnd_8014728 := by exact prefixLift 8014728
  have htrace : WordTrace (prefixWord ++ tailWord_8014728) baseStart_8014728 baseEnd_8014728 := by
    simpa [prefixWord, tailWord_8014728, baseEnd_8014728] using wordTrace_append hprefix tailTrace_8014728
  have hstable : (prefixWord ++ tailWord_8014728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014728).length < 2 ^ (prefixWord ++ tailWord_8014728).sum := by decide
  have hdescent : baseEnd_8014728 < baseStart_8014728 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014748 : List Nat := [2, 2, 3, 3, 2, 1, 2, 2, 6]
def baseStart_8014748 : Nat := 118140960795 + 8014748 * 2 ^ 59
def prefixEnd_8014748 : Nat := 4983230072969 + 3 ^ 40 * 8014748 * 2
def baseEnd_8014748 : Nat := 457268672073479277254539

theorem tailTrace_8014748 : CollatzResearch.WordTrace tailWord_8014748 prefixEnd_8014748 457268672073479277254539 := by
  unfold tailWord_8014748
  simp only [CollatzResearch.WordTrace]
  refine ⟨146160937383972140413490449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194881249845296187217987265 146160937383972140413490449)
  ·
    refine ⟨109620703037979105310117837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146160937383972140413490449 109620703037979105310117837)
    ·
      refine ⟨41107763639242164491294189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109620703037979105310117837 41107763639242164491294189)
      ·
        refine ⟨15415411364715811684235321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41107763639242164491294189 15415411364715811684235321)
        ·
          refine ⟨11561558523536858763176491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15415411364715811684235321 11561558523536858763176491)
          ·
            refine ⟨17342337785305288144764737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11561558523536858763176491 17342337785305288144764737)
            ·
              refine ⟨13006753338978966108573553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17342337785305288144764737 13006753338978966108573553)
              ·
                refine ⟨9755065004234224581430165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13006753338978966108573553 9755065004234224581430165)
                ·
                  refine ⟨457268672073479277254539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9755065004234224581430165 457268672073479277254539)
                  ·
                    rfl

theorem cell23_8014748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 6].length) (baseStart_8014748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014748 prefixEnd_8014748 := by exact prefixLift 8014748
  have htrace : WordTrace (prefixWord ++ tailWord_8014748) baseStart_8014748 baseEnd_8014748 := by
    simpa [prefixWord, tailWord_8014748, baseEnd_8014748] using wordTrace_append hprefix tailTrace_8014748
  have hstable : (prefixWord ++ tailWord_8014748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014748).length < 2 ^ (prefixWord ++ tailWord_8014748).sum := by decide
  have hdescent : baseEnd_8014748 < baseStart_8014748 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014792 : List Nat := [2, 1, 3, 1, 5, 1, 2, 3, 1, 1, 3]
def baseStart_8014792 : Nat := 118140960795 + 8014792 * 2 ^ 59
def prefixEnd_8014792 : Nat := 4983230072969 + 3 ^ 40 * 8014792 * 2
def baseEnd_8014792 : Nat := 4115440641810111323140649

theorem tailTrace_8014792 : CollatzResearch.WordTrace tailWord_8014792 prefixEnd_8014792 4115440641810111323140649 := by
  unfold tailWord_8014792
  simp only [CollatzResearch.WordTrace]
  refine ⟨146161739789892438170791315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194882319719856584227721753 146161739789892438170791315)
  ·
    refine ⟨219242609684838657256186973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146161739789892438170791315 219242609684838657256186973)
    ·
      refine ⟨82215978631814496471070115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219242609684838657256186973 82215978631814496471070115)
      ·
        refine ⟨123323967947721744706605173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82215978631814496471070115 123323967947721744706605173)
        ·
          refine ⟨11561621995098913566244235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123323967947721744706605173 11561621995098913566244235)
          ·
            refine ⟨17342432992648370349366353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11561621995098913566244235 17342432992648370349366353)
            ·
              refine ⟨13006824744486277762024765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17342432992648370349366353 13006824744486277762024765)
              ·
                refine ⟨4877559279182354160759287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13006824744486277762024765 4877559279182354160759287)
                ·
                  refine ⟨7316338918773531241138931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4877559279182354160759287 7316338918773531241138931)
                  ·
                    refine ⟨10974508378160296861708397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7316338918773531241138931 10974508378160296861708397)
                    ·
                      refine ⟨4115440641810111323140649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10974508378160296861708397 4115440641810111323140649)
                      ·
                        rfl

theorem cell23_8014792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 1, 1, 3].length) (baseStart_8014792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014792 prefixEnd_8014792 := by exact prefixLift 8014792
  have htrace : WordTrace (prefixWord ++ tailWord_8014792) baseStart_8014792 baseEnd_8014792 := by
    simpa [prefixWord, tailWord_8014792, baseEnd_8014792] using wordTrace_append hprefix tailTrace_8014792
  have hstable : (prefixWord ++ tailWord_8014792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014792).length < 2 ^ (prefixWord ++ tailWord_8014792).sum := by decide
  have hdescent : baseEnd_8014792 < baseStart_8014792 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014794 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_8014794 : Nat := 118140960795 + 8014794 * 2 ^ 59
def prefixEnd_8014794 : Nat := 4983230072969 + 3 ^ 40 * 8014794 * 2
def baseEnd_8014794 : Nat := 4115441668771420315315639

theorem tailTrace_8014794 : CollatzResearch.WordTrace tailWord_8014794 prefixEnd_8014794 4115441668771420315315639 := by
  unfold tailWord_8014794
  simp only [CollatzResearch.WordTrace]
  refine ⟨73080888131444407670788859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194882368350518420455436957 73080888131444407670788859)
  ·
    refine ⟨109621332197166611506183289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73080888131444407670788859 109621332197166611506183289)
    ·
      refine ⟨82215999147874958629637467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109621332197166611506183289 82215999147874958629637467)
      ·
        refine ⟨123323998721812437944456201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82215999147874958629637467 123323998721812437944456201)
        ·
          refine ⟨92492999041359328458342151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123323998721812437944456201 92492999041359328458342151)
          ·
            refine ⟨138739498562038992687513227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92492999041359328458342151 138739498562038992687513227)
            ·
              refine ⟨208109247843058489031269841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138739498562038992687513227 208109247843058489031269841)
              ·
                refine ⟨156081935882293866773452381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208109247843058489031269841 156081935882293866773452381)
                ·
                  refine ⟨58530725955860200040044643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156081935882293866773452381 58530725955860200040044643)
                  ·
                    refine ⟨87796088933790300060066965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58530725955860200040044643 87796088933790300060066965)
                    ·
                      refine ⟨4115441668771420315315639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87796088933790300060066965 4115441668771420315315639)
                      ·
                        rfl

theorem cell23_8014794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_8014794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014794 prefixEnd_8014794 := by exact prefixLift 8014794
  have htrace : WordTrace (prefixWord ++ tailWord_8014794) baseStart_8014794 baseEnd_8014794 := by
    simpa [prefixWord, tailWord_8014794, baseEnd_8014794] using wordTrace_append hprefix tailTrace_8014794
  have hstable : (prefixWord ++ tailWord_8014794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014794).length < 2 ^ (prefixWord ++ tailWord_8014794).sum := by decide
  have hdescent : baseEnd_8014794 < baseStart_8014794 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014798 : List Nat := [4, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4]
def baseStart_8014798 : Nat := 118140960795 + 8014798 * 2 ^ 59
def prefixEnd_8014798 : Nat := 4983230072969 + 3 ^ 40 * 8014798 * 2
def baseEnd_8014798 : Nat := 4115443722694038299665621

theorem tailTrace_8014798 : CollatzResearch.WordTrace tailWord_8014798 prefixEnd_8014798 4115443722694038299665621 := by
  unfold tailWord_8014798
  simp only [CollatzResearch.WordTrace]
  refine ⟨36540462302220392420787631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194882465611842092910867365 36540462302220392420787631)
  ·
    refine ⟨54810693453330588631181447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36540462302220392420787631 54810693453330588631181447)
    ·
      refine ⟨82216040179995882946772171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54810693453330588631181447 82216040179995882946772171)
      ·
        refine ⟨123324060269993824420158257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82216040179995882946772171 123324060269993824420158257)
        ·
          refine ⟨92493045202495368315118693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123324060269993824420158257 92493045202495368315118693)
          ·
            refine ⟨17342445975467881559084755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92493045202495368315118693 17342445975467881559084755)
            ·
              refine ⟨26013668963201822338627133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17342445975467881559084755 26013668963201822338627133)
              ·
                refine ⟨9755125861200683376985175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26013668963201822338627133 9755125861200683376985175)
                ·
                  refine ⟨14632688791801025065477763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9755125861200683376985175 14632688791801025065477763)
                  ·
                    refine ⟨21949033187701537598216645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14632688791801025065477763 21949033187701537598216645)
                    ·
                      refine ⟨4115443722694038299665621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21949033187701537598216645 4115443722694038299665621)
                      ·
                        rfl

theorem cell23_8014798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_8014798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014798 prefixEnd_8014798 := by exact prefixLift 8014798
  have htrace : WordTrace (prefixWord ++ tailWord_8014798) baseStart_8014798 baseEnd_8014798 := by
    simpa [prefixWord, tailWord_8014798, baseEnd_8014798] using wordTrace_append hprefix tailTrace_8014798
  have hstable : (prefixWord ++ tailWord_8014798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014798).length < 2 ^ (prefixWord ++ tailWord_8014798).sum := by decide
  have hdescent : baseEnd_8014798 < baseStart_8014798 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014808 : List Nat := [2, 1, 2, 2, 2, 3, 3, 2, 2, 4]
def baseStart_8014808 : Nat := 118140960795 + 8014808 * 2 ^ 59
def prefixEnd_8014808 : Nat := 4983230072969 + 3 ^ 40 * 8014808 * 2
def baseEnd_8014808 : Nat := 1371816285833527753513525

theorem tailTrace_8014808 : CollatzResearch.WordTrace tailWord_8014808 prefixEnd_8014808 1371816285833527753513525 := by
  unfold tailWord_8014808
  simp only [CollatzResearch.WordTrace]
  refine ⟨146162031573863455537082539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194882708765151274049443385 146162031573863455537082539)
  ·
    refine ⟨219243047360795183305623809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146162031573863455537082539 219243047360795183305623809)
    ·
      refine ⟨164432285520596387479217857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219243047360795183305623809 164432285520596387479217857)
      ·
        refine ⟨123324214140447290609413393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164432285520596387479217857 123324214140447290609413393)
        ·
          refine ⟨92493160605335467957060045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123324214140447290609413393 92493160605335467957060045)
          ·
            refine ⟨34684935227000800483897517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92493160605335467957060045 34684935227000800483897517)
            ·
              refine ⟨13006850710125300181461569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34684935227000800483897517 13006850710125300181461569)
              ·
                refine ⟨9755138032593975136096177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13006850710125300181461569 9755138032593975136096177)
                ·
                  refine ⟨7316353524445481352072133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9755138032593975136096177 7316353524445481352072133)
                  ·
                    refine ⟨1371816285833527753513525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7316353524445481352072133 1371816285833527753513525)
                    ·
                      rfl

theorem cell23_8014808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 2, 4].length) (baseStart_8014808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014808 prefixEnd_8014808 := by exact prefixLift 8014808
  have htrace : WordTrace (prefixWord ++ tailWord_8014808) baseStart_8014808 baseEnd_8014808 := by
    simpa [prefixWord, tailWord_8014808, baseEnd_8014808] using wordTrace_append hprefix tailTrace_8014808
  have hstable : (prefixWord ++ tailWord_8014808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014808).length < 2 ^ (prefixWord ++ tailWord_8014808).sum := by decide
  have hdescent : baseEnd_8014808 < baseStart_8014808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014818 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_8014818 : Nat := 118140960795 + 8014818 * 2 ^ 59
def prefixEnd_8014818 : Nat := 4983230072969 + 3 ^ 40 * 8014818 * 2
def baseEnd_8014818 : Nat := 4115453992307128221415529

theorem tailTrace_8014818 : CollatzResearch.WordTrace tailWord_8014818 prefixEnd_8014818 4115453992307128221415529 := by
  unfold tailWord_8014818
  simp only [CollatzResearch.WordTrace]
  refine ⟨73081106969422670695507277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194882951918460455188019405 73081106969422670695507277)
  ·
    refine ⟨27405415113533501510815229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73081106969422670695507277 27405415113533501510815229)
    ·
      refine ⟨10277030667575063066555711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27405415113533501510815229 10277030667575063066555711)
      ·
        refine ⟨15415546001362594599833567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10277030667575063066555711 15415546001362594599833567)
        ·
          refine ⟨23123319002043891899750351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15415546001362594599833567 23123319002043891899750351)
          ·
            refine ⟨34684978503065837849625527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23123319002043891899750351 34684978503065837849625527)
            ·
              refine ⟨52027467754598756774438291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34684978503065837849625527 52027467754598756774438291)
              ·
                refine ⟨78041201631898135161657437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52027467754598756774438291 78041201631898135161657437)
                ·
                  refine ⟨29265450611961800685621539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78041201631898135161657437 29265450611961800685621539)
                  ·
                    refine ⟨43898175917942701028432309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29265450611961800685621539 43898175917942701028432309)
                    ·
                      refine ⟨4115453992307128221415529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43898175917942701028432309 4115453992307128221415529)
                      ·
                        rfl

theorem cell23_8014818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_8014818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014818 prefixEnd_8014818 := by exact prefixLift 8014818
  have htrace : WordTrace (prefixWord ++ tailWord_8014818) baseStart_8014818 baseEnd_8014818 := by
    simpa [prefixWord, tailWord_8014818, baseEnd_8014818] using wordTrace_append hprefix tailTrace_8014818
  have hstable : (prefixWord ++ tailWord_8014818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014818).length < 2 ^ (prefixWord ++ tailWord_8014818).sum := by decide
  have hdescent : baseEnd_8014818 < baseStart_8014818 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014838 : List Nat := [5, 1, 1, 1, 3, 1, 4, 7]
def baseStart_8014838 : Nat := 118140960795 + 8014838 * 2 ^ 59
def prefixEnd_8014838 : Nat := 4983230072969 + 3 ^ 40 * 8014838 * 2
def baseEnd_8014838 : Nat := 152424602293341412709831

theorem tailTrace_8014838 : CollatzResearch.WordTrace tailWord_8014838 prefixEnd_8014838 152424602293341412709831 := by
  unfold tailWord_8014838
  simp only [CollatzResearch.WordTrace]
  refine ⟨18270322333601139137359823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194883438225078817465171445 18270322333601139137359823)
  ·
    refine ⟨27405483500401708706039735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18270322333601139137359823 27405483500401708706039735)
    ·
      refine ⟨41108225250602563059059603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27405483500401708706039735 41108225250602563059059603)
      ·
        refine ⟨61662337875903844588589405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41108225250602563059059603 61662337875903844588589405)
        ·
          refine ⟨23123376703463941720721027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61662337875903844588589405 23123376703463941720721027)
          ·
            refine ⟨34685065055195912581081541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23123376703463941720721027 34685065055195912581081541)
            ·
              refine ⟨6503449697849233608952789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34685065055195912581081541 6503449697849233608952789)
              ·
                refine ⟨152424602293341412709831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6503449697849233608952789 152424602293341412709831)
                ·
                  rfl

theorem cell23_8014838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_8014838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014838 prefixEnd_8014838 := by exact prefixLift 8014838
  have htrace : WordTrace (prefixWord ++ tailWord_8014838) baseStart_8014838 baseEnd_8014838 := by
    simpa [prefixWord, tailWord_8014838, baseEnd_8014838] using wordTrace_append hprefix tailTrace_8014838
  have hstable : (prefixWord ++ tailWord_8014838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014838).length < 2 ^ (prefixWord ++ tailWord_8014838).sum := by decide
  have hdescent : baseEnd_8014838 < baseStart_8014838 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014849 : List Nat := [1, 2, 4, 1, 2, 4, 1, 3, 1, 2, 2]
def baseStart_8014849 : Nat := 118140960795 + 8014849 * 2 ^ 59
def prefixEnd_8014849 : Nat := 4983230072969 + 3 ^ 40 * 8014849 * 2
def baseEnd_8014849 : Nat := 4115469910207417600127887

theorem tailTrace_8014849 : CollatzResearch.WordTrace tailWord_8014849 prefixEnd_8014849 4115469910207417600127887 := by
  unfold tailWord_8014849
  simp only [CollatzResearch.WordTrace]
  refine ⟨292325558540578375076407601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194883705693718916717605067 292325558540578375076407601)
  ·
    refine ⟨219244168905433781307305701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292325558540578375076407601 219244168905433781307305701)
    ·
      refine ⟨41108281669768833995119819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219244168905433781307305701 41108281669768833995119819)
      ·
        refine ⟨61662422504653250992679729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41108281669768833995119819 61662422504653250992679729)
        ·
          refine ⟨46246816878489938244509797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61662422504653250992679729 46246816878489938244509797)
          ·
            refine ⟨8671278164716863420845587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46246816878489938244509797 8671278164716863420845587)
            ·
              refine ⟨13006917247075295131268381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8671278164716863420845587 13006917247075295131268381)
              ·
                refine ⟨4877593967653235674225643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13006917247075295131268381 4877593967653235674225643)
                ·
                  refine ⟨7316390951479853511338465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4877593967653235674225643 7316390951479853511338465)
                  ·
                    refine ⟨5487293213609890133503849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7316390951479853511338465 5487293213609890133503849)
                    ·
                      refine ⟨4115469910207417600127887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5487293213609890133503849 4115469910207417600127887)
                      ·
                        rfl

theorem cell23_8014849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_8014849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014849 prefixEnd_8014849 := by exact prefixLift 8014849
  have htrace : WordTrace (prefixWord ++ tailWord_8014849) baseStart_8014849 baseEnd_8014849 := by
    simpa [prefixWord, tailWord_8014849, baseEnd_8014849] using wordTrace_append hprefix tailTrace_8014849
  have hstable : (prefixWord ++ tailWord_8014849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014849).length < 2 ^ (prefixWord ++ tailWord_8014849).sum := by decide
  have hdescent : baseEnd_8014849 < baseStart_8014849 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014882 : List Nat := [3, 3, 1, 1, 1, 3, 4, 1, 2, 1, 3]
def baseStart_8014882 : Nat := 118140960795 + 8014882 * 2 ^ 59
def prefixEnd_8014882 : Nat := 4983230072969 + 3 ^ 40 * 8014882 * 2
def baseEnd_8014882 : Nat := 4115486855069015971015235

theorem tailTrace_8014882 : CollatzResearch.WordTrace tailWord_8014882 prefixEnd_8014882 4115486855069015971015235 := by
  unfold tailWord_8014882
  simp only [CollatzResearch.WordTrace]
  refine ⟨73081690537364705428089725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194884508099639214474905933 73081690537364705428089725)
  ·
    refine ⟨27405633951511764535533647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73081690537364705428089725 27405633951511764535533647)
    ·
      refine ⟨41108450927267646803300471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27405633951511764535533647 41108450927267646803300471)
      ·
        refine ⟨61662676390901470204950707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41108450927267646803300471 61662676390901470204950707)
        ·
          refine ⟨92494014586352205307426061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61662676390901470204950707 92494014586352205307426061)
          ·
            refine ⟨34685255469882076990284773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92494014586352205307426061 34685255469882076990284773)
            ·
              refine ⟨6503485400602889435678395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34685255469882076990284773 6503485400602889435678395)
              ·
                refine ⟨9755228100904334153517593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6503485400602889435678395 9755228100904334153517593)
                ·
                  refine ⟨7316421075678250615138195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9755228100904334153517593 7316421075678250615138195)
                  ·
                    refine ⟨10974631613517375922707293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7316421075678250615138195 10974631613517375922707293)
                    ·
                      refine ⟨4115486855069015971015235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10974631613517375922707293 4115486855069015971015235)
                      ·
                        rfl

theorem cell23_8014882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_8014882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014882 prefixEnd_8014882 := by exact prefixLift 8014882
  have htrace : WordTrace (prefixWord ++ tailWord_8014882) baseStart_8014882 baseEnd_8014882 := by
    simpa [prefixWord, tailWord_8014882, baseEnd_8014882] using wordTrace_append hprefix tailTrace_8014882
  have hstable : (prefixWord ++ tailWord_8014882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014882).length < 2 ^ (prefixWord ++ tailWord_8014882).sum := by decide
  have hdescent : baseEnd_8014882 < baseStart_8014882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014901 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_8014901 : Nat := 118140960795 + 8014901 * 2 ^ 59
def prefixEnd_8014901 : Nat := 4983230072969 + 3 ^ 40 * 8014901 * 2
def baseEnd_8014901 : Nat := 4115496611201451396677647

theorem tailTrace_8014901 : CollatzResearch.WordTrace tailWord_8014901 prefixEnd_8014901 4115496611201451396677647 := by
  unfold tailWord_8014901
  simp only [CollatzResearch.WordTrace]
  refine ⟨292327455136389987957300557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194884970090926658638200371 292327455136389987957300557)
  ·
    refine ⟨109622795676146245483987709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292327455136389987957300557 109622795676146245483987709)
    ·
      refine ⟨41108548378554842056495391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109622795676146245483987709 41108548378554842056495391)
      ·
        refine ⟨61662822567832263084743087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41108548378554842056495391 61662822567832263084743087)
        ·
          refine ⟨92494233851748394627114631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61662822567832263084743087 92494233851748394627114631)
          ·
            refine ⟨138741350777622591940671947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92494233851748394627114631 138741350777622591940671947)
            ·
              refine ⟨208112026166433887911007921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138741350777622591940671947 208112026166433887911007921)
              ·
                refine ⟨156084019624825415933255941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208112026166433887911007921 156084019624825415933255941)
                ·
                  refine ⟨29265753679654765487485489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156084019624825415933255941 29265753679654765487485489)
                  ·
                    refine ⟨21949315259741074115614117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29265753679654765487485489 21949315259741074115614117)
                    ·
                      refine ⟨4115496611201451396677647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21949315259741074115614117 4115496611201451396677647)
                      ·
                        rfl

theorem cell23_8014901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_8014901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014901 prefixEnd_8014901 := by exact prefixLift 8014901
  have htrace : WordTrace (prefixWord ++ tailWord_8014901) baseStart_8014901 baseEnd_8014901 := by
    simpa [prefixWord, tailWord_8014901, baseEnd_8014901] using wordTrace_append hprefix tailTrace_8014901
  have hstable : (prefixWord ++ tailWord_8014901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014901).length < 2 ^ (prefixWord ++ tailWord_8014901).sum := by decide
  have hdescent : baseEnd_8014901 < baseStart_8014901 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014905 : List Nat := [1, 2, 1, 5, 2, 2, 1, 2, 1, 4, 2]
def baseStart_8014905 : Nat := 118140960795 + 8014905 * 2 ^ 59
def prefixEnd_8014905 : Nat := 4983230072969 + 3 ^ 40 * 8014905 * 2
def baseEnd_8014905 : Nat := 4115498665124069381027629

theorem tailTrace_8014905 : CollatzResearch.WordTrace tailWord_8014905 prefixEnd_8014905 4115498665124069381027629 := by
  unfold tailWord_8014905
  simp only [CollatzResearch.WordTrace]
  refine ⟨292327601028375496640446169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194885067352250331093630779 292327601028375496640446169)
  ·
    refine ⟨219245700771281622480334627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292327601028375496640446169 219245700771281622480334627)
    ·
      refine ⟨328868551156922433720501941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219245700771281622480334627 328868551156922433720501941)
      ·
        refine ⟨30831426670961478161297057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 328868551156922433720501941 30831426670961478161297057)
        ·
          refine ⟨23123570003221108620972793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30831426670961478161297057 23123570003221108620972793)
          ·
            refine ⟨17342677502415831465729595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23123570003221108620972793 17342677502415831465729595)
            ·
              refine ⟨26014016253623747198594393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17342677502415831465729595 26014016253623747198594393)
              ·
                refine ⟨19510512190217810398945795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26014016253623747198594393 19510512190217810398945795)
                ·
                  refine ⟨29265768285326715598418693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19510512190217810398945795 29265768285326715598418693)
                  ·
                    refine ⟨5487331553498759174703505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29265768285326715598418693 5487331553498759174703505)
                    ·
                      refine ⟨4115498665124069381027629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5487331553498759174703505 4115498665124069381027629)
                      ·
                        rfl

theorem cell23_8014905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_8014905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014905 prefixEnd_8014905 := by exact prefixLift 8014905
  have htrace : WordTrace (prefixWord ++ tailWord_8014905) baseStart_8014905 baseEnd_8014905 := by
    simpa [prefixWord, tailWord_8014905, baseEnd_8014905] using wordTrace_append hprefix tailTrace_8014905
  have hstable : (prefixWord ++ tailWord_8014905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014905).length < 2 ^ (prefixWord ++ tailWord_8014905).sum := by decide
  have hdescent : baseEnd_8014905 < baseStart_8014905 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014948 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 4, 5, 2]
def baseStart_8014948 : Nat := 118140960795 + 8014948 * 2 ^ 59
def prefixEnd_8014948 : Nat := 4983230072969 + 3 ^ 40 * 8014948 * 2
def baseEnd_8014948 : Nat := 4115520744792212712789931

theorem tailTrace_8014948 : CollatzResearch.WordTrace tailWord_8014948 prefixEnd_8014948 4115520744792212712789931 := by
  unfold tailWord_8014948
  simp only [CollatzResearch.WordTrace]
  refine ⟨146164584683609857492130749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194886112911479809989507665 146164584683609857492130749)
  ·
    refine ⟨54811719256353696559549031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146164584683609857492130749 54811719256353696559549031)
    ·
      refine ⟨82217578884530544839323547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54811719256353696559549031 82217578884530544839323547)
      ·
        refine ⟨123326368326795817258985321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82217578884530544839323547 123326368326795817258985321)
        ·
          refine ⟨92494776245096862944238991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123326368326795817258985321 92494776245096862944238991)
          ·
            refine ⟨138742164367645294416358487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92494776245096862944238991 138742164367645294416358487)
            ·
              refine ⟨208113246551467941624537731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138742164367645294416358487 208113246551467941624537731)
              ·
                refine ⟨312169869827201912436806597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208113246551467941624537731 312169869827201912436806597)
                ·
                  refine ⟨58531850592600358581901237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 312169869827201912436806597 58531850592600358581901237)
                  ·
                    refine ⟨5487360993056283617053241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58531850592600358581901237 5487360993056283617053241)
                    ·
                      refine ⟨4115520744792212712789931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5487360993056283617053241 4115520744792212712789931)
                      ·
                        rfl

theorem cell23_8014948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_8014948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014948 prefixEnd_8014948 := by exact prefixLift 8014948
  have htrace : WordTrace (prefixWord ++ tailWord_8014948) baseStart_8014948 baseEnd_8014948 := by
    simpa [prefixWord, tailWord_8014948, baseEnd_8014948] using wordTrace_append hprefix tailTrace_8014948
  have hstable : (prefixWord ++ tailWord_8014948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014948).length < 2 ^ (prefixWord ++ tailWord_8014948).sum := by decide
  have hdescent : baseEnd_8014948 < baseStart_8014948 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8014958 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 1, 7]
def baseStart_8014958 : Nat := 118140960795 + 8014958 * 2 ^ 59
def prefixEnd_8014958 : Nat := 4983230072969 + 3 ^ 40 * 8014958 * 2
def baseEnd_8014958 : Nat := 1371841959866252557888295

theorem tailTrace_8014958 : CollatzResearch.WordTrace tailWord_8014958 prefixEnd_8014958 1371841959866252557888295 := by
  unfold tailWord_8014958
  simp only [CollatzResearch.WordTrace]
  refine ⟨36541191762147935836515691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194886356064788991128083685 36541191762147935836515691)
  ·
    refine ⟨54811787643221903754773537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36541191762147935836515691 54811787643221903754773537)
    ·
      refine ⟨41108840732416427816080153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54811787643221903754773537 41108840732416427816080153)
      ·
        refine ⟨30831630549312320862060115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41108840732416427816080153 30831630549312320862060115)
        ·
          refine ⟨46247445823968481293090173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30831630549312320862060115 46247445823968481293090173)
          ·
            refine ⟨17342792183988180484908815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46247445823968481293090173 17342792183988180484908815)
            ·
              refine ⟨26014188275982270727363223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17342792183988180484908815 26014188275982270727363223)
              ·
                refine ⟨39021282413973406091044835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26014188275982270727363223 39021282413973406091044835)
                ·
                  refine ⟨58531923620960109136567253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39021282413973406091044835 58531923620960109136567253)
                  ·
                    refine ⟨1371841959866252557888295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58531923620960109136567253 1371841959866252557888295)
                    ·
                      rfl

theorem cell23_8014958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_8014958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8014958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8014958 prefixEnd_8014958 := by exact prefixLift 8014958
  have htrace : WordTrace (prefixWord ++ tailWord_8014958) baseStart_8014958 baseEnd_8014958 := by
    simpa [prefixWord, tailWord_8014958, baseEnd_8014958] using wordTrace_append hprefix tailTrace_8014958
  have hstable : (prefixWord ++ tailWord_8014958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8014958).length < 2 ^ (prefixWord ++ tailWord_8014958).sum := by decide
  have hdescent : baseEnd_8014958 < baseStart_8014958 := by decide
  rcases family_descends (prefixWord ++ tailWord_8014958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015015 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_8015015 : Nat := 118140960795 + 8015015 * 2 ^ 59
def prefixEnd_8015015 : Nat := 4983230072969 + 3 ^ 40 * 8015015 * 2
def baseEnd_8015015 : Nat := 4115555147996063950652123

theorem tailTrace_8015015 : CollatzResearch.WordTrace tailWord_8015015 prefixEnd_8015015 4115555147996063950652123 := by
  unfold tailWord_8015015
  simp only [CollatzResearch.WordTrace]
  refine ⟨292331613057976985426950499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194887742038651323617966999 292331613057976985426950499)
  ·
    refine ⟨438497419586965478140425749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292331613057976985426950499 438497419586965478140425749)
    ·
      refine ⟨20554566543139006787832457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 438497419586965478140425749 20554566543139006787832457)
      ·
        refine ⟨15415924907354255090874343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20554566543139006787832457 15415924907354255090874343)
        ·
          refine ⟨23123887361031382636311515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15415924907354255090874343 23123887361031382636311515)
          ·
            refine ⟨34685831041547073954467273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23123887361031382636311515 34685831041547073954467273)
            ·
              refine ⟨26014373281160305465850455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34685831041547073954467273 26014373281160305465850455)
              ·
                refine ⟨39021559921740458198775683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26014373281160305465850455 39021559921740458198775683)
                ·
                  refine ⟨58532339882610687298163525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39021559921740458198775683 58532339882610687298163525)
                  ·
                    refine ⟨10974813727989503868405661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58532339882610687298163525 10974813727989503868405661)
                    ·
                      refine ⟨4115555147996063950652123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10974813727989503868405661 4115555147996063950652123)
                      ·
                        rfl

theorem cell23_8015015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_8015015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015015 prefixEnd_8015015 := by exact prefixLift 8015015
  have htrace : WordTrace (prefixWord ++ tailWord_8015015) baseStart_8015015 baseEnd_8015015 := by
    simpa [prefixWord, tailWord_8015015, baseEnd_8015015] using wordTrace_append hprefix tailTrace_8015015
  have hstable : (prefixWord ++ tailWord_8015015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015015).length < 2 ^ (prefixWord ++ tailWord_8015015).sum := by decide
  have hdescent : baseEnd_8015015 < baseStart_8015015 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015072 : List Nat := [2, 1, 1, 3, 1, 5, 2, 1, 2, 3, 2]
def baseStart_8015072 : Nat := 118140960795 + 8015072 * 2 ^ 59
def prefixEnd_8015072 : Nat := 4983230072969 + 3 ^ 40 * 8015072 * 2
def baseEnd_8015072 : Nat := 4115584416393370227639361

theorem tailTrace_8015072 : CollatzResearch.WordTrace tailWord_8015072 prefixEnd_8015072 4115584416393370227639361 := by
  unfold tailWord_8015072
  simp only [CollatzResearch.WordTrace]
  refine ⟨146166846009385242080887735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194889128012513656107850313 146166846009385242080887735)
  ·
    refine ⟨219250269014077863121331603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146166846009385242080887735 219250269014077863121331603)
    ·
      refine ⟨328875403521116794681997405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219250269014077863121331603 328875403521116794681997405)
      ·
        refine ⟨123328276320418798005749027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328875403521116794681997405 123328276320418798005749027)
        ·
          refine ⟨184992414480628197008623541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123328276320418798005749027 184992414480628197008623541)
          ·
            refine ⟨17343038857558893469558457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184992414480628197008623541 17343038857558893469558457)
            ·
              refine ⟨13007279143169170102168843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17343038857558893469558457 13007279143169170102168843)
              ·
                refine ⟨19510918714753755153253265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13007279143169170102168843 19510918714753755153253265)
                ·
                  refine ⟨14633189036065316364939949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19510918714753755153253265 14633189036065316364939949)
                  ·
                    refine ⟨5487445888524493636852481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14633189036065316364939949 5487445888524493636852481)
                    ·
                      refine ⟨4115584416393370227639361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5487445888524493636852481 4115584416393370227639361)
                      ·
                        rfl

theorem cell23_8015072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_8015072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015072 prefixEnd_8015072 := by exact prefixLift 8015072
  have htrace : WordTrace (prefixWord ++ tailWord_8015072) baseStart_8015072 baseEnd_8015072 := by
    simpa [prefixWord, tailWord_8015072, baseEnd_8015072] using wordTrace_append hprefix tailTrace_8015072
  have hstable : (prefixWord ++ tailWord_8015072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015072).length < 2 ^ (prefixWord ++ tailWord_8015072).sum := by decide
  have hdescent : baseEnd_8015072 < baseStart_8015072 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015082 : List Nat := [3, 1, 3, 1, 1, 4, 3, 1, 1, 5]
def baseStart_8015082 : Nat := 118140960795 + 8015082 * 2 ^ 59
def prefixEnd_8015082 : Nat := 4983230072969 + 3 ^ 40 * 8015082 * 2
def baseEnd_8015082 : Nat := 1371863183733305062838105

theorem tailTrace_8015082 : CollatzResearch.WordTrace tailWord_8015082 prefixEnd_8015082 1371863183733305062838105 := by
  unfold tailWord_8015082
  simp only [CollatzResearch.WordTrace]
  refine ⟨73083514187183563967409875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194889371165822837246426333 73083514187183563967409875)
  ·
    refine ⟨109625271280775345951114813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73083514187183563967409875 109625271280775345951114813)
    ·
      refine ⟨41109476730290754731668055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109625271280775345951114813 41109476730290754731668055)
      ·
        refine ⟨61664215095436132097502083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41109476730290754731668055 61664215095436132097502083)
        ·
          refine ⟨92496322643154198146253125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61664215095436132097502083 92496322643154198146253125)
          ·
            refine ⟨17343060495591412152422461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92496322643154198146253125 17343060495591412152422461)
            ·
              refine ⟨6503647685846779557158423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17343060495591412152422461 6503647685846779557158423)
              ·
                refine ⟨9755471528770169335737635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6503647685846779557158423 9755471528770169335737635)
                ·
                  refine ⟨14633207293155254003606453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9755471528770169335737635 14633207293155254003606453)
                  ·
                    refine ⟨1371863183733305062838105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14633207293155254003606453 1371863183733305062838105)
                    ·
                      rfl

theorem cell23_8015082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_8015082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015082 prefixEnd_8015082 := by exact prefixLift 8015082
  have htrace : WordTrace (prefixWord ++ tailWord_8015082) baseStart_8015082 baseEnd_8015082 := by
    simpa [prefixWord, tailWord_8015082, baseEnd_8015082] using wordTrace_append hprefix tailTrace_8015082
  have hstable : (prefixWord ++ tailWord_8015082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015082).length < 2 ^ (prefixWord ++ tailWord_8015082).sum := by decide
  have hdescent : baseEnd_8015082 < baseStart_8015082 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015091 : List Nat := [1, 1, 1, 2, 2, 16]
def baseStart_8015091 : Nat := 118140960795 + 8015091 * 2 ^ 59
def prefixEnd_8015091 : Nat := 4983230072969 + 3 ^ 40 * 8015091 * 2
def baseEnd_8015091 : Nat := 16936601533028006803711

theorem tailTrace_8015091 : CollatzResearch.WordTrace tailWord_8015091 prefixEnd_8015091 16936601533028006803711 := by
  unfold tailWord_8015091
  simp only [CollatzResearch.WordTrace]
  refine ⟨292334385005701650406717127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194889590003801100271144751 292334385005701650406717127)
  ·
    refine ⟨438501577508552475610075691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292334385005701650406717127 438501577508552475610075691)
    ·
      refine ⟨657752366262828713415113537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438501577508552475610075691 657752366262828713415113537)
      ·
        refine ⟨493314274697121535061335153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657752366262828713415113537 493314274697121535061335153)
        ·
          refine ⟨369985706022841151296001365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493314274697121535061335153 369985706022841151296001365)
          ·
            refine ⟨16936601533028006803711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 16 369985706022841151296001365 16936601533028006803711)
            ·
              rfl

theorem cell23_8015091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 16].length) (baseStart_8015091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015091 prefixEnd_8015091 := by exact prefixLift 8015091
  have htrace : WordTrace (prefixWord ++ tailWord_8015091) baseStart_8015091 baseEnd_8015091 := by
    simpa [prefixWord, tailWord_8015091, baseEnd_8015091] using wordTrace_append hprefix tailTrace_8015091
  have hstable : (prefixWord ++ tailWord_8015091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015091).length < 2 ^ (prefixWord ++ tailWord_8015091).sum := by decide
  have hdescent : baseEnd_8015091 < baseStart_8015091 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015098 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4]
def baseStart_8015098 : Nat := 118140960795 + 8015098 * 2 ^ 59
def prefixEnd_8015098 : Nat := 4983230072969 + 3 ^ 40 * 8015098 * 2
def baseEnd_8015098 : Nat := 4115597766890387125914241

theorem tailTrace_8015098 : CollatzResearch.WordTrace tailWord_8015098 prefixEnd_8015098 4115597766890387125914241 := by
  unfold tailWord_8015098
  simp only [CollatzResearch.WordTrace]
  refine ⟨73083660079169072650555487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194889760211117527068147965 73083660079169072650555487)
  ·
    refine ⟨109625490118753608975833231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73083660079169072650555487 109625490118753608975833231)
    ·
      refine ⟨164438235178130413463749847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109625490118753608975833231 164438235178130413463749847)
      ·
        refine ⟨246657352767195620195624771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164438235178130413463749847 246657352767195620195624771)
        ·
          refine ⟨369986029150793430293437157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246657352767195620195624771 369986029150793430293437157)
          ·
            refine ⟨69372380465773768180019467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 369986029150793430293437157 69372380465773768180019467)
            ·
              refine ⟨104058570698660652270029201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69372380465773768180019467 104058570698660652270029201)
              ·
                refine ⟨78043928023995489202521901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104058570698660652270029201 78043928023995489202521901)
                ·
                  refine ⟨29266473008998308450945713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78043928023995489202521901 29266473008998308450945713)
                  ·
                    refine ⟨21949854756748731338209285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29266473008998308450945713 21949854756748731338209285)
                    ·
                      refine ⟨4115597766890387125914241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21949854756748731338209285 4115597766890387125914241)
                      ·
                        rfl

theorem cell23_8015098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_8015098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015098 prefixEnd_8015098 := by exact prefixLift 8015098
  have htrace : WordTrace (prefixWord ++ tailWord_8015098) baseStart_8015098 baseEnd_8015098 := by
    simpa [prefixWord, tailWord_8015098, baseEnd_8015098] using wordTrace_append hprefix tailTrace_8015098
  have hstable : (prefixWord ++ tailWord_8015098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015098).length < 2 ^ (prefixWord ++ tailWord_8015098).sum := by decide
  have hdescent : baseEnd_8015098 < baseStart_8015098 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015105 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 3, 2, 3]
def baseStart_8015105 : Nat := 118140960795 + 8015105 * 2 ^ 59
def prefixEnd_8015105 : Nat := 4983230072969 + 3 ^ 40 * 8015105 * 2
def baseEnd_8015105 : Nat := 4115601361254968598526709

theorem tailTrace_8015105 : CollatzResearch.WordTrace tailWord_8015105 prefixEnd_8015105 4115601361254968598526709 := by
  unfold tailWord_8015105
  simp only [CollatzResearch.WordTrace]
  refine ⟨292334895627650930797726769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194889930418433953865151179 292334895627650930797726769)
  ·
    refine ⟨219251171720738198098295077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292334895627650930797726769 219251171720738198098295077)
    ·
      refine ⟨41109594697638412143430327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219251171720738198098295077 41109594697638412143430327)
      ·
        refine ⟨61664392046457618215145491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41109594697638412143430327 61664392046457618215145491)
        ·
          refine ⟨92496588069686427322718237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61664392046457618215145491 92496588069686427322718237)
          ·
            refine ⟨34686220526132410246019339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92496588069686427322718237 34686220526132410246019339)
            ·
              refine ⟨52029330789198615369029009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34686220526132410246019339 52029330789198615369029009)
              ·
                refine ⟨39021998091898961526771757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52029330789198615369029009 39021998091898961526771757)
                ·
                  refine ⟨14633249284462110572539409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39021998091898961526771757 14633249284462110572539409)
                  ·
                    refine ⟨10974936963346582929404557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14633249284462110572539409 10974936963346582929404557)
                    ·
                      refine ⟨4115601361254968598526709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10974936963346582929404557 4115601361254968598526709)
                      ·
                        rfl

theorem cell23_8015105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_8015105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015105 prefixEnd_8015105 := by exact prefixLift 8015105
  have htrace : WordTrace (prefixWord ++ tailWord_8015105) baseStart_8015105 baseEnd_8015105 := by
    simpa [prefixWord, tailWord_8015105, baseEnd_8015105] using wordTrace_append hprefix tailTrace_8015105
  have hstable : (prefixWord ++ tailWord_8015105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015105).length < 2 ^ (prefixWord ++ tailWord_8015105).sum := by decide
  have hdescent : baseEnd_8015105 < baseStart_8015105 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015115 : List Nat := [1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 4]
def baseStart_8015115 : Nat := 118140960795 + 8015115 * 2 ^ 59
def prefixEnd_8015115 : Nat := 4983230072969 + 3 ^ 40 * 8015115 * 2
def baseEnd_8015115 : Nat := 4115606496061513559401663

theorem tailTrace_8015115 : CollatzResearch.WordTrace tailWord_8015115 prefixEnd_8015115 4115606496061513559401663 := by
  unfold tailWord_8015115
  simp only [CollatzResearch.WordTrace]
  refine ⟨292335260357614702505590799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194890173571743135003727199 292335260357614702505590799)
  ·
    refine ⟨438502890536422053758386199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292335260357614702505590799 438502890536422053758386199)
    ·
      refine ⟨657754335804633080637579299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438502890536422053758386199 657754335804633080637579299)
      ·
        refine ⟨986631503706949620956368949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657754335804633080637579299 986631503706949620956368949)
        ·
          refine ⟨92496703472526526964659589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 986631503706949620956368949 92496703472526526964659589)
          ·
            refine ⟨17343131901098723805873673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92496703472526526964659589 17343131901098723805873673)
            ·
              refine ⟨13007348925824042854405255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17343131901098723805873673 13007348925824042854405255)
              ·
                refine ⟨19511023388736064281607883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13007348925824042854405255 19511023388736064281607883)
                ·
                  refine ⟨29266535083104096422411825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19511023388736064281607883 29266535083104096422411825)
                  ·
                    refine ⟨21949901312328072316808869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29266535083104096422411825 21949901312328072316808869)
                    ·
                      refine ⟨4115606496061513559401663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21949901312328072316808869 4115606496061513559401663)
                      ·
                        rfl

theorem cell23_8015115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 4].length) (baseStart_8015115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015115 prefixEnd_8015115 := by exact prefixLift 8015115
  have htrace : WordTrace (prefixWord ++ tailWord_8015115) baseStart_8015115 baseEnd_8015115 := by
    simpa [prefixWord, tailWord_8015115, baseEnd_8015115] using wordTrace_append hprefix tailTrace_8015115
  have hstable : (prefixWord ++ tailWord_8015115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015115).length < 2 ^ (prefixWord ++ tailWord_8015115).sum := by decide
  have hdescent : baseEnd_8015115 < baseStart_8015115 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015136 : List Nat := [2, 1, 1, 5, 4, 1, 2, 1, 1, 1, 4]
def baseStart_8015136 : Nat := 118140960795 + 8015136 * 2 ^ 59
def prefixEnd_8015136 : Nat := 4983230072969 + 3 ^ 40 * 8015136 * 2
def baseEnd_8015136 : Nat := 4115617279155257977239067

theorem tailTrace_8015136 : CollatzResearch.WordTrace tailWord_8015136 prefixEnd_8015136 4115617279155257977239067 := by
  unfold tailWord_8015136
  simp only [CollatzResearch.WordTrace]
  refine ⟨146168013145269311546052631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194890684193692415394736841 146168013145269311546052631)
  ·
    refine ⟨219252019717903967319078947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146168013145269311546052631 219252019717903967319078947)
    ·
      refine ⟨328878029576855950978618421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219252019717903967319078947 328878029576855950978618421)
      ·
        refine ⟨30832315272830245404245477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 328878029576855950978618421 30832315272830245404245477)
        ·
          refine ⟨5781059113655671013296027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30832315272830245404245477 5781059113655671013296027)
          ·
            refine ⟨8671588670483506519944041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5781059113655671013296027 8671588670483506519944041)
            ·
              refine ⟨6503691502862629889958031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8671588670483506519944041 6503691502862629889958031)
              ·
                refine ⟨9755537254293944834937047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6503691502862629889958031 9755537254293944834937047)
                ·
                  refine ⟨14633305881440917252405571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9755537254293944834937047 14633305881440917252405571)
                  ·
                    refine ⟨21949958822161375878608357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14633305881440917252405571 21949958822161375878608357)
                    ·
                      refine ⟨4115617279155257977239067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21949958822161375878608357 4115617279155257977239067)
                      ·
                        rfl

theorem cell23_8015136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_8015136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015136 prefixEnd_8015136 := by exact prefixLift 8015136
  have htrace : WordTrace (prefixWord ++ tailWord_8015136) baseStart_8015136 baseEnd_8015136 := by
    simpa [prefixWord, tailWord_8015136, baseEnd_8015136] using wordTrace_append hprefix tailTrace_8015136
  have hstable : (prefixWord ++ tailWord_8015136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015136).length < 2 ^ (prefixWord ++ tailWord_8015136).sum := by decide
  have hdescent : baseEnd_8015136 < baseStart_8015136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015139 : List Nat := [1, 1, 1, 4, 2, 5, 2, 1, 1, 2, 3]
def baseStart_8015139 : Nat := 118140960795 + 8015139 * 2 ^ 59
def prefixEnd_8015139 : Nat := 4983230072969 + 3 ^ 40 * 8015139 * 2
def baseEnd_8015139 : Nat := 4115618819597221465501553

theorem tailTrace_8015139 : CollatzResearch.WordTrace tailWord_8015139 prefixEnd_8015139 4115618819597221465501553 := by
  unfold tailWord_8015139
  simp only [CollatzResearch.WordTrace]
  refine ⟨292336135709527754604464471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194890757139685169736309647 292336135709527754604464471)
  ·
    refine ⟨438504203564291631906696707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292336135709527754604464471 438504203564291631906696707)
    ·
      refine ⟨657756305346437447860045061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438504203564291631906696707 657756305346437447860045061)
      ·
        refine ⟨123329307252457021473758449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 657756305346437447860045061 123329307252457021473758449)
        ·
          refine ⟨92496980439342766105318837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123329307252457021473758449 92496980439342766105318837)
          ·
            refine ⟨8671591916188384322373641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92496980439342766105318837 8671591916188384322373641)
            ·
              refine ⟨6503693937141288241780231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8671591916188384322373641 6503693937141288241780231)
              ·
                refine ⟨9755540905711932362670347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6503693937141288241780231 9755540905711932362670347)
                ·
                  refine ⟨14633311358567898544005521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9755540905711932362670347 14633311358567898544005521)
                  ·
                    refine ⟨10974983518925923908004141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14633311358567898544005521 10974983518925923908004141)
                    ·
                      refine ⟨4115618819597221465501553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10974983518925923908004141 4115618819597221465501553)
                      ·
                        rfl

theorem cell23_8015139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_8015139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015139 prefixEnd_8015139 := by exact prefixLift 8015139
  have htrace : WordTrace (prefixWord ++ tailWord_8015139) baseStart_8015139 baseEnd_8015139 := by
    simpa [prefixWord, tailWord_8015139, baseEnd_8015139] using wordTrace_append hprefix tailTrace_8015139
  have hstable : (prefixWord ++ tailWord_8015139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015139).length < 2 ^ (prefixWord ++ tailWord_8015139).sum := by decide
  have hdescent : baseEnd_8015139 < baseStart_8015139 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015168 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 2, 6]
def baseStart_8015168 : Nat := 118140960795 + 8015168 * 2 ^ 59
def prefixEnd_8015168 : Nat := 4983230072969 + 3 ^ 40 * 8015168 * 2
def baseEnd_8015168 : Nat := 1371877903512067284012973

theorem tailTrace_8015168 : CollatzResearch.WordTrace tailWord_8015168 prefixEnd_8015168 1371877903512067284012973 := by
  unfold tailWord_8015168
  simp only [CollatzResearch.WordTrace]
  refine ⟨146168596713211346278635079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194891462284281795038180105 146168596713211346278635079)
  ·
    refine ⟨219252895069817019417952619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146168596713211346278635079 219252895069817019417952619)
    ·
      refine ⟨328879342604725529126928929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219252895069817019417952619 328879342604725529126928929)
      ·
        refine ⟨246659506953544146845196697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328879342604725529126928929 246659506953544146845196697)
        ·
          refine ⟨184994630215158110133897523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246659506953544146845196697 184994630215158110133897523)
          ·
            refine ⟨277491945322737165200846285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184994630215158110133897523 277491945322737165200846285)
            ·
              refine ⟨104059479496026436950317357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277491945322737165200846285 104059479496026436950317357)
              ·
                refine ⟨39022304811009913856369009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104059479496026436950317357 39022304811009913856369009)
                ·
                  refine ⟨29266728608257435392276757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39022304811009913856369009 29266728608257435392276757)
                  ·
                    refine ⟨1371877903512067284012973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29266728608257435392276757 1371877903512067284012973)
                    ·
                      rfl

theorem cell23_8015168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 2, 6].length) (baseStart_8015168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015168 prefixEnd_8015168 := by exact prefixLift 8015168
  have htrace : WordTrace (prefixWord ++ tailWord_8015168) baseStart_8015168 baseEnd_8015168 := by
    simpa [prefixWord, tailWord_8015168, baseEnd_8015168] using wordTrace_append hprefix tailTrace_8015168
  have hstable : (prefixWord ++ tailWord_8015168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015168).length < 2 ^ (prefixWord ++ tailWord_8015168).sum := by decide
  have hdescent : baseEnd_8015168 < baseStart_8015168 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015169 : List Nat := [1, 2, 5, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_8015169 : Nat := 118140960795 + 8015169 * 2 ^ 59
def prefixEnd_8015169 : Nat := 4983230072969 + 3 ^ 40 * 8015169 * 2
def baseEnd_8015169 : Nat := 4115634224016856348126415

theorem tailTrace_8015169 : CollatzResearch.WordTrace tailWord_8015169 prefixEnd_8015169 4115634224016856348126415 := by
  unfold tailWord_8015169
  simp only [CollatzResearch.WordTrace]
  refine ⟨292337229899419069728056561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194891486599612713152037707 292337229899419069728056561)
  ·
    refine ⟨219252922424564302296042421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292337229899419069728056561 219252922424564302296042421)
    ·
      refine ⟨20554961477302903340253977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219252922424564302296042421 20554961477302903340253977)
      ·
        refine ⟨15416221107977177505190483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20554961477302903340253977 15416221107977177505190483)
        ·
          refine ⟨23124331661965766257785725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15416221107977177505190483 23124331661965766257785725)
          ·
            refine ⟨8671624373237162346669647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23124331661965766257785725 8671624373237162346669647)
            ·
              refine ⟨13007436559855743520004471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8671624373237162346669647 13007436559855743520004471)
              ·
                refine ⟨19511154839783615280006707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13007436559855743520004471 19511154839783615280006707)
                ·
                  refine ⟨29266732259675422920010061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19511154839783615280006707 29266732259675422920010061)
                  ·
                    refine ⟨10975024597378283595003773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29266732259675422920010061 10975024597378283595003773)
                    ·
                      refine ⟨4115634224016856348126415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10975024597378283595003773 4115634224016856348126415)
                      ·
                        rfl

theorem cell23_8015169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_8015169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015169 prefixEnd_8015169 := by exact prefixLift 8015169
  have htrace : WordTrace (prefixWord ++ tailWord_8015169) baseStart_8015169 baseEnd_8015169 := by
    simpa [prefixWord, tailWord_8015169, baseEnd_8015169] using wordTrace_append hprefix tailTrace_8015169
  have hstable : (prefixWord ++ tailWord_8015169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015169).length < 2 ^ (prefixWord ++ tailWord_8015169).sum := by decide
  have hdescent : baseEnd_8015169 < baseStart_8015169 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015178 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_8015178 : Nat := 118140960795 + 8015178 * 2 ^ 59
def prefixEnd_8015178 : Nat := 4983230072969 + 3 ^ 40 * 8015178 * 2
def baseEnd_8015178 : Nat := 4115638845342746812913873

theorem tailTrace_8015178 : CollatzResearch.WordTrace tailWord_8015178 prefixEnd_8015178 4115638845342746812913873 := by
  unfold tailWord_8015178
  simp only [CollatzResearch.WordTrace]
  refine ⟨73084389539096616066283547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194891705437590976176756125 73084389539096616066283547)
  ·
    refine ⟨109626584308644924099425321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73084389539096616066283547 109626584308644924099425321)
    ·
      refine ⟨82219938231483693074568991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109626584308644924099425321 82219938231483693074568991)
      ·
        refine ⟨123329907347225539611853487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82219938231483693074568991 123329907347225539611853487)
        ·
          refine ⟨184994861020838309417780231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123329907347225539611853487 184994861020838309417780231)
          ·
            refine ⟨277492291531257464126670347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184994861020838309417780231 277492291531257464126670347)
            ·
              refine ⟨416238437296886196190005521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277492291531257464126670347 416238437296886196190005521)
              ·
                refine ⟨312178827972664647142504141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416238437296886196190005521 312178827972664647142504141)
                ·
                  refine ⟨117067060489749242678439053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312178827972664647142504141 117067060489749242678439053)
                  ·
                    refine ⟨43900147683655966004414645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117067060489749242678439053 43900147683655966004414645)
                    ·
                      refine ⟨4115638845342746812913873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43900147683655966004414645 4115638845342746812913873)
                      ·
                        rfl

theorem cell23_8015178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_8015178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015178 prefixEnd_8015178 := by exact prefixLift 8015178
  have htrace : WordTrace (prefixWord ++ tailWord_8015178) baseStart_8015178 baseEnd_8015178 := by
    simpa [prefixWord, tailWord_8015178, baseEnd_8015178] using wordTrace_append hprefix tailTrace_8015178
  have hstable : (prefixWord ++ tailWord_8015178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015178).length < 2 ^ (prefixWord ++ tailWord_8015178).sum := by decide
  have hdescent : baseEnd_8015178 < baseStart_8015178 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015192 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 6, 2, 2]
def baseStart_8015192 : Nat := 118140960795 + 8015192 * 2 ^ 59
def prefixEnd_8015192 : Nat := 4983230072969 + 3 ^ 40 * 8015192 * 2
def baseEnd_8015192 : Nat := 4115646034071909758138809

theorem tailTrace_8015192 : CollatzResearch.WordTrace tailWord_8015192 prefixEnd_8015192 4115646034071909758138809 := by
  unfold tailWord_8015192
  simp only [CollatzResearch.WordTrace]
  refine ⟨146169034389167872328071915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194892045852223829770762553 146169034389167872328071915)
  ·
    refine ⟨219253551583751808492107873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146169034389167872328071915 219253551583751808492107873)
    ·
      refine ⟨164440163687813856369080905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219253551583751808492107873 164440163687813856369080905)
      ·
        refine ⟨123330122765860392276810679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164440163687813856369080905 123330122765860392276810679)
        ·
          refine ⟨184995184148790588415216019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123330122765860392276810679 184995184148790588415216019)
          ·
            refine ⟨277492776223185882622824029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184995184148790588415216019 277492776223185882622824029)
            ·
              refine ⟨104059791083694705983559011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277492776223185882622824029 104059791083694705983559011)
              ·
                refine ⟨156089686625542058975338517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104059791083694705983559011 156089686625542058975338517)
                ·
                  refine ⟨7316704060572284014468993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156089686625542058975338517 7316704060572284014468993)
                  ·
                    refine ⟨5487528045429213010851745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7316704060572284014468993 5487528045429213010851745)
                    ·
                      refine ⟨4115646034071909758138809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5487528045429213010851745 4115646034071909758138809)
                      ·
                        rfl

theorem cell23_8015192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_8015192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015192 prefixEnd_8015192 := by exact prefixLift 8015192
  have htrace : WordTrace (prefixWord ++ tailWord_8015192) baseStart_8015192 baseEnd_8015192 := by
    simpa [prefixWord, tailWord_8015192, baseEnd_8015192] using wordTrace_append hprefix tailTrace_8015192
  have hstable : (prefixWord ++ tailWord_8015192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015192).length < 2 ^ (prefixWord ++ tailWord_8015192).sum := by decide
  have hdescent : baseEnd_8015192 < baseStart_8015192 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015225 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 2, 3, 3]
def baseStart_8015225 : Nat := 118140960795 + 8015225 * 2 ^ 59
def prefixEnd_8015225 : Nat := 4983230072969 + 3 ^ 40 * 8015225 * 2
def baseEnd_8015225 : Nat := 4115662978933508129026157

theorem tailTrace_8015225 : CollatzResearch.WordTrace tailWord_8015225 prefixEnd_8015225 4115662978933508129026157 := by
  unfold tailWord_8015225
  simp only [CollatzResearch.WordTrace]
  refine ⟨292339272387216191292095129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194892848258144127528063419 292339272387216191292095129)
  ·
    refine ⟨219254454290412143469071347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292339272387216191292095129 219254454290412143469071347)
    ·
      refine ⟨328881681435618215203607021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219254454290412143469071347 328881681435618215203607021)
      ·
        refine ⟨123330630538356830701352633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328881681435618215203607021 123330630538356830701352633)
        ·
          refine ⟨92497972903767623026014475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123330630538356830701352633 92497972903767623026014475)
          ·
            refine ⟨138746959355651434539021713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92497972903767623026014475 138746959355651434539021713)
            ·
              refine ⟨104060219516738575904266285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138746959355651434539021713 104060219516738575904266285)
              ·
                refine ⟨39022582318776965964099857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104060219516738575904266285 39022582318776965964099857)
                ·
                  refine ⟨29266936739082724473074893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39022582318776965964099857 29266936739082724473074893)
                  ·
                    refine ⟨10975101277156021677403085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29266936739082724473074893 10975101277156021677403085)
                    ·
                      refine ⟨4115662978933508129026157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10975101277156021677403085 4115662978933508129026157)
                      ·
                        rfl

theorem cell23_8015225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_8015225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015225 prefixEnd_8015225 := by exact prefixLift 8015225
  have htrace : WordTrace (prefixWord ++ tailWord_8015225) baseStart_8015225 baseEnd_8015225 := by
    simpa [prefixWord, tailWord_8015225, baseEnd_8015225] using wordTrace_append hprefix tailTrace_8015225
  have hstable : (prefixWord ++ tailWord_8015225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015225).length < 2 ^ (prefixWord ++ tailWord_8015225).sum := by decide
  have hdescent : baseEnd_8015225 < baseStart_8015225 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015230 : List Nat := [4, 2, 3, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_8015230 : Nat := 118140960795 + 8015230 * 2 ^ 59
def prefixEnd_8015230 : Nat := 4983230072969 + 3 ^ 40 * 8015230 * 2
def baseEnd_8015230 : Nat := 4115665546336780609463635

theorem tailTrace_8015230 : CollatzResearch.WordTrace tailWord_8015230 prefixEnd_8015230 4115665546336780609463635 := by
  unfold tailWord_8015230
  simp only [CollatzResearch.WordTrace]
  refine ⟨36542431844024759643253393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194892969834798718097351429 36542431844024759643253393)
  ·
    refine ⟨27406823883018569732440045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36542431844024759643253393 27406823883018569732440045)
    ·
      refine ⟨10277558956131963649665017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27406823883018569732440045 10277558956131963649665017)
      ·
        refine ⟨7708169217098972737248763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10277558956131963649665017 7708169217098972737248763)
        ·
          refine ⟨11562253825648459105873145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7708169217098972737248763 11562253825648459105873145)
          ·
            refine ⟨8671690369236344329404859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11562253825648459105873145 8671690369236344329404859)
            ·
              refine ⟨13007535553854516494107289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8671690369236344329404859 13007535553854516494107289)
              ·
                refine ⟨9755651665390887370580467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13007535553854516494107289 9755651665390887370580467)
                ·
                  refine ⟨14633477498086331055870701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9755651665390887370580467 14633477498086331055870701)
                  ·
                    refine ⟨5487554061782374145951513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14633477498086331055870701 5487554061782374145951513)
                    ·
                      refine ⟨4115665546336780609463635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5487554061782374145951513 4115665546336780609463635)
                      ·
                        rfl

theorem cell23_8015230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_8015230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015230 prefixEnd_8015230 := by exact prefixLift 8015230
  have htrace : WordTrace (prefixWord ++ tailWord_8015230) baseStart_8015230 baseEnd_8015230 := by
    simpa [prefixWord, tailWord_8015230, baseEnd_8015230] using wordTrace_append hprefix tailTrace_8015230
  have hstable : (prefixWord ++ tailWord_8015230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015230).length < 2 ^ (prefixWord ++ tailWord_8015230).sum := by decide
  have hdescent : baseEnd_8015230 < baseStart_8015230 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015266 : List Nat := [3, 3, 1, 2, 1, 4, 2, 2, 5]
def baseStart_8015266 : Nat := 118140960795 + 8015266 * 2 ^ 59
def prefixEnd_8015266 : Nat := 4983230072969 + 3 ^ 40 * 8015266 * 2
def baseEnd_8015266 : Nat := 457298225737815829845941

theorem tailTrace_8015266 : CollatzResearch.WordTrace tailWord_8015266 prefixEnd_8015266 457298225737815829845941 := by
  unfold tailWord_8015266
  simp only [CollatzResearch.WordTrace]
  refine ⟨73085191945016913823584413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194893845186711770196225101 73085191945016913823584413)
  ·
    refine ⟨27406946979381342683844155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73085191945016913823584413 27406946979381342683844155)
    ·
      refine ⟨41110420469072014025766233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27406946979381342683844155 41110420469072014025766233)
      ·
        refine ⟨30832815351804010519324675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41110420469072014025766233 30832815351804010519324675)
        ·
          refine ⟨46249223027706015778987013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30832815351804010519324675 46249223027706015778987013)
          ·
            refine ⟨8671729317694877958560065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46249223027706015778987013 8671729317694877958560065)
            ·
              refine ⟨6503796988271158468920049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8671729317694877958560065 6503796988271158468920049)
              ·
                refine ⟨4877847741203368851690037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6503796988271158468920049 4877847741203368851690037)
                ·
                  refine ⟨457298225737815829845941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4877847741203368851690037 457298225737815829845941)
                  ·
                    rfl

theorem cell23_8015266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_8015266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015266 prefixEnd_8015266 := by exact prefixLift 8015266
  have htrace : WordTrace (prefixWord ++ tailWord_8015266) baseStart_8015266 baseEnd_8015266 := by
    simpa [prefixWord, tailWord_8015266, baseEnd_8015266] using wordTrace_append hprefix tailTrace_8015266
  have hstable : (prefixWord ++ tailWord_8015266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015266).length < 2 ^ (prefixWord ++ tailWord_8015266).sum := by decide
  have hdescent : baseEnd_8015266 < baseStart_8015266 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015322 : List Nat := [3, 1, 1, 2, 3, 2, 3, 2, 6]
def baseStart_8015322 : Nat := 118140960795 + 8015322 * 2 ^ 59
def prefixEnd_8015322 : Nat := 4983230072969 + 3 ^ 40 * 8015322 * 2
def baseEnd_8015322 : Nat := 457301420728554916612579

theorem tailTrace_8015322 : CollatzResearch.WordTrace tailWord_8015322 prefixEnd_8015322 457301420728554916612579 := by
  unfold tailWord_8015322
  simp only [CollatzResearch.WordTrace]
  refine ⟨73085702566966194214594055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194895206845243184572250813 73085702566966194214594055)
  ·
    refine ⟨109628553850449291321891083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73085702566966194214594055 109628553850449291321891083)
    ·
      refine ⟨164442830775673936982836625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109628553850449291321891083 164442830775673936982836625)
      ·
        refine ⟨123332123081755452737127469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164442830775673936982836625 123332123081755452737127469)
        ·
          refine ⟨46249546155658294776422801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123332123081755452737127469 46249546155658294776422801)
          ·
            refine ⟨34687159616743721082317101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46249546155658294776422801 34687159616743721082317101)
            ·
              refine ⟨13007684856278895405868913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34687159616743721082317101 13007684856278895405868913)
              ·
                refine ⟨9755763642209171554401685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13007684856278895405868913 9755763642209171554401685)
                ·
                  refine ⟨457301420728554916612579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9755763642209171554401685 457301420728554916612579)
                  ·
                    rfl

theorem cell23_8015322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 6].length) (baseStart_8015322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015322 prefixEnd_8015322 := by exact prefixLift 8015322
  have htrace : WordTrace (prefixWord ++ tailWord_8015322) baseStart_8015322 baseEnd_8015322 := by
    simpa [prefixWord, tailWord_8015322, baseEnd_8015322] using wordTrace_append hprefix tailTrace_8015322
  have hstable : (prefixWord ++ tailWord_8015322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015322).length < 2 ^ (prefixWord ++ tailWord_8015322).sum := by decide
  have hdescent : baseEnd_8015322 < baseStart_8015322 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015352 : List Nat := [2, 1, 2, 1, 1, 5, 1, 4, 1, 5]
def baseStart_8015352 : Nat := 118140960795 + 8015352 * 2 ^ 59
def prefixEnd_8015352 : Nat := 4983230072969 + 3 ^ 40 * 8015352 * 2
def baseEnd_8015352 : Nat := 1371909396992209710712691

theorem tailTrace_8015352 : CollatzResearch.WordTrace tailWord_8015352 prefixEnd_8015352 1371909396992209710712691 := by
  unfold tailWord_8015352
  simp only [CollatzResearch.WordTrace]
  refine ⟨146171952228878045990984155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194895936305170727987978873 146171952228878045990984155)
  ·
    refine ⟨219257928343317068986476233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146171952228878045990984155 219257928343317068986476233)
    ·
      refine ⟨164443446257487801739857175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219257928343317068986476233 164443446257487801739857175)
      ·
        refine ⟨246665169386231702609785763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164443446257487801739857175 246665169386231702609785763)
        ·
          refine ⟨369997754079347553914678645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246665169386231702609785763 369997754079347553914678645)
          ·
            refine ⟨34687289444938833179501123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 369997754079347553914678645 34687289444938833179501123)
            ·
              refine ⟨52030934167408249769251685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34687289444938833179501123 52030934167408249769251685)
              ·
                refine ⟨9755800156389046831734691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52030934167408249769251685 9755800156389046831734691)
                ·
                  refine ⟨14633700234583570247602037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9755800156389046831734691 14633700234583570247602037)
                  ·
                    refine ⟨1371909396992209710712691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14633700234583570247602037 1371909396992209710712691)
                    ·
                      rfl

theorem cell23_8015352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 1, 5].length) (baseStart_8015352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015352 prefixEnd_8015352 := by exact prefixLift 8015352
  have htrace : WordTrace (prefixWord ++ tailWord_8015352) baseStart_8015352 baseEnd_8015352 := by
    simpa [prefixWord, tailWord_8015352, baseEnd_8015352] using wordTrace_append hprefix tailTrace_8015352
  have hstable : (prefixWord ++ tailWord_8015352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015352).length < 2 ^ (prefixWord ++ tailWord_8015352).sum := by decide
  have hdescent : baseEnd_8015352 < baseStart_8015352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015365 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 3, 6]
def baseStart_8015365 : Nat := 118140960795 + 8015365 * 2 ^ 59
def prefixEnd_8015365 : Nat := 4983230072969 + 3 ^ 40 * 8015365 * 2
def baseEnd_8015365 : Nat := 1371911622075045860425171

theorem tailTrace_8015365 : CollatzResearch.WordTrace tailWord_8015365 prefixEnd_8015365 1371911622075045860425171 := by
  unfold tailWord_8015365
  simp only [CollatzResearch.WordTrace]
  refine ⟨292344378606708995202191549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194896252404472663468127699 292344378606708995202191549)
  ·
    refine ⟨109629141977515873200821831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292344378606708995202191549 109629141977515873200821831)
    ·
      refine ⟨164443712966273809801232747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109629141977515873200821831 164443712966273809801232747)
      ·
        refine ⟨246665569449410714701849121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164443712966273809801232747 246665569449410714701849121)
        ·
          refine ⟨184999177087058036026386841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246665569449410714701849121 184999177087058036026386841)
          ·
            refine ⟨138749382815293527019790131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184999177087058036026386841 138749382815293527019790131)
            ·
              refine ⟨208124074222940290529685197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138749382815293527019790131 208124074222940290529685197)
              ·
                refine ⟨78046527833602608948631949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208124074222940290529685197 78046527833602608948631949)
                ·
                  refine ⟨29267447937600978355736981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78046527833602608948631949 29267447937600978355736981)
                  ·
                    refine ⟨1371911622075045860425171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29267447937600978355736981 1371911622075045860425171)
                    ·
                      rfl

theorem cell23_8015365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_8015365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015365 prefixEnd_8015365 := by exact prefixLift 8015365
  have htrace : WordTrace (prefixWord ++ tailWord_8015365) baseStart_8015365 baseEnd_8015365 := by
    simpa [prefixWord, tailWord_8015365, baseEnd_8015365] using wordTrace_append hprefix tailTrace_8015365
  have hstable : (prefixWord ++ tailWord_8015365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015365).length < 2 ^ (prefixWord ++ tailWord_8015365).sum := by decide
  have hdescent : baseEnd_8015365 < baseStart_8015365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015385 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 2, 6, 4]
def baseStart_8015385 : Nat := 118140960795 + 8015385 * 2 ^ 59
def prefixEnd_8015385 : Nat := 4983230072969 + 3 ^ 40 * 8015385 * 2
def baseEnd_8015385 : Nat := 4115745135838227503025421

theorem tailTrace_8015385 : CollatzResearch.WordTrace tailWord_8015385 prefixEnd_8015385 4115745135838227503025421 := by
  unfold tailWord_8015385
  simp only [CollatzResearch.WordTrace]
  refine ⟨292345108066636538617919609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194896738711091025745279739 292345108066636538617919609)
  ·
    refine ⟨219258831049977403963439707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292345108066636538617919609 219258831049977403963439707)
    ·
      refine ⟨328888246574966105945159561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219258831049977403963439707 328888246574966105945159561)
      ·
        refine ⟨246666184931224579458869671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328888246574966105945159561 246666184931224579458869671)
        ·
          refine ⟨369999277396836869188304507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246666184931224579458869671 369999277396836869188304507)
          ·
            refine ⟨554998916095255303782456761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369999277396836869188304507 554998916095255303782456761)
            ·
              refine ⟨416249187071441477836842571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554998916095255303782456761 416249187071441477836842571)
              ·
                refine ⟨624373780607162216755263857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416249187071441477836842571 624373780607162216755263857)
                ·
                  refine ⟨468280335455371662566447893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 624373780607162216755263857 468280335455371662566447893)
                  ·
                    refine ⟨21950640724470546682802245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 468280335455371662566447893 21950640724470546682802245)
                    ·
                      refine ⟨4115745135838227503025421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21950640724470546682802245 4115745135838227503025421)
                      ·
                        rfl

theorem cell23_8015385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_8015385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015385 prefixEnd_8015385 := by exact prefixLift 8015385
  have htrace : WordTrace (prefixWord ++ tailWord_8015385) baseStart_8015385 baseEnd_8015385 := by
    simpa [prefixWord, tailWord_8015385, baseEnd_8015385] using wordTrace_append hprefix tailTrace_8015385
  have hstable : (prefixWord ++ tailWord_8015385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015385).length < 2 ^ (prefixWord ++ tailWord_8015385).sum := by decide
  have hdescent : baseEnd_8015385 < baseStart_8015385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015402 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_8015402 : Nat := 118140960795 + 8015402 * 2 ^ 59
def prefixEnd_8015402 : Nat := 4983230072969 + 3 ^ 40 * 8015402 * 2
def baseEnd_8015402 : Nat := 4115753865009353936512843

theorem tailTrace_8015402 : CollatzResearch.WordTrace tailWord_8015402 prefixEnd_8015402 4115753865009353936512843 := by
  unfold tailWord_8015402
  simp only [CollatzResearch.WordTrace]
  refine ⟨73086432026893737630322115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194897152071716633680858973 73086432026893737630322115)
  ·
    refine ⟨109629648040340606445483173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73086432026893737630322115 109629648040340606445483173)
    ·
      refine ⟨20555559007563863708528095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109629648040340606445483173 20555559007563863708528095)
      ·
        refine ⟨30833338511345795562792143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20555559007563863708528095 30833338511345795562792143)
        ·
          refine ⟨46250007767018693344188215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30833338511345795562792143 46250007767018693344188215)
          ·
            refine ⟨69375011650528040016282323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46250007767018693344188215 69375011650528040016282323)
            ·
              refine ⟨104062517475792060024423485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69375011650528040016282323 104062517475792060024423485)
              ·
                refine ⟨39023444053422022509158807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104062517475792060024423485 39023444053422022509158807)
                ·
                  refine ⟨58535166080133033763738211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39023444053422022509158807 58535166080133033763738211)
                  ·
                    refine ⟨87802749120199550645607317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58535166080133033763738211 87802749120199550645607317)
                    ·
                      refine ⟨4115753865009353936512843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87802749120199550645607317 4115753865009353936512843)
                      ·
                        rfl

theorem cell23_8015402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_8015402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015402 prefixEnd_8015402 := by exact prefixLift 8015402
  have htrace : WordTrace (prefixWord ++ tailWord_8015402) baseStart_8015402 baseEnd_8015402 := by
    simpa [prefixWord, tailWord_8015402, baseEnd_8015402] using wordTrace_append hprefix tailTrace_8015402
  have hstable : (prefixWord ++ tailWord_8015402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015402).length < 2 ^ (prefixWord ++ tailWord_8015402).sum := by decide
  have hdescent : baseEnd_8015402 < baseStart_8015402 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015406 : List Nat := [4, 1, 3, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_8015406 : Nat := 118140960795 + 8015406 * 2 ^ 59
def prefixEnd_8015406 : Nat := 4983230072969 + 3 ^ 40 * 8015406 * 2
def baseEnd_8015406 : Nat := 4115755918931971920862825

theorem tailTrace_8015406 : CollatzResearch.WordTrace tailWord_8015406 prefixEnd_8015406 4115755918931971920862825 := by
  unfold tailWord_8015406
  simp only [CollatzResearch.WordTrace]
  refine ⟨36543234249945057400554259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194897249333040306136289381 36543234249945057400554259)
  ·
    refine ⟨54814851374917586100831389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36543234249945057400554259 54814851374917586100831389)
    ·
      refine ⟨20555569265594094787811771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54814851374917586100831389 20555569265594094787811771)
      ·
        refine ⟨30833353898391142181717657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20555569265594094787811771 30833353898391142181717657)
        ·
          refine ⟨23125015423793356636288243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30833353898391142181717657 23125015423793356636288243)
          ·
            refine ⟨34687523135690034954432365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23125015423793356636288243 34687523135690034954432365)
            ·
              refine ⟨13007821175883763107912137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34687523135690034954432365 13007821175883763107912137)
              ·
                refine ⟨9755865881912822330934103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13007821175883763107912137 9755865881912822330934103)
                ·
                  refine ⟨14633798822869233496401155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9755865881912822330934103 14633798822869233496401155)
                  ·
                    refine ⟨21950698234303850244601733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14633798822869233496401155 21950698234303850244601733)
                    ·
                      refine ⟨4115755918931971920862825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21950698234303850244601733 4115755918931971920862825)
                      ·
                        rfl

theorem cell23_8015406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_8015406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015406 prefixEnd_8015406 := by exact prefixLift 8015406
  have htrace : WordTrace (prefixWord ++ tailWord_8015406) baseStart_8015406 baseEnd_8015406 := by
    simpa [prefixWord, tailWord_8015406, baseEnd_8015406] using wordTrace_append hprefix tailTrace_8015406
  have hstable : (prefixWord ++ tailWord_8015406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015406).length < 2 ^ (prefixWord ++ tailWord_8015406).sum := by decide
  have hdescent : baseEnd_8015406 < baseStart_8015406 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015442 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 2, 7]
def baseStart_8015442 : Nat := 118140960795 + 8015442 * 2 ^ 59
def prefixEnd_8015442 : Nat := 4983230072969 + 3 ^ 40 * 8015442 * 2
def baseEnd_8015442 : Nat := 1371924801411844593337553

theorem tailTrace_8015442 : CollatzResearch.WordTrace tailWord_8015442 prefixEnd_8015442 1371924801411844593337553 := by
  unfold tailWord_8015442
  simp only [CollatzResearch.WordTrace]
  refine ⟨73086796756857509338186145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194898124684953358235163053 73086796756857509338186145)
  ·
    refine ⟨54815097567643132003639609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73086796756857509338186145 54815097567643132003639609)
    ·
      refine ⟨41111323175732349002729707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54815097567643132003639609 41111323175732349002729707)
      ·
        refine ⟨61666984763598523504094561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41111323175732349002729707 61666984763598523504094561)
        ·
          refine ⟨46250238572698892628070921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61666984763598523504094561 46250238572698892628070921)
          ·
            refine ⟨34687678929524169471053191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46250238572698892628070921 34687678929524169471053191)
            ·
              refine ⟨52031518394286254206579787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34687678929524169471053191 52031518394286254206579787)
              ·
                refine ⟨78047277591429381309869681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52031518394286254206579787 78047277591429381309869681)
                ·
                  refine ⟨58535458193572035982402261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78047277591429381309869681 58535458193572035982402261)
                  ·
                    refine ⟨1371924801411844593337553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58535458193572035982402261 1371924801411844593337553)
                    ·
                      rfl

theorem cell23_8015442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_8015442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015442 prefixEnd_8015442 := by exact prefixLift 8015442
  have htrace : WordTrace (prefixWord ++ tailWord_8015442) baseStart_8015442 baseEnd_8015442 := by
    simpa [prefixWord, tailWord_8015442, baseEnd_8015442] using wordTrace_append hprefix tailTrace_8015442
  have hstable : (prefixWord ++ tailWord_8015442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015442).length < 2 ^ (prefixWord ++ tailWord_8015442).sum := by decide
  have hdescent : baseEnd_8015442 < baseStart_8015442 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015453 : List Nat := [1, 4, 4, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_8015453 : Nat := 118140960795 + 8015453 * 2 ^ 59
def prefixEnd_8015453 : Nat := 4983230072969 + 3 ^ 40 * 8015453 * 2
def baseEnd_8015453 : Nat := 4115780052522733236975109

theorem tailTrace_8015453 : CollatzResearch.WordTrace tailWord_8015453 prefixEnd_8015453 4115780052522733236975109 := by
  unfold tailWord_8015453
  simp only [CollatzResearch.WordTrace]
  refine ⟨292347588230390186231395013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194898392153593457487596675 292347588230390186231395013)
  ·
    refine ⟨54815172793198159918386565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292347588230390186231395013 54815172793198159918386565)
    ·
      refine ⟨10277844898724654984697481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54815172793198159918386565 10277844898724654984697481)
      ·
        refine ⟨7708383674043491238523111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10277844898724654984697481 7708383674043491238523111)
        ·
          refine ⟨11562575511065236857784667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7708383674043491238523111 11562575511065236857784667)
          ·
            refine ⟨17343863266597855286677001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11562575511065236857784667 17343863266597855286677001)
            ·
              refine ⟨13007897449948391465007751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17343863266597855286677001 13007897449948391465007751)
              ·
                refine ⟨19511846174922587197511627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13007897449948391465007751 19511846174922587197511627)
                ·
                  refine ⟨29267769262383880796267441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19511846174922587197511627 29267769262383880796267441)
                  ·
                    refine ⟨21950826946787910597200581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29267769262383880796267441 21950826946787910597200581)
                    ·
                      refine ⟨4115780052522733236975109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21950826946787910597200581 4115780052522733236975109)
                      ·
                        rfl

theorem cell23_8015453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_8015453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015453 prefixEnd_8015453 := by exact prefixLift 8015453
  have htrace : WordTrace (prefixWord ++ tailWord_8015453) baseStart_8015453 baseEnd_8015453 := by
    simpa [prefixWord, tailWord_8015453, baseEnd_8015453] using wordTrace_append hprefix tailTrace_8015453
  have hstable : (prefixWord ++ tailWord_8015453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015453).length < 2 ^ (prefixWord ++ tailWord_8015453).sum := by decide
  have hdescent : baseEnd_8015453 < baseStart_8015453 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015466 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 3, 3, 2]
def baseStart_8015466 : Nat := 118140960795 + 8015466 * 2 ^ 59
def prefixEnd_8015466 : Nat := 4983230072969 + 3 ^ 40 * 8015466 * 2
def baseEnd_8015466 : Nat := 4115786727771241686112549

theorem tailTrace_8015466 : CollatzResearch.WordTrace tailWord_8015466 prefixEnd_8015466 4115786727771241686112549 := by
  unfold tailWord_8015466
  simp only [CollatzResearch.WordTrace]
  refine ⟨73087015594835772362904563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194898708252895392967745501 73087015594835772362904563)
  ·
    refine ⟨109630523392253658544356845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73087015594835772362904563 109630523392253658544356845)
    ·
      refine ⟨41111446272095121954133817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109630523392253658544356845 41111446272095121954133817)
      ·
        refine ⟨30833584704071341465600363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41111446272095121954133817 30833584704071341465600363)
        ·
          refine ⟨46250377056107012198400545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30833584704071341465600363 46250377056107012198400545)
          ·
            refine ⟨34687782792080259148800409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46250377056107012198400545 34687782792080259148800409)
            ·
              refine ⟨26015837094060194361600307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34687782792080259148800409 26015837094060194361600307)
              ·
                refine ⟨39023755641090291542400461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26015837094060194361600307 39023755641090291542400461)
                ·
                  refine ⟨14633908365408859328400173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39023755641090291542400461 14633908365408859328400173)
                  ·
                    refine ⟨5487715637028322248150065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14633908365408859328400173 5487715637028322248150065)
                    ·
                      refine ⟨4115786727771241686112549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5487715637028322248150065 4115786727771241686112549)
                      ·
                        rfl

theorem cell23_8015466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_8015466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015466 prefixEnd_8015466 := by exact prefixLift 8015466
  have htrace : WordTrace (prefixWord ++ tailWord_8015466) baseStart_8015466 baseEnd_8015466 := by
    simpa [prefixWord, tailWord_8015466, baseEnd_8015466] using wordTrace_append hprefix tailTrace_8015466
  have hstable : (prefixWord ++ tailWord_8015466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015466).length < 2 ^ (prefixWord ++ tailWord_8015466).sum := by decide
  have hdescent : baseEnd_8015466 < baseStart_8015466 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015482 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3]
def baseStart_8015482 : Nat := 118140960795 + 8015482 * 2 ^ 59
def prefixEnd_8015482 : Nat := 4983230072969 + 3 ^ 40 * 8015482 * 2
def baseEnd_8015482 : Nat := 4115794943461713623512475

theorem tailTrace_8015482 : CollatzResearch.WordTrace tailWord_8015482 prefixEnd_8015482 4115794943461713623512475 := by
  unfold tailWord_8015482
  simp only [CollatzResearch.WordTrace]
  refine ⟨73087161486821281046050175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194899097298190082789467133 73087161486821281046050175)
  ·
    refine ⟨109630742230231921569075263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73087161486821281046050175 109630742230231921569075263)
    ·
      refine ⟨164446113345347882353612895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109630742230231921569075263 164446113345347882353612895)
      ·
        refine ⟨246669170018021823530419343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164446113345347882353612895 246669170018021823530419343)
        ·
          refine ⟨370003755027032735295629015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246669170018021823530419343 370003755027032735295629015)
          ·
            refine ⟨555005632540549102943443523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370003755027032735295629015 555005632540549102943443523)
            ·
              refine ⟨832508448810823654415165285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555005632540549102943443523 832508448810823654415165285)
              ·
                refine ⟨156095334152029435202843491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 832508448810823654415165285 156095334152029435202843491)
                ·
                  refine ⟨234143001228044152804265237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156095334152029435202843491 234143001228044152804265237)
                  ·
                    refine ⟨10975453182564569662699933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 234143001228044152804265237 10975453182564569662699933)
                    ·
                      refine ⟨4115794943461713623512475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10975453182564569662699933 4115794943461713623512475)
                      ·
                        rfl

theorem cell23_8015482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3].length) (baseStart_8015482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015482 prefixEnd_8015482 := by exact prefixLift 8015482
  have htrace : WordTrace (prefixWord ++ tailWord_8015482) baseStart_8015482 baseEnd_8015482 := by
    simpa [prefixWord, tailWord_8015482, baseEnd_8015482] using wordTrace_append hprefix tailTrace_8015482
  have hstable : (prefixWord ++ tailWord_8015482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015482).length < 2 ^ (prefixWord ++ tailWord_8015482).sum := by decide
  have hdescent : baseEnd_8015482 < baseStart_8015482 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015532 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 8, 5]
def baseStart_8015532 : Nat := 118140960795 + 8015532 * 2 ^ 59
def prefixEnd_8015532 : Nat := 4983230072969 + 3 ^ 40 * 8015532 * 2
def baseEnd_8015532 : Nat := 1371940205831479475962415

theorem tailTrace_8015532 : CollatzResearch.WordTrace tailWord_8015532 prefixEnd_8015532 1371940205831479475962415 := by
  unfold tailWord_8015532
  simp only [CollatzResearch.WordTrace]
  refine ⟨146175234798551991361760425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194900313064735988482347233 146175234798551991361760425)
  ·
    refine ⟨109631426098913993521320319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146175234798551991361760425 109631426098913993521320319)
    ·
      refine ⟨164447139148370990281980479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109631426098913993521320319 164447139148370990281980479)
      ·
        refine ⟨246670708722556485422970719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164447139148370990281980479 246670708722556485422970719)
        ·
          refine ⟨370006063083834728134456079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246670708722556485422970719 370006063083834728134456079)
          ·
            refine ⟨555009094625752092201684119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370006063083834728134456079 555009094625752092201684119)
            ·
              refine ⟨832513641938628138302526179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555009094625752092201684119 832513641938628138302526179)
              ·
                refine ⟨1248770462907942207453789269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 832513641938628138302526179 1248770462907942207453789269)
                ·
                  refine ⟨14634028862202447743599093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1248770462907942207453789269 14634028862202447743599093)
                  ·
                    refine ⟨1371940205831479475962415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14634028862202447743599093 1371940205831479475962415)
                    ·
                      rfl

theorem cell23_8015532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_8015532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015532 prefixEnd_8015532 := by exact prefixLift 8015532
  have htrace : WordTrace (prefixWord ++ tailWord_8015532) baseStart_8015532 baseEnd_8015532 := by
    simpa [prefixWord, tailWord_8015532, baseEnd_8015532] using wordTrace_append hprefix tailTrace_8015532
  have hstable : (prefixWord ++ tailWord_8015532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015532).length < 2 ^ (prefixWord ++ tailWord_8015532).sum := by decide
  have hdescent : baseEnd_8015532 < baseStart_8015532 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015549 : List Nat := [1, 4, 1, 2, 1, 2, 3, 2, 2, 5]
def baseStart_8015549 : Nat := 118140960795 + 8015549 * 2 ^ 59
def prefixEnd_8015549 : Nat := 4983230072969 + 3 ^ 40 * 8015549 * 2
def baseEnd_8015549 : Nat := 1371943115555188287124889

theorem tailTrace_8015549 : CollatzResearch.WordTrace tailWord_8015549 prefixEnd_8015549 1371943115555188287124889 := by
  unfold tailWord_8015549
  simp only [CollatzResearch.WordTrace]
  refine ⟨292351089638042394626889701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194900726425361596417926467 292351089638042394626889701)
  ·
    refine ⟨54815829307132948992541819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292351089638042394626889701 54815829307132948992541819)
    ·
      refine ⟨82223743960699423488812729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54815829307132948992541819 82223743960699423488812729)
      ·
        refine ⟨61667807970524567616609547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82223743960699423488812729 61667807970524567616609547)
        ·
          refine ⟨92501711955786851424914321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61667807970524567616609547 92501711955786851424914321)
          ·
            refine ⟨69376283966840138568685741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92501711955786851424914321 69376283966840138568685741)
            ·
              refine ⟨26016106487565051963257153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69376283966840138568685741 26016106487565051963257153)
              ·
                refine ⟨19512079865673788972442865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26016106487565051963257153 19512079865673788972442865)
                ·
                  refine ⟨14634059899255341729332149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19512079865673788972442865 14634059899255341729332149)
                  ·
                    refine ⟨1371943115555188287124889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14634059899255341729332149 1371943115555188287124889)
                    ·
                      rfl

theorem cell23_8015549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_8015549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015549 prefixEnd_8015549 := by exact prefixLift 8015549
  have htrace : WordTrace (prefixWord ++ tailWord_8015549) baseStart_8015549 baseEnd_8015549 := by
    simpa [prefixWord, tailWord_8015549, baseEnd_8015549] using wordTrace_append hprefix tailTrace_8015549
  have hstable : (prefixWord ++ tailWord_8015549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015549).length < 2 ^ (prefixWord ++ tailWord_8015549).sum := by decide
  have hdescent : baseEnd_8015549 < baseStart_8015549 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015556 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 2, 5, 2]
def baseStart_8015556 : Nat := 118140960795 + 8015556 * 2 ^ 59
def prefixEnd_8015556 : Nat := 4983230072969 + 3 ^ 40 * 8015556 * 2
def baseEnd_8015556 : Nat := 4115832941030146333987135

theorem tailTrace_8015556 : CollatzResearch.WordTrace tailWord_8015556 prefixEnd_8015556 4115832941030146333987135 := by
  unfold tailWord_8015556
  simp only [CollatzResearch.WordTrace]
  refine ⟨146175672474508517411197261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194900896632678023214929681 146175672474508517411197261)
  ·
    refine ⟨54815877177940694029198973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146175672474508517411197261 54815877177940694029198973)
    ·
      refine ⟨20555953941727760260949615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54815877177940694029198973 20555953941727760260949615)
      ·
        refine ⟨30833930912591640391424423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20555953941727760260949615 30833930912591640391424423)
        ·
          refine ⟨46250896368887460587136635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30833930912591640391424423 46250896368887460587136635)
          ·
            refine ⟨69376344553331190880704953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46250896368887460587136635 69376344553331190880704953)
            ·
              refine ⟨52032258414998393160528715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69376344553331190880704953 52032258414998393160528715)
              ·
                refine ⟨78048387622497589740793073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52032258414998393160528715 78048387622497589740793073)
                ·
                  refine ⟨58536290716873192305594805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78048387622497589740793073 58536290716873192305594805)
                  ·
                    refine ⟨5487777254706861778649513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58536290716873192305594805 5487777254706861778649513)
                    ·
                      refine ⟨4115832941030146333987135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5487777254706861778649513 4115832941030146333987135)
                      ·
                        rfl

theorem cell23_8015556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_8015556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015556 prefixEnd_8015556 := by exact prefixLift 8015556
  have htrace : WordTrace (prefixWord ++ tailWord_8015556) baseStart_8015556 baseEnd_8015556 := by
    simpa [prefixWord, tailWord_8015556, baseEnd_8015556] using wordTrace_append hprefix tailTrace_8015556
  have hstable : (prefixWord ++ tailWord_8015556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015556).length < 2 ^ (prefixWord ++ tailWord_8015556).sum := by decide
  have hdescent : baseEnd_8015556 < baseStart_8015556 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015564 : List Nat := [2, 2, 1, 5, 3, 1, 2, 1, 2, 2, 2]
def baseStart_8015564 : Nat := 118140960795 + 8015564 * 2 ^ 59
def prefixEnd_8015564 : Nat := 4983230072969 + 3 ^ 40 * 8015564 * 2
def baseEnd_8015564 : Nat := 4115837048875382302687099

theorem tailTrace_8015564 : CollatzResearch.WordTrace tailWord_8015564 prefixEnd_8015564 4115837048875382302687099 := by
  unfold tailWord_8015564
  simp only [CollatzResearch.WordTrace]
  refine ⟨146175818366494026094342873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194901091155325368125790497 146175818366494026094342873)
  ·
    refine ⟨109631863774870519570757155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146175818366494026094342873 109631863774870519570757155)
    ·
      refine ⟨164447795662305779356135733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109631863774870519570757155 164447795662305779356135733)
      ·
        refine ⟨15416980843341166814637725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164447795662305779356135733 15416980843341166814637725)
        ·
          refine ⟨5781367816252937555489147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15416980843341166814637725 5781367816252937555489147)
          ·
            refine ⟨8672051724379406333233721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5781367816252937555489147 8672051724379406333233721)
            ·
              refine ⟨6504038793284554749925291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8672051724379406333233721 6504038793284554749925291)
              ·
                refine ⟨9756058189926832124887937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6504038793284554749925291 9756058189926832124887937)
                ·
                  refine ⟨7317043642445124093665953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9756058189926832124887937 7317043642445124093665953)
                  ·
                    refine ⟨5487782731833843070249465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7317043642445124093665953 5487782731833843070249465)
                    ·
                      refine ⟨4115837048875382302687099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5487782731833843070249465 4115837048875382302687099)
                      ·
                        rfl

theorem cell23_8015564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_8015564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015564 prefixEnd_8015564 := by exact prefixLift 8015564
  have htrace : WordTrace (prefixWord ++ tailWord_8015564) baseStart_8015564 baseEnd_8015564 := by
    simpa [prefixWord, tailWord_8015564, baseEnd_8015564] using wordTrace_append hprefix tailTrace_8015564
  have hstable : (prefixWord ++ tailWord_8015564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015564).length < 2 ^ (prefixWord ++ tailWord_8015564).sum := by decide
  have hdescent : baseEnd_8015564 < baseStart_8015564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015670 : List Nat := [5, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_8015670 : Nat := 118140960795 + 8015670 * 2 ^ 59
def prefixEnd_8015670 : Nat := 4983230072969 + 3 ^ 40 * 8015670 * 2
def baseEnd_8015670 : Nat := 4115891477824758887961611

theorem tailTrace_8015670 : CollatzResearch.WordTrace tailWord_8015670 prefixEnd_8015670 4115891477824758887961611 := by
  unfold tailWord_8015670
  simp only [CollatzResearch.WordTrace]
  refine ⟨18272218929412752018252779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194903668580402688194696309 18272218929412752018252779)
  ·
    refine ⟨27408328394119128027379169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18272218929412752018252779 27408328394119128027379169)
    ·
      refine ⟨20556246295589346020534377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27408328394119128027379169 20556246295589346020534377)
      ·
        refine ⟨15417184721692009515400783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20556246295589346020534377 15417184721692009515400783)
        ·
          refine ⟨23125777082538014273101175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15417184721692009515400783 23125777082538014273101175)
          ·
            refine ⟨34688665623807021409651763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23125777082538014273101175 34688665623807021409651763)
            ·
              refine ⟨52032998435710532114477645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34688665623807021409651763 52032998435710532114477645)
              ·
                refine ⟨19512374413391449542929117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52032998435710532114477645 19512374413391449542929117)
                ·
                  refine ⟨7317140405021793578598419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19512374413391449542929117 7317140405021793578598419)
                  ·
                    refine ⟨10975710607532690367897629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7317140405021793578598419 10975710607532690367897629)
                    ·
                      refine ⟨4115891477824758887961611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10975710607532690367897629 4115891477824758887961611)
                      ·
                        rfl

theorem cell23_8015670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_8015670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015670 prefixEnd_8015670 := by exact prefixLift 8015670
  have htrace : WordTrace (prefixWord ++ tailWord_8015670) baseStart_8015670 baseEnd_8015670 := by
    simpa [prefixWord, tailWord_8015670, baseEnd_8015670] using wordTrace_append hprefix tailTrace_8015670
  have hstable : (prefixWord ++ tailWord_8015670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015670).length < 2 ^ (prefixWord ++ tailWord_8015670).sum := by decide
  have hdescent : baseEnd_8015670 < baseStart_8015670 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015689 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 1, 1, 6]
def baseStart_8015689 : Nat := 118140960795 + 8015689 * 2 ^ 59
def prefixEnd_8015689 : Nat := 4983230072969 + 3 ^ 40 * 8015689 * 2
def baseEnd_8015689 : Nat := 4115901233957194313624023

theorem tailTrace_8015689 : CollatzResearch.WordTrace tailWord_8015689 prefixEnd_8015689 4115901233957194313624023 := by
  unfold tailWord_8015689
  simp only [CollatzResearch.WordTrace]
  refine ⟨292356195857535198536986121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194904130571690132357990747 292356195857535198536986121)
  ·
    refine ⟨219267146893151398902739591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292356195857535198536986121 219267146893151398902739591)
    ·
      refine ⟨328900720339727098354109387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219267146893151398902739591 328900720339727098354109387)
      ·
        refine ⟨493351080509590647531164081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328900720339727098354109387 493351080509590647531164081)
        ·
          refine ⟨370013310382192985648373061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493351080509590647531164081 370013310382192985648373061)
          ·
            refine ⟨69377495696661184809069949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 370013310382192985648373061 69377495696661184809069949)
            ·
              refine ⟨26016560886247944303401231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69377495696661184809069949 26016560886247944303401231)
              ·
                refine ⟨39024841329371916455101847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26016560886247944303401231 39024841329371916455101847)
                ·
                  refine ⟨58537261994057874682652771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39024841329371916455101847 58537261994057874682652771)
                  ·
                    refine ⟨87805892991086812023979157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58537261994057874682652771 87805892991086812023979157)
                    ·
                      refine ⟨4115901233957194313624023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87805892991086812023979157 4115901233957194313624023)
                      ·
                        rfl

theorem cell23_8015689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 1, 6].length) (baseStart_8015689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015689 prefixEnd_8015689 := by exact prefixLift 8015689
  have htrace : WordTrace (prefixWord ++ tailWord_8015689) baseStart_8015689 baseEnd_8015689 := by
    simpa [prefixWord, tailWord_8015689, baseEnd_8015689] using wordTrace_append hprefix tailTrace_8015689
  have hstable : (prefixWord ++ tailWord_8015689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015689).length < 2 ^ (prefixWord ++ tailWord_8015689).sum := by decide
  have hdescent : baseEnd_8015689 < baseStart_8015689 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015716 : List Nat := [2, 3, 1, 1, 5, 2, 9]
def baseStart_8015716 : Nat := 118140960795 + 8015716 * 2 ^ 59
def prefixEnd_8015716 : Nat := 4983230072969 + 3 ^ 40 * 8015716 * 2
def baseEnd_8015716 : Nat := 50813766641171181580079

theorem tailTrace_8015716 : CollatzResearch.WordTrace tailWord_8015716 prefixEnd_8015716 50813766641171181580079 := by
  unfold tailWord_8015716
  simp only [CollatzResearch.WordTrace]
  refine ⟨146178590314218691074109501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194904787085624921432146001 146178590314218691074109501)
  ·
    refine ⟨54816971367832009152791063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146178590314218691074109501 54816971367832009152791063)
    ·
      refine ⟨82225457051748013729186595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54816971367832009152791063 82225457051748013729186595)
      ·
        refine ⟨123338185577622020593779893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82225457051748013729186595 123338185577622020593779893)
        ·
          refine ⟨11562954897902064430666865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123338185577622020593779893 11562954897902064430666865)
          ·
            refine ⟨8672216173426548323000149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11562954897902064430666865 8672216173426548323000149)
            ·
              refine ⟨50813766641171181580079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8672216173426548323000149 50813766641171181580079)
              ·
                rfl

theorem cell23_8015716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 9].length) (baseStart_8015716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015716 prefixEnd_8015716 := by exact prefixLift 8015716
  have htrace : WordTrace (prefixWord ++ tailWord_8015716) baseStart_8015716 baseEnd_8015716 := by
    simpa [prefixWord, tailWord_8015716, baseEnd_8015716] using wordTrace_append hprefix tailTrace_8015716
  have hstable : (prefixWord ++ tailWord_8015716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015716).length < 2 ^ (prefixWord ++ tailWord_8015716).sum := by decide
  have hdescent : baseEnd_8015716 < baseStart_8015716 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015729 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 2, 7]
def baseStart_8015729 : Nat := 118140960795 + 8015729 * 2 ^ 59
def prefixEnd_8015729 : Nat := 4983230072969 + 3 ^ 40 * 8015729 * 2
def baseEnd_8015729 : Nat := 1371973924394458052374613

theorem tailTrace_8015729 : CollatzResearch.WordTrace tailWord_8015729 prefixEnd_8015729 1371973924394458052374613 := by
  unfold tailWord_8015729
  simp only [CollatzResearch.WordTrace]
  refine ⟨292357654777390285368442241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194905103184926856912294827 292357654777390285368442241)
  ·
    refine ⟨219268241083042714026331681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292357654777390285368442241 219268241083042714026331681)
    ·
      refine ⟨164451180812282035519748761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219268241083042714026331681 164451180812282035519748761)
      ·
        refine ⟨123338385609211526639811571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164451180812282035519748761 123338385609211526639811571)
        ·
          refine ⟨185007578413817289959717357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123338385609211526639811571 185007578413817289959717357)
          ·
            refine ⟨69377841905181483734894009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185007578413817289959717357 69377841905181483734894009)
            ·
              refine ⟨52033381428886112801170507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69377841905181483734894009 52033381428886112801170507)
              ·
                refine ⟨78050072143329169201755761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52033381428886112801170507 78050072143329169201755761)
                ·
                  refine ⟨58537554107496876901316821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78050072143329169201755761 58537554107496876901316821)
                  ·
                    refine ⟨1371973924394458052374613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58537554107496876901316821 1371973924394458052374613)
                    ·
                      rfl

theorem cell23_8015729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_8015729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015729 prefixEnd_8015729 := by exact prefixLift 8015729
  have htrace : WordTrace (prefixWord ++ tailWord_8015729) baseStart_8015729 baseEnd_8015729 := by
    simpa [prefixWord, tailWord_8015729, baseEnd_8015729] using wordTrace_append hprefix tailTrace_8015729
  have hstable : (prefixWord ++ tailWord_8015729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015729).length < 2 ^ (prefixWord ++ tailWord_8015729).sum := by decide
  have hdescent : baseEnd_8015729 < baseStart_8015729 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015753 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 3, 3, 2]
def baseStart_8015753 : Nat := 118140960795 + 8015753 * 2 ^ 59
def prefixEnd_8015753 : Nat := 4983230072969 + 3 ^ 40 * 8015753 * 2
def baseEnd_8015753 : Nat := 4115934096719082063223729

theorem tailTrace_8015753 : CollatzResearch.WordTrace tailWord_8015753 prefixEnd_8015753 4115934096719082063223729 := by
  unfold tailWord_8015753
  simp only [CollatzResearch.WordTrace]
  refine ⟨292358530129303337467315913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194905686752868891644877275 292358530129303337467315913)
  ·
    refine ⟨219268897596977503100486935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292358530129303337467315913 219268897596977503100486935)
    ·
      refine ⟨328903346395466254650730403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219268897596977503100486935 328903346395466254650730403)
      ·
        refine ⟨493355019593199381976095605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328903346395466254650730403 493355019593199381976095605)
        ·
          refine ⟨46252033086862442060258963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 493355019593199381976095605 46252033086862442060258963)
          ·
            refine ⟨69378049630293663090388445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46252033086862442060258963 69378049630293663090388445)
            ·
              refine ⟨26016768611360123658895667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69378049630293663090388445 26016768611360123658895667)
              ·
                refine ⟨39025152917040185488343501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26016768611360123658895667 39025152917040185488343501)
                ·
                  refine ⟨14634432343890069558128813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39025152917040185488343501 14634432343890069558128813)
                  ·
                    refine ⟨5487912128958776084298305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14634432343890069558128813 5487912128958776084298305)
                    ·
                      refine ⟨4115934096719082063223729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5487912128958776084298305 4115934096719082063223729)
                      ·
                        rfl

theorem cell23_8015753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 3, 2].length) (baseStart_8015753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015753 prefixEnd_8015753 := by exact prefixLift 8015753
  have htrace : WordTrace (prefixWord ++ tailWord_8015753) baseStart_8015753 baseEnd_8015753 := by
    simpa [prefixWord, tailWord_8015753, baseEnd_8015753] using wordTrace_append hprefix tailTrace_8015753
  have hstable : (prefixWord ++ tailWord_8015753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015753).length < 2 ^ (prefixWord ++ tailWord_8015753).sum := by decide
  have hdescent : baseEnd_8015753 < baseStart_8015753 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015777 : List Nat := [1, 2, 3, 4, 2, 1, 2, 2, 2, 1, 3]
def baseStart_8015777 : Nat := 118140960795 + 8015777 * 2 ^ 59
def prefixEnd_8015777 : Nat := 4983230072969 + 3 ^ 40 * 8015777 * 2
def baseEnd_8015777 : Nat := 4115946420254789969323619

theorem tailTrace_8015777 : CollatzResearch.WordTrace tailWord_8015777 prefixEnd_8015777 4115946420254789969323619 := by
  unfold tailWord_8015777
  simp only [CollatzResearch.WordTrace]
  refine ⟨292359405481216389566189585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194906270320810926377459723 292359405481216389566189585)
  ·
    refine ⟨219269554110912292174642189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292359405481216389566189585 219269554110912292174642189)
    ·
      refine ⟨82226082791592109565490821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219269554110912292174642189 82226082791592109565490821)
      ·
        refine ⟨15417390523423520543529529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82226082791592109565490821 15417390523423520543529529)
        ·
          refine ⟨11563042892567640407647147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15417390523423520543529529 11563042892567640407647147)
          ·
            refine ⟨17344564338851460611470721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11563042892567640407647147 17344564338851460611470721)
            ·
              refine ⟨13008423254138595458603041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17344564338851460611470721 13008423254138595458603041)
              ·
                refine ⟨9756317440603946593952281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13008423254138595458603041 9756317440603946593952281)
                ·
                  refine ⟨7317238080452959945464211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9756317440603946593952281 7317238080452959945464211)
                  ·
                    refine ⟨10975857120679439918196317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7317238080452959945464211 10975857120679439918196317)
                    ·
                      refine ⟨4115946420254789969323619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10975857120679439918196317 4115946420254789969323619)
                      ·
                        rfl

theorem cell23_8015777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_8015777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015777 prefixEnd_8015777 := by exact prefixLift 8015777
  have htrace : WordTrace (prefixWord ++ tailWord_8015777) baseStart_8015777 baseEnd_8015777 := by
    simpa [prefixWord, tailWord_8015777, baseEnd_8015777] using wordTrace_append hprefix tailTrace_8015777
  have hstable : (prefixWord ++ tailWord_8015777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015777).length < 2 ^ (prefixWord ++ tailWord_8015777).sum := by decide
  have hdescent : baseEnd_8015777 < baseStart_8015777 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015778 : List Nat := [3, 3, 1, 2, 4, 1, 2, 2, 1, 2, 2]
def baseStart_8015778 : Nat := 118140960795 + 8015778 * 2 ^ 59
def prefixEnd_8015778 : Nat := 4983230072969 + 3 ^ 40 * 8015778 * 2
def baseEnd_8015778 : Nat := 4115946933735444465411115

theorem tailTrace_8015778 : CollatzResearch.WordTrace tailWord_8015778 prefixEnd_8015778 4115946933735444465411115 := by
  unfold tailWord_8015778
  simp only [CollatzResearch.WordTrace]
  refine ⟨73089860488553191684243997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194906294636141844491317325 73089860488553191684243997)
  ·
    refine ⟨27408697683207446881591499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73089860488553191684243997 27408697683207446881591499)
    ·
      refine ⟨41113046524811170322387249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27408697683207446881591499 41113046524811170322387249)
      ·
        refine ⟨30834784893608377741790437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41113046524811170322387249 30834784893608377741790437)
        ·
          refine ⟨5781522167551570826585707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30834784893608377741790437 5781522167551570826585707)
          ·
            refine ⟨8672283251327356239878561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5781522167551570826585707 8672283251327356239878561)
            ·
              refine ⟨6504212438495517179908921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8672283251327356239878561 6504212438495517179908921)
              ·
                refine ⟨4878159328871637884931691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6504212438495517179908921 4878159328871637884931691)
                ·
                  refine ⟨7317238993307456827397537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4878159328871637884931691 7317238993307456827397537)
                  ·
                    refine ⟨5487929244980592620548153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7317238993307456827397537 5487929244980592620548153)
                    ·
                      refine ⟨4115946933735444465411115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5487929244980592620548153 4115946933735444465411115)
                      ·
                        rfl

theorem cell23_8015778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_8015778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015778 prefixEnd_8015778 := by exact prefixLift 8015778
  have htrace : WordTrace (prefixWord ++ tailWord_8015778) baseStart_8015778 baseEnd_8015778 := by
    simpa [prefixWord, tailWord_8015778, baseEnd_8015778] using wordTrace_append hprefix tailTrace_8015778
  have hstable : (prefixWord ++ tailWord_8015778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015778).length < 2 ^ (prefixWord ++ tailWord_8015778).sum := by decide
  have hdescent : baseEnd_8015778 < baseStart_8015778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015779 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 6]
def baseStart_8015779 : Nat := 118140960795 + 8015779 * 2 ^ 59
def prefixEnd_8015779 : Nat := 4983230072969 + 3 ^ 40 * 8015779 * 2
def baseEnd_8015779 : Nat := 4115947447216098961498609

theorem tailTrace_8015779 : CollatzResearch.WordTrace tailWord_8015779 prefixEnd_8015779 4115947447216098961498609 := by
  unfold tailWord_8015779
  simp only [CollatzResearch.WordTrace]
  refine ⟨292359478427209143907762391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194906318951472762605174927 292359478427209143907762391)
  ·
    refine ⟨438539217640813715861643587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292359478427209143907762391 438539217640813715861643587)
    ·
      refine ⟨657808826461220573792465381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438539217640813715861643587 657808826461220573792465381)
      ·
        refine ⟨123339154961478857586087259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 657808826461220573792465381 123339154961478857586087259)
        ·
          refine ⟨185008732442218286379130889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123339154961478857586087259 185008732442218286379130889)
          ·
            refine ⟨138756549331663714784348167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185008732442218286379130889 138756549331663714784348167)
            ·
              refine ⟨208134823997495572176522251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138756549331663714784348167 208134823997495572176522251)
              ·
                refine ⟨312202235996243358264783377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208134823997495572176522251 312202235996243358264783377)
                ·
                  refine ⟨234151676997182518698587533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312202235996243358264783377 234151676997182518698587533)
                  ·
                    refine ⟨87806878873943444511970325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 234151676997182518698587533 87806878873943444511970325)
                    ·
                      refine ⟨4115947447216098961498609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87806878873943444511970325 4115947447216098961498609)
                      ·
                        rfl

theorem cell23_8015779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_8015779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015779 prefixEnd_8015779 := by exact prefixLift 8015779
  have htrace : WordTrace (prefixWord ++ tailWord_8015779) baseStart_8015779 baseEnd_8015779 := by
    simpa [prefixWord, tailWord_8015779, baseEnd_8015779] using wordTrace_append hprefix tailTrace_8015779
  have hstable : (prefixWord ++ tailWord_8015779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015779).length < 2 ^ (prefixWord ++ tailWord_8015779).sum := by decide
  have hdescent : baseEnd_8015779 < baseStart_8015779 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015800 : List Nat := [2, 1, 2, 1, 2, 3, 1, 5, 2, 2, 2]
def baseStart_8015800 : Nat := 118140960795 + 8015800 * 2 ^ 59
def prefixEnd_8015800 : Nat := 4983230072969 + 3 ^ 40 * 8015800 * 2
def baseEnd_8015800 : Nat := 4115958230309843379336013

theorem tailTrace_8015800 : CollatzResearch.WordTrace tailWord_8015800 prefixEnd_8015800 4115958230309843379336013 := by
  unfold tailWord_8015800
  simp only [CollatzResearch.WordTrace]
  refine ⟨146180122180066532247138427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194906829573422042996184569 146180122180066532247138427)
  ·
    refine ⟨219270183270099798370707641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146180122180066532247138427 219270183270099798370707641)
    ·
      refine ⟨164452637452574848778030731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219270183270099798370707641 164452637452574848778030731)
      ·
        refine ⟨246678956178862273167046097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164452637452574848778030731 246678956178862273167046097)
        ·
          refine ⟨185009217134146704875284573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246678956178862273167046097 185009217134146704875284573)
          ·
            refine ⟨69378456425305014328231715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185009217134146704875284573 69378456425305014328231715)
            ·
              refine ⟨104067684637957521492347573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69378456425305014328231715 104067684637957521492347573)
              ·
                refine ⟨9756345434808517639907585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104067684637957521492347573 9756345434808517639907585)
                ·
                  refine ⟨7317259076106388229930689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9756345434808517639907585 7317259076106388229930689)
                  ·
                    refine ⟨5487944307079791172448017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7317259076106388229930689 5487944307079791172448017)
                    ·
                      refine ⟨4115958230309843379336013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5487944307079791172448017 4115958230309843379336013)
                      ·
                        rfl

theorem cell23_8015800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 2, 2, 2].length) (baseStart_8015800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015800 prefixEnd_8015800 := by exact prefixLift 8015800
  have htrace : WordTrace (prefixWord ++ tailWord_8015800) baseStart_8015800 baseEnd_8015800 := by
    simpa [prefixWord, tailWord_8015800, baseEnd_8015800] using wordTrace_append hprefix tailTrace_8015800
  have hstable : (prefixWord ++ tailWord_8015800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015800).length < 2 ^ (prefixWord ++ tailWord_8015800).sum := by decide
  have hdescent : baseEnd_8015800 < baseStart_8015800 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015806 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 9]
def baseStart_8015806 : Nat := 118140960795 + 8015806 * 2 ^ 59
def prefixEnd_8015806 : Nat := 4983230072969 + 3 ^ 40 * 8015806 * 2
def baseEnd_8015806 : Nat := 457329034577085595095665

theorem tailTrace_8015806 : CollatzResearch.WordTrace tailWord_8015806 prefixEnd_8015806 457329034577085595095665 := by
  unfold tailWord_8015806
  simp only [CollatzResearch.WordTrace]
  refine ⟨36545057899763915939874409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194906975465407551679330181 36545057899763915939874409)
  ·
    refine ⟨27408793424822936954905807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36545057899763915939874409 27408793424822936954905807)
    ·
      refine ⟨41113190137234405432358711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27408793424822936954905807 41113190137234405432358711)
      ·
        refine ⟨61669785205851608148538067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41113190137234405432358711 61669785205851608148538067)
        ·
          refine ⟨92504677808777412222807101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61669785205851608148538067 92504677808777412222807101)
          ·
            refine ⟨34689254178291529583552663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92504677808777412222807101 34689254178291529583552663)
            ·
              refine ⟨52033881267437294375328995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34689254178291529583552663 52033881267437294375328995)
              ·
                refine ⟨78050821901155941562993493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52033881267437294375328995 78050821901155941562993493)
                ·
                  refine ⟨457329034577085595095665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78050821901155941562993493 457329034577085595095665)
                  ·
                    rfl

theorem cell23_8015806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_8015806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015806 prefixEnd_8015806 := by exact prefixLift 8015806
  have htrace : WordTrace (prefixWord ++ tailWord_8015806) baseStart_8015806 baseEnd_8015806 := by
    simpa [prefixWord, tailWord_8015806, baseEnd_8015806] using wordTrace_append hprefix tailTrace_8015806
  have hstable : (prefixWord ++ tailWord_8015806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015806).length < 2 ^ (prefixWord ++ tailWord_8015806).sum := by decide
  have hdescent : baseEnd_8015806 < baseStart_8015806 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015823 : List Nat := [1, 1, 2, 1, 1, 5, 4, 3, 5]
def baseStart_8015823 : Nat := 118140960795 + 8015823 * 2 ^ 59
def prefixEnd_8015823 : Nat := 4983230072969 + 3 ^ 40 * 8015823 * 2
def baseEnd_8015823 : Nat := 457330004484988532149823

theorem tailTrace_8015823 : CollatzResearch.WordTrace tailWord_8015823 prefixEnd_8015823 457330004484988532149823 := by
  unfold tailWord_8015823
  simp only [CollatzResearch.WordTrace]
  refine ⟨292361083239049739422364123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194907388826033159614909415 292361083239049739422364123)
  ·
    refine ⟨438541624858574609133546185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292361083239049739422364123 438541624858574609133546185)
    ·
      refine ⟨328906218643930956850159639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438541624858574609133546185 328906218643930956850159639)
      ·
        refine ⟨493359327965896435275239459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328906218643930956850159639 493359327965896435275239459)
        ·
          refine ⟨740038991948844652912859189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493359327965896435275239459 740038991948844652912859189)
          ·
            refine ⟨69378655495204186210580549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 740038991948844652912859189 69378655495204186210580549)
            ·
              refine ⟨13008497905350784914483853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69378655495204186210580549 13008497905350784914483853)
              ·
                refine ⟨4878186714506544342931445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13008497905350784914483853 4878186714506544342931445)
                ·
                  refine ⟨457330004484988532149823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4878186714506544342931445 457330004484988532149823)
                  ·
                    rfl

theorem cell23_8015823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 5].length) (baseStart_8015823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015823 prefixEnd_8015823 := by exact prefixLift 8015823
  have htrace : WordTrace (prefixWord ++ tailWord_8015823) baseStart_8015823 baseEnd_8015823 := by
    simpa [prefixWord, tailWord_8015823, baseEnd_8015823] using wordTrace_append hprefix tailTrace_8015823
  have hstable : (prefixWord ++ tailWord_8015823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015823).length < 2 ^ (prefixWord ++ tailWord_8015823).sum := by decide
  have hdescent : baseEnd_8015823 < baseStart_8015823 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015834 : List Nat := [3, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2]
def baseStart_8015834 : Nat := 118140960795 + 8015834 * 2 ^ 59
def prefixEnd_8015834 : Nat := 4983230072969 + 3 ^ 40 * 8015834 * 2
def baseEnd_8015834 : Nat := 4115975688652096246310857

theorem tailTrace_8015834 : CollatzResearch.WordTrace tailWord_8015834 prefixEnd_8015834 4115975688652096246310857 := by
  unfold tailWord_8015834
  simp only [CollatzResearch.WordTrace]
  refine ⟨73090371110502472075253639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194907656294673258867343037 73090371110502472075253639)
  ·
    refine ⟨109635556665753708112880459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73090371110502472075253639 109635556665753708112880459)
    ·
      refine ⟨164453334998630562169320689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109635556665753708112880459 164453334998630562169320689)
      ·
        refine ⟨123340001248972921626990517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164453334998630562169320689 123340001248972921626990517)
        ·
          refine ⟨11563125117091211402530361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123340001248972921626990517 11563125117091211402530361)
          ·
            refine ⟨8672343837818408551897771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11563125117091211402530361 8672343837818408551897771)
            ·
              refine ⟨13008515756727612827846657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8672343837818408551897771 13008515756727612827846657)
              ·
                refine ⟨9756386817545709620884993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13008515756727612827846657 9756386817545709620884993)
                ·
                  refine ⟨7317290113159282215663745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9756386817545709620884993 7317290113159282215663745)
                  ·
                    refine ⟨5487967584869461661747809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7317290113159282215663745 5487967584869461661747809)
                    ·
                      refine ⟨4115975688652096246310857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5487967584869461661747809 4115975688652096246310857)
                      ·
                        rfl

theorem cell23_8015834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_8015834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015834 prefixEnd_8015834 := by exact prefixLift 8015834
  have htrace : WordTrace (prefixWord ++ tailWord_8015834) baseStart_8015834 baseEnd_8015834 := by
    simpa [prefixWord, tailWord_8015834, baseEnd_8015834] using wordTrace_append hprefix tailTrace_8015834
  have hstable : (prefixWord ++ tailWord_8015834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015834).length < 2 ^ (prefixWord ++ tailWord_8015834).sum := by decide
  have hdescent : baseEnd_8015834 < baseStart_8015834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015856 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 4]
def baseStart_8015856 : Nat := 118140960795 + 8015856 * 2 ^ 59
def prefixEnd_8015856 : Nat := 4983230072969 + 3 ^ 40 * 8015856 * 2
def baseEnd_8015856 : Nat := 4115986985226495160235755

theorem tailTrace_8015856 : CollatzResearch.WordTrace tailWord_8015856 prefixEnd_8015856 4115986985226495160235755 := by
  unfold tailWord_8015856
  simp only [CollatzResearch.WordTrace]
  refine ⟨146181143423965093029157711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194908191231953457372210281 146181143423965093029157711)
  ·
    refine ⟨219271715135947639543736567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146181143423965093029157711 219271715135947639543736567)
    ·
      refine ⟨328907572703921459315604851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219271715135947639543736567 328907572703921459315604851)
      ·
        refine ⟨493361359055882188973407277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328907572703921459315604851 493361359055882188973407277)
        ·
          refine ⟨185010509645955820865027729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 493361359055882188973407277 185010509645955820865027729)
          ·
            refine ⟨138757882234466865648770797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185010509645955820865027729 138757882234466865648770797)
            ·
              refine ⟨52034205837925074618289049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138757882234466865648770797 52034205837925074618289049)
              ·
                refine ⟨39025654378443805963716787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52034205837925074618289049 39025654378443805963716787)
                ·
                  refine ⟨58538481567665708945575181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39025654378443805963716787 58538481567665708945575181)
                  ·
                    refine ⟨21951930587874640854590693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58538481567665708945575181 21951930587874640854590693)
                    ·
                      refine ⟨4115986985226495160235755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21951930587874640854590693 4115986985226495160235755)
                      ·
                        rfl

theorem cell23_8015856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 4].length) (baseStart_8015856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015856 prefixEnd_8015856 := by exact prefixLift 8015856
  have htrace : WordTrace (prefixWord ++ tailWord_8015856) baseStart_8015856 baseEnd_8015856 := by
    simpa [prefixWord, tailWord_8015856, baseEnd_8015856] using wordTrace_append hprefix tailTrace_8015856
  have hstable : (prefixWord ++ tailWord_8015856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015856).length < 2 ^ (prefixWord ++ tailWord_8015856).sum := by decide
  have hdescent : baseEnd_8015856 < baseStart_8015856 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015873 : List Nat := [1, 2, 4, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_8015873 : Nat := 118140960795 + 8015873 * 2 ^ 59
def prefixEnd_8015873 : Nat := 4983230072969 + 3 ^ 40 * 8015873 * 2
def baseEnd_8015873 : Nat := 4115995714397621593723177

theorem tailTrace_8015873 : CollatzResearch.WordTrace tailWord_8015873 prefixEnd_8015873 4115995714397621593723177 := by
  unfold tailWord_8015873
  simp only [CollatzResearch.WordTrace]
  refine ⟨292362906888868597961684273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194908604592579065307789515 292362906888868597961684273)
  ·
    refine ⟨219272180166651448471263205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292362906888868597961684273 219272180166651448471263205)
    ·
      refine ⟨41113533781247146588361851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219272180166651448471263205 41113533781247146588361851)
      ·
        refine ⟨61670300671870719882542777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41113533781247146588361851 61670300671870719882542777)
        ·
          refine ⟨46252725503903039911907083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61670300671870719882542777 46252725503903039911907083)
          ·
            refine ⟨69379088255854559867860625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46252725503903039911907083 69379088255854559867860625)
            ·
              refine ⟨52034316191890919900895469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69379088255854559867860625 52034316191890919900895469)
              ·
                refine ⟨19512868571959094962835801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52034316191890919900895469 19512868571959094962835801)
                ·
                  refine ⟨14634651428969321222126851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19512868571959094962835801 14634651428969321222126851)
                  ·
                    refine ⟨21951977143453981833190277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14634651428969321222126851 21951977143453981833190277)
                    ·
                      refine ⟨4115995714397621593723177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21951977143453981833190277 4115995714397621593723177)
                      ·
                        rfl

theorem cell23_8015873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_8015873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015873 prefixEnd_8015873 := by exact prefixLift 8015873
  have htrace : WordTrace (prefixWord ++ tailWord_8015873) baseStart_8015873 baseEnd_8015873 := by
    simpa [prefixWord, tailWord_8015873, baseEnd_8015873] using wordTrace_append hprefix tailTrace_8015873
  have hstable : (prefixWord ++ tailWord_8015873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015873).length < 2 ^ (prefixWord ++ tailWord_8015873).sum := by decide
  have hdescent : baseEnd_8015873 < baseStart_8015873 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015896 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 8]
def baseStart_8015896 : Nat := 118140960795 + 8015896 * 2 ^ 59
def prefixEnd_8015896 : Nat := 4983230072969 + 3 ^ 40 * 8015896 * 2
def baseEnd_8015896 : Nat := 457334169383630555970619

theorem tailTrace_8015896 : CollatzResearch.WordTrace tailWord_8015896 prefixEnd_8015896 457334169383630555970619 := by
  unfold tailWord_8015896
  simp only [CollatzResearch.WordTrace]
  refine ⟨146181872883892636444885771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194909163845190181926514361 146181872883892636444885771)
  ·
    refine ⟨219272809325838954667328657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146181872883892636444885771 219272809325838954667328657)
    ·
      refine ⟨164454606994379216000496493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219272809325838954667328657 164454606994379216000496493)
      ·
        refine ⟨61670477622892206000186185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164454606994379216000496493 61670477622892206000186185)
        ·
          refine ⟨46252858217169154500139639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61670477622892206000186185 46252858217169154500139639)
          ·
            refine ⟨69379287325753731750209459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46252858217169154500139639 69379287325753731750209459)
            ·
              refine ⟨104068930988630597625314189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69379287325753731750209459 104068930988630597625314189)
              ·
                refine ⟨39025849120736474109492821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104068930988630597625314189 39025849120736474109492821)
                ·
                  refine ⟨457334169383630555970619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39025849120736474109492821 457334169383630555970619)
                  ·
                    rfl

theorem cell23_8015896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 8].length) (baseStart_8015896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015896 prefixEnd_8015896 := by exact prefixLift 8015896
  have htrace : WordTrace (prefixWord ++ tailWord_8015896) baseStart_8015896 baseEnd_8015896 := by
    simpa [prefixWord, tailWord_8015896, baseEnd_8015896] using wordTrace_append hprefix tailTrace_8015896
  have hstable : (prefixWord ++ tailWord_8015896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015896).length < 2 ^ (prefixWord ++ tailWord_8015896).sum := by decide
  have hdescent : baseEnd_8015896 < baseStart_8015896 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015900 : List Nat := [2, 2, 3, 1, 3, 1, 3, 1, 3, 4]
def baseStart_8015900 : Nat := 118140960795 + 8015900 * 2 ^ 59
def prefixEnd_8015900 : Nat := 4983230072969 + 3 ^ 40 * 8015900 * 2
def baseEnd_8015900 : Nat := 1372003192791764329361851

theorem tailTrace_8015900 : CollatzResearch.WordTrace tailWord_8015900 prefixEnd_8015900 1372003192791764329361851 := by
  unfold tailWord_8015900
  simp only [CollatzResearch.WordTrace]
  refine ⟨146181945829885390786458577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194909261106513854381944769 146181945829885390786458577)
  ·
    refine ⟨109636459372414043089843933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146181945829885390786458577 109636459372414043089843933)
    ·
      refine ⟨41113672264655266158691475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109636459372414043089843933 41113672264655266158691475)
      ·
        refine ⟨61670508396982899238037213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41113672264655266158691475 61670508396982899238037213)
        ·
          refine ⟨23126440648868587214263955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61670508396982899238037213 23126440648868587214263955)
          ·
            refine ⟨34689660973302880821395933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23126440648868587214263955 34689660973302880821395933)
            ·
              refine ⟨13008622864988580308023475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34689660973302880821395933 13008622864988580308023475)
              ·
                refine ⟨19512934297482870462035213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13008622864988580308023475 19512934297482870462035213)
                ·
                  refine ⟨7317350361556076423263205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19512934297482870462035213 7317350361556076423263205)
                  ·
                    refine ⟨1372003192791764329361851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7317350361556076423263205 1372003192791764329361851)
                    ·
                      rfl

theorem cell23_8015900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_8015900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015900 prefixEnd_8015900 := by exact prefixLift 8015900
  have htrace : WordTrace (prefixWord ++ tailWord_8015900) baseStart_8015900 baseEnd_8015900 := by
    simpa [prefixWord, tailWord_8015900, baseEnd_8015900] using wordTrace_append hprefix tailTrace_8015900
  have hstable : (prefixWord ++ tailWord_8015900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015900).length < 2 ^ (prefixWord ++ tailWord_8015900).sum := by decide
  have hdescent : baseEnd_8015900 < baseStart_8015900 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015973 : List Nat := [1, 3, 1, 3, 2, 2, 1, 3, 1, 6]
def baseStart_8015973 : Nat := 118140960795 + 8015973 * 2 ^ 59
def prefixEnd_8015973 : Nat := 4983230072969 + 3 ^ 40 * 8015973 * 2
def baseEnd_8015973 : Nat := 1372015687487690400824239

theorem tailTrace_8015973 : CollatzResearch.WordTrace tailWord_8015973 prefixEnd_8015973 1372015687487690400824239 := by
  unfold tailWord_8015973
  simp only [CollatzResearch.WordTrace]
  refine ⟨292366554188506315040324573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194911036125670876693549715 292366554188506315040324573)
  ·
    refine ⟨109637457820689868140121715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292366554188506315040324573 109637457820689868140121715)
    ·
      refine ⟨164456186731034802210182573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109637457820689868140121715 164456186731034802210182573)
      ·
        refine ⟨61671070024138050828818465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164456186731034802210182573 61671070024138050828818465)
        ·
          refine ⟨46253302518103538121613849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61671070024138050828818465 46253302518103538121613849)
          ·
            refine ⟨34689976888577653591210387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46253302518103538121613849 34689976888577653591210387)
            ·
              refine ⟨52034965332866480386815581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34689976888577653591210387 52034965332866480386815581)
              ·
                refine ⟨19513111999824930145055843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52034965332866480386815581 19513111999824930145055843)
                ·
                  refine ⟨29269667999737395217583765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19513111999824930145055843 29269667999737395217583765)
                  ·
                    refine ⟨1372015687487690400824239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29269667999737395217583765 1372015687487690400824239)
                    ·
                      rfl

theorem cell23_8015973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_8015973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015973 prefixEnd_8015973 := by exact prefixLift 8015973
  have htrace : WordTrace (prefixWord ++ tailWord_8015973) baseStart_8015973 baseEnd_8015973 := by
    simpa [prefixWord, tailWord_8015973, baseEnd_8015973] using wordTrace_append hprefix tailTrace_8015973
  have hstable : (prefixWord ++ tailWord_8015973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015973).length < 2 ^ (prefixWord ++ tailWord_8015973).sum := by decide
  have hdescent : baseEnd_8015973 < baseStart_8015973 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015990 : List Nat := [5, 1, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_8015990 : Nat := 118140960795 + 8015990 * 2 ^ 59
def prefixEnd_8015990 : Nat := 4983230072969 + 3 ^ 40 * 8015990 * 2
def baseEnd_8015990 : Nat := 1372018597211399211986713

theorem tailTrace_8015990 : CollatzResearch.WordTrace tailWord_8015990 prefixEnd_8015990 1372018597211399211986713 := by
  unfold tailWord_8015990
  simp only [CollatzResearch.WordTrace]
  refine ⟨18272948389340295433980839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194911449486296484629128949 18272948389340295433980839)
  ·
    refine ⟨27409422584010443150971259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18272948389340295433980839 27409422584010443150971259)
    ·
      refine ⟨41114133876015664726456889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27409422584010443150971259 41114133876015664726456889)
      ·
        refine ⟨30835600407011748544842667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41114133876015664726456889 30835600407011748544842667)
        ·
          refine ⟨46253400610517622817264001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30835600407011748544842667 46253400610517622817264001)
          ·
            refine ⟨34690050457888217112948001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46253400610517622817264001 34690050457888217112948001)
            ·
              refine ⟨26017537843416162834711001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34690050457888217112948001 26017537843416162834711001)
              ·
                refine ⟨19513153382562122126033251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26017537843416162834711001 19513153382562122126033251)
                ·
                  refine ⟨29269730073843183189049877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19513153382562122126033251 29269730073843183189049877)
                  ·
                    refine ⟨1372018597211399211986713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29269730073843183189049877 1372018597211399211986713)
                    ·
                      rfl

theorem cell23_8015990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_8015990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015990 prefixEnd_8015990 := by exact prefixLift 8015990
  have htrace : WordTrace (prefixWord ++ tailWord_8015990) baseStart_8015990 baseEnd_8015990 := by
    simpa [prefixWord, tailWord_8015990, baseEnd_8015990] using wordTrace_append hprefix tailTrace_8015990
  have hstable : (prefixWord ++ tailWord_8015990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015990).length < 2 ^ (prefixWord ++ tailWord_8015990).sum := by decide
  have hdescent : baseEnd_8015990 < baseStart_8015990 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8015997 : List Nat := [1, 4, 1, 1, 3, 2, 4, 1, 1, 1, 4]
def baseStart_8015997 : Nat := 118140960795 + 8015997 * 2 ^ 59
def prefixEnd_8015997 : Nat := 4983230072969 + 3 ^ 40 * 8015997 * 2
def baseEnd_8015997 : Nat := 4116059385998779108572607

theorem tailTrace_8015997 : CollatzResearch.WordTrace tailWord_8015997 prefixEnd_8015997 4116059385998779108572607 := by
  unfold tailWord_8015997
  simp only [CollatzResearch.WordTrace]
  refine ⟨292367429540419367139198245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194911619693612911426132163 292367429540419367139198245)
  ·
    refine ⟨54818893038828631338599671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292367429540419367139198245 54818893038828631338599671)
    ·
      refine ⟨82228339558242947007899507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54818893038828631338599671 82228339558242947007899507)
      ·
        refine ⟨123342509337364420511849261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82228339558242947007899507 123342509337364420511849261)
        ·
          refine ⟨46253441001511657691943473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123342509337364420511849261 46253441001511657691943473)
          ·
            refine ⟨34690080751133743268957605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46253441001511657691943473 34690080751133743268957605)
            ·
              refine ⟨6504390140837576862929551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34690080751133743268957605 6504390140837576862929551)
              ·
                refine ⟨9756585211256365294394327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6504390140837576862929551 9756585211256365294394327)
                ·
                  refine ⟨14634877816884547941591491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9756585211256365294394327 14634877816884547941591491)
                  ·
                    refine ⟨21952316725326821912387237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14634877816884547941591491 21952316725326821912387237)
                    ·
                      refine ⟨4116059385998779108572607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21952316725326821912387237 4116059385998779108572607)
                      ·
                        rfl

theorem cell23_8015997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_8015997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8015997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8015997 prefixEnd_8015997 := by exact prefixLift 8015997
  have htrace : WordTrace (prefixWord ++ tailWord_8015997) baseStart_8015997 baseEnd_8015997 := by
    simpa [prefixWord, tailWord_8015997, baseEnd_8015997] using wordTrace_append hprefix tailTrace_8015997
  have hstable : (prefixWord ++ tailWord_8015997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8015997).length < 2 ^ (prefixWord ++ tailWord_8015997).sum := by decide
  have hdescent : baseEnd_8015997 < baseStart_8015997 := by decide
  rcases family_descends (prefixWord ++ tailWord_8015997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016024 : List Nat := [2, 1, 2, 4, 3, 1, 3, 1, 2, 4]
def baseStart_8016024 : Nat := 118140960795 + 8016024 * 2 ^ 59
def prefixEnd_8016024 : Nat := 4983230072969 + 3 ^ 40 * 8016024 * 2
def baseEnd_8016024 : Nat := 1372024416658816834311661

theorem tailTrace_8016024 : CollatzResearch.WordTrace tailWord_8016024 prefixEnd_8016024 1372024416658816834311661 := by
  unfold tailWord_8016024
  simp only [CollatzResearch.WordTrace]
  refine ⟨146184207155660775375215563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194912276207547700500287417 146184207155660775375215563)
  ·
    refine ⟨219276310733491163062823345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146184207155660775375215563 219276310733491163062823345)
    ·
      refine ⟨164457233050118372297117509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219276310733491163062823345 164457233050118372297117509)
      ·
        refine ⟨30835731196897194805709533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164457233050118372297117509 30835731196897194805709533)
        ·
          refine ⟨11563399198836448052141075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30835731196897194805709533 11563399198836448052141075)
          ·
            refine ⟨17345098798254672078211613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11563399198836448052141075 17345098798254672078211613)
            ·
              refine ⟨6504412049345502029329355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17345098798254672078211613 6504412049345502029329355)
              ·
                refine ⟨9756618074018253043994033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6504412049345502029329355 9756618074018253043994033)
                ·
                  refine ⟨7317463555513689782995525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9756618074018253043994033 7317463555513689782995525)
                  ·
                    refine ⟨1372024416658816834311661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7317463555513689782995525 1372024416658816834311661)
                    ·
                      rfl

theorem cell23_8016024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 2, 4].length) (baseStart_8016024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016024 prefixEnd_8016024 := by exact prefixLift 8016024
  have htrace : WordTrace (prefixWord ++ tailWord_8016024) baseStart_8016024 baseEnd_8016024 := by
    simpa [prefixWord, tailWord_8016024, baseEnd_8016024] using wordTrace_append hprefix tailTrace_8016024
  have hstable : (prefixWord ++ tailWord_8016024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016024).length < 2 ^ (prefixWord ++ tailWord_8016024).sum := by decide
  have hdescent : baseEnd_8016024 < baseStart_8016024 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016034 : List Nat := [3, 3, 1, 3, 1, 2, 2, 2, 1, 2, 3]
def baseStart_8016034 : Nat := 118140960795 + 8016034 * 2 ^ 59
def prefixEnd_8016034 : Nat := 4983230072969 + 3 ^ 40 * 8016034 * 2
def baseEnd_8016034 : Nat := 4116078384782995463809937

theorem tailTrace_8016034 : CollatzResearch.WordTrace tailWord_8016034 prefixEnd_8016034 4116078384782995463809937 := by
  unfold tailWord_8016034
  simp only [CollatzResearch.WordTrace]
  refine ⟨73092194760321330614573789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194912519360856881638863437 73092194760321330614573789)
  ·
    refine ⟨27409573035120498980465171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73092194760321330614573789 27409573035120498980465171)
    ·
      refine ⟨41114359552680748470697757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27409573035120498980465171 41114359552680748470697757)
      ·
        refine ⟨15417884832255280676511659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41114359552680748470697757 15417884832255280676511659)
        ·
          refine ⟨23126827248382921014767489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15417884832255280676511659 23126827248382921014767489)
          ·
            refine ⟨17345120436287190761075617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23126827248382921014767489 17345120436287190761075617)
            ·
              refine ⟨13008840327215393070806713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17345120436287190761075617 13008840327215393070806713)
              ·
                refine ⟨9756630245411544803105035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13008840327215393070806713 9756630245411544803105035)
                ·
                  refine ⟨14634945368117317204657553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9756630245411544803105035 14634945368117317204657553)
                  ·
                    refine ⟨10976209026087987903493165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14634945368117317204657553 10976209026087987903493165)
                    ·
                      refine ⟨4116078384782995463809937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10976209026087987903493165 4116078384782995463809937)
                      ·
                        rfl

theorem cell23_8016034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_8016034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016034 prefixEnd_8016034 := by exact prefixLift 8016034
  have htrace : WordTrace (prefixWord ++ tailWord_8016034) baseStart_8016034 baseEnd_8016034 := by
    simpa [prefixWord, tailWord_8016034, baseEnd_8016034] using wordTrace_append hprefix tailTrace_8016034
  have hstable : (prefixWord ++ tailWord_8016034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016034).length < 2 ^ (prefixWord ++ tailWord_8016034).sum := by decide
  have hdescent : baseEnd_8016034 < baseStart_8016034 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016057 : List Nat := [1, 2, 1, 4, 1, 2, 1, 5, 1, 3, 2]
def baseStart_8016057 : Nat := 118140960795 + 8016057 * 2 ^ 59
def prefixEnd_8016057 : Nat := 4983230072969 + 3 ^ 40 * 8016057 * 2
def baseEnd_8016057 : Nat := 4116090194838048873822331

theorem tailTrace_8016057 : CollatzResearch.WordTrace tailWord_8016057 prefixEnd_8016057 4116090194838048873822331 := by
  unfold tailWord_8016057
  simp only [CollatzResearch.WordTrace]
  refine ⟨292369617920201997386382425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194913078613467998257588283 292369617920201997386382425)
  ·
    refine ⟨219277213440151498039786819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292369617920201997386382425 219277213440151498039786819)
    ·
      refine ⟨328915820160227247059680229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219277213440151498039786819 328915820160227247059680229)
      ·
        refine ⟨61671716280042608823690043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328915820160227247059680229 61671716280042608823690043)
        ·
          refine ⟨92507574420063913235535065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61671716280042608823690043 92507574420063913235535065)
          ·
            refine ⟨69380680815047934926651299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92507574420063913235535065 69380680815047934926651299)
            ·
              refine ⟨104071021222571902389976949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69380680815047934926651299 104071021222571902389976949)
              ·
                refine ⟨9756658239616115849060339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104071021222571902389976949 9756658239616115849060339)
                ·
                  refine ⟨14634987359424173773590509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9756658239616115849060339 14634987359424173773590509)
                  ·
                    refine ⟨5488120259784065165096441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14634987359424173773590509 5488120259784065165096441)
                    ·
                      refine ⟨4116090194838048873822331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5488120259784065165096441 4116090194838048873822331)
                      ·
                        rfl

theorem cell23_8016057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_8016057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016057 prefixEnd_8016057 := by exact prefixLift 8016057
  have htrace : WordTrace (prefixWord ++ tailWord_8016057) baseStart_8016057 baseEnd_8016057 := by
    simpa [prefixWord, tailWord_8016057, baseEnd_8016057] using wordTrace_append hprefix tailTrace_8016057
  have hstable : (prefixWord ++ tailWord_8016057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016057).length < 2 ^ (prefixWord ++ tailWord_8016057).sum := by decide
  have hdescent : baseEnd_8016057 < baseStart_8016057 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016065 : List Nat := [1, 2, 6, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_8016065 : Nat := 118140960795 + 8016065 * 2 ^ 59
def prefixEnd_8016065 : Nat := 4983230072969 + 3 ^ 40 * 8016065 * 2
def baseEnd_8016065 : Nat := 4116094302683284842522295

theorem tailTrace_8016065 : CollatzResearch.WordTrace tailWord_8016065 prefixEnd_8016065 4116094302683284842522295 := by
  unfold tailWord_8016065
  simp only [CollatzResearch.WordTrace]
  refine ⟨292369909704173014752673649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194913273136115343168449099 292369909704173014752673649)
  ·
    refine ⟨219277432278129761064505237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292369909704173014752673649 219277432278129761064505237)
    ·
      refine ⟨10278629638037332549898683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 219277432278129761064505237 10278629638037332549898683)
      ·
        refine ⟨15417944457055998824848025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10278629638037332549898683 15417944457055998824848025)
        ·
          refine ⟨11563458342791999118636019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15417944457055998824848025 11563458342791999118636019)
          ·
            refine ⟨17345187514187998677954029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11563458342791999118636019 17345187514187998677954029)
            ·
              refine ⟨6504445317820499504232761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17345187514187998677954029 6504445317820499504232761)
              ·
                refine ⟨4878333988365374628174571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6504445317820499504232761 4878333988365374628174571)
                ·
                  refine ⟨7317500982548061942261857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4878333988365374628174571 7317500982548061942261857)
                  ·
                    refine ⟨5488125736911046456696393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7317500982548061942261857 5488125736911046456696393)
                    ·
                      refine ⟨4116094302683284842522295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5488125736911046456696393 4116094302683284842522295)
                      ·
                        rfl

theorem cell23_8016065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_8016065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016065 prefixEnd_8016065 := by exact prefixLift 8016065
  have htrace : WordTrace (prefixWord ++ tailWord_8016065) baseStart_8016065 baseEnd_8016065 := by
    simpa [prefixWord, tailWord_8016065, baseEnd_8016065] using wordTrace_append hprefix tailTrace_8016065
  have hstable : (prefixWord ++ tailWord_8016065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016065).length < 2 ^ (prefixWord ++ tailWord_8016065).sum := by decide
  have hdescent : baseEnd_8016065 < baseStart_8016065 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016133 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 1, 1, 7]
def baseStart_8016133 : Nat := 118140960795 + 8016133 * 2 ^ 59
def prefixEnd_8016133 : Nat := 4983230072969 + 3 ^ 40 * 8016133 * 2
def baseEnd_8016133 : Nat := 4116129219367790576471981

theorem tailTrace_8016133 : CollatzResearch.WordTrace tailWord_8016133 prefixEnd_8016133 4116129219367790576471981 := by
  unfold tailWord_8016133
  simp only [CollatzResearch.WordTrace]
  refine ⟨292372389867926662366149053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194914926578617774910766035 292372389867926662366149053)
  ·
    refine ⟨109639646200472498387305895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292372389867926662366149053 109639646200472498387305895)
    ·
      refine ⟨164459469300708747580958843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109639646200472498387305895 164459469300708747580958843)
      ·
        refine ⟨246689203951063121371438265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164459469300708747580958843 246689203951063121371438265)
        ·
          refine ⟨185016902963297341028578699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246689203951063121371438265 185016902963297341028578699)
          ·
            refine ⟨277525354444946011542868049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185016902963297341028578699 277525354444946011542868049)
            ·
              refine ⟨208144015833709508657151037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277525354444946011542868049 208144015833709508657151037)
              ·
                refine ⟨78054005937641065746431639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208144015833709508657151037 78054005937641065746431639)
                ·
                  refine ⟨117081008906461598619647459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78054005937641065746431639 117081008906461598619647459)
                  ·
                    refine ⟨175621513359692397929471189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117081008906461598619647459 175621513359692397929471189)
                    ·
                      refine ⟨4116129219367790576471981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175621513359692397929471189 4116129219367790576471981)
                      ·
                        rfl

theorem cell23_8016133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_8016133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016133 prefixEnd_8016133 := by exact prefixLift 8016133
  have htrace : WordTrace (prefixWord ++ tailWord_8016133) baseStart_8016133 baseEnd_8016133 := by
    simpa [prefixWord, tailWord_8016133, baseEnd_8016133] using wordTrace_append hprefix tailTrace_8016133
  have hstable : (prefixWord ++ tailWord_8016133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016133).length < 2 ^ (prefixWord ++ tailWord_8016133).sum := by decide
  have hdescent : baseEnd_8016133 < baseStart_8016133 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016157 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 1, 7]
def baseStart_8016157 : Nat := 118140960795 + 8016157 * 2 ^ 59
def prefixEnd_8016157 : Nat := 4983230072969 + 3 ^ 40 * 8016157 * 2
def baseEnd_8016157 : Nat := 1372047180967832827523957

theorem tailTrace_8016157 : CollatzResearch.WordTrace tailWord_8016157 prefixEnd_8016157 1372047180967832827523957 := by
  unfold tailWord_8016157
  simp only [CollatzResearch.WordTrace]
  refine ⟨292373265219839714465022725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194915510146559809643348483 292373265219839714465022725)
  ·
    refine ⟨54819987228719946462191761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292373265219839714465022725 54819987228719946462191761)
    ·
      refine ⟨41114990421539959846643821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54819987228719946462191761 41114990421539959846643821)
      ·
        refine ⟨15418121408077484942491433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41114990421539959846643821 15418121408077484942491433)
        ·
          refine ⟨11563591056058113706868575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15418121408077484942491433 11563591056058113706868575)
          ·
            refine ⟨17345386584087170560302863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11563591056058113706868575 17345386584087170560302863)
            ·
              refine ⟨26018079876130755840454295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17345386584087170560302863 26018079876130755840454295)
              ·
                refine ⟨39027119814196133760681443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26018079876130755840454295 39027119814196133760681443)
                ·
                  refine ⟨58540679721294200641022165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39027119814196133760681443 58540679721294200641022165)
                  ·
                    refine ⟨1372047180967832827523957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58540679721294200641022165 1372047180967832827523957)
                    ·
                      rfl

theorem cell23_8016157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_8016157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016157 prefixEnd_8016157 := by exact prefixLift 8016157
  have htrace : WordTrace (prefixWord ++ tailWord_8016157) baseStart_8016157 baseEnd_8016157 := by
    simpa [prefixWord, tailWord_8016157, baseEnd_8016157] using wordTrace_append hprefix tailTrace_8016157
  have hstable : (prefixWord ++ tailWord_8016157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016157).length < 2 ^ (prefixWord ++ tailWord_8016157).sum := by decide
  have hdescent : baseEnd_8016157 < baseStart_8016157 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016200 : List Nat := [2, 1, 3, 1, 1, 2, 2, 5, 6]
def baseStart_8016200 : Nat := 118140960795 + 8016200 * 2 ^ 59
def prefixEnd_8016200 : Nat := 4983230072969 + 3 ^ 40 * 8016200 * 2
def baseEnd_8016200 : Nat := 457351513619071312703797

theorem tailTrace_8016200 : CollatzResearch.WordTrace tailWord_8016200 prefixEnd_8016200 457351513619071312703797 := by
  unfold tailWord_8016200
  simp only [CollatzResearch.WordTrace]
  refine ⟨146187416779341966404419027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194916555705789288539225369 146187416779341966404419027)
  ·
    refine ⟨219281125169012949606628541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146187416779341966404419027 219281125169012949606628541)
    ·
      refine ⟨82230421938379856102485703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219281125169012949606628541 82230421938379856102485703)
      ·
        refine ⟨123345632907569784153728555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82230421938379856102485703 123345632907569784153728555)
        ·
          refine ⟨185018449361354676230592833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123345632907569784153728555 185018449361354676230592833)
          ·
            refine ⟨138763837021016007172944625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185018449361354676230592833 138763837021016007172944625)
            ·
              refine ⟨104072877765762005379708469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138763837021016007172944625 104072877765762005379708469)
              ·
                refine ⟨9756832290540188004347669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104072877765762005379708469 9756832290540188004347669)
                ·
                  refine ⟨457351513619071312703797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9756832290540188004347669 457351513619071312703797)
                  ·
                    rfl

theorem cell23_8016200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 6].length) (baseStart_8016200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016200 prefixEnd_8016200 := by exact prefixLift 8016200
  have htrace : WordTrace (prefixWord ++ tailWord_8016200) baseStart_8016200 baseEnd_8016200 := by
    simpa [prefixWord, tailWord_8016200, baseEnd_8016200] using wordTrace_append hprefix tailTrace_8016200
  have hstable : (prefixWord ++ tailWord_8016200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016200).length < 2 ^ (prefixWord ++ tailWord_8016200).sum := by decide
  have hdescent : baseEnd_8016200 < baseStart_8016200 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016267 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 4]
def baseStart_8016267 : Nat := 118140960795 + 8016267 * 2 ^ 59
def prefixEnd_8016267 : Nat := 4983230072969 + 3 ^ 40 * 8016267 * 2
def baseEnd_8016267 : Nat := 4116198025775493052196365

theorem tailTrace_8016267 : CollatzResearch.WordTrace tailWord_8016267 prefixEnd_8016267 4116198025775493052196365 := by
  unfold tailWord_8016267
  simp only [CollatzResearch.WordTrace]
  refine ⟨292377277249441203251527055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194918184832960802167684703 292377277249441203251527055)
  ·
    refine ⟨438565915874161804877290583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292377277249441203251527055 438565915874161804877290583)
    ·
      refine ⟨657848873811242707315935875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438565915874161804877290583 657848873811242707315935875)
      ·
        refine ⟨986773310716864060973903813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657848873811242707315935875 986773310716864060973903813)
        ·
          refine ⟨185019995759412011432606965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 986773310716864060973903813 185019995759412011432606965)
          ·
            refine ⟨17345624602444876071806903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185019995759412011432606965 17345624602444876071806903)
            ·
              refine ⟨26018436903667314107710355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17345624602444876071806903 26018436903667314107710355)
              ·
                refine ⟨39027655355500971161565533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26018436903667314107710355 39027655355500971161565533)
                ·
                  refine ⟨14635370758312864185587075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39027655355500971161565533 14635370758312864185587075)
                  ·
                    refine ⟨21953056137469296278380613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14635370758312864185587075 21953056137469296278380613)
                    ·
                      refine ⟨4116198025775493052196365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21953056137469296278380613 4116198025775493052196365)
                      ·
                        rfl

theorem cell23_8016267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 4].length) (baseStart_8016267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016267 prefixEnd_8016267 := by exact prefixLift 8016267
  have htrace : WordTrace (prefixWord ++ tailWord_8016267) baseStart_8016267 baseEnd_8016267 := by
    simpa [prefixWord, tailWord_8016267, baseEnd_8016267] using wordTrace_append hprefix tailTrace_8016267
  have hstable : (prefixWord ++ tailWord_8016267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016267).length < 2 ^ (prefixWord ++ tailWord_8016267).sum := by decide
  have hdescent : baseEnd_8016267 < baseStart_8016267 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016295 : List Nat := [1, 1, 6, 1, 1, 4, 2, 2, 1, 1, 3]
def baseStart_8016295 : Nat := 118140960795 + 8016295 * 2 ^ 59
def prefixEnd_8016295 : Nat := 4983230072969 + 3 ^ 40 * 8016295 * 2
def baseEnd_8016295 : Nat := 4116212403233818942646237

theorem tailTrace_8016295 : CollatzResearch.WordTrace tailWord_8016295 prefixEnd_8016295 4116212403233818942646237 := by
  unfold tailWord_8016295
  simp only [CollatzResearch.WordTrace]
  refine ⟨292378298493339764033546339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194918865662226509355697559 292378298493339764033546339)
  ·
    refine ⟨438567447740009646050319509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292378298493339764033546339 438567447740009646050319509)
    ·
      refine ⟨20557849112812952158608727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 438567447740009646050319509 20557849112812952158608727)
      ·
        refine ⟨30836773669219428237913091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20557849112812952158608727 30836773669219428237913091)
        ·
          refine ⟨46255160503829142356869637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30836773669219428237913091 46255160503829142356869637)
          ·
            refine ⟨8672842594467964191913057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46255160503829142356869637 8672842594467964191913057)
            ·
              refine ⟨6504631945850973143934793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8672842594467964191913057 6504631945850973143934793)
              ·
                refine ⟨4878473959388229857951095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6504631945850973143934793 4878473959388229857951095)
                ·
                  refine ⟨7317710939082344786926643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4878473959388229857951095 7317710939082344786926643)
                  ·
                    refine ⟨10976566408623517180389965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7317710939082344786926643 10976566408623517180389965)
                    ·
                      refine ⟨4116212403233818942646237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10976566408623517180389965 4116212403233818942646237)
                      ·
                        rfl

theorem cell23_8016295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_8016295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016295 prefixEnd_8016295 := by exact prefixLift 8016295
  have htrace : WordTrace (prefixWord ++ tailWord_8016295) baseStart_8016295 baseEnd_8016295 := by
    simpa [prefixWord, tailWord_8016295, baseEnd_8016295] using wordTrace_append hprefix tailTrace_8016295
  have hstable : (prefixWord ++ tailWord_8016295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016295).length < 2 ^ (prefixWord ++ tailWord_8016295).sum := by decide
  have hdescent : baseEnd_8016295 < baseStart_8016295 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016320 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 4, 7]
def baseStart_8016320 : Nat := 118140960795 + 8016320 * 2 ^ 59
def prefixEnd_8016320 : Nat := 4983230072969 + 3 ^ 40 * 8016320 * 2
def baseEnd_8016320 : Nat := 1372075080083393781611207

theorem tailTrace_8016320 : CollatzResearch.WordTrace tailWord_8016320 prefixEnd_8016320 1372075080083393781611207 := by
  unfold tailWord_8016320
  simp only [CollatzResearch.WordTrace]
  refine ⟨146189605159124596651603207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194919473545499462202137609 146189605159124596651603207)
  ·
    refine ⟨219284407738686894977404811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146189605159124596651603207 219284407738686894977404811)
    ·
      refine ⟨328926611608030342466107217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219284407738686894977404811 328926611608030342466107217)
      ·
        refine ⟨246694958706022756849580413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328926611608030342466107217 246694958706022756849580413)
        ·
          refine ⟨92510609514758533818592655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246694958706022756849580413 92510609514758533818592655)
          ·
            refine ⟨138765914272137800727888983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92510609514758533818592655 138765914272137800727888983)
            ·
              refine ⟨208148871408206701091833475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138765914272137800727888983 208148871408206701091833475)
              ·
                refine ⟨312223307112310051637750213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208148871408206701091833475 312223307112310051637750213)
                ·
                  refine ⟨58541870083558134682078165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 312223307112310051637750213 58541870083558134682078165)
                  ·
                    refine ⟨1372075080083393781611207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58541870083558134682078165 1372075080083393781611207)
                    ·
                      rfl

theorem cell23_8016320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 4, 7].length) (baseStart_8016320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016320 prefixEnd_8016320 := by exact prefixLift 8016320
  have htrace : WordTrace (prefixWord ++ tailWord_8016320) baseStart_8016320 baseEnd_8016320 := by
    simpa [prefixWord, tailWord_8016320, baseEnd_8016320] using wordTrace_append hprefix tailTrace_8016320
  have hstable : (prefixWord ++ tailWord_8016320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016320).length < 2 ^ (prefixWord ++ tailWord_8016320).sum := by decide
  have hdescent : baseEnd_8016320 < baseStart_8016320 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016334 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3]
def baseStart_8016334 : Nat := 118140960795 + 8016334 * 2 ^ 59
def prefixEnd_8016334 : Nat := 4983230072969 + 3 ^ 40 * 8016334 * 2
def baseEnd_8016334 : Nat := 4116232428979344290058557

theorem tailTrace_8016334 : CollatzResearch.WordTrace tailWord_8016334 prefixEnd_8016334 4116232428979344290058557 := by
  unfold tailWord_8016334
  simp only [CollatzResearch.WordTrace]
  refine ⟨36547465117524809211777007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194919813960132315796144037 36547465117524809211777007)
  ·
    refine ⟨54821197676287213817665511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36547465117524809211777007 54821197676287213817665511)
    ·
      refine ⟨82231796514430820726498267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54821197676287213817665511 82231796514430820726498267)
      ·
        refine ⟨123347694771646231089747401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82231796514430820726498267 123347694771646231089747401)
        ·
          refine ⟨92510771078734673317310551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123347694771646231089747401 92510771078734673317310551)
          ·
            refine ⟨138766156618102009975965827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92510771078734673317310551 138766156618102009975965827)
            ·
              refine ⟨208149234927153014963948741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138766156618102009975965827 208149234927153014963948741)
              ·
                refine ⟨39027981548841190305740389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208149234927153014963948741 39027981548841190305740389)
                ·
                  refine ⟨7317746540407723182326323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39027981548841190305740389 7317746540407723182326323)
                  ·
                    refine ⟨10976619810611584773489485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7317746540407723182326323 10976619810611584773489485)
                    ·
                      refine ⟨4116232428979344290058557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10976619810611584773489485 4116232428979344290058557)
                      ·
                        rfl

theorem cell23_8016334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_8016334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016334 prefixEnd_8016334 := by exact prefixLift 8016334
  have htrace : WordTrace (prefixWord ++ tailWord_8016334) baseStart_8016334 baseEnd_8016334 := by
    simpa [prefixWord, tailWord_8016334, baseEnd_8016334] using wordTrace_append hprefix tailTrace_8016334
  have hstable : (prefixWord ++ tailWord_8016334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016334).length < 2 ^ (prefixWord ++ tailWord_8016334).sum := by decide
  have hdescent : baseEnd_8016334 < baseStart_8016334 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016338 : List Nat := [3, 2, 2, 4, 1, 1, 1, 3, 1, 2, 3]
def baseStart_8016338 : Nat := 118140960795 + 8016338 * 2 ^ 59
def prefixEnd_8016338 : Nat := 4983230072969 + 3 ^ 40 * 8016338 * 2
def baseEnd_8016338 : Nat := 4116234482901962274408539

theorem tailTrace_8016338 : CollatzResearch.WordTrace tailWord_8016338 prefixEnd_8016338 4116234482901962274408539 := by
  unfold tailWord_8016338
  simp only [CollatzResearch.WordTrace]
  refine ⟨73094966708045995594340417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194919911221455988251574445 73094966708045995594340417)
  ·
    refine ⟨54821225031034496695755313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73094966708045995594340417 54821225031034496695755313)
    ·
      refine ⟨41115918773275872521816485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54821225031034496695755313 41115918773275872521816485)
      ·
        refine ⟨7709234769989226097840591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41115918773275872521816485 7709234769989226097840591)
        ·
          refine ⟨11563852154983839146760887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7709234769989226097840591 11563852154983839146760887)
          ·
            refine ⟨17345778232475758720141331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11563852154983839146760887 17345778232475758720141331)
            ·
              refine ⟨26018667348713638080211997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17345778232475758720141331 26018667348713638080211997)
              ·
                refine ⟨9757000255767614280079499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26018667348713638080211997 9757000255767614280079499)
                ·
                  refine ⟨14635500383651421420119249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9757000255767614280079499 14635500383651421420119249)
                  ·
                    refine ⟨10976625287738566065089437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14635500383651421420119249 10976625287738566065089437)
                    ·
                      refine ⟨4116234482901962274408539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10976625287738566065089437 4116234482901962274408539)
                      ·
                        rfl

theorem cell23_8016338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_8016338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016338 prefixEnd_8016338 := by exact prefixLift 8016338
  have htrace : WordTrace (prefixWord ++ tailWord_8016338) baseStart_8016338 baseEnd_8016338 := by
    simpa [prefixWord, tailWord_8016338, baseEnd_8016338] using wordTrace_append hprefix tailTrace_8016338
  have hstable : (prefixWord ++ tailWord_8016338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016338).length < 2 ^ (prefixWord ++ tailWord_8016338).sum := by decide
  have hdescent : baseEnd_8016338 < baseStart_8016338 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016351 : List Nat := [1, 1, 2, 3, 3, 2, 3, 2, 2, 1, 3]
def baseStart_8016351 : Nat := 118140960795 + 8016351 * 2 ^ 59
def prefixEnd_8016351 : Nat := 4983230072969 + 3 ^ 40 * 8016351 * 2
def baseEnd_8016351 : Nat := 4116241158150470723545979

theorem tailTrace_8016351 : CollatzResearch.WordTrace tailWord_8016351 prefixEnd_8016351 4116241158150470723545979 := by
  unfold tailWord_8016351
  simp only [CollatzResearch.WordTrace]
  refine ⟨292380340981136885597584907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194920227320757923731723271 292380340981136885597584907)
  ·
    refine ⟨438570511471705328396377361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292380340981136885597584907 438570511471705328396377361)
    ·
      refine ⟨328927883603778996297283021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438570511471705328396377361 328927883603778996297283021)
      ·
        refine ⟨123347956351417123611481133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328927883603778996297283021 123347956351417123611481133)
        ·
          refine ⟨46255483631781421354305425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123347956351417123611481133 46255483631781421354305425)
          ·
            refine ⟨34691612723836066015729069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46255483631781421354305425 34691612723836066015729069)
            ·
              refine ⟨13009354771438524755898401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34691612723836066015729069 13009354771438524755898401)
              ·
                refine ⟨9757016078578893566923801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13009354771438524755898401 9757016078578893566923801)
                ·
                  refine ⟨7317762058934170175192851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9757016078578893566923801 7317762058934170175192851)
                  ·
                    refine ⟨10976643088401255262789277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7317762058934170175192851 10976643088401255262789277)
                    ·
                      refine ⟨4116241158150470723545979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10976643088401255262789277 4116241158150470723545979)
                      ·
                        rfl

theorem cell23_8016351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_8016351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016351 prefixEnd_8016351 := by exact prefixLift 8016351
  have htrace : WordTrace (prefixWord ++ tailWord_8016351) baseStart_8016351 baseEnd_8016351 := by
    simpa [prefixWord, tailWord_8016351, baseEnd_8016351] using wordTrace_append hprefix tailTrace_8016351
  have hstable : (prefixWord ++ tailWord_8016351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016351).length < 2 ^ (prefixWord ++ tailWord_8016351).sum := by decide
  have hdescent : baseEnd_8016351 < baseStart_8016351 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016377 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 2, 4, 3]
def baseStart_8016377 : Nat := 118140960795 + 8016377 * 2 ^ 59
def prefixEnd_8016377 : Nat := 4983230072969 + 3 ^ 40 * 8016377 * 2
def baseEnd_8016377 : Nat := 4116254508647487621820859

theorem tailTrace_8016377 : CollatzResearch.WordTrace tailWord_8016377 prefixEnd_8016377 4116254508647487621820859 := by
  unfold tailWord_8016377
  simp only [CollatzResearch.WordTrace]
  refine ⟨292381289279042692038031385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194920859519361794692020923 292381289279042692038031385)
  ·
    refine ⟨219285966959282019028523539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292381289279042692038031385 219285966959282019028523539)
    ·
      refine ⟨328928950438923028542785309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219285966959282019028523539 328928950438923028542785309)
      ·
        refine ⟨123348356414596135703544491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328928950438923028542785309 123348356414596135703544491)
        ·
          refine ⟨185022534621894203555316737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123348356414596135703544491 185022534621894203555316737)
          ·
            refine ⟨138766900966420652666487553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185022534621894203555316737 138766900966420652666487553)
            ·
              refine ⟨104075175724815489499865665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138766900966420652666487553 104075175724815489499865665)
              ·
                refine ⟨78056381793611617124899249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104075175724815489499865665 78056381793611617124899249)
                ·
                  refine ⟨58542286345208712843674437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78056381793611617124899249 58542286345208712843674437)
                  ·
                    refine ⟨10976678689726633658188957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58542286345208712843674437 10976678689726633658188957)
                    ·
                      refine ⟨4116254508647487621820859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10976678689726633658188957 4116254508647487621820859)
                      ·
                        rfl

theorem cell23_8016377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_8016377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016377 prefixEnd_8016377 := by exact prefixLift 8016377
  have htrace : WordTrace (prefixWord ++ tailWord_8016377) baseStart_8016377 baseEnd_8016377 := by
    simpa [prefixWord, tailWord_8016377, baseEnd_8016377] using wordTrace_append hprefix tailTrace_8016377
  have hstable : (prefixWord ++ tailWord_8016377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016377).length < 2 ^ (prefixWord ++ tailWord_8016377).sum := by decide
  have hdescent : baseEnd_8016377 < baseStart_8016377 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016429 : List Nat := [1, 5, 4, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_8016429 : Nat := 118140960795 + 8016429 * 2 ^ 59
def prefixEnd_8016429 : Nat := 4983230072969 + 3 ^ 40 * 8016429 * 2
def baseEnd_8016429 : Nat := 4116281209641521418370621

theorem tailTrace_8016429 : CollatzResearch.WordTrace tailWord_8016429 prefixEnd_8016429 4116281209641521418370621 := by
  unfold tailWord_8016429
  simp only [CollatzResearch.WordTrace]
  refine ⟨292383185874854304918924341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194922123916569536612616227 292383185874854304918924341)
  ·
    refine ⟨27410923675767591086149157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 292383185874854304918924341 27410923675767591086149157)
    ·
      refine ⟨5139548189206423328652967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27410923675767591086149157 5139548189206423328652967)
      ·
        refine ⟨7709322283809634992979451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5139548189206423328652967 7709322283809634992979451)
        ·
          refine ⟨11563983425714452489469177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7709322283809634992979451 11563983425714452489469177)
          ·
            refine ⟨8672987569285839367101883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11563983425714452489469177 8672987569285839367101883)
            ·
              refine ⟨13009481353928759050652825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8672987569285839367101883 13009481353928759050652825)
              ·
                refine ⟨9757111015446569287989619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13009481353928759050652825 9757111015446569287989619)
                ·
                  refine ⟨14635666523169853931984429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9757111015446569287989619 14635666523169853931984429)
                  ·
                    refine ⟨5488374946188695224494161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14635666523169853931984429 5488374946188695224494161)
                    ·
                      refine ⟨4116281209641521418370621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5488374946188695224494161 4116281209641521418370621)
                      ·
                        rfl

theorem cell23_8016429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_8016429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016429 prefixEnd_8016429 := by exact prefixLift 8016429
  have htrace : WordTrace (prefixWord ++ tailWord_8016429) baseStart_8016429 baseEnd_8016429 := by
    simpa [prefixWord, tailWord_8016429, baseEnd_8016429] using wordTrace_append hprefix tailTrace_8016429
  have hstable : (prefixWord ++ tailWord_8016429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016429).length < 2 ^ (prefixWord ++ tailWord_8016429).sum := by decide
  have hdescent : baseEnd_8016429 < baseStart_8016429 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016437 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_8016437 : Nat := 118140960795 + 8016437 * 2 ^ 59
def prefixEnd_8016437 : Nat := 4983230072969 + 3 ^ 40 * 8016437 * 2
def baseEnd_8016437 : Nat := 4116285317486757387070583

theorem tailTrace_8016437 : CollatzResearch.WordTrace tailWord_8016437 prefixEnd_8016437 4116285317486757387070583 := by
  unfold tailWord_8016437
  simp only [CollatzResearch.WordTrace]
  refine ⟨292383477658825322285215565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194922318439216881523477043 292383477658825322285215565)
  ·
    refine ⟨109643804122059495856955837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292383477658825322285215565 109643804122059495856955837)
    ·
      refine ⟨41116426545772310946358439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109643804122059495856955837 41116426545772310946358439)
      ·
        refine ⟨61674639818658466419537659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41116426545772310946358439 61674639818658466419537659)
        ·
          refine ⟨92511959727987699629306489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61674639818658466419537659 92511959727987699629306489)
          ·
            refine ⟨69383969795990774721979867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92511959727987699629306489 69383969795990774721979867)
            ·
              refine ⟨104075954693986162082969801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69383969795990774721979867 104075954693986162082969801)
              ·
                refine ⟨78056966020489621562227351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104075954693986162082969801 78056966020489621562227351)
                ·
                  refine ⟨117085449030734432343341027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78056966020489621562227351 117085449030734432343341027)
                  ·
                    refine ⟨175628173546101648515011541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117085449030734432343341027 175628173546101648515011541)
                    ·
                      refine ⟨4116285317486757387070583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175628173546101648515011541 4116285317486757387070583)
                      ·
                        rfl

theorem cell23_8016437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_8016437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016437 prefixEnd_8016437 := by exact prefixLift 8016437
  have htrace : WordTrace (prefixWord ++ tailWord_8016437) baseStart_8016437 baseEnd_8016437 := by
    simpa [prefixWord, tailWord_8016437, baseEnd_8016437] using wordTrace_append hprefix tailTrace_8016437
  have hstable : (prefixWord ++ tailWord_8016437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016437).length < 2 ^ (prefixWord ++ tailWord_8016437).sum := by decide
  have hdescent : baseEnd_8016437 < baseStart_8016437 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016444 : List Nat := [2, 2, 2, 2, 3, 1, 1, 3, 2, 5]
def baseStart_8016444 : Nat := 118140960795 + 8016444 * 2 ^ 59
def prefixEnd_8016444 : Nat := 4983230072969 + 3 ^ 40 * 8016444 * 2
def baseEnd_8016444 : Nat := 1372096303950446286561017

theorem tailTrace_8016444 : CollatzResearch.WordTrace tailWord_8016444 prefixEnd_8016444 1372096303950446286561017 := by
  unfold tailWord_8016444
  simp only [CollatzResearch.WordTrace]
  refine ⟨146191866484899981240360193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194922488646533308320480257 146191866484899981240360193)
  ·
    refine ⟨109643899863674985930270145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146191866484899981240360193 109643899863674985930270145)
    ·
      refine ⟨82232924897756239447702609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109643899863674985930270145 82232924897756239447702609)
      ·
        refine ⟨61674693673317179585776957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82232924897756239447702609 61674693673317179585776957)
        ·
          refine ⟨23128010127493942344666359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61674693673317179585776957 23128010127493942344666359)
          ·
            refine ⟨34692015191240913516999539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23128010127493942344666359 34692015191240913516999539)
            ·
              refine ⟨52038022786861370275499309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34692015191240913516999539 52038022786861370275499309)
              ·
                refine ⟨19514258545073013853312241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52038022786861370275499309 19514258545073013853312241)
                ·
                  refine ⟨14635693908804760389984181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19514258545073013853312241 14635693908804760389984181)
                  ·
                    refine ⟨1372096303950446286561017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14635693908804760389984181 1372096303950446286561017)
                    ·
                      rfl

theorem cell23_8016444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_8016444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016444 prefixEnd_8016444 := by exact prefixLift 8016444
  have htrace : WordTrace (prefixWord ++ tailWord_8016444) baseStart_8016444 baseEnd_8016444 := by
    simpa [prefixWord, tailWord_8016444, baseEnd_8016444] using wordTrace_append hprefix tailTrace_8016444
  have hstable : (prefixWord ++ tailWord_8016444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016444).length < 2 ^ (prefixWord ++ tailWord_8016444).sum := by decide
  have hdescent : baseEnd_8016444 < baseStart_8016444 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016461 : List Nat := [1, 6, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_8016461 : Nat := 118140960795 + 8016461 * 2 ^ 59
def prefixEnd_8016461 : Nat := 4983230072969 + 3 ^ 40 * 8016461 * 2
def baseEnd_8016461 : Nat := 1372099213674155097723491

theorem tailTrace_8016461 : CollatzResearch.WordTrace tailWord_8016461 prefixEnd_8016461 1372099213674155097723491 := by
  unfold tailWord_8016461
  simp only [CollatzResearch.WordTrace]
  refine ⟨292384353010738374384089237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194922902007158916256059491 292384353010738374384089237)
  ·
    refine ⟨13705516547378361299254183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 292384353010738374384089237 13705516547378361299254183)
    ·
      refine ⟨20558274821067541948881275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13705516547378361299254183 20558274821067541948881275)
      ·
        refine ⟨30837412231601312923321913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20558274821067541948881275 30837412231601312923321913)
        ·
          refine ⟨23128059173700984692491435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30837412231601312923321913 23128059173700984692491435)
          ·
            refine ⟨34692088760551477038737153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23128059173700984692491435 34692088760551477038737153)
            ·
              refine ⟨26019066570413607779052865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34692088760551477038737153 26019066570413607779052865)
              ·
                refine ⟨19514299927810205834289649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26019066570413607779052865 19514299927810205834289649)
                ·
                  refine ⟨14635724945857654375717237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19514299927810205834289649 14635724945857654375717237)
                  ·
                    refine ⟨1372099213674155097723491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14635724945857654375717237 1372099213674155097723491)
                    ·
                      rfl

theorem cell23_8016461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_8016461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016461 prefixEnd_8016461 := by exact prefixLift 8016461
  have htrace : WordTrace (prefixWord ++ tailWord_8016461) baseStart_8016461 baseEnd_8016461 := by
    simpa [prefixWord, tailWord_8016461, baseEnd_8016461] using wordTrace_append hprefix tailTrace_8016461
  have hstable : (prefixWord ++ tailWord_8016461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016461).length < 2 ^ (prefixWord ++ tailWord_8016461).sum := by decide
  have hdescent : baseEnd_8016461 < baseStart_8016461 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016481 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 2, 4, 2]
def baseStart_8016481 : Nat := 118140960795 + 8016481 * 2 ^ 59
def prefixEnd_8016481 : Nat := 4983230072969 + 3 ^ 40 * 8016481 * 2
def baseEnd_8016481 : Nat := 4116307910635555214920381

theorem tailTrace_8016481 : CollatzResearch.WordTrace tailWord_8016481 prefixEnd_8016481 4116307910635555214920381 := by
  unfold tailWord_8016481
  simp only [CollatzResearch.WordTrace]
  refine ⟨292385082470665917799817297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194923388313777278533211531 292385082470665917799817297)
  ·
    refine ⟨219288811852999438349862973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292385082470665917799817297 219288811852999438349862973)
    ·
      refine ⟨82233304444874789381198615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219288811852999438349862973 82233304444874789381198615)
      ·
        refine ⟨123349956667312184071797923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82233304444874789381198615 123349956667312184071797923)
        ·
          refine ⟨185024935000968276107696885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123349956667312184071797923 185024935000968276107696885)
          ·
            refine ⟨17346087656340775885096583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185024935000968276107696885 17346087656340775885096583)
            ·
              refine ⟨26019131484511163827644875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17346087656340775885096583 26019131484511163827644875)
              ·
                refine ⟨39028697226766745741467313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26019131484511163827644875 39028697226766745741467313)
                ·
                  refine ⟨29271522920075059306100485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39028697226766745741467313 29271522920075059306100485)
                  ·
                    refine ⟨5488410547514073619893841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29271522920075059306100485 5488410547514073619893841)
                    ·
                      refine ⟨4116307910635555214920381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5488410547514073619893841 4116307910635555214920381)
                      ·
                        rfl

theorem cell23_8016481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_8016481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016481 prefixEnd_8016481 := by exact prefixLift 8016481
  have htrace : WordTrace (prefixWord ++ tailWord_8016481) baseStart_8016481 baseEnd_8016481 := by
    simpa [prefixWord, tailWord_8016481, baseEnd_8016481] using wordTrace_append hprefix tailTrace_8016481
  have hstable : (prefixWord ++ tailWord_8016481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016481).length < 2 ^ (prefixWord ++ tailWord_8016481).sum := by decide
  have hdescent : baseEnd_8016481 < baseStart_8016481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016484 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 1, 4, 3]
def baseStart_8016484 : Nat := 118140960795 + 8016484 * 2 ^ 59
def prefixEnd_8016484 : Nat := 4983230072969 + 3 ^ 40 * 8016484 * 2
def baseEnd_8016484 : Nat := 4116309451077518703182867

theorem tailTrace_8016484 : CollatzResearch.WordTrace tailWord_8016484 prefixEnd_8016484 4116309451077518703182867 := by
  unfold tailWord_8016484
  simp only [CollatzResearch.WordTrace]
  refine ⟨146192595944827524656088253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194923461259770032874784337 146192595944827524656088253)
  ·
    refine ⟨54822223479310321746033095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146192595944827524656088253 54822223479310321746033095)
    ·
      refine ⟨82233335218965482619049643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54822223479310321746033095 82233335218965482619049643)
      ·
        refine ⟨123350002828448223928574465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82233335218965482619049643 123350002828448223928574465)
        ·
          refine ⟨92512502121336167946430849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123350002828448223928574465 92512502121336167946430849)
          ·
            refine ⟨69384376591002125959823137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92512502121336167946430849 69384376591002125959823137)
            ·
              refine ⟨52038282443251594469867353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69384376591002125959823137 52038282443251594469867353)
              ·
                refine ⟨39028711832438695852400515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52038282443251594469867353 39028711832438695852400515)
                ·
                  refine ⟨58543067748658043778600773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39028711832438695852400515 58543067748658043778600773)
                  ·
                    refine ⟨10976825202873383208487645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58543067748658043778600773 10976825202873383208487645)
                    ·
                      refine ⟨4116309451077518703182867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10976825202873383208487645 4116309451077518703182867)
                      ·
                        rfl

theorem cell23_8016484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_8016484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016484 prefixEnd_8016484 := by exact prefixLift 8016484
  have htrace : WordTrace (prefixWord ++ tailWord_8016484) baseStart_8016484 baseEnd_8016484 := by
    simpa [prefixWord, tailWord_8016484, baseEnd_8016484] using wordTrace_append hprefix tailTrace_8016484
  have hstable : (prefixWord ++ tailWord_8016484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016484).length < 2 ^ (prefixWord ++ tailWord_8016484).sum := by decide
  have hdescent : baseEnd_8016484 < baseStart_8016484 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016487 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 10]
def baseStart_8016487 : Nat := 118140960795 + 8016487 * 2 ^ 59
def prefixEnd_8016487 : Nat := 4983230072969 + 3 ^ 40 * 8016487 * 2
def baseEnd_8016487 : Nat := 457367887946609132382817

theorem tailTrace_8016487 : CollatzResearch.WordTrace tailWord_8016487 prefixEnd_8016487 457367887946609132382817 := by
  unfold tailWord_8016487
  simp only [CollatzResearch.WordTrace]
  refine ⟨292385301308644180824535715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194923534205762787216357143 292385301308644180824535715)
  ·
    refine ⟨438577951962966271236803573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292385301308644180824535715 438577951962966271236803573)
    ·
      refine ⟨41116682996528087928450335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 438577951962966271236803573 41116682996528087928450335)
      ·
        refine ⟨61675024494792131892675503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41116682996528087928450335 61675024494792131892675503)
        ·
          refine ⟨92512536742188197839013255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61675024494792131892675503 92512536742188197839013255)
          ·
            refine ⟨138768805113282296758519883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92512536742188197839013255 138768805113282296758519883)
            ·
              refine ⟨208153207669923445137779825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138768805113282296758519883 208153207669923445137779825)
              ·
                refine ⟨156114905752442583853334869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208153207669923445137779825 156114905752442583853334869)
                ·
                  refine ⟨457367887946609132382817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 156114905752442583853334869 457367887946609132382817)
                  ·
                    rfl

theorem cell23_8016487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 10].length) (baseStart_8016487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016487 prefixEnd_8016487 := by exact prefixLift 8016487
  have htrace : WordTrace (prefixWord ++ tailWord_8016487) baseStart_8016487 baseEnd_8016487 := by
    simpa [prefixWord, tailWord_8016487, baseEnd_8016487] using wordTrace_append hprefix tailTrace_8016487
  have hstable : (prefixWord ++ tailWord_8016487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016487).length < 2 ^ (prefixWord ++ tailWord_8016487).sum := by decide
  have hdescent : baseEnd_8016487 < baseStart_8016487 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016498 : List Nat := [3, 2, 1, 2, 4, 2, 1, 1, 2, 1, 4]
def baseStart_8016498 : Nat := 118140960795 + 8016498 * 2 ^ 59
def prefixEnd_8016498 : Nat := 4983230072969 + 3 ^ 40 * 8016498 * 2
def baseEnd_8016498 : Nat := 4116316639806681648407803

theorem tailTrace_8016498 : CollatzResearch.WordTrace tailWord_8016498 prefixEnd_8016498 4116316639806681648407803 := by
  unfold tailWord_8016498
  simp only [CollatzResearch.WordTrace]
  refine ⟨73096425627901082425796537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194923801674402886468790765 73096425627901082425796537)
  ·
    refine ⟨54822319220925811819347403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73096425627901082425796537 54822319220925811819347403)
    ·
      refine ⟨82233478831388717729021105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54822319220925811819347403 82233478831388717729021105)
      ·
        refine ⟨61675109123541538296765829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82233478831388717729021105 61675109123541538296765829)
        ·
          refine ⟨11564082960664038430643593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61675109123541538296765829 11564082960664038430643593)
          ·
            refine ⟨8673062220498028822982695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11564082960664038430643593 8673062220498028822982695)
            ·
              refine ⟨13009593330747043234474043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8673062220498028822982695 13009593330747043234474043)
              ·
                refine ⟨19514389996120564851711065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13009593330747043234474043 19514389996120564851711065)
                ·
                  refine ⟨14635792497090423638783299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19514389996120564851711065 14635792497090423638783299)
                  ·
                    refine ⟨21953688745635635458174949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14635792497090423638783299 21953688745635635458174949)
                    ·
                      refine ⟨4116316639806681648407803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21953688745635635458174949 4116316639806681648407803)
                      ·
                        rfl

theorem cell23_8016498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_8016498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016498 prefixEnd_8016498 := by exact prefixLift 8016498
  have htrace : WordTrace (prefixWord ++ tailWord_8016498) baseStart_8016498 baseEnd_8016498 := by
    simpa [prefixWord, tailWord_8016498, baseEnd_8016498] using wordTrace_append hprefix tailTrace_8016498
  have hstable : (prefixWord ++ tailWord_8016498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016498).length < 2 ^ (prefixWord ++ tailWord_8016498).sum := by decide
  have hdescent : baseEnd_8016498 < baseStart_8016498 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016527 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 5]
def baseStart_8016527 : Nat := 118140960795 + 8016527 * 2 ^ 59
def prefixEnd_8016527 : Nat := 4983230072969 + 3 ^ 40 * 8016527 * 2
def baseEnd_8016527 : Nat := 4116331530745662034945169

theorem tailTrace_8016527 : CollatzResearch.WordTrace tailWord_8016527 prefixEnd_8016527 4116331530745662034945169 := by
  unfold tailWord_8016527
  simp only [CollatzResearch.WordTrace]
  refine ⟨292386760228499267655991835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194924506818999511770661223 292386760228499267655991835)
  ·
    refine ⟨438580140342748901483987753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292386760228499267655991835 438580140342748901483987753)
    ·
      refine ⟨328935105257061676112990815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438580140342748901483987753 328935105257061676112990815)
      ·
        refine ⟨493402657885592514169486223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328935105257061676112990815 493402657885592514169486223)
        ·
          refine ⟨740103986828388771254229335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493402657885592514169486223 740103986828388771254229335)
          ·
            refine ⟨1110155980242583156881344003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740103986828388771254229335 1110155980242583156881344003)
            ·
              refine ⟨1665233970363874735322016005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110155980242583156881344003 1665233970363874735322016005)
              ·
                refine ⟨312231369443226512872878001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1665233970363874735322016005 312231369443226512872878001)
                ·
                  refine ⟨234173527082419884654658501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312231369443226512872878001 234173527082419884654658501)
                  ·
                    refine ⟨43907536327953728372748469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 234173527082419884654658501 43907536327953728372748469)
                    ·
                      refine ⟨4116331530745662034945169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43907536327953728372748469 4116331530745662034945169)
                      ·
                        rfl

theorem cell23_8016527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_8016527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016527 prefixEnd_8016527 := by exact prefixLift 8016527
  have htrace : WordTrace (prefixWord ++ tailWord_8016527) baseStart_8016527 baseEnd_8016527 := by
    simpa [prefixWord, tailWord_8016527, baseEnd_8016527] using wordTrace_append hprefix tailTrace_8016527
  have hstable : (prefixWord ++ tailWord_8016527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016527).length < 2 ^ (prefixWord ++ tailWord_8016527).sum := by decide
  have hdescent : baseEnd_8016527 < baseStart_8016527 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016541 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 1, 5, 2]
def baseStart_8016541 : Nat := 118140960795 + 8016541 * 2 ^ 59
def prefixEnd_8016541 : Nat := 4983230072969 + 3 ^ 40 * 8016541 * 2
def baseEnd_8016541 : Nat := 4116338719474824980170105

theorem tailTrace_8016541 : CollatzResearch.WordTrace tailWord_8016541 prefixEnd_8016541 4116338719474824980170105 := by
  unfold tailWord_8016541
  simp only [CollatzResearch.WordTrace]
  refine ⟨292387270850448548047001477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194924847233632365364667651 292387270850448548047001477)
  ·
    refine ⟨54822613284459102758812777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292387270850448548047001477 54822613284459102758812777)
    ·
      refine ⟨41116959963344327069109583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54822613284459102758812777 41116959963344327069109583)
      ·
        refine ⟨61675439945016490603664375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41116959963344327069109583 61675439945016490603664375)
        ·
          refine ⟨92513159917524735905496563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61675439945016490603664375 92513159917524735905496563)
          ·
            refine ⟨138769739876287103858244845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92513159917524735905496563 138769739876287103858244845)
            ·
              refine ⟨52038652453607663946841817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138769739876287103858244845 52038652453607663946841817)
              ·
                refine ⟨39028989340205747960131363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52038652453607663946841817 39028989340205747960131363)
                ·
                  refine ⟨58543484010308621940197045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39028989340205747960131363 58543484010308621940197045)
                  ·
                    refine ⟨5488451625966433306893473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58543484010308621940197045 5488451625966433306893473)
                    ·
                      refine ⟨4116338719474824980170105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5488451625966433306893473 4116338719474824980170105)
                      ·
                        rfl

theorem cell23_8016541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_8016541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016541 prefixEnd_8016541 := by exact prefixLift 8016541
  have htrace : WordTrace (prefixWord ++ tailWord_8016541) baseStart_8016541 baseEnd_8016541 := by
    simpa [prefixWord, tailWord_8016541, baseEnd_8016541] using wordTrace_append hprefix tailTrace_8016541
  have hstable : (prefixWord ++ tailWord_8016541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016541).length < 2 ^ (prefixWord ++ tailWord_8016541).sum := by decide
  have hdescent : baseEnd_8016541 < baseStart_8016541 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016584 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 1, 1, 6]
def baseStart_8016584 : Nat := 118140960795 + 8016584 * 2 ^ 59
def prefixEnd_8016584 : Nat := 4983230072969 + 3 ^ 40 * 8016584 * 2
def baseEnd_8016584 : Nat := 4116360799142968311932407

theorem tailTrace_8016584 : CollatzResearch.WordTrace tailWord_8016584 prefixEnd_8016584 4116360799142968311932407 := by
  unfold tailWord_8016584
  simp only [CollatzResearch.WordTrace]
  refine ⟨146194419594646383195408403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194925892792861844260544537 146194419594646383195408403)
  ·
    refine ⟨219291629391969574793112605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146194419594646383195408403 219291629391969574793112605)
    ·
      refine ⟨82234361021988590547417227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219291629391969574793112605 82234361021988590547417227)
      ·
        refine ⟨123351541532982885821125841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82234361021988590547417227 123351541532982885821125841)
        ·
          refine ⟨92513656149737164365844381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123351541532982885821125841 92513656149737164365844381)
          ·
            refine ⟨34692621056151436637191643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92513656149737164365844381 34692621056151436637191643)
            ·
              refine ⟨52038931584227154955787465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34692621056151436637191643 52038931584227154955787465)
              ·
                refine ⟨39029198688170366216840599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52038931584227154955787465 39029198688170366216840599)
                ·
                  refine ⟨58543798032255549325260899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39029198688170366216840599 58543798032255549325260899)
                  ·
                    refine ⟨87815697048383323987891349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58543798032255549325260899 87815697048383323987891349)
                    ·
                      refine ⟨4116360799142968311932407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87815697048383323987891349 4116360799142968311932407)
                      ·
                        rfl

theorem cell23_8016584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_8016584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016584 prefixEnd_8016584 := by exact prefixLift 8016584
  have htrace : WordTrace (prefixWord ++ tailWord_8016584) baseStart_8016584 baseEnd_8016584 := by
    simpa [prefixWord, tailWord_8016584, baseEnd_8016584] using wordTrace_append hprefix tailTrace_8016584
  have hstable : (prefixWord ++ tailWord_8016584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016584).length < 2 ^ (prefixWord ++ tailWord_8016584).sum := by decide
  have hdescent : baseEnd_8016584 < baseStart_8016584 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016628 : List Nat := [2, 6, 1, 1, 2, 11]
def baseStart_8016628 : Nat := 118140960795 + 8016628 * 2 ^ 59
def prefixEnd_8016628 : Nat := 4983230072969 + 3 ^ 40 * 8016628 * 2
def baseEnd_8016628 : Nat := 16939849350994922385935

theorem tailTrace_8016628 : CollatzResearch.WordTrace tailWord_8016628 prefixEnd_8016628 16939849350994922385935 := by
  unfold tailWord_8016628
  simp only [CollatzResearch.WordTrace]
  refine ⟨146195222000566680952709269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194926962667422241270279025 146195222000566680952709269)
  ·
    refine ⟨6852901031276563169658247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146195222000566680952709269 6852901031276563169658247)
    ·
      refine ⟨10279351546914844754487371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6852901031276563169658247 10279351546914844754487371)
      ·
        refine ⟨15419027320372267131731057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10279351546914844754487371 15419027320372267131731057)
        ·
          refine ⟨11564270490279200348798293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15419027320372267131731057 11564270490279200348798293)
          ·
            refine ⟨16939849350994922385935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11564270490279200348798293 16939849350994922385935)
            ·
              rfl

theorem cell23_8016628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 11].length) (baseStart_8016628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016628 prefixEnd_8016628 := by exact prefixLift 8016628
  have htrace : WordTrace (prefixWord ++ tailWord_8016628) baseStart_8016628 baseEnd_8016628 := by
    simpa [prefixWord, tailWord_8016628, baseEnd_8016628] using wordTrace_append hprefix tailTrace_8016628
  have hstable : (prefixWord ++ tailWord_8016628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016628).length < 2 ^ (prefixWord ++ tailWord_8016628).sum := by decide
  have hdescent : baseEnd_8016628 < baseStart_8016628 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016634 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5]
def baseStart_8016634 : Nat := 118140960795 + 8016634 * 2 ^ 59
def prefixEnd_8016634 : Nat := 4983230072969 + 3 ^ 40 * 8016634 * 2
def baseEnd_8016634 : Nat := 4116386473175693116307177

theorem tailTrace_8016634 : CollatzResearch.WordTrace tailWord_8016634 prefixEnd_8016634 4116386473175693116307177 := by
  unfold tailWord_8016634
  simp only [CollatzResearch.WordTrace]
  refine ⟨73097665709777906232534239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194927108559407749953424637 73097665709777906232534239)
  ·
    refine ⟨109646498564666859348801359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73097665709777906232534239 109646498564666859348801359)
    ·
      refine ⟨164469747847000289023202039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109646498564666859348801359 164469747847000289023202039)
      ·
        refine ⟨246704621770500433534803059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164469747847000289023202039 246704621770500433534803059)
        ·
          refine ⟨370056932655750650302204589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246704621770500433534803059 370056932655750650302204589)
          ·
            refine ⟨138771349745906493863326721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370056932655750650302204589 138771349745906493863326721)
            ·
              refine ⟨104078512309429870397495041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138771349745906493863326721 104078512309429870397495041)
              ·
                refine ⟨78058884232072402798121281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104078512309429870397495041 78058884232072402798121281)
                ·
                  refine ⟨58544163174054302098590961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78058884232072402798121281 58544163174054302098590961)
                  ·
                    refine ⟨43908122380540726573943221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58544163174054302098590961 43908122380540726573943221)
                    ·
                      refine ⟨4116386473175693116307177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43908122380540726573943221 4116386473175693116307177)
                      ·
                        rfl

theorem cell23_8016634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_8016634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016634 prefixEnd_8016634 := by exact prefixLift 8016634
  have htrace : WordTrace (prefixWord ++ tailWord_8016634) baseStart_8016634 baseEnd_8016634 := by
    simpa [prefixWord, tailWord_8016634, baseEnd_8016634] using wordTrace_append hprefix tailTrace_8016634
  have hstable : (prefixWord ++ tailWord_8016634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016634).length < 2 ^ (prefixWord ++ tailWord_8016634).sum := by decide
  have hdescent : baseEnd_8016634 < baseStart_8016634 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016648 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 3, 3, 2]
def baseStart_8016648 : Nat := 118140960795 + 8016648 * 2 ^ 59
def prefixEnd_8016648 : Nat := 4983230072969 + 3 ^ 40 * 8016648 * 2
def baseEnd_8016648 : Nat := 4116393661904856061532113

theorem tailTrace_8016648 : CollatzResearch.WordTrace tailWord_8016648 prefixEnd_8016648 4116393661904856061532113 := by
  unfold tailWord_8016648
  simp only [CollatzResearch.WordTrace]
  refine ⟨146195586730530452660573299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194927448974040603547431065 146195586730530452660573299)
  ·
    refine ⟨219293380095795678990859949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146195586730530452660573299 219293380095795678990859949)
    ·
      refine ⟨82235017535923379621572481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219293380095795678990859949 82235017535923379621572481)
      ·
        refine ⟨61676263151942534716179361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82235017535923379621572481 61676263151942534716179361)
        ·
          refine ⟨46257197363956901037134521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61676263151942534716179361 46257197363956901037134521)
          ·
            refine ⟨34692898022967675777850891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46257197363956901037134521 34692898022967675777850891)
            ·
              refine ⟨52039347034451513666776337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34692898022967675777850891 52039347034451513666776337)
              ·
                refine ⟨39029510275838635250082253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52039347034451513666776337 39029510275838635250082253)
                ·
                  refine ⟨14636066353439488218780845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39029510275838635250082253 14636066353439488218780845)
                  ·
                    refine ⟨5488524882539808082042817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14636066353439488218780845 5488524882539808082042817)
                    ·
                      refine ⟨4116393661904856061532113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5488524882539808082042817 4116393661904856061532113)
                      ·
                        rfl

theorem cell23_8016648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_8016648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016648 prefixEnd_8016648 := by exact prefixLift 8016648
  have htrace : WordTrace (prefixWord ++ tailWord_8016648) baseStart_8016648 baseEnd_8016648 := by
    simpa [prefixWord, tailWord_8016648, baseEnd_8016648] using wordTrace_append hprefix tailTrace_8016648
  have hstable : (prefixWord ++ tailWord_8016648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016648).length < 2 ^ (prefixWord ++ tailWord_8016648).sum := by decide
  have hdescent : baseEnd_8016648 < baseStart_8016648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016684 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 9]
def baseStart_8016684 : Nat := 118140960795 + 8016684 * 2 ^ 59
def prefixEnd_8016684 : Nat := 4983230072969 + 3 ^ 40 * 8016684 * 2
def baseEnd_8016684 : Nat := 457379127467601991186883

theorem tailTrace_8016684 : CollatzResearch.WordTrace tailWord_8016684 prefixEnd_8016684 457379127467601991186883 := by
  unfold tailWord_8016684
  simp only [CollatzResearch.WordTrace]
  refine ⟨146196243244465241734728553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194928324325953655646304737 146196243244465241734728553)
  ·
    refine ⟨109647182433348931301046415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146196243244465241734728553 109647182433348931301046415)
    ·
      refine ⟨164470773650023396951569623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109647182433348931301046415 164470773650023396951569623)
      ·
        refine ⟨246706160475035095427354435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164470773650023396951569623 246706160475035095427354435)
        ·
          refine ⟨370059240712552643141031653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246706160475035095427354435 370059240712552643141031653)
          ·
            refine ⟨69386107633603620588943435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 370059240712552643141031653 69386107633603620588943435)
            ·
              refine ⟨104079161450405430883415153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69386107633603620588943435 104079161450405430883415153)
              ·
                refine ⟨78059371087804073162561365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104079161450405430883415153 78059371087804073162561365)
                ·
                  refine ⟨457379127467601991186883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78059371087804073162561365 457379127467601991186883)
                  ·
                    rfl

theorem cell23_8016684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 9].length) (baseStart_8016684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016684 prefixEnd_8016684 := by exact prefixLift 8016684
  have htrace : WordTrace (prefixWord ++ tailWord_8016684) baseStart_8016684 baseEnd_8016684 := by
    simpa [prefixWord, tailWord_8016684, baseEnd_8016684] using wordTrace_append hprefix tailTrace_8016684
  have hstable : (prefixWord ++ tailWord_8016684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016684).length < 2 ^ (prefixWord ++ tailWord_8016684).sum := by decide
  have hdescent : baseEnd_8016684 < baseStart_8016684 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016691 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 4]
def baseStart_8016691 : Nat := 118140960795 + 8016691 * 2 ^ 59
def prefixEnd_8016691 : Nat := 4983230072969 + 3 ^ 40 * 8016691 * 2
def baseEnd_8016691 : Nat := 4116415741572999393294415

theorem tailTrace_8016691 : CollatzResearch.WordTrace tailWord_8016691 prefixEnd_8016691 4116415741572999393294415 := by
  unfold tailWord_8016691
  simp only [CollatzResearch.WordTrace]
  refine ⟨292392741799905123664961927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194928494533270082443307951 292392741799905123664961927)
  ·
    refine ⟨438589112699857685497442891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292392741799905123664961927 438589112699857685497442891)
    ·
      refine ⟨657883669049786528246164337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438589112699857685497442891 657883669049786528246164337)
      ·
        refine ⟨493412751787339896184623253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657883669049786528246164337 493412751787339896184623253)
        ·
          refine ⟨23128722740031557633654215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 493412751787339896184623253 23128722740031557633654215)
          ·
            refine ⟨34693084110047336450481323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23128722740031557633654215 34693084110047336450481323)
            ·
              refine ⟨52039626165071004675721985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34693084110047336450481323 52039626165071004675721985)
              ·
                refine ⟨39029719623803253506791489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52039626165071004675721985 39029719623803253506791489)
                ·
                  refine ⟨29272289717852440130093617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39029719623803253506791489 29272289717852440130093617)
                  ·
                    refine ⟨21954217288389330097570213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29272289717852440130093617 21954217288389330097570213)
                    ·
                      refine ⟨4116415741572999393294415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21954217288389330097570213 4116415741572999393294415)
                      ·
                        rfl

theorem cell23_8016691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 4].length) (baseStart_8016691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016691 prefixEnd_8016691 := by exact prefixLift 8016691
  have htrace : WordTrace (prefixWord ++ tailWord_8016691) baseStart_8016691 baseEnd_8016691 := by
    simpa [prefixWord, tailWord_8016691, baseEnd_8016691] using wordTrace_append hprefix tailTrace_8016691
  have hstable : (prefixWord ++ tailWord_8016691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016691).length < 2 ^ (prefixWord ++ tailWord_8016691).sum := by decide
  have hdescent : baseEnd_8016691 < baseStart_8016691 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016712 : List Nat := [2, 1, 3, 1, 1, 3, 5, 1, 2, 2, 2]
def baseStart_8016712 : Nat := 118140960795 + 8016712 * 2 ^ 59
def prefixEnd_8016712 : Nat := 4983230072969 + 3 ^ 40 * 8016712 * 2
def baseEnd_8016712 : Nat := 4116426524666743811131819

theorem tailTrace_8016712 : CollatzResearch.WordTrace tailWord_8016712 prefixEnd_8016712 4116426524666743811131819 := by
  unfold tailWord_8016712
  simp only [CollatzResearch.WordTrace]
  refine ⟨146196753866414522125738195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194929005155219362834317593 146196753866414522125738195)
  ·
    refine ⟨219295130799621783188607293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146196753866414522125738195 219295130799621783188607293)
    ·
      refine ⟨82235674049858168695727735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219295130799621783188607293 82235674049858168695727735)
      ·
        refine ⟨123353511074787253043591603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82235674049858168695727735 123353511074787253043591603)
        ·
          refine ⟨185030266612180879565387405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123353511074787253043591603 185030266612180879565387405)
          ·
            refine ⟨69386349979567829837020277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185030266612180879565387405 69386349979567829837020277)
            ·
              refine ⟨6504970310584484047220651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69386349979567829837020277 6504970310584484047220651)
              ·
                refine ⟨9757455465876726070830977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6504970310584484047220651 9757455465876726070830977)
                ·
                  refine ⟨7318091599407544553123233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9757455465876726070830977 7318091599407544553123233)
                  ·
                    refine ⟨5488568699555658414842425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7318091599407544553123233 5488568699555658414842425)
                    ·
                      refine ⟨4116426524666743811131819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5488568699555658414842425 4116426524666743811131819)
                      ·
                        rfl

theorem cell23_8016712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_8016712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016712 prefixEnd_8016712 := by exact prefixLift 8016712
  have htrace : WordTrace (prefixWord ++ tailWord_8016712) baseStart_8016712 baseEnd_8016712 := by
    simpa [prefixWord, tailWord_8016712, baseEnd_8016712] using wordTrace_append hprefix tailTrace_8016712
  have hstable : (prefixWord ++ tailWord_8016712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016712).length < 2 ^ (prefixWord ++ tailWord_8016712).sum := by decide
  have hdescent : baseEnd_8016712 < baseStart_8016712 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016758 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_8016758 : Nat := 118140960795 + 8016758 * 2 ^ 59
def prefixEnd_8016758 : Nat := 4983230072969 + 3 ^ 40 * 8016758 * 2
def baseEnd_8016758 : Nat := 4116450144776850631156607

theorem tailTrace_8016758 : CollatzResearch.WordTrace tailWord_8016758 prefixEnd_8016758 4116450144776850631156607 := by
  unfold tailWord_8016758
  simp only [CollatzResearch.WordTrace]
  refine ⟨18274699093166399631728183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194930123660441596071767285 18274699093166399631728183)
  ·
    refine ⟨27412048639749599447592275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18274699093166399631728183 27412048639749599447592275)
    ·
      refine ⟨41118072959624399171388413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27412048639749599447592275 41118072959624399171388413)
      ·
        refine ⟨15419277359859149689270655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41118072959624399171388413 15419277359859149689270655)
        ·
          refine ⟨23128916039788724533905983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15419277359859149689270655 23128916039788724533905983)
          ·
            refine ⟨34693374059683086800858975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23128916039788724533905983 34693374059683086800858975)
            ·
              refine ⟨52040061089524630201288463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34693374059683086800858975 52040061089524630201288463)
              ·
                refine ⟨78060091634286945301932695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52040061089524630201288463 78060091634286945301932695)
                ·
                  refine ⟨117090137451430417952899043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78060091634286945301932695 117090137451430417952899043)
                  ·
                    refine ⟨175635206177145626929348565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117090137451430417952899043 175635206177145626929348565)
                    ·
                      refine ⟨4116450144776850631156607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175635206177145626929348565 4116450144776850631156607)
                      ·
                        rfl

theorem cell23_8016758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_8016758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016758 prefixEnd_8016758 := by exact prefixLift 8016758
  have htrace : WordTrace (prefixWord ++ tailWord_8016758) baseStart_8016758 baseEnd_8016758 := by
    simpa [prefixWord, tailWord_8016758, baseEnd_8016758] using wordTrace_append hprefix tailTrace_8016758
  have hstable : (prefixWord ++ tailWord_8016758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016758).length < 2 ^ (prefixWord ++ tailWord_8016758).sum := by decide
  have hdescent : baseEnd_8016758 < baseStart_8016758 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016869 : List Nat := [1, 3, 1, 6, 1, 1, 2, 1, 3, 1, 3]
def baseStart_8016869 : Nat := 118140960795 + 8016869 * 2 ^ 59
def prefixEnd_8016869 : Nat := 4983230072969 + 3 ^ 40 * 8016869 * 2
def baseEnd_8016869 : Nat := 4116507141129499696868597

theorem tailTrace_8016869 : CollatzResearch.WordTrace tailWord_8016869 prefixEnd_8016869 4116507141129499696868597 := by
  unfold tailWord_8016869
  simp only [CollatzResearch.WordTrace]
  refine ⟨292399233993260260064941661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194932822662173506709961107 292399233993260260064941661)
  ·
    refine ⟨109649712747472597524353123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292399233993260260064941661 109649712747472597524353123)
    ·
      refine ⟨164474569121208896286529685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109649712747472597524353123 164474569121208896286529685)
      ·
        refine ⟨7709745427556667013431079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 164474569121208896286529685 7709745427556667013431079)
        ·
          refine ⟨11564618141335000520146619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7709745427556667013431079 11564618141335000520146619)
          ·
            refine ⟨17346927212002500780219929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11564618141335000520146619 17346927212002500780219929)
            ·
              refine ⟨13010195409001875585164947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17346927212002500780219929 13010195409001875585164947)
              ·
                refine ⟨19515293113502813377747421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13010195409001875585164947 19515293113502813377747421)
                ·
                  refine ⟨7318234917563555016655283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19515293113502813377747421 7318234917563555016655283)
                  ·
                    refine ⟨10977352376345332524982925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7318234917563555016655283 10977352376345332524982925)
                    ·
                      refine ⟨4116507141129499696868597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10977352376345332524982925 4116507141129499696868597)
                      ·
                        rfl

theorem cell23_8016869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_8016869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016869 prefixEnd_8016869 := by exact prefixLift 8016869
  have htrace : WordTrace (prefixWord ++ tailWord_8016869) baseStart_8016869 baseEnd_8016869 := by
    simpa [prefixWord, tailWord_8016869, baseEnd_8016869] using wordTrace_append hprefix tailTrace_8016869
  have hstable : (prefixWord ++ tailWord_8016869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016869).length < 2 ^ (prefixWord ++ tailWord_8016869).sum := by decide
  have hdescent : baseEnd_8016869 < baseStart_8016869 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016892 : List Nat := [2, 2, 2, 1, 2, 3, 2, 2, 3, 2, 2]
def baseStart_8016892 : Nat := 118140960795 + 8016892 * 2 ^ 59
def prefixEnd_8016892 : Nat := 4983230072969 + 3 ^ 40 * 8016892 * 2
def baseEnd_8016892 : Nat := 4116518951184553106880991

theorem tailTrace_8016892 : CollatzResearch.WordTrace tailWord_8016892 prefixEnd_8016892 4116518951184553106880991 := by
  unfold tailWord_8016892
  simp only [CollatzResearch.WordTrace]
  refine ⟨146200036436088467496514465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194933381914784623328685953 146200036436088467496514465)
  ·
    refine ⟨109650027327066350622385849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146200036436088467496514465 109650027327066350622385849)
    ·
      refine ⟨82237520495299762966789387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109650027327066350622385849 82237520495299762966789387)
      ·
        refine ⟨123356280742949644450184081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82237520495299762966789387 123356280742949644450184081)
        ·
          refine ⟨92517210557212233337638061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123356280742949644450184081 92517210557212233337638061)
          ·
            refine ⟨34693953958954587501614273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92517210557212233337638061 34693953958954587501614273)
            ·
              refine ⟨26020465469215940626210705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34693953958954587501614273 26020465469215940626210705)
              ·
                refine ⟨19515349101911955469658029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26020465469215940626210705 19515349101911955469658029)
                ·
                  refine ⟨7318255913216983301121761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19515349101911955469658029 7318255913216983301121761)
                  ·
                    refine ⟨5488691934912737475841321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7318255913216983301121761 5488691934912737475841321)
                    ·
                      refine ⟨4116518951184553106880991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5488691934912737475841321 4116518951184553106880991)
                      ·
                        rfl

theorem cell23_8016892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_8016892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016892 prefixEnd_8016892 := by exact prefixLift 8016892
  have htrace : WordTrace (prefixWord ++ tailWord_8016892) baseStart_8016892 baseEnd_8016892 := by
    simpa [prefixWord, tailWord_8016892, baseEnd_8016892] using wordTrace_append hprefix tailTrace_8016892
  have hstable : (prefixWord ++ tailWord_8016892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016892).length < 2 ^ (prefixWord ++ tailWord_8016892).sum := by decide
  have hdescent : baseEnd_8016892 < baseStart_8016892 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016911 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 6, 7]
def baseStart_8016911 : Nat := 118140960795 + 8016911 * 2 ^ 59
def prefixEnd_8016911 : Nat := 4983230072969 + 3 ^ 40 * 8016911 * 2
def baseEnd_8016911 : Nat := 1372176235772329510847801

theorem tailTrace_8016911 : CollatzResearch.WordTrace tailWord_8016911 prefixEnd_8016911 1372176235772329510847801 := by
  unfold tailWord_8016911
  simp only [CollatzResearch.WordTrace]
  refine ⟨292400765859108101237970587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194933843906072067491980391 292400765859108101237970587)
  ·
    refine ⟨438601148788662151856955881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292400765859108101237970587 438601148788662151856955881)
    ·
      refine ⟨328950861591496613892716911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438601148788662151856955881 328950861591496613892716911)
      ·
        refine ⟨493426292387244920839075367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328950861591496613892716911 493426292387244920839075367)
        ·
          refine ⟨740139438580867381258613051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493426292387244920839075367 740139438580867381258613051)
          ·
            refine ⟨1110209157871301071887919577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740139438580867381258613051 1110209157871301071887919577)
            ·
              refine ⟨832656868403475803915939683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1110209157871301071887919577 832656868403475803915939683)
              ·
                refine ⟨1248985302605213705873909525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 832656868403475803915939683 1248985302605213705873909525)
                ·
                  refine ⟨58546186059619392462839509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1248985302605213705873909525 58546186059619392462839509)
                  ·
                    refine ⟨1372176235772329510847801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58546186059619392462839509 1372176235772329510847801)
                    ·
                      rfl

theorem cell23_8016911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 7].length) (baseStart_8016911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016911 prefixEnd_8016911 := by exact prefixLift 8016911
  have htrace : WordTrace (prefixWord ++ tailWord_8016911) baseStart_8016911 baseEnd_8016911 := by
    simpa [prefixWord, tailWord_8016911, baseEnd_8016911] using wordTrace_append hprefix tailTrace_8016911
  have hstable : (prefixWord ++ tailWord_8016911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016911).length < 2 ^ (prefixWord ++ tailWord_8016911).sum := by decide
  have hdescent : baseEnd_8016911 < baseStart_8016911 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016952 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 3, 3, 2]
def baseStart_8016952 : Nat := 118140960795 + 8016952 * 2 ^ 59
def prefixEnd_8016952 : Nat := 4983230072969 + 3 ^ 40 * 8016952 * 2
def baseEnd_8016952 : Nat := 4116549760023822872130715

theorem tailTrace_8016952 : CollatzResearch.WordTrace tailWord_8016952 prefixEnd_8016952 4116549760023822872130715 := by
  unfold tailWord_8016952
  simp only [CollatzResearch.WordTrace]
  refine ⟨146201130625979782620106555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194934840834639710160142073 146201130625979782620106555)
  ·
    refine ⟨219301695938969673930159833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146201130625979782620106555 219301695938969673930159833)
    ·
      refine ⟨164476271954227255447619875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219301695938969673930159833 164476271954227255447619875)
      ·
        refine ⟨246714407931340883171429813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164476271954227255447619875 246714407931340883171429813)
        ·
          refine ⟨23129475743563207797321545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 246714407931340883171429813 23129475743563207797321545)
          ·
            refine ⟨17347106807672405847991159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23129475743563207797321545 17347106807672405847991159)
            ·
              refine ⟨26020660211508608771986739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17347106807672405847991159 26020660211508608771986739)
              ·
                refine ⟨39030990317262913157980109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26020660211508608771986739 39030990317262913157980109)
                ·
                  refine ⟨14636621368973592434242541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39030990317262913157980109 14636621368973592434242541)
                  ·
                    refine ⟨5488733013365097162840953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14636621368973592434242541 5488733013365097162840953)
                    ·
                      refine ⟨4116549760023822872130715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5488733013365097162840953 4116549760023822872130715)
                      ·
                        rfl

theorem cell23_8016952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 3, 3, 2].length) (baseStart_8016952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016952 prefixEnd_8016952 := by exact prefixLift 8016952
  have htrace : WordTrace (prefixWord ++ tailWord_8016952) baseStart_8016952 baseEnd_8016952 := by
    simpa [prefixWord, tailWord_8016952, baseEnd_8016952] using wordTrace_append hprefix tailTrace_8016952
  have hstable : (prefixWord ++ tailWord_8016952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016952).length < 2 ^ (prefixWord ++ tailWord_8016952).sum := by decide
  have hdescent : baseEnd_8016952 < baseStart_8016952 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016965 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 3, 4, 2]
def baseStart_8016965 : Nat := 118140960795 + 8016965 * 2 ^ 59
def prefixEnd_8016965 : Nat := 4983230072969 + 3 ^ 40 * 8016965 * 2
def baseEnd_8016965 : Nat := 4116556435272331321268155

theorem tailTrace_8016965 : CollatzResearch.WordTrace tailWord_8016965 prefixEnd_8016965 4116556435272331321268155 := by
  unfold tailWord_8016965
  simp only [CollatzResearch.WordTrace]
  refine ⟨292402735400912468460436349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194935156933941645640290899 292402735400912468460436349)
  ·
    refine ⟨109651025775342175672663631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292402735400912468460436349 109651025775342175672663631)
    ·
      refine ⟨164476538663013263508995447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109651025775342175672663631 164476538663013263508995447)
      ·
        refine ⟨246714807994519895263493171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164476538663013263508995447 246714807994519895263493171)
        ·
          refine ⟨370072211991779842895239757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246714807994519895263493171 370072211991779842895239757)
          ·
            refine ⟨138777079496917441085714909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370072211991779842895239757 138777079496917441085714909)
            ·
              refine ⟨52041404811344040407143091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138777079496917441085714909 52041404811344040407143091)
              ·
                refine ⟨78062107217016060610714637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52041404811344040407143091 78062107217016060610714637)
                ·
                  refine ⟨29273290206381022729017989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78062107217016060610714637 29273290206381022729017989)
                  ·
                    refine ⟨5488741913696441761690873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29273290206381022729017989 5488741913696441761690873)
                    ·
                      refine ⟨4116556435272331321268155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5488741913696441761690873 4116556435272331321268155)
                      ·
                        rfl

theorem cell23_8016965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 4, 2].length) (baseStart_8016965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016965 prefixEnd_8016965 := by exact prefixLift 8016965
  have htrace : WordTrace (prefixWord ++ tailWord_8016965) baseStart_8016965 baseEnd_8016965 := by
    simpa [prefixWord, tailWord_8016965, baseEnd_8016965] using wordTrace_append hprefix tailTrace_8016965
  have hstable : (prefixWord ++ tailWord_8016965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016965).length < 2 ^ (prefixWord ++ tailWord_8016965).sum := by decide
  have hdescent : baseEnd_8016965 < baseStart_8016965 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016968 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 2, 1, 5]
def baseStart_8016968 : Nat := 118140960795 + 8016968 * 2 ^ 59
def prefixEnd_8016968 : Nat := 4983230072969 + 3 ^ 40 * 8016968 * 2
def baseEnd_8016968 : Nat := 4116557975714294809530641

theorem tailTrace_8016968 : CollatzResearch.WordTrace tailWord_8016968 prefixEnd_8016968 4116557975714294809530641 := by
  unfold tailWord_8016968
  simp only [CollatzResearch.WordTrace]
  refine ⟨146201422409950799986397779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194935229879934399981863705 146201422409950799986397779)
  ·
    refine ⟨219302133614926199979596669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146201422409950799986397779 219302133614926199979596669)
    ·
      refine ⟨82238300105597324992348751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219302133614926199979596669 82238300105597324992348751)
      ·
        refine ⟨123357450158395987488523127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82238300105597324992348751 123357450158395987488523127)
        ·
          refine ⟨185036175237593981232784691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123357450158395987488523127 185036175237593981232784691)
          ·
            refine ⟨277554262856390971849177037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185036175237593981232784691 277554262856390971849177037)
            ·
              refine ⟨104082848571146614443441389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277554262856390971849177037 104082848571146614443441389)
              ·
                refine ⟨39031068214179980416290521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104082848571146614443441389 39031068214179980416290521)
                ·
                  refine ⟨29273301160634985312217891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39031068214179980416290521 29273301160634985312217891)
                  ·
                    refine ⟨43909951740952477968326837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29273301160634985312217891 43909951740952477968326837)
                    ·
                      refine ⟨4116557975714294809530641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43909951740952477968326837 4116557975714294809530641)
                      ·
                        rfl

theorem cell23_8016968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_8016968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016968 prefixEnd_8016968 := by exact prefixLift 8016968
  have htrace : WordTrace (prefixWord ++ tailWord_8016968) baseStart_8016968 baseEnd_8016968 := by
    simpa [prefixWord, tailWord_8016968, baseEnd_8016968] using wordTrace_append hprefix tailTrace_8016968
  have hstable : (prefixWord ++ tailWord_8016968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016968).length < 2 ^ (prefixWord ++ tailWord_8016968).sum := by decide
  have hdescent : baseEnd_8016968 < baseStart_8016968 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8016999 : List Nat := [1, 1, 5, 1, 1, 3, 2, 3, 2, 2, 2]
def baseStart_8016999 : Nat := 118140960795 + 8016999 * 2 ^ 59
def prefixEnd_8016999 : Nat := 4983230072969 + 3 ^ 40 * 8016999 * 2
def baseEnd_8016999 : Nat := 4116573893614584188242999

theorem tailTrace_8016999 : CollatzResearch.WordTrace tailWord_8016999 prefixEnd_8016999 4116573893614584188242999 := by
  unfold tailWord_8016999
  simp only [CollatzResearch.WordTrace]
  refine ⟨292403975482789292267174051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194935983655192861511449367 292403975482789292267174051)
  ·
    refine ⟨438605963224183938400761077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292403975482789292267174051 438605963224183938400761077)
    ·
      refine ⟨41119309052267244225071351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 438605963224183938400761077 41119309052267244225071351)
      ·
        refine ⟨61678963578400866337607027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41119309052267244225071351 61678963578400866337607027)
        ·
          refine ⟨92518445367601299506410541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61678963578400866337607027 92518445367601299506410541)
          ·
            refine ⟨34694417012850487314903953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92518445367601299506410541 34694417012850487314903953)
            ·
              refine ⟨26020812759637865486177965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34694417012850487314903953 26020812759637865486177965)
              ·
                refine ⟨9757804784864199557316737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26020812759637865486177965 9757804784864199557316737)
                ·
                  refine ⟨7318353588648149667987553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9757804784864199557316737 7318353588648149667987553)
                  ·
                    refine ⟨5488765191486112250990665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7318353588648149667987553 5488765191486112250990665)
                    ·
                      refine ⟨4116573893614584188242999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5488765191486112250990665 4116573893614584188242999)
                      ·
                        rfl

theorem cell23_8016999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_8016999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8016999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8016999 prefixEnd_8016999 := by exact prefixLift 8016999
  have htrace : WordTrace (prefixWord ++ tailWord_8016999) baseStart_8016999 baseEnd_8016999 := by
    simpa [prefixWord, tailWord_8016999, baseEnd_8016999] using wordTrace_append hprefix tailTrace_8016999
  have hstable : (prefixWord ++ tailWord_8016999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8016999).length < 2 ^ (prefixWord ++ tailWord_8016999).sum := by decide
  have hdescent : baseEnd_8016999 < baseStart_8016999 := by decide
  rcases family_descends (prefixWord ++ tailWord_8016999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017005 : List Nat := [1, 5, 1, 1, 2, 3, 1, 2, 7]
def baseStart_8017005 : Nat := 118140960795 + 8017005 * 2 ^ 59
def prefixEnd_8017005 : Nat := 4983230072969 + 3 ^ 40 * 8017005 * 2
def baseEnd_8017005 : Nat := 457397441610945684974219

theorem tailTrace_8017005 : CollatzResearch.WordTrace tailWord_8017005 prefixEnd_8017005 457397441610945684974219 := by
  unfold tailWord_8017005
  simp only [CollatzResearch.WordTrace]
  refine ⟨292404194320767555291892469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194936129547178370194594979 292404194320767555291892469)
  ·
    refine ⟨27412893217571958308614919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 292404194320767555291892469 27412893217571958308614919)
    ·
      refine ⟨41119339826357937462922379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27412893217571958308614919 41119339826357937462922379)
      ·
        refine ⟨61679009739536906194383569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41119339826357937462922379 61679009739536906194383569)
        ·
          refine ⟨46259257304652679645787677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61679009739536906194383569 46259257304652679645787677)
          ·
            refine ⟨17347221489244754867170379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46259257304652679645787677 17347221489244754867170379)
            ·
              refine ⟨26020832233867132300755569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17347221489244754867170379 26020832233867132300755569)
              ·
                refine ⟨19515624175400349225566677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26020832233867132300755569 19515624175400349225566677)
                ·
                  refine ⟨457397441610945684974219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19515624175400349225566677 457397441610945684974219)
                  ·
                    rfl

theorem cell23_8017005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_8017005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017005 prefixEnd_8017005 := by exact prefixLift 8017005
  have htrace : WordTrace (prefixWord ++ tailWord_8017005) baseStart_8017005 baseEnd_8017005 := by
    simpa [prefixWord, tailWord_8017005, baseEnd_8017005] using wordTrace_append hprefix tailTrace_8017005
  have hstable : (prefixWord ++ tailWord_8017005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017005).length < 2 ^ (prefixWord ++ tailWord_8017005).sum := by decide
  have hdescent : baseEnd_8017005 < baseStart_8017005 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017068 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 6]
def baseStart_8017068 : Nat := 118140960795 + 8017068 * 2 ^ 59
def prefixEnd_8017068 : Nat := 4983230072969 + 3 ^ 40 * 8017068 * 2
def baseEnd_8017068 : Nat := 4116609323779744418280181

theorem tailTrace_8017068 : CollatzResearch.WordTrace tailWord_8017068 prefixEnd_8017068 4116609323779744418280181 := by
  unfold tailWord_8017068
  simp only [CollatzResearch.WordTrace]
  refine ⟨146203246059769658525717929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194937661413026211367623905 146203246059769658525717929)
  ·
    refine ⟨109652434544827243894288447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146203246059769658525717929 109652434544827243894288447)
    ·
      refine ⟨164478651817240865841432671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109652434544827243894288447 164478651817240865841432671)
      ·
        refine ⟨246717977725861298762149007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164478651817240865841432671 246717977725861298762149007)
        ·
          refine ⟨370076966588791948143223511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246717977725861298762149007 370076966588791948143223511)
          ·
            refine ⟨555115449883187922214835267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370076966588791948143223511 555115449883187922214835267)
            ·
              refine ⟨832673174824781883322252901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555115449883187922214835267 832673174824781883322252901)
              ·
                refine ⟨156126220279646603122922419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 832673174824781883322252901 156126220279646603122922419)
                ·
                  refine ⟨234189330419469904684383629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156126220279646603122922419 234189330419469904684383629)
                  ·
                    refine ⟨87820998907301214256643861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 234189330419469904684383629 87820998907301214256643861)
                    ·
                      refine ⟨4116609323779744418280181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87820998907301214256643861 4116609323779744418280181)
                      ·
                        rfl

theorem cell23_8017068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_8017068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017068 prefixEnd_8017068 := by exact prefixLift 8017068
  have htrace : WordTrace (prefixWord ++ tailWord_8017068) baseStart_8017068 baseEnd_8017068 := by
    simpa [prefixWord, tailWord_8017068, baseEnd_8017068] using wordTrace_append hprefix tailTrace_8017068
  have hstable : (prefixWord ++ tailWord_8017068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017068).length < 2 ^ (prefixWord ++ tailWord_8017068).sum := by decide
  have hdescent : baseEnd_8017068 < baseStart_8017068 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017075 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 3]
def baseStart_8017075 : Nat := 118140960795 + 8017075 * 2 ^ 59
def prefixEnd_8017075 : Nat := 4983230072969 + 3 ^ 40 * 8017075 * 2
def baseEnd_8017075 : Nat := 4116612918144325890892649

theorem tailTrace_8017075 : CollatzResearch.WordTrace tailWord_8017075 prefixEnd_8017075 4116612918144325890892649 := by
  unfold tailWord_8017075
  simp only [CollatzResearch.WordTrace]
  refine ⟨292406747430513957246940679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194937831620342638164627119 292406747430513957246940679)
  ·
    refine ⟨438610121145770935870411019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292406747430513957246940679 438610121145770935870411019)
    ·
      refine ⟨657915181718656403805616529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438610121145770935870411019 657915181718656403805616529)
      ·
        refine ⟨493436386288992302854212397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657915181718656403805616529 493436386288992302854212397)
        ·
          refine ⟨185038644858372113570329649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 493436386288992302854212397 185038644858372113570329649)
          ·
            refine ⟨138778983643779085177747237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185038644858372113570329649 138778983643779085177747237)
            ·
              refine ⟨26021059433208578470827607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138778983643779085177747237 26021059433208578470827607)
              ·
                refine ⟨39031589149812867706241411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26021059433208578470827607 39031589149812867706241411)
                ·
                  refine ⟨58547383724719301559362117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39031589149812867706241411 58547383724719301559362117)
                  ·
                    refine ⟨10977634448384869042380397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58547383724719301559362117 10977634448384869042380397)
                    ·
                      refine ⟨4116612918144325890892649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10977634448384869042380397 4116612918144325890892649)
                      ·
                        rfl

theorem cell23_8017075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 3].length) (baseStart_8017075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017075 prefixEnd_8017075 := by exact prefixLift 8017075
  have htrace : WordTrace (prefixWord ++ tailWord_8017075) baseStart_8017075 baseEnd_8017075 := by
    simpa [prefixWord, tailWord_8017075, baseEnd_8017075] using wordTrace_append hprefix tailTrace_8017075
  have hstable : (prefixWord ++ tailWord_8017075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017075).length < 2 ^ (prefixWord ++ tailWord_8017075).sum := by decide
  have hdescent : baseEnd_8017075 < baseStart_8017075 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017089 : List Nat := [1, 2, 6, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_8017089 : Nat := 118140960795 + 8017089 * 2 ^ 59
def prefixEnd_8017089 : Nat := 4983230072969 + 3 ^ 40 * 8017089 * 2
def baseEnd_8017089 : Nat := 4116620106873488836117585

theorem tailTrace_8017089 : CollatzResearch.WordTrace tailWord_8017089 prefixEnd_8017089 4116620106873488836117585 := by
  unfold tailWord_8017089
  simp only [CollatzResearch.WordTrace]
  refine ⟨292407258052463237637950321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194938172034975491758633547 292407258052463237637950321)
  ·
    refine ⟨219305443539347428228462741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292407258052463237637950321 219305443539347428228462741)
    ·
      refine ⟨10279942665906910698209191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 219305443539347428228462741 10279942665906910698209191)
      ·
        refine ⟨15419913998860366047313787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10279942665906910698209191 15419913998860366047313787)
        ·
          refine ⟨23129870998290549070970681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15419913998860366047313787 23129870998290549070970681)
          ·
            refine ⟨17347403248717911803228011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23129870998290549070970681 17347403248717911803228011)
            ·
              refine ⟨26021104873076867704842017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17347403248717911803228011 26021104873076867704842017)
              ·
                refine ⟨19515828654807650778631513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26021104873076867704842017 19515828654807650778631513)
                ·
                  refine ⟨14636871491105738083973635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19515828654807650778631513 14636871491105738083973635)
                  ·
                    refine ⟨21955307236658607125960453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14636871491105738083973635 21955307236658607125960453)
                    ·
                      refine ⟨4116620106873488836117585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21955307236658607125960453 4116620106873488836117585)
                      ·
                        rfl

theorem cell23_8017089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_8017089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017089 prefixEnd_8017089 := by exact prefixLift 8017089
  have htrace : WordTrace (prefixWord ++ tailWord_8017089) baseStart_8017089 baseEnd_8017089 := by
    simpa [prefixWord, tailWord_8017089, baseEnd_8017089] using wordTrace_append hprefix tailTrace_8017089
  have hstable : (prefixWord ++ tailWord_8017089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017089).length < 2 ^ (prefixWord ++ tailWord_8017089).sum := by decide
  have hdescent : baseEnd_8017089 < baseStart_8017089 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017112 : List Nat := [2, 1, 2, 2, 5, 1, 1, 3, 6]
def baseStart_8017112 : Nat := 118140960795 + 8017112 * 2 ^ 59
def prefixEnd_8017112 : Nat := 4983230072969 + 3 ^ 40 * 8017112 * 2
def baseEnd_8017112 : Nat := 457403546325393582903331

theorem tailTrace_8017112 : CollatzResearch.WordTrace tailWord_8017112 prefixEnd_8017112 457403546325393582903331 := by
  unfold tailWord_8017112
  simp only [CollatzResearch.WordTrace]
  refine ⟨146204048465689956283018795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194938731287586608377358393 146204048465689956283018795)
  ·
    refine ⟨219306072698534934424528193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146204048465689956283018795 219306072698534934424528193)
    ·
      refine ⟨164479554523901200818396145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219306072698534934424528193 164479554523901200818396145)
      ·
        refine ⟨123359665892925900613797109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164479554523901200818396145 123359665892925900613797109)
        ·
          refine ⟨11564968677461803182543479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123359665892925900613797109 11564968677461803182543479)
          ·
            refine ⟨17347453016192704773815219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11564968677461803182543479 17347453016192704773815219)
            ·
              refine ⟨26021179524289057160722829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17347453016192704773815219 26021179524289057160722829)
              ·
                refine ⟨9757942321608396435271061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26021179524289057160722829 9757942321608396435271061)
                ·
                  refine ⟨457403546325393582903331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9757942321608396435271061 457403546325393582903331)
                  ·
                    rfl

theorem cell23_8017112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 6].length) (baseStart_8017112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017112 prefixEnd_8017112 := by exact prefixLift 8017112
  have htrace : WordTrace (prefixWord ++ tailWord_8017112) baseStart_8017112 baseEnd_8017112 := by
    simpa [prefixWord, tailWord_8017112, baseEnd_8017112] using wordTrace_append hprefix tailTrace_8017112
  have hstable : (prefixWord ++ tailWord_8017112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017112).length < 2 ^ (prefixWord ++ tailWord_8017112).sum := by decide
  have hdescent : baseEnd_8017112 < baseStart_8017112 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017162 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2]
def baseStart_8017162 : Nat := 118140960795 + 8017162 * 2 ^ 59
def prefixEnd_8017162 : Nat := 4983230072969 + 3 ^ 40 * 8017162 * 2
def baseEnd_8017162 : Nat := 4116657590961267050504749

theorem tailTrace_8017162 : CollatzResearch.WordTrace tailWord_8017162 prefixEnd_8017162 4116657590961267050504749 := by
  unfold tailWord_8017162
  simp only [CollatzResearch.WordTrace]
  refine ⟨73102480145299692776339435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194939947054132514070238493 73102480145299692776339435)
  ·
    refine ⟨109653720217949539164509153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73102480145299692776339435 109653720217949539164509153)
    ·
      refine ⟨82240290163462154373381865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109653720217949539164509153 82240290163462154373381865)
      ·
        refine ⟨61680217622596615780036399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82240290163462154373381865 61680217622596615780036399)
        ·
          refine ⟨92520326433894923670054599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61680217622596615780036399 92520326433894923670054599)
          ·
            refine ⟨138780489650842385505081899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92520326433894923670054599 138780489650842385505081899)
            ·
              refine ⟨208170734476263578257622849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138780489650842385505081899 208170734476263578257622849)
              ·
                refine ⟨156128050857197683693217137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208170734476263578257622849 156128050857197683693217137)
                ·
                  refine ⟨117096038142898262769912853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156128050857197683693217137 117096038142898262769912853)
                  ·
                    refine ⟨5488876787948356067339665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117096038142898262769912853 5488876787948356067339665)
                    ·
                      refine ⟨4116657590961267050504749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5488876787948356067339665 4116657590961267050504749)
                      ·
                        rfl

theorem cell23_8017162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_8017162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017162 prefixEnd_8017162 := by exact prefixLift 8017162
  have htrace : WordTrace (prefixWord ++ tailWord_8017162) baseStart_8017162 baseEnd_8017162 := by
    simpa [prefixWord, tailWord_8017162, baseEnd_8017162] using wordTrace_append hprefix tailTrace_8017162
  have hstable : (prefixWord ++ tailWord_8017162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017162).length < 2 ^ (prefixWord ++ tailWord_8017162).sum := by decide
  have hdescent : baseEnd_8017162 < baseStart_8017162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017183 : List Nat := [1, 1, 2, 4, 5, 1, 1, 1, 2, 3, 2]
def baseStart_8017183 : Nat := 118140960795 + 8017183 * 2 ^ 59
def prefixEnd_8017183 : Nat := 4983230072969 + 3 ^ 40 * 8017183 * 2
def baseEnd_8017183 : Nat := 4116668374055011468342153

theorem tailTrace_8017183 : CollatzResearch.WordTrace tailWord_8017183 prefixEnd_8017183 4116668374055011468342153 := by
  unfold tailWord_8017183
  simp only [CollatzResearch.WordTrace]
  refine ⟨292410686514122691691872203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194940457676081794461248135 292410686514122691691872203)
  ·
    refine ⟨438616029771184037537808305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292410686514122691691872203 438616029771184037537808305)
    ·
      refine ⟨328962022328388028153356229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438616029771184037537808305 328962022328388028153356229)
      ·
        refine ⟨61680379186572755278754293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328962022328388028153356229 61680379186572755278754293)
        ·
          refine ⟨5782535548741195807383215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61680379186572755278754293 5782535548741195807383215)
          ·
            refine ⟨8673803323111793711074823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5782535548741195807383215 8673803323111793711074823)
            ·
              refine ⟨13010704984667690566612235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8673803323111793711074823 13010704984667690566612235)
              ·
                refine ⟨19516057477001535849918353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13010704984667690566612235 19516057477001535849918353)
                ·
                  refine ⟨14637043107751151887438765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19516057477001535849918353 14637043107751151887438765)
                  ·
                    refine ⟨5488891165406681957789537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14637043107751151887438765 5488891165406681957789537)
                    ·
                      refine ⟨4116668374055011468342153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5488891165406681957789537 4116668374055011468342153)
                      ·
                        rfl

theorem cell23_8017183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_8017183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017183 prefixEnd_8017183 := by exact prefixLift 8017183
  have htrace : WordTrace (prefixWord ++ tailWord_8017183) baseStart_8017183 baseEnd_8017183 := by
    simpa [prefixWord, tailWord_8017183, baseEnd_8017183] using wordTrace_append hprefix tailTrace_8017183
  have hstable : (prefixWord ++ tailWord_8017183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017183).length < 2 ^ (prefixWord ++ tailWord_8017183).sum := by decide
  have hdescent : baseEnd_8017183 < baseStart_8017183 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017319 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_8017319 : Nat := 118140960795 + 8017319 * 2 ^ 59
def prefixEnd_8017319 : Nat := 4983230072969 + 3 ^ 40 * 8017319 * 2
def baseEnd_8017319 : Nat := 4116738207424022936241527

theorem tailTrace_8017319 : CollatzResearch.WordTrace tailWord_8017319 prefixEnd_8017319 4116738207424022936241527 := by
  unfold tailWord_8017319
  simp only [CollatzResearch.WordTrace]
  refine ⟨292415646841629986918823011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194943764561086657945882007 292415646841629986918823011)
  ·
    refine ⟨438623470262444980378234517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292415646841629986918823011 438623470262444980378234517)
    ·
      refine ⟨20560475168552108455229743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 438623470262444980378234517 20560475168552108455229743)
      ·
        refine ⟨30840712752828162682844615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20560475168552108455229743 30840712752828162682844615)
        ·
          refine ⟨46261069129242244024266923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30840712752828162682844615 46261069129242244024266923)
          ·
            refine ⟨69391603693863366036400385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46261069129242244024266923 69391603693863366036400385)
            ·
              refine ⟨52043702770397524527300289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69391603693863366036400385 52043702770397524527300289)
              ·
                refine ⟨39032777077798143395475217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52043702770397524527300289 39032777077798143395475217)
                ·
                  refine ⟨29274582808348607546606413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39032777077798143395475217 29274582808348607546606413)
                  ·
                    refine ⟨10977968553130727829977405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29274582808348607546606413 10977968553130727829977405)
                    ·
                      refine ⟨4116738207424022936241527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10977968553130727829977405 4116738207424022936241527)
                      ·
                        rfl

theorem cell23_8017319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_8017319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017319 prefixEnd_8017319 := by exact prefixLift 8017319
  have htrace : WordTrace (prefixWord ++ tailWord_8017319) baseStart_8017319 baseEnd_8017319 := by
    simpa [prefixWord, tailWord_8017319, baseEnd_8017319] using wordTrace_append hprefix tailTrace_8017319
  have hstable : (prefixWord ++ tailWord_8017319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017319).length < 2 ^ (prefixWord ++ tailWord_8017319).sum := by decide
  have hdescent : baseEnd_8017319 < baseStart_8017319 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017329 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 1, 7, 2]
def baseStart_8017329 : Nat := 118140960795 + 8017329 * 2 ^ 59
def prefixEnd_8017329 : Nat := 4983230072969 + 3 ^ 40 * 8017329 * 2
def baseEnd_8017329 : Nat := 4116743342230567897116481

theorem tailTrace_8017329 : CollatzResearch.WordTrace tailWord_8017329 prefixEnd_8017329 4116743342230567897116481 := by
  unfold tailWord_8017329
  simp only [CollatzResearch.WordTrace]
  refine ⟨292416011571593758626687041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194944007714395839084458027 292416011571593758626687041)
  ·
    refine ⟨219312008678695318970015281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292416011571593758626687041 219312008678695318970015281)
    ·
      refine ⟨164484006509021489227511461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219312008678695318970015281 164484006509021489227511461)
      ·
        refine ⟨30840751220441529230158399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164484006509021489227511461 30840751220441529230158399)
        ·
          refine ⟨46261126830662293845237599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30840751220441529230158399 46261126830662293845237599)
          ·
            refine ⟨69391690245993440767856399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46261126830662293845237599 69391690245993440767856399)
            ·
              refine ⟨104087535368990161151784599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69391690245993440767856399 104087535368990161151784599)
              ·
                refine ⟨156131303053485241727676899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104087535368990161151784599 156131303053485241727676899)
                ·
                  refine ⟨234196954580227862591515349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156131303053485241727676899 234196954580227862591515349)
                  ·
                    refine ⟨5488991122974090529488641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 234196954580227862591515349 5488991122974090529488641)
                    ·
                      refine ⟨4116743342230567897116481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5488991122974090529488641 4116743342230567897116481)
                      ·
                        rfl

theorem cell23_8017329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_8017329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017329 prefixEnd_8017329 := by exact prefixLift 8017329
  have htrace : WordTrace (prefixWord ++ tailWord_8017329) baseStart_8017329 baseEnd_8017329 := by
    simpa [prefixWord, tailWord_8017329, baseEnd_8017329] using wordTrace_append hprefix tailTrace_8017329
  have hstable : (prefixWord ++ tailWord_8017329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017329).length < 2 ^ (prefixWord ++ tailWord_8017329).sum := by decide
  have hdescent : baseEnd_8017329 < baseStart_8017329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017356 : List Nat := [2, 2, 1, 4, 2, 3, 1, 1, 2, 5]
def baseStart_8017356 : Nat := 118140960795 + 8017356 * 2 ^ 59
def prefixEnd_8017356 : Nat := 4983230072969 + 3 ^ 40 * 8017356 * 2
def baseEnd_8017356 : Nat := 1372252402069413097159619

theorem tailTrace_8017356 : CollatzResearch.WordTrace tailWord_8017356 prefixEnd_8017356 1372252402069413097159619 := by
  unfold tailWord_8017356
  simp only [CollatzResearch.WordTrace]
  refine ⟨146208498171247971118959961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194944664228330628158613281 146208498171247971118959961)
  ·
    refine ⟨109656373628435978339219971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146208498171247971118959961 109656373628435978339219971)
    ·
      refine ⟨164484560442653967508829957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109656373628435978339219971 164484560442653967508829957)
      ·
        refine ⟨30840855082997618907905617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164484560442653967508829957 30840855082997618907905617)
        ·
          refine ⟨23130641312248214180929213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30840855082997618907905617 23130641312248214180929213)
          ·
            refine ⟨8673990492093080317848455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23130641312248214180929213 8673990492093080317848455)
            ·
              refine ⟨13010985738139620476772683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8673990492093080317848455 13010985738139620476772683)
              ·
                refine ⟨19516478607209430715159025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13010985738139620476772683 19516478607209430715159025)
                ·
                  refine ⟨14637358955407073036369269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19516478607209430715159025 14637358955407073036369269)
                  ·
                    refine ⟨1372252402069413097159619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14637358955407073036369269 1372252402069413097159619)
                    ·
                      rfl

theorem cell23_8017356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 2, 5].length) (baseStart_8017356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017356 prefixEnd_8017356 := by exact prefixLift 8017356
  have htrace : WordTrace (prefixWord ++ tailWord_8017356) baseStart_8017356 baseEnd_8017356 := by
    simpa [prefixWord, tailWord_8017356, baseEnd_8017356] using wordTrace_append hprefix tailTrace_8017356
  have hstable : (prefixWord ++ tailWord_8017356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017356).length < 2 ^ (prefixWord ++ tailWord_8017356).sum := by decide
  have hdescent : baseEnd_8017356 < baseStart_8017356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017359 : List Nat := [1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 4]
def baseStart_8017359 : Nat := 118140960795 + 8017359 * 2 ^ 59
def prefixEnd_8017359 : Nat := 4983230072969 + 3 ^ 40 * 8017359 * 2
def baseEnd_8017359 : Nat := 4116758746650202779741343

theorem tailTrace_8017359 : CollatzResearch.WordTrace tailWord_8017359 prefixEnd_8017359 4116758746650202779741343 := by
  unfold tailWord_8017359
  simp only [CollatzResearch.WordTrace]
  refine ⟨292417105761485073750279131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194944737174323382500186087 292417105761485073750279131)
  ·
    refine ⟨438625658642227610625418697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292417105761485073750279131 438625658642227610625418697)
    ·
      refine ⟨328969243981670707969064023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438625658642227610625418697 328969243981670707969064023)
      ·
        refine ⟨493453865972506061953596035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328969243981670707969064023 493453865972506061953596035)
        ·
          refine ⟨740180798958759092930394053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493453865972506061953596035 740180798958759092930394053)
          ·
            refine ⟨138783899804767329924448885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 740180798958759092930394053 138783899804767329924448885)
            ·
              refine ⟨13010990606696937180417083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138783899804767329924448885 13010990606696937180417083)
              ·
                refine ⟨19516485910045405770625625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13010990606696937180417083 19516485910045405770625625)
                ·
                  refine ⟨14637364432534054327969219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19516485910045405770625625 14637364432534054327969219)
                  ·
                    refine ⟨21956046648801081491953829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14637364432534054327969219 21956046648801081491953829)
                    ·
                      refine ⟨4116758746650202779741343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21956046648801081491953829 4116758746650202779741343)
                      ·
                        rfl

theorem cell23_8017359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 4].length) (baseStart_8017359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017359 prefixEnd_8017359 := by exact prefixLift 8017359
  have htrace : WordTrace (prefixWord ++ tailWord_8017359) baseStart_8017359 baseEnd_8017359 := by
    simpa [prefixWord, tailWord_8017359, baseEnd_8017359] using wordTrace_append hprefix tailTrace_8017359
  have hstable : (prefixWord ++ tailWord_8017359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017359).length < 2 ^ (prefixWord ++ tailWord_8017359).sum := by decide
  have hdescent : baseEnd_8017359 < baseStart_8017359 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017402 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6]
def baseStart_8017402 : Nat := 118140960795 + 8017402 * 2 ^ 59
def prefixEnd_8017402 : Nat := 4983230072969 + 3 ^ 40 * 8017402 * 2
def baseEnd_8017402 : Nat := 4116780826318346111503645

theorem tailTrace_8017402 : CollatzResearch.WordTrace tailWord_8017402 prefixEnd_8017402 4116780826318346111503645 := by
  unfold tailWord_8017402
  simp only [CollatzResearch.WordTrace]
  refine ⟨73104668525082323023523615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194945782733552861396062973 73104668525082323023523615)
  ·
    refine ⟨109657002787623484535285423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73104668525082323023523615 109657002787623484535285423)
    ·
      refine ⟨164485504181435226802928135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109657002787623484535285423 164485504181435226802928135)
      ·
        refine ⟨246728256272152840204392203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164485504181435226802928135 246728256272152840204392203)
        ·
          refine ⟨370092384408229260306588305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246728256272152840204392203 370092384408229260306588305)
          ·
            refine ⟨277569288306171945229941229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370092384408229260306588305 277569288306171945229941229)
            ·
              refine ⟨104088483114814479461227961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277569288306171945229941229 104088483114814479461227961)
              ·
                refine ⟨78066362336110859595920971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104088483114814479461227961 78066362336110859595920971)
                ·
                  refine ⟨117099543504166289393881457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78066362336110859595920971 117099543504166289393881457)
                  ·
                    refine ⟨87824657628124717045411093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117099543504166289393881457 87824657628124717045411093)
                    ·
                      refine ⟨4116780826318346111503645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87824657628124717045411093 4116780826318346111503645)
                      ·
                        rfl

theorem cell23_8017402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_8017402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017402 prefixEnd_8017402 := by exact prefixLift 8017402
  have htrace : WordTrace (prefixWord ++ tailWord_8017402) baseStart_8017402 baseEnd_8017402 := by
    simpa [prefixWord, tailWord_8017402, baseEnd_8017402] using wordTrace_append hprefix tailTrace_8017402
  have hstable : (prefixWord ++ tailWord_8017402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017402).length < 2 ^ (prefixWord ++ tailWord_8017402).sum := by decide
  have hdescent : baseEnd_8017402 < baseStart_8017402 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017420 : List Nat := [2, 2, 1, 2, 5, 2, 1, 3, 1, 4]
def baseStart_8017420 : Nat := 118140960795 + 8017420 * 2 ^ 59
def prefixEnd_8017420 : Nat := 4983230072969 + 3 ^ 40 * 8017420 * 2
def baseEnd_8017420 : Nat := 1372263356323375680359521

theorem tailTrace_8017420 : CollatzResearch.WordTrace tailWord_8017420 prefixEnd_8017420 1372263356323375680359521 := by
  unfold tailWord_8017420
  simp only [CollatzResearch.WordTrace]
  refine ⟨146209665307132040584124857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194946220409509387445499809 146209665307132040584124857)
  ·
    refine ⟨109657248980349030438093643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146209665307132040584124857 109657248980349030438093643)
    ·
      refine ⟨164485873470523545657140465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109657248980349030438093643 164485873470523545657140465)
      ·
        refine ⟨123364405102892659242855349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164485873470523545657140465 123364405102892659242855349)
        ·
          refine ⟨11565412978396186804017689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123364405102892659242855349 11565412978396186804017689)
          ·
            refine ⟨8674059733797140103013267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11565412978396186804017689 8674059733797140103013267)
            ·
              refine ⟨13011089600695710154519901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8674059733797140103013267 13011089600695710154519901)
              ·
                refine ⟨4879158600260891307944963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13011089600695710154519901 4879158600260891307944963)
                ·
                  refine ⟨7318737900391336961917445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4879158600260891307944963 7318737900391336961917445)
                  ·
                    refine ⟨1372263356323375680359521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7318737900391336961917445 1372263356323375680359521)
                    ·
                      rfl

theorem cell23_8017420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 1, 4].length) (baseStart_8017420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017420 prefixEnd_8017420 := by exact prefixLift 8017420
  have htrace : WordTrace (prefixWord ++ tailWord_8017420) baseStart_8017420 baseEnd_8017420 := by
    simpa [prefixWord, tailWord_8017420, baseEnd_8017420] using wordTrace_append hprefix tailTrace_8017420
  have hstable : (prefixWord ++ tailWord_8017420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017420).length < 2 ^ (prefixWord ++ tailWord_8017420).sum := by decide
  have hdescent : baseEnd_8017420 < baseStart_8017420 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017516 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 3]
def baseStart_8017516 : Nat := 118140960795 + 8017516 * 2 ^ 59
def prefixEnd_8017516 : Nat := 4983230072969 + 3 ^ 40 * 8017516 * 2
def baseEnd_8017516 : Nat := 4116839363112958665478121

theorem tailTrace_8017516 : CollatzResearch.WordTrace tailWord_8017516 prefixEnd_8017516 4116839363112958665478121 := by
  unfold tailWord_8017516
  simp only [CollatzResearch.WordTrace]
  refine ⟨146211416010958144781872201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194948554681277526375829601 146211416010958144781872201)
  ·
    refine ⟨109658562008218608586404151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146211416010958144781872201 109658562008218608586404151)
    ·
      refine ⟨164487843012327912879606227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109658562008218608586404151 164487843012327912879606227)
      ·
        refine ⟨246731764518491869319409341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164487843012327912879606227 246731764518491869319409341)
        ·
          refine ⟨92524411694434450994778503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246731764518491869319409341 92524411694434450994778503)
          ·
            refine ⟨138786617541651676492167755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92524411694434450994778503 138786617541651676492167755)
            ·
              refine ⟨208179926312477514738251633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138786617541651676492167755 208179926312477514738251633)
              ·
                refine ⟨156134944734358136053688725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208179926312477514738251633 156134944734358136053688725)
                ·
                  refine ⟨7318825534423037627516659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156134944734358136053688725 7318825534423037627516659)
                  ·
                    refine ⟨10978238301634556441274989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7318825534423037627516659 10978238301634556441274989)
                    ·
                      refine ⟨4116839363112958665478121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10978238301634556441274989 4116839363112958665478121)
                      ·
                        rfl

theorem cell23_8017516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 3].length) (baseStart_8017516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017516 prefixEnd_8017516 := by exact prefixLift 8017516
  have htrace : WordTrace (prefixWord ++ tailWord_8017516) baseStart_8017516 baseEnd_8017516 := by
    simpa [prefixWord, tailWord_8017516, baseEnd_8017516] using wordTrace_append hprefix tailTrace_8017516
  have hstable : (prefixWord ++ tailWord_8017516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017516).length < 2 ^ (prefixWord ++ tailWord_8017516).sum := by decide
  have hdescent : baseEnd_8017516 < baseStart_8017516 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017529 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 2, 2, 5]
def baseStart_8017529 : Nat := 118140960795 + 8017529 * 2 ^ 59
def prefixEnd_8017529 : Nat := 4983230072969 + 3 ^ 40 * 8017529 * 2
def baseEnd_8017529 : Nat := 4116846038361467114615561

theorem tailTrace_8017529 : CollatzResearch.WordTrace tailWord_8017529 prefixEnd_8017529 4116846038361467114615561 := by
  unfold tailWord_8017529
  simp only [CollatzResearch.WordTrace]
  refine ⟨292423306170869192783967641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194948870780579461855978427 292423306170869192783967641)
  ·
    refine ⟨219317479628151894587975731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292423306170869192783967641 219317479628151894587975731)
    ·
      refine ⟨328976219442227841881963597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219317479628151894587975731 328976219442227841881963597)
      ·
        refine ⟨123366082290835440705736349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328976219442227841881963597 123366082290835440705736349)
        ·
          refine ⟨46262280859063290264651131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123366082290835440705736349 46262280859063290264651131)
          ·
            refine ⟨69393421288594935396976697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46262280859063290264651131 69393421288594935396976697)
            ·
              refine ⟨52045065966446201547732523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69393421288594935396976697 52045065966446201547732523)
              ·
                refine ⟨78067598949669302321598785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52045065966446201547732523 78067598949669302321598785)
                ·
                  refine ⟨58550699212251976741199089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78067598949669302321598785 58550699212251976741199089)
                  ·
                    refine ⟨43913024409188982555899317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58550699212251976741199089 43913024409188982555899317)
                    ·
                      refine ⟨4116846038361467114615561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43913024409188982555899317 4116846038361467114615561)
                      ·
                        rfl

theorem cell23_8017529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_8017529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017529 prefixEnd_8017529 := by exact prefixLift 8017529
  have htrace : WordTrace (prefixWord ++ tailWord_8017529) baseStart_8017529 baseEnd_8017529 := by
    simpa [prefixWord, tailWord_8017529, baseEnd_8017529] using wordTrace_append hprefix tailTrace_8017529
  have hstable : (prefixWord ++ tailWord_8017529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017529).length < 2 ^ (prefixWord ++ tailWord_8017529).sum := by decide
  have hdescent : baseEnd_8017529 < baseStart_8017529 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017550 : List Nat := [4, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3]
def baseStart_8017550 : Nat := 118140960795 + 8017550 * 2 ^ 59
def prefixEnd_8017550 : Nat := 4983230072969 + 3 ^ 40 * 8017550 * 2
def baseEnd_8017550 : Nat := 4116856821455211532452965

theorem tailTrace_8017550 : CollatzResearch.WordTrace tailWord_8017550 prefixEnd_8017550 4116856821455211532452965 := by
  unfold tailWord_8017550
  simp only [CollatzResearch.WordTrace]
  refine ⟨36553009012974139171310263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194949381402528742246988069 36553009012974139171310263)
  ·
    refine ⟨54829513519461208756965395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36553009012974139171310263 54829513519461208756965395)
    ·
      refine ⟨82244270279191813135448093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54829513519461208756965395 82244270279191813135448093)
      ·
        refine ⟨30841601354696929925793035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82244270279191813135448093 30841601354696929925793035)
        ·
          refine ⟨46262402032045394888689553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30841601354696929925793035 46262402032045394888689553)
          ·
            refine ⟨34696801524034046166517165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46262402032045394888689553 34696801524034046166517165)
            ·
              refine ⟨13011300571512767312443937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34696801524034046166517165 13011300571512767312443937)
              ·
                refine ⟨9758475428634575484332953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13011300571512767312443937 9758475428634575484332953)
                ·
                  refine ⟨7318856571475931613249715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9758475428634575484332953 7318856571475931613249715)
                  ·
                    refine ⟨10978284857213897419874573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7318856571475931613249715 10978284857213897419874573)
                    ·
                      refine ⟨4116856821455211532452965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10978284857213897419874573 4116856821455211532452965)
                      ·
                        rfl

theorem cell23_8017550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_8017550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017550 prefixEnd_8017550 := by exact prefixLift 8017550
  have htrace : WordTrace (prefixWord ++ tailWord_8017550) baseStart_8017550 baseEnd_8017550 := by
    simpa [prefixWord, tailWord_8017550, baseEnd_8017550] using wordTrace_append hprefix tailTrace_8017550
  have hstable : (prefixWord ++ tailWord_8017550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017550).length < 2 ^ (prefixWord ++ tailWord_8017550).sum := by decide
  have hdescent : baseEnd_8017550 < baseStart_8017550 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017567 : List Nat := [1, 1, 2, 7, 2, 1, 1, 1, 1, 3, 3]
def baseStart_8017567 : Nat := 118140960795 + 8017567 * 2 ^ 59
def prefixEnd_8017567 : Nat := 4983230072969 + 3 ^ 40 * 8017567 * 2
def baseEnd_8017567 : Nat := 4116865550626337965940387

theorem tailTrace_8017567 : CollatzResearch.WordTrace tailWord_8017567 prefixEnd_8017567 4116865550626337965940387 := by
  unfold tailWord_8017567
  simp only [CollatzResearch.WordTrace]
  refine ⟨292424692144731525273850955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194949794763154350182567303 292424692144731525273850955)
  ·
    refine ⟨438637038217097287910776433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292424692144731525273850955 438637038217097287910776433)
    ·
      refine ⟨328977778662822965933082325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438637038217097287910776433 328977778662822965933082325)
      ·
        refine ⟨7710416687409913264056617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 328977778662822965933082325 7710416687409913264056617)
        ·
          refine ⟨5782812515557434948042463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7710416687409913264056617 5782812515557434948042463)
          ·
            refine ⟨8674218773336152422063695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5782812515557434948042463 8674218773336152422063695)
            ·
              refine ⟨13011328160004228633095543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8674218773336152422063695 13011328160004228633095543)
              ·
                refine ⟨19516992240006342949643315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13011328160004228633095543 19516992240006342949643315)
                ·
                  refine ⟨29275488360009514424464973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19516992240006342949643315 29275488360009514424464973)
                  ·
                    refine ⟨10978308135003567909174365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29275488360009514424464973 10978308135003567909174365)
                    ·
                      refine ⟨4116865550626337965940387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10978308135003567909174365 4116865550626337965940387)
                      ·
                        rfl

theorem cell23_8017567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_8017567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017567 prefixEnd_8017567 := by exact prefixLift 8017567
  have htrace : WordTrace (prefixWord ++ tailWord_8017567) baseStart_8017567 baseEnd_8017567 := by
    simpa [prefixWord, tailWord_8017567, baseEnd_8017567] using wordTrace_append hprefix tailTrace_8017567
  have hstable : (prefixWord ++ tailWord_8017567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017567).length < 2 ^ (prefixWord ++ tailWord_8017567).sum := by decide
  have hdescent : baseEnd_8017567 < baseStart_8017567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017573 : List Nat := [1, 3, 1, 2, 1, 2, 5, 1, 1, 4, 2]
def baseStart_8017573 : Nat := 118140960795 + 8017573 * 2 ^ 59
def prefixEnd_8017573 : Nat := 4983230072969 + 3 ^ 40 * 8017573 * 2
def baseEnd_8017573 : Nat := 4116868631510264942465359

theorem tailTrace_8017573 : CollatzResearch.WordTrace tailWord_8017573 prefixEnd_8017573 4116868631510264942465359 := by
  unfold tailWord_8017573
  simp only [CollatzResearch.WordTrace]
  refine ⟨292424910982709788298569373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194949940655139858865712915 292424910982709788298569373)
  ·
    refine ⟨109659341618516170611963515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292424910982709788298569373 109659341618516170611963515)
    ·
      refine ⟨164489012427774255917945273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109659341618516170611963515 164489012427774255917945273)
      ·
        refine ⟨123366759320830691938458955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164489012427774255917945273 123366759320830691938458955)
        ·
          refine ⟨185050138981246037907688433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123366759320830691938458955 185050138981246037907688433)
          ·
            refine ⟨138787604235934528430766325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185050138981246037907688433 138787604235934528430766325)
            ·
              refine ⟨13011337897118862040384343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138787604235934528430766325 13011337897118862040384343)
              ·
                refine ⟨19517006845678293060576515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13011337897118862040384343 19517006845678293060576515)
                ·
                  refine ⟨29275510268517439590864773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19517006845678293060576515 29275510268517439590864773)
                  ·
                    refine ⟨5489158175347019923287145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29275510268517439590864773 5489158175347019923287145)
                    ·
                      refine ⟨4116868631510264942465359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5489158175347019923287145 4116868631510264942465359)
                      ·
                        rfl

theorem cell23_8017573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_8017573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017573 prefixEnd_8017573 := by exact prefixLift 8017573
  have htrace : WordTrace (prefixWord ++ tailWord_8017573) baseStart_8017573 baseEnd_8017573 := by
    simpa [prefixWord, tailWord_8017573, baseEnd_8017573] using wordTrace_append hprefix tailTrace_8017573
  have hstable : (prefixWord ++ tailWord_8017573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017573).length < 2 ^ (prefixWord ++ tailWord_8017573).sum := by decide
  have hdescent : baseEnd_8017573 < baseStart_8017573 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017656 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 7, 4]
def baseStart_8017656 : Nat := 118140960795 + 8017656 * 2 ^ 59
def prefixEnd_8017656 : Nat := 4983230072969 + 3 ^ 40 * 8017656 * 2
def baseEnd_8017656 : Nat := 1372303750134862705909159

theorem tailTrace_8017656 : CollatzResearch.WordTrace tailWord_8017656 prefixEnd_8017656 1372303750134862705909159 := by
  unfold tailWord_8017656
  simp only [CollatzResearch.WordTrace]
  refine ⟨146213969120704546736920411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194951958827606062315893881 146213969120704546736920411)
  ·
    refine ⟨219320953681056820105380617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146213969120704546736920411 219320953681056820105380617)
    ·
      refine ⟨164490715260792615079035463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219320953681056820105380617 164490715260792615079035463)
      ·
        refine ⟨246736072891188922618553195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164490715260792615079035463 246736072891188922618553195)
        ·
          refine ⟨370104109336783383927829793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246736072891188922618553195 370104109336783383927829793)
          ·
            refine ⟨277578082002587537945872345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370104109336783383927829793 277578082002587537945872345)
            ·
              refine ⟨208183561501940653459404259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277578082002587537945872345 208183561501940653459404259)
              ·
                refine ⟨312275342252910980189106389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208183561501940653459404259 312275342252910980189106389)
                ·
                  refine ⟨7318953334052601098182181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 312275342252910980189106389 7318953334052601098182181)
                  ·
                    refine ⟨1372303750134862705909159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7318953334052601098182181 1372303750134862705909159)
                    ·
                      rfl

theorem cell23_8017656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 7, 4].length) (baseStart_8017656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017656 prefixEnd_8017656 := by exact prefixLift 8017656
  have htrace : WordTrace (prefixWord ++ tailWord_8017656) baseStart_8017656 baseEnd_8017656 := by
    simpa [prefixWord, tailWord_8017656, baseEnd_8017656] using wordTrace_append hprefix tailTrace_8017656
  have hstable : (prefixWord ++ tailWord_8017656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017656).length < 2 ^ (prefixWord ++ tailWord_8017656).sum := by decide
  have hdescent : baseEnd_8017656 < baseStart_8017656 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017694 : List Nat := [4, 3, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_8017694 : Nat := 118140960795 + 8017694 * 2 ^ 59
def prefixEnd_8017694 : Nat := 4983230072969 + 3 ^ 40 * 8017694 * 2
def baseEnd_8017694 : Nat := 1372310254223152989684101

theorem tailTrace_8017694 : CollatzResearch.WordTrace tailWord_8017694 prefixEnd_8017694 1372310254223152989684101 := by
  unfold tailWord_8017694
  simp only [CollatzResearch.WordTrace]
  refine ⟨36553665526908928245465517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194952882810180950642482757 36553665526908928245465517)
  ·
    refine ⟨13707624572590848092049569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36553665526908928245465517 13707624572590848092049569)
    ·
      refine ⟨10280718429443136069037177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13707624572590848092049569 10280718429443136069037177)
      ·
        refine ⟨7710538822082352051777883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10280718429443136069037177 7710538822082352051777883)
        ·
          refine ⟨11565808233123528077666825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7710538822082352051777883 11565808233123528077666825)
          ·
            refine ⟨8674356174842646058250119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11565808233123528077666825 8674356174842646058250119)
            ·
              refine ⟨13011534262263969087375179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8674356174842646058250119 13011534262263969087375179)
              ·
                refine ⟨19517301393395953631062769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13011534262263969087375179 19517301393395953631062769)
                ·
                  refine ⟨14637976045046965223297077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19517301393395953631062769 14637976045046965223297077)
                  ·
                    refine ⟨1372310254223152989684101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14637976045046965223297077 1372310254223152989684101)
                    ·
                      rfl

theorem cell23_8017694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_8017694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017694 prefixEnd_8017694 := by exact prefixLift 8017694
  have htrace : WordTrace (prefixWord ++ tailWord_8017694) baseStart_8017694 baseEnd_8017694 := by
    simpa [prefixWord, tailWord_8017694, baseEnd_8017694] using wordTrace_append hprefix tailTrace_8017694
  have hstable : (prefixWord ++ tailWord_8017694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017694).length < 2 ^ (prefixWord ++ tailWord_8017694).sum := by decide
  have hdescent : baseEnd_8017694 < baseStart_8017694 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017700 : List Nat := [2, 3, 1, 3, 2, 1, 3, 1, 2, 2, 3]
def baseStart_8017700 : Nat := 118140960795 + 8017700 * 2 ^ 59
def prefixEnd_8017700 : Nat := 4983230072969 + 3 ^ 40 * 8017700 * 2
def baseEnd_8017700 : Nat := 4116933843553385945577275

theorem tailTrace_8017700 : CollatzResearch.WordTrace tailWord_8017700 prefixEnd_8017700 4116933843553385945577275 := by
  unfold tailWord_8017700
  simp only [CollatzResearch.WordTrace]
  refine ⟨146214771526624844494221277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194953028702166459325628369 146214771526624844494221277)
  ·
    refine ⟨54830539322484316685332979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146214771526624844494221277 54830539322484316685332979)
    ·
      refine ⟨82245808983726475027999469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54830539322484316685332979 82245808983726475027999469)
      ·
        refine ⟨30842178368897428135499801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82245808983726475027999469 30842178368897428135499801)
        ·
          refine ⟨23131633776673071101624851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30842178368897428135499801 23131633776673071101624851)
          ·
            refine ⟨34697450665009606652437277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23131633776673071101624851 34697450665009606652437277)
            ·
              refine ⟨13011543999378602494663979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34697450665009606652437277 13011543999378602494663979)
              ·
                refine ⟨19517315999067903741995969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13011543999378602494663979 19517315999067903741995969)
                ·
                  refine ⟨14637986999300927806496977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19517315999067903741995969 14637986999300927806496977)
                  ·
                    refine ⟨10978490249475695854872733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14637986999300927806496977 10978490249475695854872733)
                    ·
                      refine ⟨4116933843553385945577275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10978490249475695854872733 4116933843553385945577275)
                      ·
                        rfl

theorem cell23_8017700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_8017700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017700 prefixEnd_8017700 := by exact prefixLift 8017700
  have htrace : WordTrace (prefixWord ++ tailWord_8017700) baseStart_8017700 baseEnd_8017700 := by
    simpa [prefixWord, tailWord_8017700, baseEnd_8017700] using wordTrace_append hprefix tailTrace_8017700
  have hstable : (prefixWord ++ tailWord_8017700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017700).length < 2 ^ (prefixWord ++ tailWord_8017700).sum := by decide
  have hdescent : baseEnd_8017700 < baseStart_8017700 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017753 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 2, 6, 2]
def baseStart_8017753 : Nat := 118140960795 + 8017753 * 2 ^ 59
def prefixEnd_8017753 : Nat := 4983230072969 + 3 ^ 40 * 8017753 * 2
def baseEnd_8017753 : Nat := 4116961058028074238214531

theorem tailTrace_8017753 : CollatzResearch.WordTrace tailWord_8017753 prefixEnd_8017753 4116961058028074238214531 := by
  unfold tailWord_8017753
  simp only [CollatzResearch.WordTrace]
  refine ⟨292431476122057679040121913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194954317414705119360081275 292431476122057679040121913)
  ·
    refine ⟨219323607091543259280091435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292431476122057679040121913 219323607091543259280091435)
    ·
      refine ⟨328985410637314888920137153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219323607091543259280091435 328985410637314888920137153)
      ·
        refine ⟨246739057977986166690102865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328985410637314888920137153 246739057977986166690102865)
        ·
          refine ⟨185054293483489625017577149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246739057977986166690102865 185054293483489625017577149)
          ·
            refine ⟨69395360056308609381591431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185054293483489625017577149 69395360056308609381591431)
            ·
              refine ⟨104093040084462914072387147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69395360056308609381591431 104093040084462914072387147)
              ·
                refine ⟨156139560126694371108580721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104093040084462914072387147 156139560126694371108580721)
                ·
                  refine ⟨117104670095020778331435541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156139560126694371108580721 117104670095020778331435541)
                  ·
                    refine ⟨5489281410704098984286041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117104670095020778331435541 5489281410704098984286041)
                    ·
                      refine ⟨4116961058028074238214531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5489281410704098984286041 4116961058028074238214531)
                      ·
                        rfl

theorem cell23_8017753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 6, 2].length) (baseStart_8017753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017753 prefixEnd_8017753 := by exact prefixLift 8017753
  have htrace : WordTrace (prefixWord ++ tailWord_8017753) baseStart_8017753 baseEnd_8017753 := by
    simpa [prefixWord, tailWord_8017753, baseEnd_8017753] using wordTrace_append hprefix tailTrace_8017753
  have hstable : (prefixWord ++ tailWord_8017753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017753).length < 2 ^ (prefixWord ++ tailWord_8017753).sum := by decide
  have hdescent : baseEnd_8017753 < baseStart_8017753 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017773 : List Nat := [1, 5, 1, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_8017773 : Nat := 118140960795 + 8017773 * 2 ^ 59
def prefixEnd_8017773 : Nat := 4983230072969 + 3 ^ 40 * 8017773 * 2
def baseEnd_8017773 : Nat := 4116971327641164159964439

theorem tailTrace_8017773 : CollatzResearch.WordTrace tailWord_8017773 prefixEnd_8017773 4116971327641164159964439 := by
  unfold tailWord_8017773
  simp only [CollatzResearch.WordTrace]
  refine ⟨292432205581985222455849973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194954803721323481637233315 292432205581985222455849973)
  ·
    refine ⟨27415519273311114605235935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 292432205581985222455849973 27415519273311114605235935)
    ·
      refine ⟨41123278909966671907853903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27415519273311114605235935 41123278909966671907853903)
      ·
        refine ⟨61684918364950007861780855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41123278909966671907853903 61684918364950007861780855)
        ·
          refine ⟨92527377547425011792671283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61684918364950007861780855 92527377547425011792671283)
          ·
            refine ⟨138791066321137517689006925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92527377547425011792671283 138791066321137517689006925)
            ·
              refine ⟨52046649870426569133377597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138791066321137517689006925 52046649870426569133377597)
              ·
                refine ⟨19517493701409963425016599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52046649870426569133377597 19517493701409963425016599)
                ·
                  refine ⟨29276240552114945137524899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19517493701409963425016599 29276240552114945137524899)
                  ·
                    refine ⟨43914360828172417706287349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29276240552114945137524899 43914360828172417706287349)
                    ·
                      refine ⟨4116971327641164159964439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43914360828172417706287349 4116971327641164159964439)
                      ·
                        rfl

theorem cell23_8017773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_8017773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017773 prefixEnd_8017773 := by exact prefixLift 8017773
  have htrace : WordTrace (prefixWord ++ tailWord_8017773) baseStart_8017773 baseEnd_8017773 := by
    simpa [prefixWord, tailWord_8017773, baseEnd_8017773] using wordTrace_append hprefix tailTrace_8017773
  have hstable : (prefixWord ++ tailWord_8017773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017773).length < 2 ^ (prefixWord ++ tailWord_8017773).sum := by decide
  have hdescent : baseEnd_8017773 < baseStart_8017773 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017803 : List Nat := [1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 3]
def baseStart_8017803 : Nat := 118140960795 + 8017803 * 2 ^ 59
def prefixEnd_8017803 : Nat := 4983230072969 + 3 ^ 40 * 8017803 * 2
def baseEnd_8017803 : Nat := 4116986732060799042589301

theorem tailTrace_8017803 : CollatzResearch.WordTrace tailWord_8017803 prefixEnd_8017803 4116986732060799042589301 := by
  unfold tailWord_8017803
  simp only [CollatzResearch.WordTrace]
  refine ⟨292433299771876537579442063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194955533181251025052961375 292433299771876537579442063)
  ·
    refine ⟨438649949657814806369163095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292433299771876537579442063 438649949657814806369163095)
    ·
      refine ⟨657974924486722209553744643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438649949657814806369163095 657974924486722209553744643)
      ·
        refine ⟨986962386730083314330616965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657974924486722209553744643 986962386730083314330616965)
        ·
          refine ⟨185055447511890621436990681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 986962386730083314330616965 185055447511890621436990681)
          ·
            refine ⟨138791585633917966077743011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185055447511890621436990681 138791585633917966077743011)
            ·
              refine ⟨208187378450876949116614517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138791585633917966077743011 208187378450876949116614517)
              ·
                refine ⟨19517566729769713979682611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208187378450876949116614517 19517566729769713979682611)
                ·
                  refine ⟨29276350094654570969523917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19517566729769713979682611 29276350094654570969523917)
                  ·
                    refine ⟨10978631285495464113571469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29276350094654570969523917 10978631285495464113571469)
                    ·
                      refine ⟨4116986732060799042589301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10978631285495464113571469 4116986732060799042589301)
                      ·
                        rfl

theorem cell23_8017803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 3].length) (baseStart_8017803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017803 prefixEnd_8017803 := by exact prefixLift 8017803
  have htrace : WordTrace (prefixWord ++ tailWord_8017803) baseStart_8017803 baseEnd_8017803 := by
    simpa [prefixWord, tailWord_8017803, baseEnd_8017803] using wordTrace_append hprefix tailTrace_8017803
  have hstable : (prefixWord ++ tailWord_8017803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017803).length < 2 ^ (prefixWord ++ tailWord_8017803).sum := by decide
  have hdescent : baseEnd_8017803 < baseStart_8017803 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017814 : List Nat := [5, 3, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_8017814 : Nat := 118140960795 + 8017814 * 2 ^ 59
def prefixEnd_8017814 : Nat := 4983230072969 + 3 ^ 40 * 8017814 * 2
def baseEnd_8017814 : Nat := 1372330793449332833183917

theorem tailTrace_8017814 : CollatzResearch.WordTrace tailWord_8017814 prefixEnd_8017814 1372330793449332833183917 := by
  unfold tailWord_8017814
  simp only [CollatzResearch.WordTrace]
  refine ⟨18277106310927292903630781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194955800649891124305394997 18277106310927292903630781)
  ·
    refine ⟨6853914866597734838861543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18277106310927292903630781 6853914866597734838861543)
    ·
      refine ⟨10280872299896602258292315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6853914866597734838861543 10280872299896602258292315)
      ·
        refine ⟨15421308449844903387438473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10280872299896602258292315 15421308449844903387438473)
        ·
          refine ⟨11565981337383677540578855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15421308449844903387438473 11565981337383677540578855)
          ·
            refine ⟨17348972006075516310868283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11565981337383677540578855 17348972006075516310868283)
            ·
              refine ⟨26023458009113274466302425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17348972006075516310868283 26023458009113274466302425)
              ·
                refine ⟨19517593506834955849726819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26023458009113274466302425 19517593506834955849726819)
                ·
                  refine ⟨29276390260252433774590229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19517593506834955849726819 29276390260252433774590229)
                  ·
                    refine ⟨1372330793449332833183917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29276390260252433774590229 1372330793449332833183917)
                    ·
                      rfl

theorem cell23_8017814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_8017814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017814 prefixEnd_8017814 := by exact prefixLift 8017814
  have htrace : WordTrace (prefixWord ++ tailWord_8017814) baseStart_8017814 baseEnd_8017814 := by
    simpa [prefixWord, tailWord_8017814, baseEnd_8017814] using wordTrace_append hprefix tailTrace_8017814
  have hstable : (prefixWord ++ tailWord_8017814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017814).length < 2 ^ (prefixWord ++ tailWord_8017814).sum := by decide
  have hdescent : baseEnd_8017814 < baseStart_8017814 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017820 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 3, 3, 3]
def baseStart_8017820 : Nat := 118140960795 + 8017820 * 2 ^ 59
def prefixEnd_8017820 : Nat := 4983230072969 + 3 ^ 40 * 8017820 * 2
def baseEnd_8017820 : Nat := 4116995461231925476076723

theorem tailTrace_8017820 : CollatzResearch.WordTrace tailWord_8017820 prefixEnd_8017820 4116995461231925476076723 := by
  unfold tailWord_8017820
  simp only [CollatzResearch.WordTrace]
  refine ⟨146216959906407474741405457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194955946541876632988540609 146216959906407474741405457)
  ·
    refine ⟨109662719929805606056054093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146216959906407474741405457 109662719929805606056054093)
    ·
      refine ⟨41123519973677102271020285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109662719929805606056054093 41123519973677102271020285)
      ·
        refine ⟨15421319990128913351632607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41123519973677102271020285 15421319990128913351632607)
        ·
          refine ⟨23131979985193370027448911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15421319990128913351632607 23131979985193370027448911)
          ·
            refine ⟨34697969977790055041173367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23131979985193370027448911 34697969977790055041173367)
            ·
              refine ⟨52046954966685082561760051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34697969977790055041173367 52046954966685082561760051)
              ·
                refine ⟨78070432450027623842640077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52046954966685082561760051 78070432450027623842640077)
                ·
                  refine ⟨29276412168760358940990029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78070432450027623842640077 29276412168760358940990029)
                  ·
                    refine ⟨10978654563285134602871261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29276412168760358940990029 10978654563285134602871261)
                    ·
                      refine ⟨4116995461231925476076723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10978654563285134602871261 4116995461231925476076723)
                      ·
                        rfl

theorem cell23_8017820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_8017820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017820 prefixEnd_8017820 := by exact prefixLift 8017820
  have htrace : WordTrace (prefixWord ++ tailWord_8017820) baseStart_8017820 baseEnd_8017820 := by
    simpa [prefixWord, tailWord_8017820, baseEnd_8017820] using wordTrace_append hprefix tailTrace_8017820
  have hstable : (prefixWord ++ tailWord_8017820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017820).length < 2 ^ (prefixWord ++ tailWord_8017820).sum := by decide
  have hdescent : baseEnd_8017820 < baseStart_8017820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017844 : List Nat := [2, 5, 2, 1, 3, 1, 1, 8]
def baseStart_8017844 : Nat := 118140960795 + 8017844 * 2 ^ 59
def prefixEnd_8017844 : Nat := 4983230072969 + 3 ^ 40 * 8017844 * 2
def baseEnd_8017844 : Nat := 152481769806208643784319

theorem tailTrace_8017844 : CollatzResearch.WordTrace tailWord_8017844 prefixEnd_8017844 152481769806208643784319 := by
  unfold tailWord_8017844
  simp only [CollatzResearch.WordTrace]
  refine ⟨146217397582364000790842293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194956530109818667721123057 146217397582364000790842293)
  ·
    refine ⟨13707881023346625074141465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146217397582364000790842293 13707881023346625074141465)
    ·
      refine ⟨10280910767509968805606099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13707881023346625074141465 10280910767509968805606099)
      ·
        refine ⟨15421366151264953208409149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10280910767509968805606099 15421366151264953208409149)
        ·
          refine ⟨5783012306724357453153431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15421366151264953208409149 5783012306724357453153431)
          ·
            refine ⟨8674518460086536179730147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5783012306724357453153431 8674518460086536179730147)
            ·
              refine ⟨13011777690129804269595221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8674518460086536179730147 13011777690129804269595221)
              ·
                refine ⟨152481769806208643784319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13011777690129804269595221 152481769806208643784319)
                ·
                  rfl

theorem cell23_8017844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 8].length) (baseStart_8017844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017844 prefixEnd_8017844 := by exact prefixLift 8017844
  have htrace : WordTrace (prefixWord ++ tailWord_8017844) baseStart_8017844 baseEnd_8017844 := by
    simpa [prefixWord, tailWord_8017844, baseEnd_8017844] using wordTrace_append hprefix tailTrace_8017844
  have hstable : (prefixWord ++ tailWord_8017844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017844).length < 2 ^ (prefixWord ++ tailWord_8017844).sum := by decide
  have hdescent : baseEnd_8017844 < baseStart_8017844 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017853 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 1, 8]
def baseStart_8017853 : Nat := 118140960795 + 8017853 * 2 ^ 59
def prefixEnd_8017853 : Nat := 4983230072969 + 3 ^ 40 * 8017853 * 2
def baseEnd_8017853 : Nat := 1372337468697841282321357

theorem tailTrace_8017853 : CollatzResearch.WordTrace tailWord_8017853 prefixEnd_8017853 1372337468697841282321357 := by
  unfold tailWord_8017853
  simp only [CollatzResearch.WordTrace]
  refine ⟨292435123421695396118762213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194956748947796930745841475 292435123421695396118762213)
  ·
    refine ⟨54831585641567886772267915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292435123421695396118762213 54831585641567886772267915)
    ·
      refine ⟨82247378462351830158401873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54831585641567886772267915 82247378462351830158401873)
      ·
        refine ⟨61685533846763872618801405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82247378462351830158401873 61685533846763872618801405)
        ·
          refine ⟨23132075192536452232050527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61685533846763872618801405 23132075192536452232050527)
          ·
            refine ⟨34698112788804678348075791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23132075192536452232050527 34698112788804678348075791)
            ·
              refine ⟨52047169183207017522113687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34698112788804678348075791 52047169183207017522113687)
              ·
                refine ⟨78070753774810526283170531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52047169183207017522113687 78070753774810526283170531)
                ·
                  refine ⟨117106130662215789424755797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78070753774810526283170531 117106130662215789424755797)
                  ·
                    refine ⟨1372337468697841282321357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117106130662215789424755797 1372337468697841282321357)
                    ·
                      rfl

theorem cell23_8017853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_8017853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017853 prefixEnd_8017853 := by exact prefixLift 8017853
  have htrace : WordTrace (prefixWord ++ tailWord_8017853) baseStart_8017853 baseEnd_8017853 := by
    simpa [prefixWord, tailWord_8017853, baseEnd_8017853] using wordTrace_append hprefix tailTrace_8017853
  have hstable : (prefixWord ++ tailWord_8017853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017853).length < 2 ^ (prefixWord ++ tailWord_8017853).sum := by decide
  have hdescent : baseEnd_8017853 < baseStart_8017853 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017863 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 3]
def baseStart_8017863 : Nat := 118140960795 + 8017863 * 2 ^ 59
def prefixEnd_8017863 : Nat := 4983230072969 + 3 ^ 40 * 8017863 * 2
def baseEnd_8017863 : Nat := 4117017540900068807839025

theorem tailTrace_8017863 : CollatzResearch.WordTrace tailWord_8017863 prefixEnd_8017863 4117017540900068807839025 := by
  unfold tailWord_8017863
  simp only [CollatzResearch.WordTrace]
  refine ⟨292435488151659167826626243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194956992101106111884417495 292435488151659167826626243)
  ·
    refine ⟨438653232227488751739939365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292435488151659167826626243 438653232227488751739939365)
    ·
      refine ⟨82247481042654140951238631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 438653232227488751739939365 82247481042654140951238631)
      ·
        refine ⟨123371221563981211426857947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82247481042654140951238631 123371221563981211426857947)
        ·
          refine ⟨185056832345971817140286921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123371221563981211426857947 185056832345971817140286921)
          ·
            refine ⟨138792624259478862855215191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185056832345971817140286921 138792624259478862855215191)
            ·
              refine ⟨208188936389218294282822787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138792624259478862855215191 208188936389218294282822787)
              ·
                refine ⟨312283404583827441424234181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208188936389218294282822787 312283404583827441424234181)
                ·
                  refine ⟨58553138359467645267043909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 312283404583827441424234181 58553138359467645267043909)
                  ·
                    refine ⟨10978713442400183487570733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58553138359467645267043909 10978713442400183487570733)
                    ·
                      refine ⟨4117017540900068807839025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10978713442400183487570733 4117017540900068807839025)
                      ·
                        rfl

theorem cell23_8017863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_8017863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017863 prefixEnd_8017863 := by exact prefixLift 8017863
  have htrace : WordTrace (prefixWord ++ tailWord_8017863) baseStart_8017863 baseEnd_8017863 := by
    simpa [prefixWord, tailWord_8017863, baseEnd_8017863] using wordTrace_append hprefix tailTrace_8017863
  have hstable : (prefixWord ++ tailWord_8017863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017863).length < 2 ^ (prefixWord ++ tailWord_8017863).sum := by decide
  have hdescent : baseEnd_8017863 < baseStart_8017863 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017877 : List Nat := [1, 3, 2, 3, 2, 1, 2, 2, 1, 4, 2]
def baseStart_8017877 : Nat := 118140960795 + 8017877 * 2 ^ 59
def prefixEnd_8017877 : Nat := 4983230072969 + 3 ^ 40 * 8017877 * 2
def baseEnd_8017877 : Nat := 4117024729629231753063961

theorem tailTrace_8017877 : CollatzResearch.WordTrace tailWord_8017877 prefixEnd_8017877 4117024729629231753063961 := by
  unfold tailWord_8017877
  simp only [CollatzResearch.WordTrace]
  refine ⟨292435998773608448217635885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194957332515738965478423923 292435998773608448217635885)
  ·
    refine ⟨109663499540103168081613457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292435998773608448217635885 109663499540103168081613457)
    ·
      refine ⟨82247624655077376061210093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109663499540103168081613457 82247624655077376061210093)
      ·
        refine ⟨30842859245654016022953785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82247624655077376061210093 30842859245654016022953785)
        ·
          refine ⟨23132144434240512017215339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30842859245654016022953785 23132144434240512017215339)
          ·
            refine ⟨34698216651360768025823009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23132144434240512017215339 34698216651360768025823009)
            ·
              refine ⟨26023662488520576019367257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34698216651360768025823009 26023662488520576019367257)
              ·
                refine ⟨19517746866390432014525443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26023662488520576019367257 19517746866390432014525443)
                ·
                  refine ⟨29276620299585648021788165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19517746866390432014525443 29276620299585648021788165)
                  ·
                    refine ⟨5489366306172309004085281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29276620299585648021788165 5489366306172309004085281)
                    ·
                      refine ⟨4117024729629231753063961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5489366306172309004085281 4117024729629231753063961)
                      ·
                        rfl

theorem cell23_8017877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_8017877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017877 prefixEnd_8017877 := by exact prefixLift 8017877
  have htrace : WordTrace (prefixWord ++ tailWord_8017877) baseStart_8017877 baseEnd_8017877 := by
    simpa [prefixWord, tailWord_8017877, baseEnd_8017877] using wordTrace_append hprefix tailTrace_8017877
  have hstable : (prefixWord ++ tailWord_8017877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017877).length < 2 ^ (prefixWord ++ tailWord_8017877).sum := by decide
  have hdescent : baseEnd_8017877 < baseStart_8017877 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017881 : List Nat := [1, 2, 1, 2, 6, 2, 2, 1, 1, 3, 2]
def baseStart_8017881 : Nat := 118140960795 + 8017881 * 2 ^ 59
def prefixEnd_8017881 : Nat := 4983230072969 + 3 ^ 40 * 8017881 * 2
def baseEnd_8017881 : Nat := 4117026783551849737413943

theorem tailTrace_8017881 : CollatzResearch.WordTrace tailWord_8017881 prefixEnd_8017881 4117026783551849737413943 := by
  unfold tailWord_8017881
  simp only [CollatzResearch.WordTrace]
  refine ⟨292436144665593956900781497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194957429777062637933854331 292436144665593956900781497)
  ·
    refine ⟨219327108499195467675586123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292436144665593956900781497 219327108499195467675586123)
    ·
      refine ⟨328990662748793201513379185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219327108499195467675586123 328990662748793201513379185)
      ·
        refine ⟨246742997061594901135034389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328990662748793201513379185 246742997061594901135034389)
        ·
          refine ⟨11566077987262260990704737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 246742997061594901135034389 11566077987262260990704737)
          ·
            refine ⟨8674558490446695743028553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11566077987262260990704737 8674558490446695743028553)
            ·
              refine ⟨6505918867835021807271415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8674558490446695743028553 6505918867835021807271415)
              ·
                refine ⟨9758878301752532710907123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6505918867835021807271415 9758878301752532710907123)
                ·
                  refine ⟨14638317452628799066360685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9758878301752532710907123 14638317452628799066360685)
                  ·
                    refine ⟨5489369044735799649885257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14638317452628799066360685 5489369044735799649885257)
                    ·
                      refine ⟨4117026783551849737413943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5489369044735799649885257 4117026783551849737413943)
                      ·
                        rfl

theorem cell23_8017881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 1, 3, 2].length) (baseStart_8017881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017881 prefixEnd_8017881 := by exact prefixLift 8017881
  have htrace : WordTrace (prefixWord ++ tailWord_8017881) baseStart_8017881 baseEnd_8017881 := by
    simpa [prefixWord, tailWord_8017881, baseEnd_8017881] using wordTrace_append hprefix tailTrace_8017881
  have hstable : (prefixWord ++ tailWord_8017881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017881).length < 2 ^ (prefixWord ++ tailWord_8017881).sum := by decide
  have hdescent : baseEnd_8017881 < baseStart_8017881 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017913 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 1, 7]
def baseStart_8017913 : Nat := 118140960795 + 8017913 * 2 ^ 59
def prefixEnd_8017913 : Nat := 4983230072969 + 3 ^ 40 * 8017913 * 2
def baseEnd_8017913 : Nat := 1372347738310931204071265

theorem tailTrace_8017913 : CollatzResearch.WordTrace tailWord_8017913 prefixEnd_8017913 1372347738310931204071265 := by
  unfold tailWord_8017913
  simp only [CollatzResearch.WordTrace]
  refine ⟨292437311801478026365946393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194958207867652017577297595 292437311801478026365946393)
  ·
    refine ⟨219327983851108519774459795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292437311801478026365946393 219327983851108519774459795)
    ·
      refine ⟨328991975776662779661689693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219327983851108519774459795 328991975776662779661689693)
      ·
        refine ⟨123371990916248542373133635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328991975776662779661689693 123371990916248542373133635)
        ·
          refine ⟨185057986374372813559700453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123371990916248542373133635 185057986374372813559700453)
          ·
            refine ⟨34698372445194902542443835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185057986374372813559700453 34698372445194902542443835)
            ·
              refine ⟨52047558667792353813665753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34698372445194902542443835 52047558667792353813665753)
              ·
                refine ⟨39035669000844265360249315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52047558667792353813665753 39035669000844265360249315)
                ·
                  refine ⟨58553503501266398040373973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39035669000844265360249315 58553503501266398040373973)
                  ·
                    refine ⟨1372347738310931204071265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58553503501266398040373973 1372347738310931204071265)
                    ·
                      rfl

theorem cell23_8017913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 7].length) (baseStart_8017913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017913 prefixEnd_8017913 := by exact prefixLift 8017913
  have htrace : WordTrace (prefixWord ++ tailWord_8017913) baseStart_8017913 baseEnd_8017913 := by
    simpa [prefixWord, tailWord_8017913, baseEnd_8017913] using wordTrace_append hprefix tailTrace_8017913
  have hstable : (prefixWord ++ tailWord_8017913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017913).length < 2 ^ (prefixWord ++ tailWord_8017913).sum := by decide
  have hdescent : baseEnd_8017913 < baseStart_8017913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8017963 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 4]
def baseStart_8017963 : Nat := 118140960795 + 8017963 * 2 ^ 59
def prefixEnd_8017963 : Nat := 4983230072969 + 3 ^ 40 * 8017963 * 2
def baseEnd_8017963 : Nat := 4117068888965518416588565

theorem tailTrace_8017963 : CollatzResearch.WordTrace tailWord_8017963 prefixEnd_8017963 4117068888965518416588565 := by
  unfold tailWord_8017963
  simp only [CollatzResearch.WordTrace]
  refine ⟨292439135451296884905266543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194959423634197923270177695 292439135451296884905266543)
  ·
    refine ⟨438658703176945327357899815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292439135451296884905266543 438658703176945327357899815)
    ·
      refine ⟨657988054765417991036849723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438658703176945327357899815 657988054765417991036849723)
      ·
        refine ⟨986982082148126986555274585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657988054765417991036849723 986982082148126986555274585)
        ·
          refine ⟨740236561611095239916455939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 986982082148126986555274585 740236561611095239916455939)
          ·
            refine ⟨1110354842416642859874683909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740236561611095239916455939 1110354842416642859874683909)
            ·
              refine ⟨208191532953120536226503233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1110354842416642859874683909 208191532953120536226503233)
              ·
                refine ⟨156143649714840402169877425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208191532953120536226503233 156143649714840402169877425)
                ·
                  refine ⟨117107737286130301627408069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156143649714840402169877425 117107737286130301627408069)
                  ·
                    refine ⟨21957700741149431555139013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117107737286130301627408069 21957700741149431555139013)
                    ·
                      refine ⟨4117068888965518416588565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21957700741149431555139013 4117068888965518416588565)
                      ·
                        rfl

theorem cell23_8017963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 4].length) (baseStart_8017963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8017963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8017963 prefixEnd_8017963 := by exact prefixLift 8017963
  have htrace : WordTrace (prefixWord ++ tailWord_8017963) baseStart_8017963 baseEnd_8017963 := by
    simpa [prefixWord, tailWord_8017963, baseEnd_8017963] using wordTrace_append hprefix tailTrace_8017963
  have hstable : (prefixWord ++ tailWord_8017963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8017963).length < 2 ^ (prefixWord ++ tailWord_8017963).sum := by decide
  have hdescent : baseEnd_8017963 < baseStart_8017963 := by decide
  rcases family_descends (prefixWord ++ tailWord_8017963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018017 : List Nat := [1, 2, 3, 1, 1, 2, 1, 5, 3, 1, 3]
def baseStart_8018017 : Nat := 118140960795 + 8018017 * 2 ^ 59
def prefixEnd_8018017 : Nat := 4983230072969 + 3 ^ 40 * 8018017 * 2
def baseEnd_8018017 : Nat := 4117096616920861205313317

theorem tailTrace_8018017 : CollatzResearch.WordTrace tailWord_8018017 prefixEnd_8018017 4117096616920861205313317 := by
  unfold tailWord_8018017
  simp only [CollatzResearch.WordTrace]
  refine ⟨292441104993101252127732305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194960736662067501418488203 292441104993101252127732305)
  ·
    refine ⟨219330828744825939095799229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292441104993101252127732305 219330828744825939095799229)
    ·
      refine ⟨82249060779309727160924711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219330828744825939095799229 82249060779309727160924711)
      ·
        refine ⟨123373591168964590741387067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82249060779309727160924711 123373591168964590741387067)
        ·
          refine ⟨185060386753446886112080601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123373591168964590741387067 185060386753446886112080601)
          ·
            refine ⟨138795290065085164584060451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185060386753446886112080601 138795290065085164584060451)
            ·
              refine ⟨208192935097627746876090677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138795290065085164584060451 208192935097627746876090677)
              ·
                refine ⟨19518087665402601269633501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208192935097627746876090677 19518087665402601269633501)
                ·
                  refine ⟨7319282874525975476112563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19518087665402601269633501 7319282874525975476112563)
                  ·
                    refine ⟨10978924311788963214168845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7319282874525975476112563 10978924311788963214168845)
                    ·
                      refine ⟨4117096616920861205313317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10978924311788963214168845 4117096616920861205313317)
                      ·
                        rfl

theorem cell23_8018017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_8018017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018017 prefixEnd_8018017 := by exact prefixLift 8018017
  have htrace : WordTrace (prefixWord ++ tailWord_8018017) baseStart_8018017 baseEnd_8018017 := by
    simpa [prefixWord, tailWord_8018017, baseEnd_8018017] using wordTrace_append hprefix tailTrace_8018017
  have hstable : (prefixWord ++ tailWord_8018017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018017).length < 2 ^ (prefixWord ++ tailWord_8018017).sum := by decide
  have hdescent : baseEnd_8018017 < baseStart_8018017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018020 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 3, 5]
def baseStart_8018020 : Nat := 118140960795 + 8018020 * 2 ^ 59
def prefixEnd_8018020 : Nat := 4983230072969 + 3 ^ 40 * 8018020 * 2
def baseEnd_8018020 : Nat := 1372366052454274897858601

theorem tailTrace_8018020 : CollatzResearch.WordTrace tailWord_8018020 prefixEnd_8018020 1372366052454274897858601 := by
  unfold tailWord_8018020
  simp only [CollatzResearch.WordTrace]
  refine ⟨146220607206045191820045757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194960809608060255760061009 146220607206045191820045757)
  ·
    refine ⟨54832727702266946932517159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146220607206045191820045757 54832727702266946932517159)
    ·
      refine ⟨82249091553400420398775739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54832727702266946932517159 82249091553400420398775739)
      ·
        refine ⟨123373637330100630598163609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82249091553400420398775739 123373637330100630598163609)
        ·
          refine ⟨92530227997575472948622707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123373637330100630598163609 92530227997575472948622707)
          ·
            refine ⟨138795341996363209422934061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92530227997575472948622707 138795341996363209422934061)
            ·
              refine ⟨52048253248636203533600273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138795341996363209422934061 52048253248636203533600273)
              ·
                refine ⟨39036189936477152650200205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52048253248636203533600273 39036189936477152650200205)
                ·
                  refine ⟨14638571226178932243825077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39036189936477152650200205 14638571226178932243825077)
                  ·
                    refine ⟨1372366052454274897858601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14638571226178932243825077 1372366052454274897858601)
                    ·
                      rfl

theorem cell23_8018020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_8018020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018020 prefixEnd_8018020 := by exact prefixLift 8018020
  have htrace : WordTrace (prefixWord ++ tailWord_8018020) baseStart_8018020 baseEnd_8018020 := by
    simpa [prefixWord, tailWord_8018020, baseEnd_8018020] using wordTrace_append hprefix tailTrace_8018020
  have hstable : (prefixWord ++ tailWord_8018020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018020).length < 2 ^ (prefixWord ++ tailWord_8018020).sum := by decide
  have hdescent : baseEnd_8018020 < baseStart_8018020 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018030 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_8018030 : Nat := 118140960795 + 8018030 * 2 ^ 59
def prefixEnd_8018030 : Nat := 4983230072969 + 3 ^ 40 * 8018030 * 2
def baseEnd_8018030 : Nat := 4117103292169369654450757

theorem tailTrace_8018030 : CollatzResearch.WordTrace tailWord_8018030 prefixEnd_8018030 4117103292169369654450757 := by
  unfold tailWord_8018030
  simp only [CollatzResearch.WordTrace]
  refine ⟨36555197392756769418494443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194961052761369436898637029 36555197392756769418494443)
  ·
    refine ⟨54832796089135154127741665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36555197392756769418494443 54832796089135154127741665)
    ·
      refine ⟨41124597066851365595806249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54832796089135154127741665 41124597066851365595806249)
      ·
        refine ⟨30843447800138524196854687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41124597066851365595806249 30843447800138524196854687)
        ·
          refine ⟨46265171700207786295282031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30843447800138524196854687 46265171700207786295282031)
          ·
            refine ⟨69397757550311679442923047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46265171700207786295282031 69397757550311679442923047)
            ·
              refine ⟨104096636325467519164384571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69397757550311679442923047 104096636325467519164384571)
              ·
                refine ⟨156144954488201278746576857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104096636325467519164384571 156144954488201278746576857)
                ·
                  refine ⟨117108715866150959059932643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156144954488201278746576857 117108715866150959059932643)
                  ·
                    refine ⟨175663073799226438589898965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117108715866150959059932643 175663073799226438589898965)
                    ·
                      refine ⟨4117103292169369654450757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175663073799226438589898965 4117103292169369654450757)
                      ·
                        rfl

theorem cell23_8018030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_8018030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018030 prefixEnd_8018030 := by exact prefixLift 8018030
  have htrace : WordTrace (prefixWord ++ tailWord_8018030) baseStart_8018030 baseEnd_8018030 := by
    simpa [prefixWord, tailWord_8018030, baseEnd_8018030] using wordTrace_append hprefix tailTrace_8018030
  have hstable : (prefixWord ++ tailWord_8018030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018030).length < 2 ^ (prefixWord ++ tailWord_8018030).sum := by decide
  have hdescent : baseEnd_8018030 < baseStart_8018030 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018034 : List Nat := [3, 2, 1, 2, 2, 3, 1, 2, 3, 1, 3]
def baseStart_8018034 : Nat := 118140960795 + 8018034 * 2 ^ 59
def prefixEnd_8018034 : Nat := 4983230072969 + 3 ^ 40 * 8018034 * 2
def baseEnd_8018034 : Nat := 4117105346091987638800739

theorem tailTrace_8018034 : CollatzResearch.WordTrace tailWord_8018034 prefixEnd_8018034 4117105346091987638800739 := by
  unfold tailWord_8018034
  simp only [CollatzResearch.WordTrace]
  refine ⟨73110431258509916007775289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194961150022693109354067437 73110431258509916007775289)
  ·
    refine ⟨54832823443882437005831467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73110431258509916007775289 54832823443882437005831467)
    ·
      refine ⟨82249235165823655508747201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54832823443882437005831467 82249235165823655508747201)
      ·
        refine ⟨61686926374367741631560401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82249235165823655508747201 61686926374367741631560401)
        ·
          refine ⟨46265194780775806223670301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61686926374367741631560401 46265194780775806223670301)
          ·
            refine ⟨17349448042790927333876363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46265194780775806223670301 17349448042790927333876363)
            ·
              refine ⟨26024172064186391000814545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17349448042790927333876363 26024172064186391000814545)
              ·
                refine ⟨19518129048139793250610909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26024172064186391000814545 19518129048139793250610909)
                ·
                  refine ⟨7319298393052422468979091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19518129048139793250610909 7319298393052422468979091)
                  ·
                    refine ⟨10978947589578633703468637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7319298393052422468979091 10978947589578633703468637)
                    ·
                      refine ⟨4117105346091987638800739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10978947589578633703468637 4117105346091987638800739)
                      ·
                        rfl

theorem cell23_8018034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_8018034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018034 prefixEnd_8018034 := by exact prefixLift 8018034
  have htrace : WordTrace (prefixWord ++ tailWord_8018034) baseStart_8018034 baseEnd_8018034 := by
    simpa [prefixWord, tailWord_8018034, baseEnd_8018034] using wordTrace_append hprefix tailTrace_8018034
  have hstable : (prefixWord ++ tailWord_8018034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018034).length < 2 ^ (prefixWord ++ tailWord_8018034).sum := by decide
  have hdescent : baseEnd_8018034 < baseStart_8018034 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018044 : List Nat := [2, 2, 2, 1, 1, 4, 3, 1, 2, 3, 2]
def baseStart_8018044 : Nat := 118140960795 + 8018044 * 2 ^ 59
def prefixEnd_8018044 : Nat := 4983230072969 + 3 ^ 40 * 8018044 * 2
def baseEnd_8018044 : Nat := 4117110480898532599675693

theorem tailTrace_8018044 : CollatzResearch.WordTrace tailWord_8018044 prefixEnd_8018044 4117110480898532599675693 := by
  unfold tailWord_8018044
  simp only [CollatzResearch.WordTrace]
  refine ⟨146221044882001717869482593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194961393176002290492643457 146221044882001717869482593)
  ·
    refine ⟨109665783661501288402111945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146221044882001717869482593 109665783661501288402111945)
    ·
      refine ⟨82249337746125966301583959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109665783661501288402111945 82249337746125966301583959)
      ·
        refine ⟨123374006619188949452375939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82249337746125966301583959 123374006619188949452375939)
        ·
          refine ⟨185061009928783424178563909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123374006619188949452375939 185061009928783424178563909)
          ·
            refine ⟨34698939361646892033480733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185061009928783424178563909 34698939361646892033480733)
            ·
              refine ⟨13012102260617584512555275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34698939361646892033480733 13012102260617584512555275)
              ·
                refine ⟨19518153390926376768832913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13012102260617584512555275 19518153390926376768832913)
                ·
                  refine ⟨14638615043194782576624685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19518153390926376768832913 14638615043194782576624685)
                  ·
                    refine ⟨5489480641198043466234257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14638615043194782576624685 5489480641198043466234257)
                    ·
                      refine ⟨4117110480898532599675693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5489480641198043466234257 4117110480898532599675693)
                      ·
                        rfl

theorem cell23_8018044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_8018044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018044 prefixEnd_8018044 := by exact prefixLift 8018044
  have htrace : WordTrace (prefixWord ++ tailWord_8018044) baseStart_8018044 baseEnd_8018044 := by
    simpa [prefixWord, tailWord_8018044, baseEnd_8018044] using wordTrace_append hprefix tailTrace_8018044
  have hstable : (prefixWord ++ tailWord_8018044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018044).length < 2 ^ (prefixWord ++ tailWord_8018044).sum := by decide
  have hdescent : baseEnd_8018044 < baseStart_8018044 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018051 : List Nat := [1, 1, 1, 3, 3, 4, 2, 3, 1, 1, 3]
def baseStart_8018051 : Nat := 118140960795 + 8018051 * 2 ^ 59
def prefixEnd_8018051 : Nat := 4983230072969 + 3 ^ 40 * 8018051 * 2
def baseEnd_8018051 : Nat := 4117114075263114072288161

theorem tailTrace_8018051 : CollatzResearch.WordTrace tailWord_8018051 prefixEnd_8018051 4117114075263114072288161 := by
  unfold tailWord_8018051
  simp only [CollatzResearch.WordTrace]
  refine ⟨292442345074978075934470007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194961563383318717289646671 292442345074978075934470007)
  ·
    refine ⟨438663517612467113901705011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292442345074978075934470007 438663517612467113901705011)
    ·
      refine ⟨657995276418700670852557517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438663517612467113901705011 657995276418700670852557517)
      ·
        refine ⟨246748228657012751569709069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 657995276418700670852557517 246748228657012751569709069)
        ·
          refine ⟨92530585746379781838640901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246748228657012751569709069 92530585746379781838640901)
          ·
            refine ⟨17349484827446209094745169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92530585746379781838640901 17349484827446209094745169)
            ·
              refine ⟨13012113620584656821058877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17349484827446209094745169 13012113620584656821058877)
              ·
                refine ⟨4879542607719246307897079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13012113620584656821058877 4879542607719246307897079)
                ·
                  refine ⟨7319313911578869461845619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4879542607719246307897079 7319313911578869461845619)
                  ·
                    refine ⟨10978970867368304192768429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7319313911578869461845619 10978970867368304192768429)
                    ·
                      refine ⟨4117114075263114072288161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10978970867368304192768429 4117114075263114072288161)
                      ·
                        rfl

theorem cell23_8018051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 1, 1, 3].length) (baseStart_8018051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018051 prefixEnd_8018051 := by exact prefixLift 8018051
  have htrace : WordTrace (prefixWord ++ tailWord_8018051) baseStart_8018051 baseEnd_8018051 := by
    simpa [prefixWord, tailWord_8018051, baseEnd_8018051] using wordTrace_append hprefix tailTrace_8018051
  have hstable : (prefixWord ++ tailWord_8018051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018051).length < 2 ^ (prefixWord ++ tailWord_8018051).sum := by decide
  have hdescent : baseEnd_8018051 < baseStart_8018051 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018057 : List Nat := [1, 2, 1, 1, 4, 2, 3, 3, 1, 1, 4]
def baseStart_8018057 : Nat := 118140960795 + 8018057 * 2 ^ 59
def prefixEnd_8018057 : Nat := 4983230072969 + 3 ^ 40 * 8018057 * 2
def baseEnd_8018057 : Nat := 4117117156147041048813133

theorem tailTrace_8018057 : CollatzResearch.WordTrace tailWord_8018057 prefixEnd_8018057 4117117156147041048813133 := by
  unfold tailWord_8018057
  simp only [CollatzResearch.WordTrace]
  refine ⟨292442563912956338959188425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194961709275304225972792283 292442563912956338959188425)
  ·
    refine ⟨219331922934717254219391319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292442563912956338959188425 219331922934717254219391319)
    ·
      refine ⟨328997884402075881329086979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219331922934717254219391319 328997884402075881329086979)
      ·
        refine ⟨493496826603113821993630469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328997884402075881329086979 493496826603113821993630469)
        ·
          refine ⟨92530654988083841623805713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 493496826603113821993630469 92530654988083841623805713)
          ·
            refine ⟨69397991241062881217854285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92530654988083841623805713 69397991241062881217854285)
            ·
              refine ⟨26024246715398580456695357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69397991241062881217854285 26024246715398580456695357)
              ·
                refine ⟨9759092518274467671260759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26024246715398580456695357 9759092518274467671260759)
                ·
                  refine ⟨14638638777411701506891139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9759092518274467671260759 14638638777411701506891139)
                  ·
                    refine ⟨21957958166117552260336709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14638638777411701506891139 21957958166117552260336709)
                    ·
                      refine ⟨4117117156147041048813133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21957958166117552260336709 4117117156147041048813133)
                      ·
                        rfl

theorem cell23_8018057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 1, 4].length) (baseStart_8018057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018057 prefixEnd_8018057 := by exact prefixLift 8018057
  have htrace : WordTrace (prefixWord ++ tailWord_8018057) baseStart_8018057 baseEnd_8018057 := by
    simpa [prefixWord, tailWord_8018057, baseEnd_8018057] using wordTrace_append hprefix tailTrace_8018057
  have hstable : (prefixWord ++ tailWord_8018057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018057).length < 2 ^ (prefixWord ++ tailWord_8018057).sum := by decide
  have hdescent : baseEnd_8018057 < baseStart_8018057 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018068 : List Nat := [2, 4, 2, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_8018068 : Nat := 118140960795 + 8018068 * 2 ^ 59
def prefixEnd_8018068 : Nat := 4983230072969 + 3 ^ 40 * 8018068 * 2
def baseEnd_8018068 : Nat := 4117122804434240505775583

theorem tailTrace_8018068 : CollatzResearch.WordTrace tailWord_8018068 prefixEnd_8018068 4117122804434240505775583 := by
  unfold tailWord_8018068
  simp only [CollatzResearch.WordTrace]
  refine ⟨146221482557958243918919429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194961976743944325225225905 146221482557958243918919429)
  ·
    refine ⟨27416527979617170734797393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146221482557958243918919429 27416527979617170734797393)
    ·
      refine ⟨20562395984712878051098045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27416527979617170734797393 20562395984712878051098045)
      ·
        refine ⟨7710898494267329269161767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20562395984712878051098045 7710898494267329269161767)
        ·
          refine ⟨11566347741400993903742651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7710898494267329269161767 11566347741400993903742651)
          ·
            refine ⟨17349521612101490855613977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11566347741400993903742651 17349521612101490855613977)
            ·
              refine ⟨13012141209076118141710483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17349521612101490855613977 13012141209076118141710483)
              ·
                refine ⟨19518211813614177212565725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13012141209076118141710483 19518211813614177212565725)
                ·
                  refine ⟨7319329430105316454712147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19518211813614177212565725 7319329430105316454712147)
                  ·
                    refine ⟨10978994145157974682068221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7319329430105316454712147 10978994145157974682068221)
                    ·
                      refine ⟨4117122804434240505775583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10978994145157974682068221 4117122804434240505775583)
                      ·
                        rfl

theorem cell23_8018068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_8018068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018068 prefixEnd_8018068 := by exact prefixLift 8018068
  have htrace : WordTrace (prefixWord ++ tailWord_8018068) baseStart_8018068 baseEnd_8018068 := by
    simpa [prefixWord, tailWord_8018068, baseEnd_8018068] using wordTrace_append hprefix tailTrace_8018068
  have hstable : (prefixWord ++ tailWord_8018068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018068).length < 2 ^ (prefixWord ++ tailWord_8018068).sum := by decide
  have hdescent : baseEnd_8018068 < baseStart_8018068 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018077 : List Nat := [1, 4, 2, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_8018077 : Nat := 118140960795 + 8018077 * 2 ^ 59
def prefixEnd_8018077 : Nat := 4983230072969 + 3 ^ 40 * 8018077 * 2
def baseEnd_8018077 : Nat := 4117127425760130970563041

theorem tailTrace_8018077 : CollatzResearch.WordTrace tailWord_8018077 prefixEnd_8018077 4117127425760130970563041 := by
  unfold tailWord_8018077
  simp only [CollatzResearch.WordTrace]
  refine ⟨292443293372883882374916485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194962195581922588249944323 292443293372883882374916485)
  ·
    refine ⟨54833117507415727945296841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292443293372883882374916485 54833117507415727945296841)
    ·
      refine ⟨41124838130561795958972631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54833117507415727945296841 41124838130561795958972631)
      ·
        refine ⟨61687257195842693938458947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41124838130561795958972631 61687257195842693938458947)
        ·
          refine ⟨92530885793764040907688421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61687257195842693938458947 92530885793764040907688421)
          ·
            refine ⟨17349541086330757670191579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92530885793764040907688421 17349541086330757670191579)
            ·
              refine ⟨26024311629496136505287369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17349541086330757670191579 26024311629496136505287369)
              ·
                refine ⟨19518233722122102378965527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26024311629496136505287369 19518233722122102378965527)
                ·
                  refine ⟨29277350583183153568448291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19518233722122102378965527 29277350583183153568448291)
                  ·
                    refine ⟨43916025874774730352672437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29277350583183153568448291 43916025874774730352672437)
                    ·
                      refine ⟨4117127425760130970563041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43916025874774730352672437 4117127425760130970563041)
                      ·
                        rfl

theorem cell23_8018077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_8018077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018077 prefixEnd_8018077 := by exact prefixLift 8018077
  have htrace : WordTrace (prefixWord ++ tailWord_8018077) baseStart_8018077 baseEnd_8018077 := by
    simpa [prefixWord, tailWord_8018077, baseEnd_8018077] using wordTrace_append hprefix tailTrace_8018077
  have hstable : (prefixWord ++ tailWord_8018077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018077).length < 2 ^ (prefixWord ++ tailWord_8018077).sum := by decide
  have hdescent : baseEnd_8018077 < baseStart_8018077 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018084 : List Nat := [2, 3, 1, 2, 4, 2, 1, 1, 1, 6]
def baseStart_8018084 : Nat := 118140960795 + 8018084 * 2 ^ 59
def prefixEnd_8018084 : Nat := 4983230072969 + 3 ^ 40 * 8018084 * 2
def baseEnd_8018084 : Nat := 1372377006708237481058503

theorem tailTrace_8018084 : CollatzResearch.WordTrace tailWord_8018084 prefixEnd_8018084 1372377006708237481058503 := by
  unfold tailWord_8018084
  simp only [CollatzResearch.WordTrace]
  refine ⟨146221774341929261285210653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194962365789239015046947537 146221774341929261285210653)
  ·
    refine ⟨54833165378223472981953995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146221774341929261285210653 54833165378223472981953995)
    ·
      refine ⟨82249748067335209472930993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54833165378223472981953995 82249748067335209472930993)
      ·
        refine ⟨61687311050501407104698245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82249748067335209472930993 61687311050501407104698245)
        ·
          refine ⟨11566370821969013832130921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61687311050501407104698245 11566370821969013832130921)
          ·
            refine ⟨8674778116476760374098191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11566370821969013832130921 8674778116476760374098191)
            ·
              refine ⟨13012167174715140561147287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8674778116476760374098191 13012167174715140561147287)
              ·
                refine ⟨19518250762072710841720931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13012167174715140561147287 19518250762072710841720931)
                ·
                  refine ⟨29277376143109066262581397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19518250762072710841720931 29277376143109066262581397)
                  ·
                    refine ⟨1372377006708237481058503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29277376143109066262581397 1372377006708237481058503)
                    ·
                      rfl

theorem cell23_8018084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_8018084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018084 prefixEnd_8018084 := by exact prefixLift 8018084
  have htrace : WordTrace (prefixWord ++ tailWord_8018084) baseStart_8018084 baseEnd_8018084 := by
    simpa [prefixWord, tailWord_8018084, baseEnd_8018084] using wordTrace_append hprefix tailTrace_8018084
  have hstable : (prefixWord ++ tailWord_8018084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018084).length < 2 ^ (prefixWord ++ tailWord_8018084).sum := by decide
  have hdescent : baseEnd_8018084 < baseStart_8018084 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018097 : List Nat := [1, 2, 2, 5, 2, 1, 1, 9]
def baseStart_8018097 : Nat := 118140960795 + 8018097 * 2 ^ 59
def prefixEnd_8018097 : Nat := 4983230072969 + 3 ^ 40 * 8018097 * 2
def baseEnd_8018097 : Nat := 152486581310119292307887

theorem tailTrace_8018097 : CollatzResearch.WordTrace tailWord_8018097 prefixEnd_8018097 152486581310119292307887 := by
  unfold tailWord_8018097
  simp only [CollatzResearch.WordTrace]
  refine ⟨292444022832811425790644545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194962681888540950527096363 292444022832811425790644545)
  ·
    refine ⟨219333017124608569342983409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292444022832811425790644545 219333017124608569342983409)
    ·
      refine ⟨164499762843456427007237557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219333017124608569342983409 164499762843456427007237557)
      ·
        refine ⟨15421852766574040031928521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164499762843456427007237557 15421852766574040031928521)
        ·
          refine ⟨11566389574930530023946391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15421852766574040031928521 11566389574930530023946391)
          ·
            refine ⟨17349584362395795035919587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11566389574930530023946391 17349584362395795035919587)
            ·
              refine ⟨26024376543593692553879381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17349584362395795035919587 26024376543593692553879381)
              ·
                refine ⟨152486581310119292307887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26024376543593692553879381 152486581310119292307887)
                ·
                  rfl

theorem cell23_8018097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 9].length) (baseStart_8018097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018097 prefixEnd_8018097 := by exact prefixLift 8018097
  have htrace : WordTrace (prefixWord ++ tailWord_8018097) baseStart_8018097 baseEnd_8018097 := by
    simpa [prefixWord, tailWord_8018097, baseEnd_8018097] using wordTrace_append hprefix tailTrace_8018097
  have hstable : (prefixWord ++ tailWord_8018097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018097).length < 2 ^ (prefixWord ++ tailWord_8018097).sum := by decide
  have hdescent : baseEnd_8018097 < baseStart_8018097 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018107 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 6, 1, 3]
def baseStart_8018107 : Nat := 118140960795 + 8018107 * 2 ^ 59
def prefixEnd_8018107 : Nat := 4983230072969 + 3 ^ 40 * 8018107 * 2
def baseEnd_8018107 : Nat := 4117142830179765853187903

theorem tailTrace_8018107 : CollatzResearch.WordTrace tailWord_8018107 prefixEnd_8018107 4117142830179765853187903 := by
  unfold tailWord_8018107
  simp only [CollatzResearch.WordTrace]
  refine ⟨292444387562775197498508575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194962925041850131665672383 292444387562775197498508575)
  ·
    refine ⟨438666581344162796247762863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292444387562775197498508575 438666581344162796247762863)
    ·
      refine ⟨657999872016244194371644295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438666581344162796247762863 657999872016244194371644295)
      ·
        refine ⟨986999808024366291557466443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657999872016244194371644295 986999808024366291557466443)
        ·
          refine ⟨1480499712036549437336199665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 986999808024366291557466443 1480499712036549437336199665)
          ·
            refine ⟨1110374784027412078002149749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1480499712036549437336199665 1110374784027412078002149749)
            ·
              refine ⟨104097636002569882312701539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1110374784027412078002149749 104097636002569882312701539)
              ·
                refine ⟨156146454003854823469052309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104097636002569882312701539 156146454003854823469052309)
                ·
                  refine ⟨7319365031430694850111827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156146454003854823469052309 7319365031430694850111827)
                  ·
                    refine ⟨10979047547146042275167741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7319365031430694850111827 10979047547146042275167741)
                    ·
                      refine ⟨4117142830179765853187903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10979047547146042275167741 4117142830179765853187903)
                      ·
                        rfl

theorem cell23_8018107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 1, 3].length) (baseStart_8018107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018107 prefixEnd_8018107 := by exact prefixLift 8018107
  have htrace : WordTrace (prefixWord ++ tailWord_8018107) baseStart_8018107 baseEnd_8018107 := by
    simpa [prefixWord, tailWord_8018107, baseEnd_8018107] using wordTrace_append hprefix tailTrace_8018107
  have hstable : (prefixWord ++ tailWord_8018107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018107).length < 2 ^ (prefixWord ++ tailWord_8018107).sum := by decide
  have hdescent : baseEnd_8018107 < baseStart_8018107 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018114 : List Nat := [3, 5, 1, 1, 1, 1, 11]
def baseStart_8018114 : Nat := 118140960795 + 8018114 * 2 ^ 59
def prefixEnd_8018114 : Nat := 4983230072969 + 3 ^ 40 * 8018114 * 2
def baseEnd_8018114 : Nat := 50828968204251201553091

theorem tailTrace_8018114 : CollatzResearch.WordTrace tailWord_8018114 prefixEnd_8018114 50828968204251201553091 := by
  unfold tailWord_8018114
  simp only [CollatzResearch.WordTrace]
  refine ⟨73111160718437459423503349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194963095249166558462675597 73111160718437459423503349)
  ·
    refine ⟨6854171317353511820953439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73111160718437459423503349 6854171317353511820953439)
    ·
      refine ⟨10281256976030267731430159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6854171317353511820953439 10281256976030267731430159)
      ·
        refine ⟨15421885464045401597145239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10281256976030267731430159 15421885464045401597145239)
        ·
          refine ⟨23132828196068102395717859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15421885464045401597145239 23132828196068102395717859)
          ·
            refine ⟨34699242294102153593576789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23132828196068102395717859 34699242294102153593576789)
            ·
              refine ⟨50828968204251201553091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34699242294102153593576789 50828968204251201553091)
              ·
                rfl

theorem cell23_8018114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 11].length) (baseStart_8018114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018114 prefixEnd_8018114 := by exact prefixLift 8018114
  have htrace : WordTrace (prefixWord ++ tailWord_8018114) baseStart_8018114 baseEnd_8018114 := by
    simpa [prefixWord, tailWord_8018114, baseEnd_8018114] using wordTrace_append hprefix tailTrace_8018114
  have hstable : (prefixWord ++ tailWord_8018114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018114).length < 2 ^ (prefixWord ++ tailWord_8018114).sum := by decide
  have hdescent : baseEnd_8018114 < baseStart_8018114 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018120 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_8018120 : Nat := 118140960795 + 8018120 * 2 ^ 59
def prefixEnd_8018120 : Nat := 4983230072969 + 3 ^ 40 * 8018120 * 2
def baseEnd_8018120 : Nat := 4117149505428274302325343

theorem tailTrace_8018120 : CollatzResearch.WordTrace tailWord_8018120 prefixEnd_8018120 4117149505428274302325343 := by
  unfold tailWord_8018120
  simp only [CollatzResearch.WordTrace]
  refine ⟨146222430855864050359365907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194963241141152067145821209 146222430855864050359365907)
  ·
    refine ⟨219333646283796075539048861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146222430855864050359365907 219333646283796075539048861)
    ·
      refine ⟨82250117356423528327143323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219333646283796075539048861 82250117356423528327143323)
      ·
        refine ⟨123375176034635292490714985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82250117356423528327143323 123375176034635292490714985)
        ·
          refine ⟨92531382025976469368036239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123375176034635292490714985 92531382025976469368036239)
          ·
            refine ⟨138797073038964704052054359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92531382025976469368036239 138797073038964704052054359)
            ·
              refine ⟨208195609558447056078081539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138797073038964704052054359 208195609558447056078081539)
              ·
                refine ⟨312293414337670584117122309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208195609558447056078081539 312293414337670584117122309)
                ·
                  refine ⟨58555015188313234521960433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 312293414337670584117122309 58555015188313234521960433)
                  ·
                    refine ⟨43916261391234925891470325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58555015188313234521960433 43916261391234925891470325)
                    ·
                      refine ⟨4117149505428274302325343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43916261391234925891470325 4117149505428274302325343)
                      ·
                        rfl

theorem cell23_8018120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_8018120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018120 prefixEnd_8018120 := by exact prefixLift 8018120
  have htrace : WordTrace (prefixWord ++ tailWord_8018120) baseStart_8018120 baseEnd_8018120 := by
    simpa [prefixWord, tailWord_8018120, baseEnd_8018120] using wordTrace_append hprefix tailTrace_8018120
  have hstable : (prefixWord ++ tailWord_8018120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018120).length < 2 ^ (prefixWord ++ tailWord_8018120).sum := by decide
  have hdescent : baseEnd_8018120 < baseStart_8018120 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018151 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 3, 3, 2]
def baseStart_8018151 : Nat := 118140960795 + 8018151 * 2 ^ 59
def prefixEnd_8018151 : Nat := 4983230072969 + 3 ^ 40 * 8018151 * 2
def baseEnd_8018151 : Nat := 4117165423328563681037701

theorem tailTrace_8018151 : CollatzResearch.WordTrace tailWord_8018151 prefixEnd_8018151 4117165423328563681037701 := by
  unfold tailWord_8018151
  simp only [CollatzResearch.WordTrace]
  refine ⟨292445992374615793013110307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194963994916410528675406871 292445992374615793013110307)
  ·
    refine ⟨438668988561923689519665461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292445992374615793013110307 438668988561923689519665461)
    ·
      refine ⟨41125217677680345892468637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 438668988561923689519665461 41125217677680345892468637)
      ·
        refine ⟨15421956629130129709675739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41125217677680345892468637 15421956629130129709675739)
        ·
          refine ⟨23132934943695194564513609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15421956629130129709675739 23132934943695194564513609)
          ·
            refine ⟨17349701207771395923385207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23132934943695194564513609 17349701207771395923385207)
            ·
              refine ⟨26024551811657093885077811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17349701207771395923385207 26024551811657093885077811)
              ·
                refine ⟨39036827717485640827616717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26024551811657093885077811 39036827717485640827616717)
                ·
                  refine ⟨14638810394057115310356269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39036827717485640827616717 14638810394057115310356269)
                  ·
                    refine ⟨5489553897771418241383601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14638810394057115310356269 5489553897771418241383601)
                    ·
                      refine ⟨4117165423328563681037701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5489553897771418241383601 4117165423328563681037701)
                      ·
                        rfl

theorem cell23_8018151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_8018151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018151 prefixEnd_8018151 := by exact prefixLift 8018151
  have htrace : WordTrace (prefixWord ++ tailWord_8018151) baseStart_8018151 baseEnd_8018151 := by
    simpa [prefixWord, tailWord_8018151, baseEnd_8018151] using wordTrace_append hprefix tailTrace_8018151
  have hstable : (prefixWord ++ tailWord_8018151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018151).length < 2 ^ (prefixWord ++ tailWord_8018151).sum := by decide
  have hdescent : baseEnd_8018151 < baseStart_8018151 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018177 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_8018177 : Nat := 118140960795 + 8018177 * 2 ^ 59
def prefixEnd_8018177 : Nat := 4983230072969 + 3 ^ 40 * 8018177 * 2
def baseEnd_8018177 : Nat := 4117178773825580579312581

theorem tailTrace_8018177 : CollatzResearch.WordTrace tailWord_8018177 prefixEnd_8018177 4117178773825580579312581 := by
  unfold tailWord_8018177
  simp only [CollatzResearch.WordTrace]
  refine ⟨292446940672521599453556785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194964627115014399635704523 292446940672521599453556785)
  ·
    refine ⟨219335205504391199590167589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292446940672521599453556785 219335205504391199590167589)
    ·
      refine ⟨41125351032073349923156423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219335205504391199590167589 41125351032073349923156423)
      ·
        refine ⟨61688026548110024884734635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41125351032073349923156423 61688026548110024884734635)
        ·
          refine ⟨92532039822165037327101953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61688026548110024884734635 92532039822165037327101953)
          ·
            refine ⟨69399029866623777995326465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92532039822165037327101953 69399029866623777995326465)
            ·
              refine ⟨52049272399967833496494849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69399029866623777995326465 52049272399967833496494849)
              ·
                refine ⟨39036954299975875122371137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52049272399967833496494849 39036954299975875122371137)
                ·
                  refine ⟨29277715724981906341778353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39036954299975875122371137 29277715724981906341778353)
                  ·
                    refine ⟨21958286793736429756333765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29277715724981906341778353 21958286793736429756333765)
                    ·
                      refine ⟨4117178773825580579312581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21958286793736429756333765 4117178773825580579312581)
                      ·
                        rfl

theorem cell23_8018177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_8018177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018177 prefixEnd_8018177 := by exact prefixLift 8018177
  have htrace : WordTrace (prefixWord ++ tailWord_8018177) baseStart_8018177 baseEnd_8018177 := by
    simpa [prefixWord, tailWord_8018177, baseEnd_8018177] using wordTrace_append hprefix tailTrace_8018177
  have hstable : (prefixWord ++ tailWord_8018177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018177).length < 2 ^ (prefixWord ++ tailWord_8018177).sum := by decide
  have hdescent : baseEnd_8018177 < baseStart_8018177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018197 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 1, 5, 3]
def baseStart_8018197 : Nat := 118140960795 + 8018197 * 2 ^ 59
def prefixEnd_8018197 : Nat := 4983230072969 + 3 ^ 40 * 8018197 * 2
def baseEnd_8018197 : Nat := 4117189043438670501062489

theorem tailTrace_8018197 : CollatzResearch.WordTrace tailWord_8018197 prefixEnd_8018197 4117189043438670501062489 := by
  unfold tailWord_8018197
  simp only [CollatzResearch.WordTrace]
  refine ⟨292447670132449142869284845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194965113421632761912856563 292447670132449142869284845)
  ·
    refine ⟨109667876299668428575981817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292447670132449142869284845 109667876299668428575981817)
    ·
      refine ⟨82250907224751321431986363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109667876299668428575981817 82250907224751321431986363)
      ·
        refine ⟨123376360837126982147979545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82250907224751321431986363 123376360837126982147979545)
        ·
          refine ⟨92532270627845236610984659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123376360837126982147979545 92532270627845236610984659)
          ·
            refine ⟨138798405941767854916476989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92532270627845236610984659 138798405941767854916476989)
            ·
              refine ⟨52049402228162945593678871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138798405941767854916476989 52049402228162945593678871)
              ·
                refine ⟨78074103342244418390518307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52049402228162945593678871 78074103342244418390518307)
                ·
                  refine ⟨117111155013366627585777461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78074103342244418390518307 117111155013366627585777461)
                  ·
                    refine ⟨10979170782503121336166637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117111155013366627585777461 10979170782503121336166637)
                    ·
                      refine ⟨4117189043438670501062489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10979170782503121336166637 4117189043438670501062489)
                      ·
                        rfl

theorem cell23_8018197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_8018197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018197 prefixEnd_8018197 := by exact prefixLift 8018197
  have htrace : WordTrace (prefixWord ++ tailWord_8018197) baseStart_8018197 baseEnd_8018197 := by
    simpa [prefixWord, tailWord_8018197, baseEnd_8018197] using wordTrace_append hprefix tailTrace_8018197
  have hstable : (prefixWord ++ tailWord_8018197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018197).length < 2 ^ (prefixWord ++ tailWord_8018197).sum := by decide
  have hdescent : baseEnd_8018197 < baseStart_8018197 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018254 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2]
def baseStart_8018254 : Nat := 118140960795 + 8018254 * 2 ^ 59
def prefixEnd_8018254 : Nat := 4983230072969 + 3 ^ 40 * 8018254 * 2
def baseEnd_8018254 : Nat := 4117218311835976778049727

theorem tailTrace_8018254 : CollatzResearch.WordTrace tailWord_8018254 prefixEnd_8018254 4117218311835976778049727 := by
  unfold tailWord_8018254
  simp only [CollatzResearch.WordTrace]
  refine ⟨36556218636655330200513727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194966499395495094402739877 36556218636655330200513727)
  ·
    refine ⟨54834327954982995300770591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36556218636655330200513727 54834327954982995300770591)
    ·
      refine ⟨82251491932474492951155887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54834327954982995300770591 82251491932474492951155887)
      ·
        refine ⟨123377237898711739426733831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82251491932474492951155887 123377237898711739426733831)
        ·
          refine ⟨185065856848067609140100747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123377237898711739426733831 185065856848067609140100747)
          ·
            refine ⟨277598785272101413710151121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185065856848067609140100747 277598785272101413710151121)
            ·
              refine ⟨208199088954076060282613341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277598785272101413710151121 208199088954076060282613341)
              ·
                refine ⟨78074658357778522605980003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208199088954076060282613341 78074658357778522605980003)
                ·
                  refine ⟨117111987536667783908970005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78074658357778522605980003 117111987536667783908970005)
                  ·
                    refine ⟨5489624415781302370732969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117111987536667783908970005 5489624415781302370732969)
                    ·
                      refine ⟨4117218311835976778049727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5489624415781302370732969 4117218311835976778049727)
                      ·
                        rfl

theorem cell23_8018254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_8018254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018254 prefixEnd_8018254 := by exact prefixLift 8018254
  have htrace : WordTrace (prefixWord ++ tailWord_8018254) baseStart_8018254 baseEnd_8018254 := by
    simpa [prefixWord, tailWord_8018254, baseEnd_8018254] using wordTrace_append hprefix tailTrace_8018254
  have hstable : (prefixWord ++ tailWord_8018254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018254).length < 2 ^ (prefixWord ++ tailWord_8018254).sum := by decide
  have hdescent : baseEnd_8018254 < baseStart_8018254 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018277 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 8]
def baseStart_8018277 : Nat := 118140960795 + 8018277 * 2 ^ 59
def prefixEnd_8018277 : Nat := 4983230072969 + 3 ^ 40 * 8018277 * 2
def baseEnd_8018277 : Nat := 457470013543447798673569

theorem tailTrace_8018277 : CollatzResearch.WordTrace tailWord_8018277 prefixEnd_8018277 457470013543447798673569 := by
  unfold tailWord_8018277
  simp only [CollatzResearch.WordTrace]
  refine ⟨292450587972159316532197085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194967058648106211021464723 292450587972159316532197085)
  ·
    refine ⟨109668970489559743699573907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292450587972159316532197085 109668970489559743699573907)
    ·
      refine ⟨164503455734339615549360861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109668970489559743699573907 164503455734339615549360861)
      ·
        refine ⟨61688795900377355831010323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164503455734339615549360861 61688795900377355831010323)
        ·
          refine ⟨92533193850566033746515485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61688795900377355831010323 92533193850566033746515485)
          ·
            refine ⟨34699947693962262654943307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92533193850566033746515485 34699947693962262654943307)
            ·
              refine ⟨52049921540943393982414961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34699947693962262654943307 52049921540943393982414961)
              ·
                refine ⟨39037441155707545486811221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52049921540943393982414961 39037441155707545486811221)
                ·
                  refine ⟨457470013543447798673569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39037441155707545486811221 457470013543447798673569)
                  ·
                    rfl

theorem cell23_8018277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 8].length) (baseStart_8018277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018277 prefixEnd_8018277 := by exact prefixLift 8018277
  have htrace : WordTrace (prefixWord ++ tailWord_8018277) baseStart_8018277 baseEnd_8018277 := by
    simpa [prefixWord, tailWord_8018277, baseEnd_8018277] using wordTrace_append hprefix tailTrace_8018277
  have hstable : (prefixWord ++ tailWord_8018277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018277).length < 2 ^ (prefixWord ++ tailWord_8018277).sum := by decide
  have hdescent : baseEnd_8018277 < baseStart_8018277 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018341 : List Nat := [1, 3, 1, 2, 1, 1, 7, 1, 1, 5]
def baseStart_8018341 : Nat := 118140960795 + 8018341 * 2 ^ 59
def prefixEnd_8018341 : Nat := 4983230072969 + 3 ^ 40 * 8018341 * 2
def baseEnd_8018341 : Nat := 1372420994884305979220609

theorem tailTrace_8018341 : CollatzResearch.WordTrace tailWord_8018341 prefixEnd_8018341 1372420994884305979220609 := by
  unfold tailWord_8018341
  simp only [CollatzResearch.WordTrace]
  refine ⟨292452922243927455462526877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194968614829284970308351251 292452922243927455462526877)
  ·
    refine ⟨109669845841472795798447579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292452922243927455462526877 109669845841472795798447579)
    ·
      refine ⟨164504768762209193697671369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109669845841472795798447579 164504768762209193697671369)
      ·
        refine ⟨123378576571656895273253527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164504768762209193697671369 123378576571656895273253527)
        ·
          refine ⟨185067864857485342909880291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123378576571656895273253527 185067864857485342909880291)
          ·
            refine ⟨277601797286228014364820437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185067864857485342909880291 277601797286228014364820437)
            ·
              refine ⟨6506292123895969086675479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 277601797286228014364820437 6506292123895969086675479)
              ·
                refine ⟨9759438185843953630013219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6506292123895969086675479 9759438185843953630013219)
                ·
                  refine ⟨14639157278765930445019829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9759438185843953630013219 14639157278765930445019829)
                  ·
                    refine ⟨1372420994884305979220609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14639157278765930445019829 1372420994884305979220609)
                    ·
                      rfl

theorem cell23_8018341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 1, 5].length) (baseStart_8018341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018341 prefixEnd_8018341 := by exact prefixLift 8018341
  have htrace : WordTrace (prefixWord ++ tailWord_8018341) baseStart_8018341 baseEnd_8018341 := by
    simpa [prefixWord, tailWord_8018341, baseEnd_8018341] using wordTrace_append hprefix tailTrace_8018341
  have hstable : (prefixWord ++ tailWord_8018341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018341).length < 2 ^ (prefixWord ++ tailWord_8018341).sum := by decide
  have hdescent : baseEnd_8018341 < baseStart_8018341 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018349 : List Nat := [1, 5, 2, 2, 3, 1, 2, 2, 1, 4]
def baseStart_8018349 : Nat := 118140960795 + 8018349 * 2 ^ 59
def prefixEnd_8018349 : Nat := 4983230072969 + 3 ^ 40 * 8018349 * 2
def baseEnd_8018349 : Nat := 1372422364166051302120597

theorem tailTrace_8018349 : CollatzResearch.WordTrace tailWord_8018349 prefixEnd_8018349 1372422364166051302120597 := by
  unfold tailWord_8018349
  simp only [CollatzResearch.WordTrace]
  refine ⟨292453214027898472828818101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194968809351932315219212067 292453214027898472828818101)
  ·
    refine ⟨27417488815115481827701697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 292453214027898472828818101 27417488815115481827701697)
    ·
      refine ⟨20563116611336611370776273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27417488815115481827701697 20563116611336611370776273)
      ·
        refine ⟨15422337458502458528082205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20563116611336611370776273 15422337458502458528082205)
        ·
          refine ⟨5783376546938421948030827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15422337458502458528082205 5783376546938421948030827)
          ·
            refine ⟨8675064820407632922046241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5783376546938421948030827 8675064820407632922046241)
            ·
              refine ⟨6506298615305724691534681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8675064820407632922046241 6506298615305724691534681)
              ·
                refine ⟨4879723961479293518651011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6506298615305724691534681 4879723961479293518651011)
                ·
                  refine ⟨7319585942218940277976517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4879723961479293518651011 7319585942218940277976517)
                  ·
                    refine ⟨1372422364166051302120597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7319585942218940277976517 1372422364166051302120597)
                    ·
                      rfl

theorem cell23_8018349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_8018349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018349 prefixEnd_8018349 := by exact prefixLift 8018349
  have htrace : WordTrace (prefixWord ++ tailWord_8018349) baseStart_8018349 baseEnd_8018349 := by
    simpa [prefixWord, tailWord_8018349, baseEnd_8018349] using wordTrace_append hprefix tailTrace_8018349
  have hstable : (prefixWord ++ tailWord_8018349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018349).length < 2 ^ (prefixWord ++ tailWord_8018349).sum := by decide
  have hdescent : baseEnd_8018349 < baseStart_8018349 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8018378 : List Nat := [3, 1, 2, 1, 2, 2, 3, 2, 3, 2, 2]
def baseStart_8018378 : Nat := 118140960795 + 8018378 * 2 ^ 59
def prefixEnd_8018378 : Nat := 4983230072969 + 3 ^ 40 * 8018378 * 2
def baseEnd_8018378 : Nat := 4117281983437134292899157

theorem tailTrace_8018378 : CollatzResearch.WordTrace tailWord_8018378 prefixEnd_8018378 4117281983437134292899157 := by
  unfold tailWord_8018378
  simp only [CollatzResearch.WordTrace]
  refine ⟨73113567936198352695405947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194969514496528940521082525 73113567936198352695405947)
  ·
    refine ⟨109670351904297529043108921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73113567936198352695405947 109670351904297529043108921)
    ·
      refine ⟨82252763928223146782331691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109670351904297529043108921 82252763928223146782331691)
      ·
        refine ⟨123379145892334720173497537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82252763928223146782331691 123379145892334720173497537)
        ·
          refine ⟨92534359419251040130123153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123379145892334720173497537 92534359419251040130123153)
          ·
            refine ⟨69400769564438280097592365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92534359419251040130123153 69400769564438280097592365)
            ·
              refine ⟨26025288586664355036597137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69400769564438280097592365 26025288586664355036597137)
              ·
                refine ⟨19518966439998266277447853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26025288586664355036597137 19518966439998266277447853)
                ·
                  refine ⟨7319612414999349854042945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19518966439998266277447853 7319612414999349854042945)
                  ·
                    refine ⟨5489709311249512390532209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7319612414999349854042945 5489709311249512390532209)
                    ·
                      refine ⟨4117281983437134292899157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5489709311249512390532209 4117281983437134292899157)
                      ·
                        rfl

theorem cell23_8018378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_8018378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8018378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8018378 prefixEnd_8018378 := by exact prefixLift 8018378
  have htrace : WordTrace (prefixWord ++ tailWord_8018378) baseStart_8018378 baseEnd_8018378 := by
    simpa [prefixWord, tailWord_8018378, baseEnd_8018378] using wordTrace_append hprefix tailTrace_8018378
  have hstable : (prefixWord ++ tailWord_8018378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8018378).length < 2 ^ (prefixWord ++ tailWord_8018378).sum := by decide
  have hdescent : baseEnd_8018378 < baseStart_8018378 := by decide
  rcases family_descends (prefixWord ++ tailWord_8018378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
