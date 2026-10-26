import V185TrunkScan22Chunk265

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2371082 : List Nat := [3, 1, 2, 2, 2, 2, 3, 2, 2, 3]
def baseStart_2371082 : Nat := 118140960795 + 2371082 * 2 ^ 59
def prefixEnd_2371082 : Nat := 4983230072969 + 3 ^ 40 * 2371082 * 2
def baseEnd_2371082 : Nat := 811669824815998242980399

theorem tailTrace_2371082 : CollatzResearch.WordTrace tailWord_2371082 prefixEnd_2371082 811669824815998242980399 := by
  unfold tailWord_2371082
  simp only [CollatzResearch.WordTrace]
  refine ⟨21620116298995584352776875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57653643463988224940738333 21620116298995584352776875)
  ·
    refine ⟨32430174448493376529165313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21620116298995584352776875 32430174448493376529165313)
    ·
      refine ⟨24322630836370032396873985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32430174448493376529165313 24322630836370032396873985)
      ·
        refine ⟨18241973127277524297655489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24322630836370032396873985 18241973127277524297655489)
        ·
          refine ⟨13681479845458143223241617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18241973127277524297655489 13681479845458143223241617)
          ·
            refine ⟨10261109884093607417431213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13681479845458143223241617 10261109884093607417431213)
            ·
              refine ⟨3847916206535102781536705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10261109884093607417431213 3847916206535102781536705)
              ·
                refine ⟨2885937154901327086152529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3847916206535102781536705 2885937154901327086152529)
                ·
                  refine ⟨2164452866175995314614397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2885937154901327086152529 2164452866175995314614397)
                  ·
                    refine ⟨811669824815998242980399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2164452866175995314614397 811669824815998242980399)
                    ·
                      rfl

theorem cell22_2371082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_2371082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371082 prefixEnd_2371082 := by exact prefixLift 2371082
  have htrace : WordTrace (prefixWord ++ tailWord_2371082) baseStart_2371082 baseEnd_2371082 := by
    simpa [prefixWord, tailWord_2371082, baseEnd_2371082] using wordTrace_append hprefix tailTrace_2371082
  have hstable : (prefixWord ++ tailWord_2371082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371082).length < 2 ^ (prefixWord ++ tailWord_2371082).sum := by decide
  have hdescent : baseEnd_2371082 < baseStart_2371082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371123 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 7]
def baseStart_2371123 : Nat := 118140960795 + 2371123 * 2 ^ 59
def prefixEnd_2371123 : Nat := 4983230072969 + 3 ^ 40 * 2371123 * 2
def baseEnd_2371123 : Nat := 270561286651295934235091

theorem tailTrace_2371123 : CollatzResearch.WordTrace tailWord_2371123 prefixEnd_2371123 270561286651295934235091 := by
  unfold tailWord_2371123
  simp only [CollatzResearch.WordTrace]
  refine ⟨86481960588833801413350023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57654640392555867608900015 86481960588833801413350023)
  ·
    refine ⟨129722940883250702120025035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86481960588833801413350023 129722940883250702120025035)
    ·
      refine ⟨194584411324876053180037553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129722940883250702120025035 194584411324876053180037553)
      ·
        refine ⟨145938308493657039885028165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194584411324876053180037553 145938308493657039885028165)
        ·
          refine ⟨27363432842560694978442781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145938308493657039885028165 27363432842560694978442781)
          ·
            refine ⟨10261287315960260616916043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27363432842560694978442781 10261287315960260616916043)
            ·
              refine ⟨15391930973940390925374065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10261287315960260616916043 15391930973940390925374065)
              ·
                refine ⟨11543948230455293194030549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15391930973940390925374065 11543948230455293194030549)
                ·
                  refine ⟨270561286651295934235091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11543948230455293194030549 270561286651295934235091)
                  ·
                    rfl

theorem cell22_2371123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 7].length) (baseStart_2371123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371123 prefixEnd_2371123 := by exact prefixLift 2371123
  have htrace : WordTrace (prefixWord ++ tailWord_2371123) baseStart_2371123 baseEnd_2371123 := by
    simpa [prefixWord, tailWord_2371123, baseEnd_2371123] using wordTrace_append hprefix tailTrace_2371123
  have hstable : (prefixWord ++ tailWord_2371123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371123).length < 2 ^ (prefixWord ++ tailWord_2371123).sum := by decide
  have hdescent : baseEnd_2371123 < baseStart_2371123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371168 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 8]
def baseStart_2371168 : Nat := 118140960795 + 2371168 * 2 ^ 59
def prefixEnd_2371168 : Nat := 4983230072969 + 3 ^ 40 * 2371168 * 2
def baseEnd_2371168 : Nat := 270566421457840895110045

theorem tailTrace_2371168 : CollatzResearch.WordTrace tailWord_2371168 prefixEnd_2371168 270566421457840895110045 := by
  unfold tailWord_2371168
  simp only [CollatzResearch.WordTrace]
  refine ⟨43241800936835387049369079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57655734582447182732492105 43241800936835387049369079)
  ·
    refine ⟨64862701405253080574053619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43241800936835387049369079 64862701405253080574053619)
    ·
      refine ⟨97294052107879620861080429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64862701405253080574053619 97294052107879620861080429)
      ·
        refine ⟨36485269540454857822905161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97294052107879620861080429 36485269540454857822905161)
        ·
          refine ⟨27363952155341143367178871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36485269540454857822905161 27363952155341143367178871)
          ·
            refine ⟨41045928233011715050768307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27363952155341143367178871 41045928233011715050768307)
            ·
              refine ⟨61568892349517572576152461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41045928233011715050768307 61568892349517572576152461)
              ·
                refine ⟨23088334631069089716057173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61568892349517572576152461 23088334631069089716057173)
                ·
                  refine ⟨270566421457840895110045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23088334631069089716057173 270566421457840895110045)
                  ·
                    rfl

theorem cell22_2371168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 8].length) (baseStart_2371168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371168 prefixEnd_2371168 := by exact prefixLift 2371168
  have htrace : WordTrace (prefixWord ++ tailWord_2371168) baseStart_2371168 baseEnd_2371168 := by
    simpa [prefixWord, tailWord_2371168, baseEnd_2371168] using wordTrace_append hprefix tailTrace_2371168
  have hstable : (prefixWord ++ tailWord_2371168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371168).length < 2 ^ (prefixWord ++ tailWord_2371168).sum := by decide
  have hdescent : baseEnd_2371168 < baseStart_2371168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371232 : List Nat := [2, 1, 1, 4, 3, 1, 3, 1, 2, 4]
def baseStart_2371232 : Nat := 118140960795 + 2371232 * 2 ^ 59
def prefixEnd_2371232 : Nat := 4983230072969 + 3 ^ 40 * 2371232 * 2
def baseEnd_2371232 : Nat := 811721172881447851729939

theorem tailTrace_2371232 : CollatzResearch.WordTrace tailWord_2371232 prefixEnd_2371232 811721172881447851729939 := by
  unfold tailWord_2371232
  simp only [CollatzResearch.WordTrace]
  refine ⟨43242968072719456514533975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57657290763625942019378633 43242968072719456514533975)
  ·
    refine ⟨64864452109079184771800963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43242968072719456514533975 64864452109079184771800963)
    ·
      refine ⟨97296678163618777157701445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64864452109079184771800963 97296678163618777157701445)
      ·
        refine ⟨18243127155678520717069021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97296678163618777157701445 18243127155678520717069021)
        ·
          refine ⟨6841172683379445268900883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18243127155678520717069021 6841172683379445268900883)
          ·
            refine ⟨10261759025069167903351325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6841172683379445268900883 10261759025069167903351325)
            ·
              refine ⟨3848159634400937963756747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10261759025069167903351325 3848159634400937963756747)
              ·
                refine ⟨5772239451601406945635121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3848159634400937963756747 5772239451601406945635121)
                ·
                  refine ⟨4329179588701055209226341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5772239451601406945635121 4329179588701055209226341)
                  ·
                    refine ⟨811721172881447851729939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4329179588701055209226341 811721172881447851729939)
                    ·
                      rfl

theorem cell22_2371232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 2, 4].length) (baseStart_2371232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371232 prefixEnd_2371232 := by exact prefixLift 2371232
  have htrace : WordTrace (prefixWord ++ tailWord_2371232) baseStart_2371232 baseEnd_2371232 := by
    simpa [prefixWord, tailWord_2371232, baseEnd_2371232] using wordTrace_append hprefix tailTrace_2371232
  have hstable : (prefixWord ++ tailWord_2371232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371232).length < 2 ^ (prefixWord ++ tailWord_2371232).sum := by decide
  have hdescent : baseEnd_2371232 < baseStart_2371232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371275 : List Nat := [1, 1, 1, 1, 3, 2, 1, 7, 5]
def baseStart_2371275 : Nat := 118140960795 + 2371275 * 2 ^ 59
def prefixEnd_2371275 : Nat := 4983230072969 + 3 ^ 40 * 2371275 * 2
def baseEnd_2371275 : Nat := 270578630886736690968269

theorem tailTrace_2371275 : CollatzResearch.WordTrace tailWord_2371275 prefixEnd_2371275 270578630886736690968269 := by
  unfold tailWord_2371275
  simp only [CollatzResearch.WordTrace]
  refine ⟨86487504484283131372883279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57658336322855420915255519 86487504484283131372883279)
  ·
    refine ⟨129731256726424697059324919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86487504484283131372883279 129731256726424697059324919)
    ·
      refine ⟨194596885089637045588987379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129731256726424697059324919 194596885089637045588987379)
      ·
        refine ⟨291895327634455568383481069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194596885089637045588987379 291895327634455568383481069)
        ·
          refine ⟨109460747862920838143805401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291895327634455568383481069 109460747862920838143805401)
          ·
            refine ⟨82095560897190628607854051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109460747862920838143805401 82095560897190628607854051)
            ·
              refine ⟨123143341345785942911781077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82095560897190628607854051 123143341345785942911781077)
              ·
                refine ⟨2886172062791858036994869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 123143341345785942911781077 2886172062791858036994869)
                ·
                  refine ⟨270578630886736690968269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2886172062791858036994869 270578630886736690968269)
                  ·
                    rfl

theorem cell22_2371275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 5].length) (baseStart_2371275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371275 prefixEnd_2371275 := by exact prefixLift 2371275
  have htrace : WordTrace (prefixWord ++ tailWord_2371275) baseStart_2371275 baseEnd_2371275 := by
    simpa [prefixWord, tailWord_2371275, baseEnd_2371275] using wordTrace_append hprefix tailTrace_2371275
  have hstable : (prefixWord ++ tailWord_2371275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371275).length < 2 ^ (prefixWord ++ tailWord_2371275).sum := by decide
  have hdescent : baseEnd_2371275 < baseStart_2371275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371305 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 5, 4]
def baseStart_2371305 : Nat := 118140960795 + 2371305 * 2 ^ 59
def prefixEnd_2371305 : Nat := 4983230072969 + 3 ^ 40 * 2371305 * 2
def baseEnd_2371305 : Nat := 811746162273299994654715

theorem tailTrace_2371305 : CollatzResearch.WordTrace tailWord_2371305 prefixEnd_2371305 811746162273299994654715 := by
  unfold tailWord_2371305
  simp only [CollatzResearch.WordTrace]
  refine ⟨86488598674174446496475369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57659065782782964330983579 86488598674174446496475369)
  ·
    refine ⟨64866449005630834872356527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86488598674174446496475369 64866449005630834872356527)
    ·
      refine ⟨97299673508446252308534791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64866449005630834872356527 97299673508446252308534791)
      ·
        refine ⟨145949510262669378462802187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97299673508446252308534791 145949510262669378462802187)
        ·
          refine ⟨218924265394004067694203281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145949510262669378462802187 218924265394004067694203281)
          ·
            refine ⟨164193199045503050770652461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218924265394004067694203281 164193199045503050770652461)
            ·
              refine ⟨61572449642063644038994673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164193199045503050770652461 61572449642063644038994673)
              ·
                refine ⟨46179337231547733029246005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61572449642063644038994673 46179337231547733029246005)
                ·
                  refine ⟨4329312865457599971491813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46179337231547733029246005 4329312865457599971491813)
                  ·
                    refine ⟨811746162273299994654715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4329312865457599971491813 811746162273299994654715)
                    ·
                      rfl

theorem cell22_2371305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 4].length) (baseStart_2371305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371305 prefixEnd_2371305 := by exact prefixLift 2371305
  have htrace : WordTrace (prefixWord ++ tailWord_2371305) baseStart_2371305 baseEnd_2371305 := by
    simpa [prefixWord, tailWord_2371305, baseEnd_2371305] using wordTrace_append hprefix tailTrace_2371305
  have hstable : (prefixWord ++ tailWord_2371305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371305).length < 2 ^ (prefixWord ++ tailWord_2371305).sum := by decide
  have hdescent : baseEnd_2371305 < baseStart_2371305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371320 : List Nat := [2, 1, 2, 1, 1, 2, 2, 5, 6]
def baseStart_2371320 : Nat := 118140960795 + 2371320 * 2 ^ 59
def prefixEnd_2371320 : Nat := 4983230072969 + 3 ^ 40 * 2371320 * 2
def baseEnd_2371320 : Nat := 270583765693281651843223

theorem tailTrace_2371320 : CollatzResearch.WordTrace tailWord_2371320 prefixEnd_2371320 270583765693281651843223 := by
  unfold tailWord_2371320
  simp only [CollatzResearch.WordTrace]
  refine ⟨43244572884560052029135707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57659430512746736038847609 43244572884560052029135707)
  ·
    refine ⟨64866859326840078043703561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43244572884560052029135707 64866859326840078043703561)
    ·
      refine ⟨48650144495130058532777671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64866859326840078043703561 48650144495130058532777671)
      ·
        refine ⟨72975216742695087799166507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48650144495130058532777671 72975216742695087799166507)
        ·
          refine ⟨109462825114042631698749761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72975216742695087799166507 109462825114042631698749761)
          ·
            refine ⟨82097118835531973774062321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109462825114042631698749761 82097118835531973774062321)
            ·
              refine ⟨61572839126648980330546741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82097118835531973774062321 61572839126648980330546741)
              ·
                refine ⟨5772453668123341905988757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61572839126648980330546741 5772453668123341905988757)
                ·
                  refine ⟨270583765693281651843223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5772453668123341905988757 270583765693281651843223)
                  ·
                    rfl

theorem cell22_2371320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 6].length) (baseStart_2371320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371320 prefixEnd_2371320 := by exact prefixLift 2371320
  have htrace : WordTrace (prefixWord ++ tailWord_2371320) baseStart_2371320 baseEnd_2371320 := by
    simpa [prefixWord, tailWord_2371320, baseEnd_2371320] using wordTrace_append hprefix tailTrace_2371320
  have hstable : (prefixWord ++ tailWord_2371320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371320).length < 2 ^ (prefixWord ++ tailWord_2371320).sum := by decide
  have hdescent : baseEnd_2371320 < baseStart_2371320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371352 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 6, 3]
def baseStart_2371352 : Nat := 118140960795 + 2371352 * 2 ^ 59
def prefixEnd_2371352 : Nat := 4983230072969 + 3 ^ 40 * 2371352 * 2
def baseEnd_2371352 : Nat := 811762251333807538729571

theorem tailTrace_2371352 : CollatzResearch.WordTrace tailWord_2371352 prefixEnd_2371352 811762251333807538729571 := by
  unfold tailWord_2371352
  simp only [CollatzResearch.WordTrace]
  refine ⟨43245156452502086761718155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57660208603336115682290873 43245156452502086761718155)
  ·
    refine ⟨64867734678753130142577233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43245156452502086761718155 64867734678753130142577233)
    ·
      refine ⟨48650801009064847606932925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64867734678753130142577233 48650801009064847606932925)
      ·
        refine ⟨18244050378399317852599847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48650801009064847606932925 18244050378399317852599847)
        ·
          refine ⟨27366075567598976778899771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18244050378399317852599847 27366075567598976778899771)
          ·
            refine ⟨41049113351398465168349657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27366075567598976778899771 41049113351398465168349657)
            ·
              refine ⟨30786835013548848876262243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41049113351398465168349657 30786835013548848876262243)
              ·
                refine ⟨46180252520323273314393365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30786835013548848876262243 46180252520323273314393365)
                ·
                  refine ⟨2164699336890153436612189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46180252520323273314393365 2164699336890153436612189)
                  ·
                    refine ⟨811762251333807538729571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2164699336890153436612189 811762251333807538729571)
                    ·
                      rfl

theorem cell22_2371352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 6, 3].length) (baseStart_2371352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371352 prefixEnd_2371352 := by exact prefixLift 2371352
  have htrace : WordTrace (prefixWord ++ tailWord_2371352) baseStart_2371352 baseEnd_2371352 := by
    simpa [prefixWord, tailWord_2371352, baseEnd_2371352] using wordTrace_append hprefix tailTrace_2371352
  have hstable : (prefixWord ++ tailWord_2371352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371352).length < 2 ^ (prefixWord ++ tailWord_2371352).sum := by decide
  have hdescent : baseEnd_2371352 < baseStart_2371352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371365 : List Nat := [1, 3, 1, 2, 3, 12]
def baseStart_2371365 : Nat := 118140960795 + 2371365 * 2 ^ 59
def prefixEnd_2371365 : Nat := 4983230072969 + 3 ^ 40 * 2371365 * 2
def baseEnd_2371365 : Nat := 10021811129623207878451

theorem tailTrace_2371365 : CollatzResearch.WordTrace tailWord_2371365 prefixEnd_2371365 10021811129623207878451 := by
  unfold tailWord_2371365
  simp only [CollatzResearch.WordTrace]
  refine ⟨86490787053957076743659549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57660524702638051162439699 86490787053957076743659549)
  ·
    refine ⟨32434045145233903778872331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86490787053957076743659549 32434045145233903778872331)
    ·
      refine ⟨48651067717850855668308497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32434045145233903778872331 48651067717850855668308497)
      ·
        refine ⟨36488300788388141751231373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48651067717850855668308497 36488300788388141751231373)
        ·
          refine ⟨13683112795645553156711765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36488300788388141751231373 13683112795645553156711765)
          ·
            refine ⟨10021811129623207878451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 13683112795645553156711765 10021811129623207878451)
            ·
              rfl

theorem cell22_2371365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 12].length) (baseStart_2371365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371365 prefixEnd_2371365 := by exact prefixLift 2371365
  have htrace : WordTrace (prefixWord ++ tailWord_2371365) baseStart_2371365 baseEnd_2371365 := by
    simpa [prefixWord, tailWord_2371365, baseEnd_2371365] using wordTrace_append hprefix tailTrace_2371365
  have hstable : (prefixWord ++ tailWord_2371365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371365).length < 2 ^ (prefixWord ++ tailWord_2371365).sum := by decide
  have hdescent : baseEnd_2371365 < baseStart_2371365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371420 : List Nat := [2, 2, 4, 2, 3, 1, 1, 2, 2, 3]
def baseStart_2371420 : Nat := 118140960795 + 2371420 * 2 ^ 59
def prefixEnd_2371420 : Nat := 4983230072969 + 3 ^ 40 * 2371420 * 2
def baseEnd_2371420 : Nat := 811785529123478028029363

theorem tailTrace_2371420 : CollatzResearch.WordTrace tailWord_2371420 prefixEnd_2371420 811785529123478028029363 := by
  unfold tailWord_2371420
  simp only [CollatzResearch.WordTrace]
  refine ⟨43246396534378910568455857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57661862045838547424607809 43246396534378910568455857)
  ·
    refine ⟨32434797400784182926341893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43246396534378910568455857 32434797400784182926341893)
    ·
      refine ⟨6081524512647034298689105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32434797400784182926341893 6081524512647034298689105)
      ·
        refine ⟨4561143384485275724016829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6081524512647034298689105 4561143384485275724016829)
        ·
          refine ⟨1710428769181978396506311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4561143384485275724016829 1710428769181978396506311)
          ·
            refine ⟨2565643153772967594759467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1710428769181978396506311 2565643153772967594759467)
            ·
              refine ⟨3848464730659451392139201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2565643153772967594759467 3848464730659451392139201)
              ·
                refine ⟨2886348547994588544104401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3848464730659451392139201 2886348547994588544104401)
                ·
                  refine ⟨2164761410995941408078301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2886348547994588544104401 2164761410995941408078301)
                  ·
                    refine ⟨811785529123478028029363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2164761410995941408078301 811785529123478028029363)
                    ·
                      rfl

theorem cell22_2371420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_2371420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371420 prefixEnd_2371420 := by exact prefixLift 2371420
  have htrace : WordTrace (prefixWord ++ tailWord_2371420) baseStart_2371420 baseEnd_2371420 := by
    simpa [prefixWord, tailWord_2371420, baseEnd_2371420] using wordTrace_append hprefix tailTrace_2371420
  have hstable : (prefixWord ++ tailWord_2371420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371420).length < 2 ^ (prefixWord ++ tailWord_2371420).sum := by decide
  have hdescent : baseEnd_2371420 < baseStart_2371420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371431 : List Nat := [1, 1, 5, 1, 2, 1, 1, 6, 1, 3]
def baseStart_2371431 : Nat := 118140960795 + 2371431 * 2 ^ 59
def prefixEnd_2371431 : Nat := 4983230072969 + 3 ^ 40 * 2371431 * 2
def baseEnd_2371431 : Nat := 811789294648277666004329

theorem tailTrace_2371431 : CollatzResearch.WordTrace tailWord_2371431 prefixEnd_2371431 811789294648277666004329 := by
  unfold tailWord_2371431
  simp only [CollatzResearch.WordTrace]
  refine ⟨86493194271717970015562147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57662129514478646677041431 86493194271717970015562147)
  ·
    refine ⟨129739791407576955023343221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86493194271717970015562147 129739791407576955023343221)
    ·
      refine ⟨12163105444460339533438427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129739791407576955023343221 12163105444460339533438427)
      ·
        refine ⟨18244658166690509300157641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12163105444460339533438427 18244658166690509300157641)
        ·
          refine ⟨13683493625017881975118231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18244658166690509300157641 13683493625017881975118231)
          ·
            refine ⟨20525240437526822962677347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13683493625017881975118231 20525240437526822962677347)
            ·
              refine ⟨30787860656290234444016021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20525240437526822962677347 30787860656290234444016021)
              ·
                refine ⟨1443180968263604739563251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30787860656290234444016021 1443180968263604739563251)
                ·
                  refine ⟨2164771452395407109344877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443180968263604739563251 2164771452395407109344877)
                  ·
                    refine ⟨811789294648277666004329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2164771452395407109344877 811789294648277666004329)
                    ·
                      rfl

theorem cell22_2371431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_2371431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371431 prefixEnd_2371431 := by exact prefixLift 2371431
  have htrace : WordTrace (prefixWord ++ tailWord_2371431) baseStart_2371431 baseEnd_2371431 := by
    simpa [prefixWord, tailWord_2371431, baseEnd_2371431] using wordTrace_append hprefix tailTrace_2371431
  have hstable : (prefixWord ++ tailWord_2371431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371431).length < 2 ^ (prefixWord ++ tailWord_2371431).sum := by decide
  have hdescent : baseEnd_2371431 < baseStart_2371431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371508 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_2371508 : Nat := 118140960795 + 2371508 * 2 ^ 59
def prefixEnd_2371508 : Nat := 4983230072969 + 3 ^ 40 * 2371508 * 2
def baseEnd_2371508 : Nat := 811815653321875131829093

theorem tailTrace_2371508 : CollatzResearch.WordTrace tailWord_2371508 prefixEnd_2371508 811815653321875131829093 := by
  unfold tailWord_2371508
  simp only [CollatzResearch.WordTrace]
  refine ⟨43248001346219506083057589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57664001794959341444076785 43248001346219506083057589)
  ·
    refine ⟨4054500126208078695286649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43248001346219506083057589 4054500126208078695286649)
    ·
      refine ⟨3040875094656059021464987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4054500126208078695286649 3040875094656059021464987)
      ·
        refine ⟨4561312641984088532197481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3040875094656059021464987 4561312641984088532197481)
        ·
          refine ⟨3420984481488066399148111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4561312641984088532197481 3420984481488066399148111)
          ·
            refine ⟨5131476722232099598722167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3420984481488066399148111 5131476722232099598722167)
            ·
              refine ⟨7697215083348149398083251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5131476722232099598722167 7697215083348149398083251)
              ·
                refine ⟨11545822625022224097124877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7697215083348149398083251 11545822625022224097124877)
                ·
                  refine ⟨4329683484383334036421829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11545822625022224097124877 4329683484383334036421829)
                  ·
                    refine ⟨811815653321875131829093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4329683484383334036421829 811815653321875131829093)
                    ·
                      rfl

theorem cell22_2371508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_2371508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371508 prefixEnd_2371508 := by exact prefixLift 2371508
  have htrace : WordTrace (prefixWord ++ tailWord_2371508) baseStart_2371508 baseEnd_2371508 := by
    simpa [prefixWord, tailWord_2371508, baseEnd_2371508] using wordTrace_append hprefix tailTrace_2371508
  have hstable : (prefixWord ++ tailWord_2371508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371508).length < 2 ^ (prefixWord ++ tailWord_2371508).sum := by decide
  have hdescent : baseEnd_2371508 < baseStart_2371508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371519 : List Nat := [1, 1, 2, 2, 2, 1, 6, 1, 2, 4]
def baseStart_2371519 : Nat := 118140960795 + 2371519 * 2 ^ 59
def prefixEnd_2371519 : Nat := 4983230072969 + 3 ^ 40 * 2371519 * 2
def baseEnd_2371519 : Nat := 811819418846674769804059

theorem tailTrace_2371519 : CollatzResearch.WordTrace tailWord_2371519 prefixEnd_2371519 811819418846674769804059 := by
  unfold tailWord_2371519
  simp only [CollatzResearch.WordTrace]
  refine ⟨86496403895399161044765611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57664269263599440696510407 86496403895399161044765611)
  ·
    refine ⟨129744605843098741567148417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86496403895399161044765611 129744605843098741567148417)
    ·
      refine ⟨97308454382324056175361313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129744605843098741567148417 97308454382324056175361313)
      ·
        refine ⟨72981340786743042131520985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97308454382324056175361313 72981340786743042131520985)
        ·
          refine ⟨54736005590057281598640739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72981340786743042131520985 54736005590057281598640739)
          ·
            refine ⟨82104008385085922397961109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54736005590057281598640739 82104008385085922397961109)
            ·
              refine ⟨3848625393050902612404427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82104008385085922397961109 3848625393050902612404427)
              ·
                refine ⟨5772938089576353918606641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3848625393050902612404427 5772938089576353918606641)
                ·
                  refine ⟨4329703567182265438954981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5772938089576353918606641 4329703567182265438954981)
                  ·
                    refine ⟨811819418846674769804059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4329703567182265438954981 811819418846674769804059)
                    ·
                      rfl

theorem cell22_2371519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 4].length) (baseStart_2371519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371519 prefixEnd_2371519 := by exact prefixLift 2371519
  have htrace : WordTrace (prefixWord ++ tailWord_2371519) baseStart_2371519 baseEnd_2371519 := by
    simpa [prefixWord, tailWord_2371519, baseEnd_2371519] using wordTrace_append hprefix tailTrace_2371519
  have hstable : (prefixWord ++ tailWord_2371519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371519).length < 2 ^ (prefixWord ++ tailWord_2371519).sum := by decide
  have hdescent : baseEnd_2371519 < baseStart_2371519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371566 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 5, 3]
def baseStart_2371566 : Nat := 118140960795 + 2371566 * 2 ^ 59
def prefixEnd_2371566 : Nat := 4983230072969 + 3 ^ 40 * 2371566 * 2
def baseEnd_2371566 : Nat := 811835507907182313878915

theorem tailTrace_2371566 : CollatzResearch.WordTrace tailWord_2371566 prefixEnd_2371566 811835507907182313878915 := by
  unfold tailWord_2371566
  simp only [CollatzResearch.WordTrace]
  refine ⟨10812264765778611008965819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57665412084152592047817701 10812264765778611008965819)
  ·
    refine ⟨16218397148667916513448729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10812264765778611008965819 16218397148667916513448729)
    ·
      refine ⟨12163797861500937385086547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16218397148667916513448729 12163797861500937385086547)
      ·
        refine ⟨18245696792251406077629821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12163797861500937385086547 18245696792251406077629821)
        ·
          refine ⟨6842136297094277279111183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18245696792251406077629821 6842136297094277279111183)
          ·
            refine ⟨10263204445641415918666775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6842136297094277279111183 10263204445641415918666775)
            ·
              refine ⟨15394806668462123878000163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10263204445641415918666775 15394806668462123878000163)
              ·
                refine ⟨23092210002693185817000245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15394806668462123878000163 23092210002693185817000245)
                ·
                  refine ⟨2164894687752486170343773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23092210002693185817000245 2164894687752486170343773)
                  ·
                    refine ⟨811835507907182313878915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2164894687752486170343773 811835507907182313878915)
                    ·
                      rfl

theorem cell22_2371566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_2371566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371566 prefixEnd_2371566 := by exact prefixLift 2371566
  have htrace : WordTrace (prefixWord ++ tailWord_2371566) baseStart_2371566 baseEnd_2371566 := by
    simpa [prefixWord, tailWord_2371566, baseEnd_2371566] using wordTrace_append hprefix tailTrace_2371566
  have hstable : (prefixWord ++ tailWord_2371566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371566).length < 2 ^ (prefixWord ++ tailWord_2371566).sum := by decide
  have hdescent : baseEnd_2371566 < baseStart_2371566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371613 : List Nat := [1, 4, 2, 2, 2, 2, 3, 1, 5]
def baseStart_2371613 : Nat := 118140960795 + 2371613 * 2 ^ 59
def prefixEnd_2371613 : Nat := 4983230072969 + 3 ^ 40 * 2371613 * 2
def baseEnd_2371613 : Nat := 270617198989229952651257

theorem tailTrace_2371613 : CollatzResearch.WordTrace tailWord_2371613 prefixEnd_2371613 270617198989229952651257 := by
  unfold tailWord_2371613
  simp only [CollatzResearch.WordTrace]
  refine ⟨86499832357058615098687493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57666554904705743399124995 86499832357058615098687493)
  ·
    refine ⟨16218718566948490331003905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86499832357058615098687493 16218718566948490331003905)
    ·
      refine ⟨12164038925211367748252929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16218718566948490331003905 12164038925211367748252929)
      ·
        refine ⟨9123029193908525811189697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12164038925211367748252929 9123029193908525811189697)
        ·
          refine ⟨6842271895431394358392273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9123029193908525811189697 6842271895431394358392273)
          ·
            refine ⟨5131703921573545768794205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6842271895431394358392273 5131703921573545768794205)
            ·
              refine ⟨1924388970590079663297827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5131703921573545768794205 1924388970590079663297827)
              ·
                refine ⟨2886583455885119494946741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1924388970590079663297827 2886583455885119494946741)
                ·
                  refine ⟨270617198989229952651257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2886583455885119494946741 270617198989229952651257)
                  ·
                    rfl

theorem cell22_2371613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_2371613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371613 prefixEnd_2371613 := by exact prefixLift 2371613
  have htrace : WordTrace (prefixWord ++ tailWord_2371613) baseStart_2371613 baseEnd_2371613 := by
    simpa [prefixWord, tailWord_2371613, baseEnd_2371613] using wordTrace_append hprefix tailTrace_2371613
  have hstable : (prefixWord ++ tailWord_2371613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371613).length < 2 ^ (prefixWord ++ tailWord_2371613).sum := by decide
  have hdescent : baseEnd_2371613 < baseStart_2371613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371639 : List Nat := [1, 1, 3, 1, 2, 2, 2, 4, 1, 5]
def baseStart_2371639 : Nat := 118140960795 + 2371639 * 2 ^ 59
def prefixEnd_2371639 : Nat := 4983230072969 + 3 ^ 40 * 2371639 * 2
def baseEnd_2371639 : Nat := 811860497299034456803691

theorem tailTrace_2371639 : CollatzResearch.WordTrace tailWord_2371639 prefixEnd_2371639 811860497299034456803691 := by
  unfold tailWord_2371639
  simp only [CollatzResearch.WordTrace]
  refine ⟨86500780654964421539133971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57667187103309614359422647 86500780654964421539133971)
  ·
    refine ⟨129751170982446632308700957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86500780654964421539133971 129751170982446632308700957)
    ·
      refine ⟨48656689118417487115762859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129751170982446632308700957 48656689118417487115762859)
      ·
        refine ⟨72985033677626230673644289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48656689118417487115762859 72985033677626230673644289)
        ·
          refine ⟨54738775258219673005233217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72985033677626230673644289 54738775258219673005233217)
          ·
            refine ⟨41054081443664754753924913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54738775258219673005233217 41054081443664754753924913)
            ·
              refine ⟨30790561082748566065443685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41054081443664754753924913 30790561082748566065443685)
              ·
                refine ⟨5773230203015356137270691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30790561082748566065443685 5773230203015356137270691)
                ·
                  refine ⟨8659845304523034205906037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5773230203015356137270691 8659845304523034205906037)
                  ·
                    refine ⟨811860497299034456803691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8659845304523034205906037 811860497299034456803691)
                    ·
                      rfl

theorem cell22_2371639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_2371639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371639 prefixEnd_2371639 := by exact prefixLift 2371639
  have htrace : WordTrace (prefixWord ++ tailWord_2371639) baseStart_2371639 baseEnd_2371639 := by
    simpa [prefixWord, tailWord_2371639, baseEnd_2371639] using wordTrace_append hprefix tailTrace_2371639
  have hstable : (prefixWord ++ tailWord_2371639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371639).length < 2 ^ (prefixWord ++ tailWord_2371639).sum := by decide
  have hdescent : baseEnd_2371639 < baseStart_2371639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371669 : List Nat := [1, 3, 2, 2, 1, 3, 1, 9]
def baseStart_2371669 : Nat := 118140960795 + 2371669 * 2 ^ 59
def prefixEnd_2371669 : Nat := 4983230072969 + 3 ^ 40 * 2371669 * 2
def baseEnd_2371669 : Nat := 90207862990236042061511

theorem tailTrace_2371669 : CollatzResearch.WordTrace tailWord_2371669 prefixEnd_2371669 90207862990236042061511 := by
  unfold tailWord_2371669
  simp only [CollatzResearch.WordTrace]
  refine ⟨86501874844855736662726061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57667916563237157775150707 86501874844855736662726061)
  ·
    refine ⟨32438203066820901248522273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86501874844855736662726061 32438203066820901248522273)
    ·
      refine ⟨24328652300115675936391705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32438203066820901248522273 24328652300115675936391705)
      ·
        refine ⟨18246489225086756952293779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24328652300115675936391705 18246489225086756952293779)
        ·
          refine ⟨27369733837630135428440669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18246489225086756952293779 27369733837630135428440669)
          ·
            refine ⟨10263650189111300785665251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27369733837630135428440669 10263650189111300785665251)
            ·
              refine ⟨15395475283666951178497877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10263650189111300785665251 15395475283666951178497877)
              ·
                refine ⟨90207862990236042061511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15395475283666951178497877 90207862990236042061511)
                ·
                  rfl

theorem cell22_2371669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 9].length) (baseStart_2371669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371669 prefixEnd_2371669 := by exact prefixLift 2371669
  have htrace : WordTrace (prefixWord ++ tailWord_2371669) baseStart_2371669 baseEnd_2371669 := by
    simpa [prefixWord, tailWord_2371669, baseEnd_2371669] using wordTrace_append hprefix tailTrace_2371669
  have hstable : (prefixWord ++ tailWord_2371669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371669).length < 2 ^ (prefixWord ++ tailWord_2371669).sum := by decide
  have hdescent : baseEnd_2371669 < baseStart_2371669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371684 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_2371684 : Nat := 118140960795 + 2371684 * 2 ^ 59
def prefixEnd_2371684 : Nat := 4983230072969 + 3 ^ 40 * 2371684 * 2
def baseEnd_2371684 : Nat := 811875901718669339428553

theorem tailTrace_2371684 : CollatzResearch.WordTrace tailWord_2371684 prefixEnd_2371684 811875901718669339428553 := by
  unfold tailWord_2371684
  simp only [CollatzResearch.WordTrace]
  refine ⟨43251210969900697112261053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57668281293200929483014737 43251210969900697112261053)
  ·
    refine ⟨16219204113712761417097895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43251210969900697112261053 16219204113712761417097895)
    ·
      refine ⟨24328806170569142125646843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16219204113712761417097895 24328806170569142125646843)
      ·
        refine ⟨36493209255853713188470265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24328806170569142125646843 36493209255853713188470265)
        ·
          refine ⟨27369906941890284891352699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36493209255853713188470265 27369906941890284891352699)
          ·
            refine ⟨41054860412835427337029049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27369906941890284891352699 41054860412835427337029049)
            ·
              refine ⟨30791145309626570502771787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41054860412835427337029049 30791145309626570502771787)
              ·
                refine ⟨46186717964439855754157681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30791145309626570502771787 46186717964439855754157681)
                ·
                  refine ⟨34640038473329891815618261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46186717964439855754157681 34640038473329891815618261)
                  ·
                    refine ⟨811875901718669339428553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34640038473329891815618261 811875901718669339428553)
                    ·
                      rfl

theorem cell22_2371684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_2371684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371684 prefixEnd_2371684 := by exact prefixLift 2371684
  have htrace : WordTrace (prefixWord ++ tailWord_2371684) baseStart_2371684 baseEnd_2371684 := by
    simpa [prefixWord, tailWord_2371684, baseEnd_2371684] using wordTrace_append hprefix tailTrace_2371684
  have hstable : (prefixWord ++ tailWord_2371684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371684).length < 2 ^ (prefixWord ++ tailWord_2371684).sum := by decide
  have hdescent : baseEnd_2371684 < baseStart_2371684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371759 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 10]
def baseStart_2371759 : Nat := 118140960795 + 2371759 * 2 ^ 59
def prefixEnd_2371759 : Nat := 4983230072969 + 3 ^ 40 * 2371759 * 2
def baseEnd_2371759 : Nat := 270633858583798047934441

theorem tailTrace_2371759 : CollatzResearch.WordTrace tailWord_2371759 prefixEnd_2371759 270633858583798047934441 := by
  unfold tailWord_2371759
  simp only [CollatzResearch.WordTrace]
  refine ⟨86505157414529682033502331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57670104943019788022334887 86505157414529682033502331)
  ·
    refine ⟨129757736121794523050253497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86505157414529682033502331 129757736121794523050253497)
    ·
      refine ⟨97318302091345892287690123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129757736121794523050253497 97318302091345892287690123)
      ·
        refine ⟨145977453137018838431535185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97318302091345892287690123 145977453137018838431535185)
        ·
          refine ⟨109483089852764128823651389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145977453137018838431535185 109483089852764128823651389)
          ·
            refine ⟨41056158694786548308869271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109483089852764128823651389 41056158694786548308869271)
            ·
              refine ⟨61584238042179822463303907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41056158694786548308869271 61584238042179822463303907)
              ·
                refine ⟨92376357063269733694955861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61584238042179822463303907 92376357063269733694955861)
                ·
                  refine ⟨270633858583798047934441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 92376357063269733694955861 270633858583798047934441)
                  ·
                    rfl

theorem cell22_2371759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 10].length) (baseStart_2371759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371759 prefixEnd_2371759 := by exact prefixLift 2371759
  have htrace : WordTrace (prefixWord ++ tailWord_2371759) baseStart_2371759 baseEnd_2371759 := by
    simpa [prefixWord, tailWord_2371759, baseEnd_2371759] using wordTrace_append hprefix tailTrace_2371759
  have hstable : (prefixWord ++ tailWord_2371759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371759).length < 2 ^ (prefixWord ++ tailWord_2371759).sum := by decide
  have hdescent : baseEnd_2371759 < baseStart_2371759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371776 : List Nat := [2, 1, 1, 2, 5, 1, 1, 3, 6]
def baseStart_2371776 : Nat := 118140960795 + 2371776 * 2 ^ 59
def prefixEnd_2371776 : Nat := 4983230072969 + 3 ^ 40 * 2371776 * 2
def baseEnd_2371776 : Nat := 270635798399603922042757

theorem tailTrace_2371776 : CollatzResearch.WordTrace tailWord_2371776 prefixEnd_2371776 270635798399603922042757 := by
  unfold tailWord_2371776
  simp only [CollatzResearch.WordTrace]
  refine ⟨43252888727734046968435591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57670518303645395957914121 43252888727734046968435591)
  ·
    refine ⟨64879333091601070452653387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43252888727734046968435591 64879333091601070452653387)
    ·
      refine ⟨97318999637401605678980081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64879333091601070452653387 97318999637401605678980081)
      ·
        refine ⟨72989249728051204259235061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97318999637401605678980081 72989249728051204259235061)
        ·
          refine ⟨6842742162004800399303287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72989249728051204259235061 6842742162004800399303287)
          ·
            refine ⟨10264113243007200598954931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6842742162004800399303287 10264113243007200598954931)
            ·
              refine ⟨15396169864510800898432397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10264113243007200598954931 15396169864510800898432397)
              ·
                refine ⟨5773563699191550336912149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15396169864510800898432397 5773563699191550336912149)
                ·
                  refine ⟨270635798399603922042757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5773563699191550336912149 270635798399603922042757)
                  ·
                    rfl

theorem cell22_2371776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 6].length) (baseStart_2371776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371776 prefixEnd_2371776 := by exact prefixLift 2371776
  have htrace : WordTrace (prefixWord ++ tailWord_2371776) baseStart_2371776 baseEnd_2371776 := by
    simpa [prefixWord, tailWord_2371776, baseEnd_2371776] using wordTrace_append hprefix tailTrace_2371776
  have hstable : (prefixWord ++ tailWord_2371776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371776).length < 2 ^ (prefixWord ++ tailWord_2371776).sum := by decide
  have hdescent : baseEnd_2371776 < baseStart_2371776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371823 : List Nat := [1, 1, 2, 1, 6, 2, 1, 2, 2, 4]
def baseStart_2371823 : Nat := 118140960795 + 2371823 * 2 ^ 59
def prefixEnd_2371823 : Nat := 4983230072969 + 3 ^ 40 * 2371823 * 2
def baseEnd_2371823 : Nat := 811923484259319310203127

theorem tailTrace_2371823 : CollatzResearch.WordTrace tailWord_2371823 prefixEnd_2371823 811923484259319310203127 := by
  unfold tailWord_2371823
  simp only [CollatzResearch.WordTrace]
  refine ⟨86507491686297820963832123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57671661124198547309221415 86507491686297820963832123)
  ·
    refine ⟨129761237529446731445748185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86507491686297820963832123 129761237529446731445748185)
    ·
      refine ⟨97320928147085048584311139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129761237529446731445748185 97320928147085048584311139)
      ·
        refine ⟨145981392220627572876466709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97320928147085048584311139 145981392220627572876466709)
        ·
          refine ⟨6842877760341917478584377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 145981392220627572876466709 6842877760341917478584377)
          ·
            refine ⟨5132158320256438108938283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6842877760341917478584377 5132158320256438108938283)
            ·
              refine ⟨7698237480384657163407425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5132158320256438108938283 7698237480384657163407425)
              ·
                refine ⟨5773678110288492872555569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7698237480384657163407425 5773678110288492872555569)
                ·
                  refine ⟨4330258582716369654416677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5773678110288492872555569 4330258582716369654416677)
                  ·
                    refine ⟨811923484259319310203127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4330258582716369654416677 811923484259319310203127)
                    ·
                      rfl

theorem cell22_2371823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 4].length) (baseStart_2371823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371823 prefixEnd_2371823 := by exact prefixLift 2371823
  have htrace : WordTrace (prefixWord ++ tailWord_2371823) baseStart_2371823 baseEnd_2371823 := by
    simpa [prefixWord, tailWord_2371823, baseEnd_2371823] using wordTrace_append hprefix tailTrace_2371823
  have hstable : (prefixWord ++ tailWord_2371823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371823).length < 2 ^ (prefixWord ++ tailWord_2371823).sum := by decide
  have hdescent : baseEnd_2371823 < baseStart_2371823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371838 : List Nat := [4, 2, 2, 1, 1, 1, 4, 7]
def baseStart_2371838 : Nat := 118140960795 + 2371838 * 2 ^ 59
def prefixEnd_2371838 : Nat := 4983230072969 + 3 ^ 40 * 2371838 * 2
def baseEnd_2371838 : Nat := 90214291007318252342009

theorem tailTrace_2371838 : CollatzResearch.WordTrace tailWord_2371838 prefixEnd_2371838 90214291007318252342009 := by
  unfold tailWord_2371838
  simp only [CollatzResearch.WordTrace]
  refine ⟨10813504847655434815703521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57672025854162319017085445 10813504847655434815703521)
  ·
    refine ⟨8110128635741576111777641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10813504847655434815703521 8110128635741576111777641)
    ·
      refine ⟨6082596476806182083833231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8110128635741576111777641 6082596476806182083833231)
      ·
        refine ⟨9123894715209273125749847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6082596476806182083833231 9123894715209273125749847)
        ·
          refine ⟨13685842072813909688624771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9123894715209273125749847 13685842072813909688624771)
          ·
            refine ⟨20528763109220864532937157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13685842072813909688624771 20528763109220864532937157)
            ·
              refine ⟨3849143082978912099925717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20528763109220864532937157 3849143082978912099925717)
              ·
                refine ⟨90214291007318252342009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3849143082978912099925717 90214291007318252342009)
                ·
                  rfl

theorem cell22_2371838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_2371838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371838 prefixEnd_2371838 := by exact prefixLift 2371838
  have htrace : WordTrace (prefixWord ++ tailWord_2371838) baseStart_2371838 baseEnd_2371838 := by
    simpa [prefixWord, tailWord_2371838, baseEnd_2371838] using wordTrace_append hprefix tailTrace_2371838
  have hstable : (prefixWord ++ tailWord_2371838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371838).length < 2 ^ (prefixWord ++ tailWord_2371838).sum := by decide
  have hdescent : baseEnd_2371838 < baseStart_2371838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371842 : List Nat := [3, 4, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_2371842 : Nat := 118140960795 + 2371842 * 2 ^ 59
def prefixEnd_2371842 : Nat := 4983230072969 + 3 ^ 40 * 2371842 * 2
def baseEnd_2371842 : Nat := 811929988347609593978069

theorem tailTrace_2371842 : CollatzResearch.WordTrace tailWord_2371842 prefixEnd_2371842 811929988347609593978069 := by
  unfold tailWord_2371842
  simp only [CollatzResearch.WordTrace]
  refine ⟨21627046168307246802193445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57672123115485991472515853 21627046168307246802193445)
  ·
    refine ⟨4055071156557608775411271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21627046168307246802193445 4055071156557608775411271)
    ·
      refine ⟨6082606734836413163116907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4055071156557608775411271 6082606734836413163116907)
      ·
        refine ⟨9123910102254619744675361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6082606734836413163116907 9123910102254619744675361)
        ·
          refine ⟨6842932576690964808506521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9123910102254619744675361 6842932576690964808506521)
          ·
            refine ⟨5132199432518223606379891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6842932576690964808506521 5132199432518223606379891)
            ·
              refine ⟨7698299148777335409569837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5132199432518223606379891 7698299148777335409569837)
              ·
                refine ⟨2886862180791500778588689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7698299148777335409569837 2886862180791500778588689)
                ·
                  refine ⟨2165146635593625583941517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2886862180791500778588689 2165146635593625583941517)
                  ·
                    refine ⟨811929988347609593978069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2165146635593625583941517 811929988347609593978069)
                    ·
                      rfl

theorem cell22_2371842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_2371842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371842 prefixEnd_2371842 := by exact prefixLift 2371842
  have htrace : WordTrace (prefixWord ++ tailWord_2371842) baseStart_2371842 baseEnd_2371842 := by
    simpa [prefixWord, tailWord_2371842, baseEnd_2371842] using wordTrace_append hprefix tailTrace_2371842
  have hstable : (prefixWord ++ tailWord_2371842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371842).length < 2 ^ (prefixWord ++ tailWord_2371842).sum := by decide
  have hdescent : baseEnd_2371842 < baseStart_2371842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371887 : List Nat := [1, 1, 2, 1, 2, 1, 8, 2, 1, 3]
def baseStart_2371887 : Nat := 118140960795 + 2371887 * 2 ^ 59
def prefixEnd_2371887 : Nat := 4983230072969 + 3 ^ 40 * 2371887 * 2
def baseEnd_2371887 : Nat := 811945392767244476602931

theorem tailTrace_2371887 : CollatzResearch.WordTrace tailWord_2371887 prefixEnd_2371887 811945392767244476602931 := by
  unfold tailWord_2371887
  simp only [CollatzResearch.WordTrace]
  refine ⟨86509825958065959894161915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57673217305377306596107943 86509825958065959894161915)
  ·
    refine ⟨129764738937098939841242873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86509825958065959894161915 129764738937098939841242873)
    ·
      refine ⟨97323554202824204880932155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129764738937098939841242873 97323554202824204880932155)
      ·
        refine ⟨145985331304236307321398233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97323554202824204880932155 145985331304236307321398233)
        ·
          refine ⟨109488998478177230491048675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145985331304236307321398233 109488998478177230491048675)
          ·
            refine ⟨164233497717265845736573013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109488998478177230491048675 164233497717265845736573013)
            ·
              refine ⟨1924611301374209129725465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 164233497717265845736573013 1924611301374209129725465)
              ·
                refine ⟨1443458476030656847294099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1924611301374209129725465 1443458476030656847294099)
                ·
                  refine ⟨2165187714045985270941149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443458476030656847294099 2165187714045985270941149)
                  ·
                    refine ⟨811945392767244476602931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2165187714045985270941149 811945392767244476602931)
                    ·
                      rfl

theorem cell22_2371887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 1, 3].length) (baseStart_2371887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371887 prefixEnd_2371887 := by exact prefixLift 2371887
  have htrace : WordTrace (prefixWord ++ tailWord_2371887) baseStart_2371887 baseEnd_2371887 := by
    simpa [prefixWord, tailWord_2371887, baseEnd_2371887] using wordTrace_append hprefix tailTrace_2371887
  have hstable : (prefixWord ++ tailWord_2371887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371887).length < 2 ^ (prefixWord ++ tailWord_2371887).sum := by decide
  have hdescent : baseEnd_2371887 < baseStart_2371887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371898 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 2, 5]
def baseStart_2371898 : Nat := 118140960795 + 2371898 * 2 ^ 59
def prefixEnd_2371898 : Nat := 4983230072969 + 3 ^ 40 * 2371898 * 2
def baseEnd_2371898 : Nat := 811949158292044114577897

theorem tailTrace_2371898 : CollatzResearch.WordTrace tailWord_2371898 prefixEnd_2371898 811949158292044114577897 := by
  unfold tailWord_2371898
  simp only [CollatzResearch.WordTrace]
  refine ⟨21627556790256527193203087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57673484774017405848541565 21627556790256527193203087)
  ·
    refine ⟨32441335185384790789804631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21627556790256527193203087 32441335185384790789804631)
    ·
      refine ⟨48662002778077186184706947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32441335185384790789804631 48662002778077186184706947)
      ·
        refine ⟨72993004167115779277060421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48662002778077186184706947 72993004167115779277060421)
        ·
          refine ⟨13686188281334208614448829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72993004167115779277060421 13686188281334208614448829)
          ·
            refine ⟨5132320605500328230418311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13686188281334208614448829 5132320605500328230418311)
            ·
              refine ⟨7698480908250492345627467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5132320605500328230418311 7698480908250492345627467)
              ·
                refine ⟨11547721362375738518441201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7698480908250492345627467 11547721362375738518441201)
                ·
                  refine ⟨8660791021781803888830901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11547721362375738518441201 8660791021781803888830901)
                  ·
                    refine ⟨811949158292044114577897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8660791021781803888830901 811949158292044114577897)
                    ·
                      rfl

theorem cell22_2371898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_2371898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371898 prefixEnd_2371898 := by exact prefixLift 2371898
  have htrace : WordTrace (prefixWord ++ tailWord_2371898) baseStart_2371898 baseEnd_2371898 := by
    simpa [prefixWord, tailWord_2371898, baseEnd_2371898] using wordTrace_append hprefix tailTrace_2371898
  have hstable : (prefixWord ++ tailWord_2371898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371898).length < 2 ^ (prefixWord ++ tailWord_2371898).sum := by decide
  have hdescent : baseEnd_2371898 < baseStart_2371898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371913 : List Nat := [1, 2, 1, 1, 2, 3, 1, 6, 1, 4]
def baseStart_2371913 : Nat := 118140960795 + 2371913 * 2 ^ 59
def prefixEnd_2371913 : Nat := 4983230072969 + 3 ^ 40 * 2371913 * 2
def baseEnd_2371913 : Nat := 811954293098589075452851

theorem tailTrace_2371913 : CollatzResearch.WordTrace tailWord_2371913 prefixEnd_2371913 811954293098589075452851 := by
  unfold tailWord_2371913
  simp only [CollatzResearch.WordTrace]
  refine ⟨86510774255971766334608393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57673849503981177556405595 86510774255971766334608393)
  ·
    refine ⟨64883080691978824750956295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86510774255971766334608393 64883080691978824750956295)
    ·
      refine ⟨97324621037968237126434443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64883080691978824750956295 97324621037968237126434443)
      ·
        refine ⟨145986931556952355689651665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97324621037968237126434443 145986931556952355689651665)
        ·
          refine ⟨109490198667714266767238749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145986931556952355689651665 109490198667714266767238749)
          ·
            refine ⟨41058824500392850037714531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109490198667714266767238749 41058824500392850037714531)
            ·
              refine ⟨61588236750589275056571797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41058824500392850037714531 61588236750589275056571797)
              ·
                refine ⟨2886948597683872268276803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61588236750589275056571797 2886948597683872268276803)
                ·
                  refine ⟨4330422896525808402415205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2886948597683872268276803 4330422896525808402415205)
                  ·
                    refine ⟨811954293098589075452851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4330422896525808402415205 811954293098589075452851)
                    ·
                      rfl

theorem cell22_2371913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 4].length) (baseStart_2371913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371913 prefixEnd_2371913 := by exact prefixLift 2371913
  have htrace : WordTrace (prefixWord ++ tailWord_2371913) baseStart_2371913 baseEnd_2371913 := by
    simpa [prefixWord, tailWord_2371913, baseEnd_2371913] using wordTrace_append hprefix tailTrace_2371913
  have hstable : (prefixWord ++ tailWord_2371913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371913).length < 2 ^ (prefixWord ++ tailWord_2371913).sum := by decide
  have hdescent : baseEnd_2371913 < baseStart_2371913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372048 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 7, 4]
def baseStart_2372048 : Nat := 118140960795 + 2372048 * 2 ^ 59
def prefixEnd_2372048 : Nat := 4983230072969 + 3 ^ 40 * 2372048 * 2
def baseEnd_2372048 : Nat := 812000506357493723327437

theorem tailTrace_2372048 : CollatzResearch.WordTrace tailWord_2372048 prefixEnd_2372048 812000506357493723327437 := by
  unfold tailWord_2372048
  simp only [CollatzResearch.WordTrace]
  refine ⟨43257849055241342195386399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57677132073655122927181865 43257849055241342195386399)
  ·
    refine ⟨64886773582862013293079599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43257849055241342195386399 64886773582862013293079599)
    ·
      refine ⟨97330160374293019939619399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64886773582862013293079599 97330160374293019939619399)
      ·
        refine ⟨145995240561439529909429099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97330160374293019939619399 145995240561439529909429099)
        ·
          refine ⟨218992860842159294864143649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145995240561439529909429099 218992860842159294864143649)
          ·
            refine ⟨164244645631619471148107737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218992860842159294864143649 164244645631619471148107737)
            ·
              refine ⟨123183484223714603361080803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164244645631619471148107737 123183484223714603361080803)
              ·
                refine ⟨184775226335571905041621205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123183484223714603361080803 184775226335571905041621205)
                ·
                  refine ⟨4330669367239966524412997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 184775226335571905041621205 4330669367239966524412997)
                  ·
                    refine ⟨812000506357493723327437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4330669367239966524412997 812000506357493723327437)
                    ·
                      rfl

theorem cell22_2372048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 7, 4].length) (baseStart_2372048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372048 prefixEnd_2372048 := by exact prefixLift 2372048
  have htrace : WordTrace (prefixWord ++ tailWord_2372048) baseStart_2372048 baseEnd_2372048 := by
    simpa [prefixWord, tailWord_2372048, baseEnd_2372048] using wordTrace_append hprefix tailTrace_2372048
  have hstable : (prefixWord ++ tailWord_2372048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372048).length < 2 ^ (prefixWord ++ tailWord_2372048).sum := by decide
  have hdescent : baseEnd_2372048 < baseStart_2372048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372052 : List Nat := [2, 4, 1, 2, 2, 2, 2, 2, 5]
def baseStart_2372052 : Nat := 118140960795 + 2372052 * 2 ^ 59
def prefixEnd_2372052 : Nat := 4983230072969 + 3 ^ 40 * 2372052 * 2
def baseEnd_2372052 : Nat := 270667291879746348742475

theorem tailTrace_2372052 : CollatzResearch.WordTrace tailWord_2372052 prefixEnd_2372052 270667291879746348742475 := by
  unfold tailWord_2372052
  simp only [CollatzResearch.WordTrace]
  refine ⟨43257922001234096536959205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57677229334978795382612273 43257922001234096536959205)
  ·
    refine ⟨8110860375231393100679851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43257922001234096536959205 8110860375231393100679851)
    ·
      refine ⟨12166290562847089651019777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8110860375231393100679851 12166290562847089651019777)
      ·
        refine ⟨9124717922135317238264833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12166290562847089651019777 9124717922135317238264833)
        ·
          refine ⟨6843538441601487928698625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9124717922135317238264833 6843538441601487928698625)
          ·
            refine ⟨5132653831201115946523969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6843538441601487928698625 5132653831201115946523969)
            ·
              refine ⟨3849490373400836959892977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5132653831201115946523969 3849490373400836959892977)
              ·
                refine ⟨2887117780050627719919733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3849490373400836959892977 2887117780050627719919733)
                ·
                  refine ⟨270667291879746348742475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2887117780050627719919733 270667291879746348742475)
                  ·
                    rfl

theorem cell22_2372052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_2372052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372052 prefixEnd_2372052 := by exact prefixLift 2372052
  have htrace : WordTrace (prefixWord ++ tailWord_2372052) baseStart_2372052 baseEnd_2372052 := by
    simpa [prefixWord, tailWord_2372052, baseEnd_2372052] using wordTrace_append hprefix tailTrace_2372052
  have hstable : (prefixWord ++ tailWord_2372052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372052).length < 2 ^ (prefixWord ++ tailWord_2372052).sum := by decide
  have hdescent : baseEnd_2372052 < baseStart_2372052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372095 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 4, 3]
def baseStart_2372095 : Nat := 118140960795 + 2372095 * 2 ^ 59
def prefixEnd_2372095 : Nat := 4983230072969 + 3 ^ 40 * 2372095 * 2
def baseEnd_2372095 : Nat := 812016595418001267402293

theorem tailTrace_2372095 : CollatzResearch.WordTrace tailWord_2372095 prefixEnd_2372095 812016595418001267402293 := by
  unfold tailWord_2372095
  simp only [CollatzResearch.WordTrace]
  refine ⟨86517412341312411417733739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57678274894208274278489159 86517412341312411417733739)
  ·
    refine ⟨129776118511968617126600609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86517412341312411417733739 129776118511968617126600609)
    ·
      refine ⟨97332088883976462844950457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129776118511968617126600609 97332088883976462844950457)
      ·
        refine ⟨72999066662982347133712843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97332088883976462844950457 72999066662982347133712843)
        ·
          refine ⟨109498599994473520700569265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72999066662982347133712843 109498599994473520700569265)
          ·
            refine ⟨82123949995855140525426949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109498599994473520700569265 82123949995855140525426949)
            ·
              refine ⟨15398240624222838848517553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82123949995855140525426949 15398240624222838848517553)
              ·
                refine ⟨11548680468167129136388165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15398240624222838848517553 11548680468167129136388165)
                ·
                  refine ⟨2165377587781336713072781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11548680468167129136388165 2165377587781336713072781)
                  ·
                    refine ⟨812016595418001267402293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2165377587781336713072781 812016595418001267402293)
                    ·
                      rfl

theorem cell22_2372095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 3].length) (baseStart_2372095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372095 prefixEnd_2372095 := by exact prefixLift 2372095
  have htrace : WordTrace (prefixWord ++ tailWord_2372095) baseStart_2372095 baseEnd_2372095 := by
    simpa [prefixWord, tailWord_2372095, baseEnd_2372095] using wordTrace_append hprefix tailTrace_2372095
  have hstable : (prefixWord ++ tailWord_2372095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372095).length < 2 ^ (prefixWord ++ tailWord_2372095).sum := by decide
  have hdescent : baseEnd_2372095 < baseStart_2372095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372097 : List Nat := [1, 2, 4, 1, 3, 1, 1, 5, 4]
def baseStart_2372097 : Nat := 118140960795 + 2372097 * 2 ^ 59
def prefixEnd_2372097 : Nat := 4983230072969 + 3 ^ 40 * 2372097 * 2
def baseEnd_2372097 : Nat := 270672426686291309617429

theorem tailTrace_2372097 : CollatzResearch.WordTrace tailWord_2372097 prefixEnd_2372097 270672426686291309617429 := by
  unfold tailWord_2372097
  simp only [CollatzResearch.WordTrace]
  refine ⟨86517485287305165759306545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57678323524870110506204363 86517485287305165759306545)
  ·
    refine ⟨64888113965478874319479909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86517485287305165759306545 64888113965478874319479909)
    ·
      refine ⟨12166521368527288934902483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64888113965478874319479909 12166521368527288934902483)
      ·
        refine ⟨18249782052790933402353725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12166521368527288934902483 18249782052790933402353725)
        ·
          refine ⟨6843668269796600025882647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18249782052790933402353725 6843668269796600025882647)
          ·
            refine ⟨10265502404694900038823971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6843668269796600025882647 10265502404694900038823971)
            ·
              refine ⟨15398253607042350058235957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10265502404694900038823971 15398253607042350058235957)
              ·
                refine ⟨1443586275660220317959621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15398253607042350058235957 1443586275660220317959621)
                ·
                  refine ⟨270672426686291309617429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1443586275660220317959621 270672426686291309617429)
                  ·
                    rfl

theorem cell22_2372097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 4].length) (baseStart_2372097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372097 prefixEnd_2372097 := by exact prefixLift 2372097
  have htrace : WordTrace (prefixWord ++ tailWord_2372097) baseStart_2372097 baseEnd_2372097 := by
    simpa [prefixWord, tailWord_2372097, baseEnd_2372097] using wordTrace_append hprefix tailTrace_2372097
  have hstable : (prefixWord ++ tailWord_2372097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372097).length < 2 ^ (prefixWord ++ tailWord_2372097).sum := by decide
  have hdescent : baseEnd_2372097 < baseStart_2372097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372129 : List Nat := [1, 2, 3, 2, 2, 1, 5, 1, 2, 3]
def baseStart_2372129 : Nat := 118140960795 + 2372129 * 2 ^ 59
def prefixEnd_2372129 : Nat := 4983230072969 + 3 ^ 40 * 2372129 * 2
def baseEnd_2372129 : Nat := 812028234312836512052189

theorem tailTrace_2372129 : CollatzResearch.WordTrace tailWord_2372129 prefixEnd_2372129 812028234312836512052189 := by
  unfold tailWord_2372129
  simp only [CollatzResearch.WordTrace]
  refine ⟨86518652423189235224471441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57679101615459490149647627 86518652423189235224471441)
  ·
    refine ⟨64888989317391926418353581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86518652423189235224471441 64888989317391926418353581)
    ·
      refine ⟨24333370994021972406882593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64888989317391926418353581 24333370994021972406882593)
      ·
        refine ⟨18250028245516479305161945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24333370994021972406882593 18250028245516479305161945)
        ·
          refine ⟨13687521184137359478871459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18250028245516479305161945 13687521184137359478871459)
          ·
            refine ⟨20531281776206039218307189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13687521184137359478871459 20531281776206039218307189)
            ·
              refine ⟨1924807666519316176716299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20531281776206039218307189 1924807666519316176716299)
              ·
                refine ⟨2887211499778974265074449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1924807666519316176716299 2887211499778974265074449)
                ·
                  refine ⟨2165408624834230698805837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2887211499778974265074449 2165408624834230698805837)
                  ·
                    refine ⟨812028234312836512052189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2165408624834230698805837 812028234312836512052189)
                    ·
                      rfl

theorem cell22_2372129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_2372129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372129 prefixEnd_2372129 := by exact prefixLift 2372129
  have htrace : WordTrace (prefixWord ++ tailWord_2372129) baseStart_2372129 baseEnd_2372129 := by
    simpa [prefixWord, tailWord_2372129, baseEnd_2372129] using wordTrace_append hprefix tailTrace_2372129
  have hstable : (prefixWord ++ tailWord_2372129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372129).length < 2 ^ (prefixWord ++ tailWord_2372129).sum := by decide
  have hdescent : baseEnd_2372129 < baseStart_2372129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372142 : List Nat := [4, 1, 3, 1, 3, 1, 1, 8]
def baseStart_2372142 : Nat := 118140960795 + 2372142 * 2 ^ 59
def prefixEnd_2372142 : Nat := 4983230072969 + 3 ^ 40 * 2372142 * 2
def baseEnd_2372142 : Nat := 90225853830945423497461

theorem tailTrace_2372142 : CollatzResearch.WordTrace tailWord_2372142 prefixEnd_2372142 90225853830945423497461 := by
  unfold tailWord_2372142
  simp only [CollatzResearch.WordTrace]
  refine ⟨10814890821517767305586835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57679417714761425629796453 10814890821517767305586835)
  ·
    refine ⟨16222336232276650958380253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10814890821517767305586835 16222336232276650958380253)
    ·
      refine ⟨6083376087103744109392595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16222336232276650958380253 6083376087103744109392595)
      ·
        refine ⟨9125064130655616164088893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6083376087103744109392595 9125064130655616164088893)
        ·
          refine ⟨3421899048995856061533335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9125064130655616164088893 3421899048995856061533335)
          ·
            refine ⟨5132848573493784092300003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3421899048995856061533335 5132848573493784092300003)
            ·
              refine ⟨7699272860240676138450005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5132848573493784092300003 7699272860240676138450005)
              ·
                refine ⟨90225853830945423497461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7699272860240676138450005 90225853830945423497461)
                ·
                  rfl

theorem cell22_2372142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_2372142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372142 prefixEnd_2372142 := by exact prefixLift 2372142
  have htrace : WordTrace (prefixWord ++ tailWord_2372142) baseStart_2372142 baseEnd_2372142 := by
    simpa [prefixWord, tailWord_2372142, baseEnd_2372142] using wordTrace_append hprefix tailTrace_2372142
  have hstable : (prefixWord ++ tailWord_2372142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372142).length < 2 ^ (prefixWord ++ tailWord_2372142).sum := by decide
  have hdescent : baseEnd_2372142 < baseStart_2372142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372148 : List Nat := [2, 5, 1, 3, 1, 2, 1, 3, 4]
def baseStart_2372148 : Nat := 118140960795 + 2372148 * 2 ^ 59
def prefixEnd_2372148 : Nat := 4983230072969 + 3 ^ 40 * 2372148 * 2
def baseEnd_2372148 : Nat := 270678246133708931942377

theorem tailTrace_2372148 : CollatzResearch.WordTrace tailWord_2372148 prefixEnd_2372148 270678246133708931942377 := by
  unfold tailWord_2372148
  simp only [CollatzResearch.WordTrace]
  refine ⟨43259672705060200734706549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57679563606746934312942065 43259672705060200734706549)
  ·
    refine ⟨4055594316099393818878739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43259672705060200734706549 4055594316099393818878739)
    ·
      refine ⟨6083391474149090728318109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4055594316099393818878739 6083391474149090728318109)
      ·
        refine ⟨2281271802805909023119291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6083391474149090728318109 2281271802805909023119291)
        ·
          refine ⟨3421907704208863534678937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2281271802805909023119291 3421907704208863534678937)
          ·
            refine ⟨2566430778156647651009203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3421907704208863534678937 2566430778156647651009203)
            ·
              refine ⟨3849646167234971476513805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2566430778156647651009203 3849646167234971476513805)
              ·
                refine ⟨1443617312713114303692677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3849646167234971476513805 1443617312713114303692677)
                ·
                  refine ⟨270678246133708931942377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1443617312713114303692677 270678246133708931942377)
                  ·
                    rfl

theorem cell22_2372148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_2372148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372148 prefixEnd_2372148 := by exact prefixLift 2372148
  have htrace : WordTrace (prefixWord ++ tailWord_2372148) baseStart_2372148 baseEnd_2372148 := by
    simpa [prefixWord, tailWord_2372148, baseEnd_2372148] using wordTrace_append hprefix tailTrace_2372148
  have hstable : (prefixWord ++ tailWord_2372148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372148).length < 2 ^ (prefixWord ++ tailWord_2372148).sum := by decide
  have hdescent : baseEnd_2372148 < baseStart_2372148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372170 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 7]
def baseStart_2372170 : Nat := 118140960795 + 2372170 * 2 ^ 59
def prefixEnd_2372170 : Nat := 4983230072969 + 3 ^ 40 * 2372170 * 2
def baseEnd_2372170 : Nat := 270680756483575357259021

theorem tailTrace_2372170 : CollatzResearch.WordTrace tailWord_2372170 prefixEnd_2372170 270680756483575357259021 := by
  unfold tailWord_2372170
  simp only [CollatzResearch.WordTrace]
  refine ⟨21630036954010174806678491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57680098544027132817809309 21630036954010174806678491)
  ·
    refine ⟨32445055431015262210017737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21630036954010174806678491 32445055431015262210017737)
    ·
      refine ⟨24333791573261446657513303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32445055431015262210017737 24333791573261446657513303)
      ·
        refine ⟨36500687359892169986269955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24333791573261446657513303 36500687359892169986269955)
        ·
          refine ⟨54751031039838254979404933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36500687359892169986269955 54751031039838254979404933)
          ·
            refine ⟨10265818319969672808638425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54751031039838254979404933 10265818319969672808638425)
            ·
              refine ⟨7699363739977254606478819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10265818319969672808638425 7699363739977254606478819)
              ·
                refine ⟨11549045609965881909718229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7699363739977254606478819 11549045609965881909718229)
                ·
                  refine ⟨270680756483575357259021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11549045609965881909718229 270680756483575357259021)
                  ·
                    rfl

theorem cell22_2372170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_2372170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372170 prefixEnd_2372170 := by exact prefixLift 2372170
  have htrace : WordTrace (prefixWord ++ tailWord_2372170) baseStart_2372170 baseEnd_2372170 := by
    simpa [prefixWord, tailWord_2372170, baseEnd_2372170] using wordTrace_append hprefix tailTrace_2372170
  have hstable : (prefixWord ++ tailWord_2372170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372170).length < 2 ^ (prefixWord ++ tailWord_2372170).sum := by decide
  have hdescent : baseEnd_2372170 < baseStart_2372170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372174 : List Nat := [4, 1, 1, 1, 1, 2, 2, 6, 1, 3]
def baseStart_2372174 : Nat := 118140960795 + 2372174 * 2 ^ 59
def prefixEnd_2372174 : Nat := 4983230072969 + 3 ^ 40 * 2372174 * 2
def baseEnd_2372174 : Nat := 812043638732471394677051

theorem tailTrace_2372174 : CollatzResearch.WordTrace tailWord_2372174 prefixEnd_2372174 812043638732471394677051 := by
  unfold tailWord_2372174
  simp only [CollatzResearch.WordTrace]
  refine ⟨10815036713503275988732447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57680195805350805273239717 10815036713503275988732447)
  ·
    refine ⟨16222555070254913983098671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10815036713503275988732447 16222555070254913983098671)
    ·
      refine ⟨24333832605382370974648007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16222555070254913983098671 24333832605382370974648007)
      ·
        refine ⟨36500748908073556461972011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24333832605382370974648007 36500748908073556461972011)
        ·
          refine ⟨54751123362110334692958017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36500748908073556461972011 54751123362110334692958017)
          ·
            refine ⟨41063342521582751019718513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54751123362110334692958017 41063342521582751019718513)
            ·
              refine ⟨30797506891187063264788885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41063342521582751019718513 30797506891187063264788885)
              ·
                refine ⟨1443633135524393590536979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30797506891187063264788885 1443633135524393590536979)
                ·
                  refine ⟨2165449703286590385805469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443633135524393590536979 2165449703286590385805469)
                  ·
                    refine ⟨812043638732471394677051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2165449703286590385805469 812043638732471394677051)
                    ·
                      rfl

theorem cell22_2372174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_2372174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372174 prefixEnd_2372174 := by exact prefixLift 2372174
  have htrace : WordTrace (prefixWord ++ tailWord_2372174) baseStart_2372174 baseEnd_2372174 := by
    simpa [prefixWord, tailWord_2372174, baseEnd_2372174] using wordTrace_append hprefix tailTrace_2372174
  have hstable : (prefixWord ++ tailWord_2372174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372174).length < 2 ^ (prefixWord ++ tailWord_2372174).sum := by decide
  have hdescent : baseEnd_2372174 < baseStart_2372174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372247 : List Nat := [1, 1, 3, 3, 2, 1, 4, 1, 1, 5]
def baseStart_2372247 : Nat := 118140960795 + 2372247 * 2 ^ 59
def prefixEnd_2372247 : Nat := 4983230072969 + 3 ^ 40 * 2372247 * 2
def baseEnd_2372247 : Nat := 812068628124323537601827

theorem tailTrace_2372247 : CollatzResearch.WordTrace tailWord_2372247 prefixEnd_2372247 812068628124323537601827 := by
  unfold tailWord_2372247
  simp only [CollatzResearch.WordTrace]
  refine ⟨86522956236761741377266995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57681970824507827584844663 86522956236761741377266995)
  ·
    refine ⟨129784434355142612065900493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86522956236761741377266995 129784434355142612065900493)
    ·
      refine ⟨48669162883178479524712685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129784434355142612065900493 48669162883178479524712685)
      ·
        refine ⟨18250936081191929821767257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48669162883178479524712685 18250936081191929821767257)
        ·
          refine ⟨13688202060893947366325443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18250936081191929821767257 13688202060893947366325443)
          ·
            refine ⟨20532303091340921049488165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13688202060893947366325443 20532303091340921049488165)
            ·
              refine ⟨3849806829626422696779031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20532303091340921049488165 3849806829626422696779031)
              ·
                refine ⟨5774710244439634045168547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3849806829626422696779031 5774710244439634045168547)
                ·
                  refine ⟨8662065366659451067752821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5774710244439634045168547 8662065366659451067752821)
                  ·
                    refine ⟨812068628124323537601827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8662065366659451067752821 812068628124323537601827)
                    ·
                      rfl

theorem cell22_2372247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_2372247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372247 prefixEnd_2372247 := by exact prefixLift 2372247
  have htrace : WordTrace (prefixWord ++ tailWord_2372247) baseStart_2372247 baseEnd_2372247 := by
    simpa [prefixWord, tailWord_2372247, baseEnd_2372247] using wordTrace_append hprefix tailTrace_2372247
  have hstable : (prefixWord ++ tailWord_2372247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372247).length < 2 ^ (prefixWord ++ tailWord_2372247).sum := by decide
  have hdescent : baseEnd_2372247 < baseStart_2372247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372277 : List Nat := [1, 3, 3, 3, 1, 2, 9]
def baseStart_2372277 : Nat := 118140960795 + 2372277 * 2 ^ 59
def prefixEnd_2372277 : Nat := 4983230072969 + 3 ^ 40 * 2372277 * 2
def baseEnd_2372277 : Nat := 30076996212496794790805

theorem tailTrace_2372277 : CollatzResearch.WordTrace tailWord_2372277 prefixEnd_2372277 30076996212496794790805 := by
  unfold tailWord_2372277
  simp only [CollatzResearch.WordTrace]
  refine ⟨86524050426653056500859085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57682700284435371000572723 86524050426653056500859085)
  ·
    refine ⟨32446518909994896187822157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86524050426653056500859085 32446518909994896187822157)
    ·
      refine ⟨12167444591248086070433309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32446518909994896187822157 12167444591248086070433309)
      ·
        refine ⟨4562791721718032276412491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12167444591248086070433309 4562791721718032276412491)
        ·
          refine ⟨6844187582577048414618737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4562791721718032276412491 6844187582577048414618737)
          ·
            refine ⟨5133140686932786310964053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6844187582577048414618737 5133140686932786310964053)
            ·
              refine ⟨30076996212496794790805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5133140686932786310964053 30076996212496794790805)
              ·
                rfl

theorem cell22_2372277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 9].length) (baseStart_2372277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372277 prefixEnd_2372277 := by exact prefixLift 2372277
  have htrace : WordTrace (prefixWord ++ tailWord_2372277) baseStart_2372277 baseEnd_2372277 := by
    simpa [prefixWord, tailWord_2372277, baseEnd_2372277] using wordTrace_append hprefix tailTrace_2372277
  have hstable : (prefixWord ++ tailWord_2372277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372277).length < 2 ^ (prefixWord ++ tailWord_2372277).sum := by decide
  have hdescent : baseEnd_2372277 < baseStart_2372277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372369 : List Nat := [1, 2, 2, 1, 1, 3, 5, 2, 1, 4]
def baseStart_2372369 : Nat := 118140960795 + 2372369 * 2 ^ 59
def prefixEnd_2372369 : Nat := 4983230072969 + 3 ^ 40 * 2372369 * 2
def baseEnd_2372369 : Nat := 812110391217555886051453

theorem tailTrace_2372369 : CollatzResearch.WordTrace tailWord_2372369 prefixEnd_2372369 812110391217555886051453 := by
  unfold tailWord_2372369
  simp only [CollatzResearch.WordTrace]
  refine ⟨86527405942319756213208161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57684937294879837475472107 86527405942319756213208161)
  ·
    refine ⟨64895554456739817159906121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86527405942319756213208161 64895554456739817159906121)
    ·
      refine ⟨48671665842554862869929591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64895554456739817159906121 48671665842554862869929591)
      ·
        refine ⟨73007498763832294304894387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48671665842554862869929591 73007498763832294304894387)
        ·
          refine ⟨109511248145748441457341581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73007498763832294304894387 109511248145748441457341581)
          ·
            refine ⟨41066718054655665546503093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109511248145748441457341581 41066718054655665546503093)
            ·
              refine ⟨3850004817623968644984665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41066718054655665546503093 3850004817623968644984665)
              ·
                refine ⟨2887503613217976483738499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3850004817623968644984665 2887503613217976483738499)
                ·
                  refine ⟨4331255419826964725607749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2887503613217976483738499 4331255419826964725607749)
                  ·
                    refine ⟨812110391217555886051453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4331255419826964725607749 812110391217555886051453)
                    ·
                      rfl

theorem cell22_2372369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_2372369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372369 prefixEnd_2372369 := by exact prefixLift 2372369
  have htrace : WordTrace (prefixWord ++ tailWord_2372369) baseStart_2372369 baseEnd_2372369 := by
    simpa [prefixWord, tailWord_2372369, baseEnd_2372369] using wordTrace_append hprefix tailTrace_2372369
  have hstable : (prefixWord ++ tailWord_2372369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372369).length < 2 ^ (prefixWord ++ tailWord_2372369).sum := by decide
  have hdescent : baseEnd_2372369 < baseStart_2372369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372394 : List Nat := [3, 1, 4, 3, 2, 1, 2, 2, 1, 3]
def baseStart_2372394 : Nat := 118140960795 + 2372394 * 2 ^ 59
def prefixEnd_2372394 : Nat := 4983230072969 + 3 ^ 40 * 2372394 * 2
def baseEnd_2372394 : Nat := 812118949228464154176377

theorem tailTrace_2372394 : CollatzResearch.WordTrace tailWord_2372394 prefixEnd_2372394 812118949228464154176377 := by
  unfold tailWord_2372394
  simp only [CollatzResearch.WordTrace]
  refine ⟨21632079441807296370717059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57685545178152790321912157 21632079441807296370717059)
  ·
    refine ⟨32448119162710944556075589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21632079441807296370717059 32448119162710944556075589)
    ·
      refine ⟨6084022343008302104264173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32448119162710944556075589 6084022343008302104264173)
      ·
        refine ⟨2281508378628113289099065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6084022343008302104264173 2281508378628113289099065)
        ·
          refine ⟨1711131283971084966824299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2281508378628113289099065 1711131283971084966824299)
          ·
            refine ⟨2566696925956627450236449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1711131283971084966824299 2566696925956627450236449)
            ·
              refine ⟨1925022694467470587677337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2566696925956627450236449 1925022694467470587677337)
              ·
                refine ⟨1443767020850602940758003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1925022694467470587677337 1443767020850602940758003)
                ·
                  refine ⟨2165650531275904411137005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443767020850602940758003 2165650531275904411137005)
                  ·
                    refine ⟨812118949228464154176377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2165650531275904411137005 812118949228464154176377)
                    ·
                      rfl

theorem cell22_2372394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_2372394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372394 prefixEnd_2372394 := by exact prefixLift 2372394
  have htrace : WordTrace (prefixWord ++ tailWord_2372394) baseStart_2372394 baseEnd_2372394 := by
    simpa [prefixWord, tailWord_2372394, baseEnd_2372394] using wordTrace_append hprefix tailTrace_2372394
  have hstable : (prefixWord ++ tailWord_2372394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372394).length < 2 ^ (prefixWord ++ tailWord_2372394).sum := by decide
  have hdescent : baseEnd_2372394 < baseStart_2372394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372450 : List Nat := [3, 3, 2, 1, 3, 2, 1, 2, 2, 3]
def baseStart_2372450 : Nat := 118140960795 + 2372450 * 2 ^ 59
def prefixEnd_2372450 : Nat := 4983230072969 + 3 ^ 40 * 2372450 * 2
def baseEnd_2372450 : Nat := 812138119172898674776205

theorem tailTrace_2372450 : CollatzResearch.WordTrace tailWord_2372450 prefixEnd_2372450 812138119172898674776205 := by
  unfold tailWord_2372450
  simp only [CollatzResearch.WordTrace]
  refine ⟨21632590063756576761726701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57686906836684204697937869 21632590063756576761726701)
  ·
    refine ⟨8112221273908716285647513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21632590063756576761726701 8112221273908716285647513)
    ·
      refine ⟨6084165955431537214235635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8112221273908716285647513 6084165955431537214235635)
      ·
        refine ⟨9126248933147305821353453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6084165955431537214235635 9126248933147305821353453)
        ·
          refine ⟨3422343349930239683007545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9126248933147305821353453 3422343349930239683007545)
          ·
            refine ⟨2566757512447679762255659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3422343349930239683007545 2566757512447679762255659)
            ·
              refine ⟨3850136268671519643383489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2566757512447679762255659 3850136268671519643383489)
              ·
                refine ⟨2887602201503639732537617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3850136268671519643383489 2887602201503639732537617)
                ·
                  refine ⟨2165701651127729799403213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2887602201503639732537617 2165701651127729799403213)
                  ·
                    refine ⟨812138119172898674776205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2165701651127729799403213 812138119172898674776205)
                    ·
                      rfl

theorem cell22_2372450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_2372450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372450 prefixEnd_2372450 := by exact prefixLift 2372450
  have htrace : WordTrace (prefixWord ++ tailWord_2372450) baseStart_2372450 baseEnd_2372450 := by
    simpa [prefixWord, tailWord_2372450, baseEnd_2372450] using wordTrace_append hprefix tailTrace_2372450
  have hstable : (prefixWord ++ tailWord_2372450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372450).length < 2 ^ (prefixWord ++ tailWord_2372450).sum := by decide
  have hdescent : baseEnd_2372450 < baseStart_2372450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372472 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 1, 7]
def baseStart_2372472 : Nat := 118140960795 + 2372472 * 2 ^ 59
def prefixEnd_2372472 : Nat := 4983230072969 + 3 ^ 40 * 2372472 * 2
def baseEnd_2372472 : Nat := 812145650222497950726137

theorem tailTrace_2372472 : CollatzResearch.WordTrace tailWord_2372472 prefixEnd_2372472 812145650222497950726137 := by
  unfold tailWord_2372472
  simp only [CollatzResearch.WordTrace]
  refine ⟨43265581330473302402103835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57687441773964403202805113 43265581330473302402103835)
  ·
    refine ⟨64898371995709953603155753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43265581330473302402103835 64898371995709953603155753)
    ·
      refine ⟨48673778996782465202366815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64898371995709953603155753 48673778996782465202366815)
      ·
        refine ⟨73010668495173697803550223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48673778996782465202366815 73010668495173697803550223)
        ·
          refine ⟨109516002742760546705325335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73010668495173697803550223 109516002742760546705325335)
          ·
            refine ⟨164274004114140820057988003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109516002742760546705325335 164274004114140820057988003)
            ·
              refine ⟨246411006171211230086982005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164274004114140820057988003 246411006171211230086982005)
              ·
                refine ⟨23101031828551052820654563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 246411006171211230086982005 23101031828551052820654563)
                ·
                  refine ⟨34651547742826579230981845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23101031828551052820654563 34651547742826579230981845)
                  ·
                    refine ⟨812145650222497950726137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34651547742826579230981845 812145650222497950726137)
                    ·
                      rfl

theorem cell22_2372472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_2372472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372472 prefixEnd_2372472 := by exact prefixLift 2372472
  have htrace : WordTrace (prefixWord ++ tailWord_2372472) baseStart_2372472 baseEnd_2372472 := by
    simpa [prefixWord, tailWord_2372472, baseEnd_2372472] using wordTrace_append hprefix tailTrace_2372472
  have hstable : (prefixWord ++ tailWord_2372472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372472).length < 2 ^ (prefixWord ++ tailWord_2372472).sum := by decide
  have hdescent : baseEnd_2372472 < baseStart_2372472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372564 : List Nat := [2, 4, 1, 2, 1, 12]
def baseStart_2372564 : Nat := 118140960795 + 2372564 * 2 ^ 59
def prefixEnd_2372564 : Nat := 4983230072969 + 3 ^ 40 * 2372564 * 2
def baseEnd_2372564 : Nat := 10026878317316547869455

theorem tailTrace_2372564 : CollatzResearch.WordTrace tailWord_2372564 prefixEnd_2372564 10026878317316547869455 := by
  unfold tailWord_2372564
  simp only [CollatzResearch.WordTrace]
  refine ⟨43267259088306652258278373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57689678784408869677704497 43267259088306652258278373)
  ·
    refine ⟨8112611079057497298427195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43267259088306652258278373 8112611079057497298427195)
    ·
      refine ⟨12168916618586245947640793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8112611079057497298427195 12168916618586245947640793)
      ·
        refine ⟨9126687463939684460730595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12168916618586245947640793 9126687463939684460730595)
        ·
          refine ⟨13690031195909526691095893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9126687463939684460730595 13690031195909526691095893)
          ·
            refine ⟨10026878317316547869455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 13690031195909526691095893 10026878317316547869455)
            ·
              rfl

theorem cell22_2372564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 12].length) (baseStart_2372564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372564 prefixEnd_2372564 := by exact prefixLift 2372564
  have htrace : WordTrace (prefixWord ++ tailWord_2372564) baseStart_2372564 baseEnd_2372564 := by
    simpa [prefixWord, tailWord_2372564, baseEnd_2372564] using wordTrace_append hprefix tailTrace_2372564
  have hstable : (prefixWord ++ tailWord_2372564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372564).length < 2 ^ (prefixWord ++ tailWord_2372564).sum := by decide
  have hdescent : baseEnd_2372564 < baseStart_2372564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372568 : List Nat := [2, 1, 2, 2, 2, 4, 2, 2, 2, 3]
def baseStart_2372568 : Nat := 118140960795 + 2372568 * 2 ^ 59
def prefixEnd_2372568 : Nat := 4983230072969 + 3 ^ 40 * 2372568 * 2
def baseEnd_2372568 : Nat := 812178512984385700325843

theorem tailTrace_2372568 : CollatzResearch.WordTrace tailWord_2372568 prefixEnd_2372568 812178512984385700325843 := by
  unfold tailWord_2372568
  simp only [CollatzResearch.WordTrace]
  refine ⟨43267332034299406599851179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57689776045732542133134905 43267332034299406599851179)
  ·
    refine ⟨64900998051449109899776769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43267332034299406599851179 64900998051449109899776769)
    ·
      refine ⟨48675748538586832424832577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64900998051449109899776769 48675748538586832424832577)
      ·
        refine ⟨36506811403940124318624433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48675748538586832424832577 36506811403940124318624433)
        ·
          refine ⟨27380108552955093238968325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36506811403940124318624433 27380108552955093238968325)
          ·
            refine ⟨5133770353679079982306561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27380108552955093238968325 5133770353679079982306561)
            ·
              refine ⟨3850327765259309986729921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5133770353679079982306561 3850327765259309986729921)
              ·
                refine ⟨2887745823944482490047441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3850327765259309986729921 2887745823944482490047441)
                ·
                  refine ⟨2165809367958361867535581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2887745823944482490047441 2165809367958361867535581)
                  ·
                    refine ⟨812178512984385700325843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2165809367958361867535581 812178512984385700325843)
                    ·
                      rfl

theorem cell22_2372568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 2, 3].length) (baseStart_2372568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372568 prefixEnd_2372568 := by exact prefixLift 2372568
  have htrace : WordTrace (prefixWord ++ tailWord_2372568) baseStart_2372568 baseEnd_2372568 := by
    simpa [prefixWord, tailWord_2372568, baseEnd_2372568] using wordTrace_append hprefix tailTrace_2372568
  have hstable : (prefixWord ++ tailWord_2372568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372568).length < 2 ^ (prefixWord ++ tailWord_2372568).sum := by decide
  have hdescent : baseEnd_2372568 < baseStart_2372568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372570 : List Nat := [3, 1, 1, 2, 4, 3, 2, 2, 4]
def baseStart_2372570 : Nat := 118140960795 + 2372570 * 2 ^ 59
def prefixEnd_2372570 : Nat := 4983230072969 + 3 ^ 40 * 2372570 * 2
def baseEnd_2372570 : Nat := 270726399208419453925279

theorem tailTrace_2372570 : CollatzResearch.WordTrace tailWord_2372570 prefixEnd_2372570 270726399208419453925279 := by
  unfold tailWord_2372570
  simp only [CollatzResearch.WordTrace]
  refine ⟨21633684253647891885318791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57689824676394378360850109 21633684253647891885318791)
  ·
    refine ⟨32450526380471837827978187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21633684253647891885318791 32450526380471837827978187)
    ·
      refine ⟨48675789570707756741967281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32450526380471837827978187 48675789570707756741967281)
      ·
        refine ⟨36506842178030817556475461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48675789570707756741967281 36506842178030817556475461)
        ·
          refine ⟨6845032908380778291839149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36506842178030817556475461 6845032908380778291839149)
          ·
            refine ⟨2566887340642791859439681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6845032908380778291839149 2566887340642791859439681)
            ·
              refine ⟨1925165505482093894579761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2566887340642791859439681 1925165505482093894579761)
              ·
                refine ⟨1443874129111570420934821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1925165505482093894579761 1443874129111570420934821)
                ·
                  refine ⟨270726399208419453925279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1443874129111570420934821 270726399208419453925279)
                  ·
                    rfl

theorem cell22_2372570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 4].length) (baseStart_2372570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372570 prefixEnd_2372570 := by exact prefixLift 2372570
  have htrace : WordTrace (prefixWord ++ tailWord_2372570) baseStart_2372570 baseEnd_2372570 := by
    simpa [prefixWord, tailWord_2372570, baseEnd_2372570] using wordTrace_append hprefix tailTrace_2372570
  have hstable : (prefixWord ++ tailWord_2372570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372570).length < 2 ^ (prefixWord ++ tailWord_2372570).sum := by decide
  have hdescent : baseEnd_2372570 < baseStart_2372570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372598 : List Nat := [5, 1, 1, 1, 3, 2, 3, 6]
def baseStart_2372598 : Nat := 118140960795 + 2372598 * 2 ^ 59
def prefixEnd_2372598 : Nat := 4983230072969 + 3 ^ 40 * 2372598 * 2
def baseEnd_2372598 : Nat := 90243198066386180230639

theorem tailTrace_2372598 : CollatzResearch.WordTrace tailWord_2372598 prefixEnd_2372598 90243198066386180230639 := by
  unfold tailWord_2372598
  simp only [CollatzResearch.WordTrace]
  refine ⟨5408484891155633020205903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57690505505660085548862965 5408484891155633020205903)
  ·
    refine ⟨8112727336733449530308855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5408484891155633020205903 8112727336733449530308855)
    ·
      refine ⟨12169091005100174295463283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8112727336733449530308855 12169091005100174295463283)
      ·
        refine ⟨18253636507650261443194925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12169091005100174295463283 18253636507650261443194925)
        ·
          refine ⟨6845113690368848041198097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18253636507650261443194925 6845113690368848041198097)
          ·
            refine ⟨5133835267776636030898573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6845113690368848041198097 5133835267776636030898573)
            ·
              refine ⟨1925188225416238511586965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5133835267776636030898573 1925188225416238511586965)
              ·
                refine ⟨90243198066386180230639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1925188225416238511586965 90243198066386180230639)
                ·
                  rfl

theorem cell22_2372598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_2372598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372598 prefixEnd_2372598 := by exact prefixLift 2372598
  have htrace : WordTrace (prefixWord ++ tailWord_2372598) baseStart_2372598 baseEnd_2372598 := by
    simpa [prefixWord, tailWord_2372598, baseEnd_2372598] using wordTrace_append hprefix tailTrace_2372598
  have hstable : (prefixWord ++ tailWord_2372598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372598).length < 2 ^ (prefixWord ++ tailWord_2372598).sum := by decide
  have hdescent : baseEnd_2372598 < baseStart_2372598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372641 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 2, 5]
def baseStart_2372641 : Nat := 118140960795 + 2372641 * 2 ^ 59
def prefixEnd_2372641 : Nat := 4983230072969 + 3 ^ 40 * 2372641 * 2
def baseEnd_2372641 : Nat := 812203502376237843250619

theorem tailTrace_2372641 : CollatzResearch.WordTrace tailWord_2372641 prefixEnd_2372641 812203502376237843250619 := by
  unfold tailWord_2372641
  simp only [CollatzResearch.WordTrace]
  refine ⟨86537326597334346667109777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57691551064889564444739851 86537326597334346667109777)
  ·
    refine ⟨64902994948000760000332333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86537326597334346667109777 64902994948000760000332333)
    ·
      refine ⟨24338623105500285000124625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64902994948000760000332333 24338623105500285000124625)
      ·
        refine ⟨18253967329125213750093469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24338623105500285000124625 18253967329125213750093469)
        ·
          refine ⟨6845237748421955156285051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18253967329125213750093469 6845237748421955156285051)
          ·
            refine ⟨10267856622632932734427577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6845237748421955156285051 10267856622632932734427577)
            ·
              refine ⟨7700892466974699550820683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10267856622632932734427577 7700892466974699550820683)
              ·
                refine ⟨11551338700462049326231025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7700892466974699550820683 11551338700462049326231025)
                ·
                  refine ⟨8663504025346536994673269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11551338700462049326231025 8663504025346536994673269)
                  ·
                    refine ⟨812203502376237843250619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8663504025346536994673269 812203502376237843250619)
                    ·
                      rfl

theorem cell22_2372641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_2372641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372641 prefixEnd_2372641 := by exact prefixLift 2372641
  have htrace : WordTrace (prefixWord ++ tailWord_2372641) baseStart_2372641 baseEnd_2372641 := by
    simpa [prefixWord, tailWord_2372641, baseEnd_2372641] using wordTrace_append hprefix tailTrace_2372641
  have hstable : (prefixWord ++ tailWord_2372641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372641).length < 2 ^ (prefixWord ++ tailWord_2372641).sum := by decide
  have hdescent : baseEnd_2372641 < baseStart_2372641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372643 : List Nat := [1, 1, 1, 4, 3, 3, 3, 1, 5]
def baseStart_2372643 : Nat := 118140960795 + 2372643 * 2 ^ 59
def prefixEnd_2372643 : Nat := 4983230072969 + 3 ^ 40 * 2372643 * 2
def baseEnd_2372643 : Nat := 270734729005703501566871

theorem tailTrace_2372643 : CollatzResearch.WordTrace tailWord_2372643 prefixEnd_2372643 270734729005703501566871 := by
  unfold tailWord_2372643
  simp only [CollatzResearch.WordTrace]
  refine ⟨86537399543327101008682583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57691599695551400672455055 86537399543327101008682583)
  ·
    refine ⟨129806099314990651513023875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86537399543327101008682583 129806099314990651513023875)
    ·
      refine ⟨194709148972485977269535813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129806099314990651513023875 194709148972485977269535813)
      ·
        refine ⟨36507965432341120738037965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194709148972485977269535813 36507965432341120738037965)
        ·
          refine ⟨13690487037127920276764237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36507965432341120738037965 13690487037127920276764237)
          ·
            refine ⟨5133932638922970103786589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13690487037127920276764237 5133932638922970103786589)
            ·
              refine ⟨1925224739596113788919971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5133932638922970103786589 1925224739596113788919971)
              ·
                refine ⟨2887837109394170683379957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1925224739596113788919971 2887837109394170683379957)
                ·
                  refine ⟨270734729005703501566871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2887837109394170683379957 270734729005703501566871)
                  ·
                    rfl

theorem cell22_2372643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 5].length) (baseStart_2372643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372643 prefixEnd_2372643 := by exact prefixLift 2372643
  have htrace : WordTrace (prefixWord ++ tailWord_2372643) baseStart_2372643 baseEnd_2372643 := by
    simpa [prefixWord, tailWord_2372643, baseEnd_2372643] using wordTrace_append hprefix tailTrace_2372643
  have hstable : (prefixWord ++ tailWord_2372643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372643).length < 2 ^ (prefixWord ++ tailWord_2372643).sum := by decide
  have hdescent : baseEnd_2372643 < baseStart_2372643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372694 : List Nat := [5, 2, 2, 1, 2, 2, 2, 1, 5]
def baseStart_2372694 : Nat := 118140960795 + 2372694 * 2 ^ 59
def prefixEnd_2372694 : Nat := 4983230072969 + 3 ^ 40 * 2372694 * 2
def baseEnd_2372694 : Nat := 270740548453121123891819

theorem tailTrace_2372694 : CollatzResearch.WordTrace tailWord_2372694 prefixEnd_2372694 270740548453121123891819 := by
  unfold tailWord_2372694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5408703729133896044924321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57692839777428224479192757 5408703729133896044924321)
  ·
    refine ⟨4056527796850422033693241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5408703729133896044924321 4056527796850422033693241)
    ·
      refine ⟨3042395847637816525269931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4056527796850422033693241 3042395847637816525269931)
      ·
        refine ⟨4563593771456724787904897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3042395847637816525269931 4563593771456724787904897)
        ·
          refine ⟨3422695328592543590928673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4563593771456724787904897 3422695328592543590928673)
          ·
            refine ⟨2567021496444407693196505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3422695328592543590928673 2567021496444407693196505)
            ·
              refine ⟨1925266122333305769897379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2567021496444407693196505 1925266122333305769897379)
              ·
                refine ⟨2887899183499958654846069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1925266122333305769897379 2887899183499958654846069)
                ·
                  refine ⟨270740548453121123891819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2887899183499958654846069 270740548453121123891819)
                  ·
                    rfl

theorem cell22_2372694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_2372694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372694 prefixEnd_2372694 := by exact prefixLift 2372694
  have htrace : WordTrace (prefixWord ++ tailWord_2372694) baseStart_2372694 baseEnd_2372694 := by
    simpa [prefixWord, tailWord_2372694, baseEnd_2372694] using wordTrace_append hprefix tailTrace_2372694
  have hstable : (prefixWord ++ tailWord_2372694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372694).length < 2 ^ (prefixWord ++ tailWord_2372694).sum := by decide
  have hdescent : baseEnd_2372694 < baseStart_2372694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372703 : List Nat := [1, 1, 2, 3, 1, 1, 5, 3, 2, 3]
def baseStart_2372703 : Nat := 118140960795 + 2372703 * 2 ^ 59
def prefixEnd_2372703 : Nat := 4983230072969 + 3 ^ 40 * 2372703 * 2
def baseEnd_2372703 : Nat := 812224726243290348200429

theorem tailTrace_2372703 : CollatzResearch.WordTrace tailWord_2372703 prefixEnd_2372703 812224726243290348200429 := by
  unfold tailWord_2372703
  simp only [CollatzResearch.WordTrace]
  refine ⟨86539587923109731255866763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57693058615406487503911175 86539587923109731255866763)
  ·
    refine ⟨129809381884664596883800145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86539587923109731255866763 129809381884664596883800145)
    ·
      refine ⟨97357036413498447662850109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129809381884664596883800145 97357036413498447662850109)
      ·
        refine ⟨36508888655061917873568791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97357036413498447662850109 36508888655061917873568791)
        ·
          refine ⟨54763332982592876810353187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36508888655061917873568791 54763332982592876810353187)
          ·
            refine ⟨82144999473889315215529781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54763332982592876810353187 82144999473889315215529781)
            ·
              refine ⟨7701093700677123301455917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82144999473889315215529781 7701093700677123301455917)
              ·
                refine ⟨2887910137753921238045969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7701093700677123301455917 2887910137753921238045969)
                ·
                  refine ⟨2165932603315440928534477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2887910137753921238045969 2165932603315440928534477)
                  ·
                    refine ⟨812224726243290348200429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2165932603315440928534477 812224726243290348200429)
                    ·
                      rfl

theorem cell22_2372703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 3].length) (baseStart_2372703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372703 prefixEnd_2372703 := by exact prefixLift 2372703
  have htrace : WordTrace (prefixWord ++ tailWord_2372703) baseStart_2372703 baseEnd_2372703 := by
    simpa [prefixWord, tailWord_2372703, baseEnd_2372703] using wordTrace_append hprefix tailTrace_2372703
  have hstable : (prefixWord ++ tailWord_2372703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372703).length < 2 ^ (prefixWord ++ tailWord_2372703).sum := by decide
  have hdescent : baseEnd_2372703 < baseStart_2372703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372718 : List Nat := [4, 1, 2, 2, 1, 2, 1, 3, 2, 4]
def baseStart_2372718 : Nat := 118140960795 + 2372718 * 2 ^ 59
def prefixEnd_2372718 : Nat := 4983230072969 + 3 ^ 40 * 2372718 * 2
def baseEnd_2372718 : Nat := 812229861049835309075383

theorem tailTrace_2372718 : CollatzResearch.WordTrace tailWord_2372718 prefixEnd_2372718 812229861049835309075383 := by
  unfold tailWord_2372718
  simp only [CollatzResearch.WordTrace]
  refine ⟨10817516877256923602207851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57693423345370259211775205 10817516877256923602207851)
  ·
    refine ⟨16226275315885385403311777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10817516877256923602207851 16226275315885385403311777)
    ·
      refine ⟨12169706486914039052483833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16226275315885385403311777 12169706486914039052483833)
      ·
        refine ⟨9127279865185529289362875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12169706486914039052483833 9127279865185529289362875)
        ·
          refine ⟨13690919797778293934044313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9127279865185529289362875 13690919797778293934044313)
          ·
            refine ⟨10268189848333720450533235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13690919797778293934044313 10268189848333720450533235)
            ·
              refine ⟨15402284772500580675799853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10268189848333720450533235 15402284772500580675799853)
              ·
                refine ⟨5775856789687717753424945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15402284772500580675799853 5775856789687717753424945)
                ·
                  refine ⟨4331892592265788315068709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5775856789687717753424945 4331892592265788315068709)
                  ·
                    refine ⟨812229861049835309075383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4331892592265788315068709 812229861049835309075383)
                    ·
                      rfl

theorem cell22_2372718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_2372718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372718 prefixEnd_2372718 := by exact prefixLift 2372718
  have htrace : WordTrace (prefixWord ++ tailWord_2372718) baseStart_2372718 baseEnd_2372718 := by
    simpa [prefixWord, tailWord_2372718, baseEnd_2372718] using wordTrace_append hprefix tailTrace_2372718
  have hstable : (prefixWord ++ tailWord_2372718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372718).length < 2 ^ (prefixWord ++ tailWord_2372718).sum := by decide
  have hdescent : baseEnd_2372718 < baseStart_2372718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372746 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 1, 8]
def baseStart_2372746 : Nat := 118140960795 + 2372746 * 2 ^ 59
def prefixEnd_2372746 : Nat := 4983230072969 + 3 ^ 40 * 2372746 * 2
def baseEnd_2372746 : Nat := 812239446022052569375297

theorem tailTrace_2372746 : CollatzResearch.WordTrace tailWord_2372746 prefixEnd_2372746 812239446022052569375297 := by
  unfold tailWord_2372746
  simp only [CollatzResearch.WordTrace]
  refine ⟨21635289065488487399920523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57694104174635966399788061 21635289065488487399920523)
  ·
    refine ⟨32452933598232731099880785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21635289065488487399920523 32452933598232731099880785)
    ·
      refine ⟨24339700198674548324910589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32452933598232731099880785 24339700198674548324910589)
      ·
        refine ⟨9127387574502955621841471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24339700198674548324910589 9127387574502955621841471)
        ·
          refine ⟨13691081361754433432762207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9127387574502955621841471 13691081361754433432762207)
          ·
            refine ⟨20536622042631650149143311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13691081361754433432762207 20536622042631650149143311)
            ·
              refine ⟨30804933063947475223714967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20536622042631650149143311 30804933063947475223714967)
              ·
                refine ⟨46207399595921212835572451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30804933063947475223714967 46207399595921212835572451)
                ·
                  refine ⟨69311099393881819253358677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46207399595921212835572451 69311099393881819253358677)
                  ·
                    refine ⟨812239446022052569375297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69311099393881819253358677 812239446022052569375297)
                    ·
                      rfl

theorem cell22_2372746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_2372746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372746 prefixEnd_2372746 := by exact prefixLift 2372746
  have htrace : WordTrace (prefixWord ++ tailWord_2372746) baseStart_2372746 baseEnd_2372746 := by
    simpa [prefixWord, tailWord_2372746, baseEnd_2372746] using wordTrace_append hprefix tailTrace_2372746
  have hstable : (prefixWord ++ tailWord_2372746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372746).length < 2 ^ (prefixWord ++ tailWord_2372746).sum := by decide
  have hdescent : baseEnd_2372746 < baseStart_2372746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372851 : List Nat := [1, 1, 1, 2, 2, 5, 10]
def baseStart_2372851 : Nat := 118140960795 + 2372851 * 2 ^ 59
def prefixEnd_2372851 : Nat := 4983230072969 + 3 ^ 40 * 2372851 * 2
def baseEnd_2372851 : Nat := 30084273691402492425925

theorem tailTrace_2372851 : CollatzResearch.WordTrace tailWord_2372851 prefixEnd_2372851 30084273691402492425925 := by
  unfold tailWord_2372851
  simp only [CollatzResearch.WordTrace]
  refine ⟨86544985926573552532254407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57696657284382368354836271 86544985926573552532254407)
  ·
    refine ⟨129817478889860328798381611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86544985926573552532254407 129817478889860328798381611)
    ·
      refine ⟨194726218334790493197572417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129817478889860328798381611 194726218334790493197572417)
      ·
        refine ⟨146044663751092869898179313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194726218334790493197572417 146044663751092869898179313)
        ·
          refine ⟨109533497813319652423634485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146044663751092869898179313 109533497813319652423634485)
          ·
            refine ⟨10268765419998717414715733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109533497813319652423634485 10268765419998717414715733)
            ·
              refine ⟨30084273691402492425925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10268765419998717414715733 30084273691402492425925)
              ·
                rfl

theorem cell22_2372851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 10].length) (baseStart_2372851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372851 prefixEnd_2372851 := by exact prefixLift 2372851
  have htrace : WordTrace (prefixWord ++ tailWord_2372851) baseStart_2372851 baseEnd_2372851 := by
    simpa [prefixWord, tailWord_2372851, baseEnd_2372851] using wordTrace_append hprefix tailTrace_2372851
  have hstable : (prefixWord ++ tailWord_2372851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372851).length < 2 ^ (prefixWord ++ tailWord_2372851).sum := by decide
  have hdescent : baseEnd_2372851 < baseStart_2372851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372868 : List Nat := [2, 3, 2, 2, 2, 1, 1, 9]
def baseStart_2372868 : Nat := 118140960795 + 2372868 * 2 ^ 59
def prefixEnd_2372868 : Nat := 4983230072969 + 3 ^ 40 * 2372868 * 2
def baseEnd_2372868 : Nat := 90253467679476101980547

theorem tailTrace_2372868 : CollatzResearch.WordTrace tailWord_2372868 prefixEnd_2372868 90253467679476101980547 := by
  unfold tailWord_2372868
  simp only [CollatzResearch.WordTrace]
  refine ⟨43272802983755982217811629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57697070645007976290415505 43272802983755982217811629)
  ·
    refine ⟨16227301118908493331679361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43272802983755982217811629 16227301118908493331679361)
    ·
      refine ⟨12170475839181369998759521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16227301118908493331679361 12170475839181369998759521)
      ·
        refine ⟨9127856879386027499069641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12170475839181369998759521 9127856879386027499069641)
        ·
          refine ⟨6845892659539520624302231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9127856879386027499069641 6845892659539520624302231)
          ·
            refine ⟨10268838989309280936453347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6845892659539520624302231 10268838989309280936453347)
            ·
              refine ⟨15403258483963921404680021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10268838989309280936453347 15403258483963921404680021)
              ·
                refine ⟨90253467679476101980547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15403258483963921404680021 90253467679476101980547)
                ·
                  rfl

theorem cell22_2372868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 9].length) (baseStart_2372868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372868 prefixEnd_2372868 := by exact prefixLift 2372868
  have htrace : WordTrace (prefixWord ++ tailWord_2372868) baseStart_2372868 baseEnd_2372868 := by
    simpa [prefixWord, tailWord_2372868, baseEnd_2372868] using wordTrace_append hprefix tailTrace_2372868
  have hstable : (prefixWord ++ tailWord_2372868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372868).length < 2 ^ (prefixWord ++ tailWord_2372868).sum := by decide
  have hdescent : baseEnd_2372868 < baseStart_2372868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372872 : List Nat := [2, 1, 3, 2, 4, 1, 1, 3, 2, 3]
def baseStart_2372872 : Nat := 118140960795 + 2372872 * 2 ^ 59
def prefixEnd_2372872 : Nat := 4983230072969 + 3 ^ 40 * 2372872 * 2
def baseEnd_2372872 : Nat := 812282578397030240724911

theorem tailTrace_2372872 : CollatzResearch.WordTrace tailWord_2372872 prefixEnd_2372872 812282578397030240724911 := by
  unfold tailWord_2372872
  simp only [CollatzResearch.WordTrace]
  refine ⟨43272875929748736559384435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57697167906331648745845913 43272875929748736559384435)
  ·
    refine ⟨64909313894623104839076653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43272875929748736559384435 64909313894623104839076653)
    ·
      refine ⟨24340992710483664314653745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64909313894623104839076653 24340992710483664314653745)
      ·
        refine ⟨18255744532862748235990309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24340992710483664314653745 18255744532862748235990309)
        ·
          refine ⟨3422952099911765294248183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18255744532862748235990309 3422952099911765294248183)
          ·
            refine ⟨5134428149867647941372275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3422952099911765294248183 5134428149867647941372275)
            ·
              refine ⟨7701642224801471912058413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5134428149867647941372275 7701642224801471912058413)
              ·
                refine ⟨2888115834300551967021905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7701642224801471912058413 2888115834300551967021905)
                ·
                  refine ⟨2166086875725413975266429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2888115834300551967021905 2166086875725413975266429)
                  ·
                    refine ⟨812282578397030240724911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2166086875725413975266429 812282578397030240724911)
                    ·
                      rfl

theorem cell22_2372872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_2372872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372872 prefixEnd_2372872 := by exact prefixLift 2372872
  have htrace : WordTrace (prefixWord ++ tailWord_2372872) baseStart_2372872 baseEnd_2372872 := by
    simpa [prefixWord, tailWord_2372872, baseEnd_2372872] using wordTrace_append hprefix tailTrace_2372872
  have hstable : (prefixWord ++ tailWord_2372872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372872).length < 2 ^ (prefixWord ++ tailWord_2372872).sum := by decide
  have hdescent : baseEnd_2372872 < baseStart_2372872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372928 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 2, 5]
def baseStart_2372928 : Nat := 118140960795 + 2372928 * 2 ^ 59
def prefixEnd_2372928 : Nat := 4983230072969 + 3 ^ 40 * 2372928 * 2
def baseEnd_2372928 : Nat := 812301748341464761324739

theorem tailTrace_2372928 : CollatzResearch.WordTrace tailWord_2372928 prefixEnd_2372928 812301748341464761324739 := by
  unfold tailWord_2372928
  simp only [CollatzResearch.WordTrace]
  refine ⟨43273897173647297341403719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57698529564863063121871625 43273897173647297341403719)
  ·
    refine ⟨64910845760470946012105579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43273897173647297341403719 64910845760470946012105579)
    ·
      refine ⟨97366268640706419018158369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64910845760470946012105579 97366268640706419018158369)
      ·
        refine ⟨73024701480529814263618777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97366268640706419018158369 73024701480529814263618777)
        ·
          refine ⟨54768526110397360697714083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73024701480529814263618777 54768526110397360697714083)
          ·
            refine ⟨82152789165596041046571125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54768526110397360697714083 82152789165596041046571125)
            ·
              refine ⟨7701823984274628848116043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82152789165596041046571125 7701823984274628848116043)
              ·
                refine ⟨11552735976411943272174065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7701823984274628848116043 11552735976411943272174065)
                ·
                  refine ⟨8664551982308957454130549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11552735976411943272174065 8664551982308957454130549)
                  ·
                    refine ⟨812301748341464761324739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8664551982308957454130549 812301748341464761324739)
                    ·
                      rfl

theorem cell22_2372928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 2, 5].length) (baseStart_2372928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372928 prefixEnd_2372928 := by exact prefixLift 2372928
  have htrace : WordTrace (prefixWord ++ tailWord_2372928) baseStart_2372928 baseEnd_2372928 := by
    simpa [prefixWord, tailWord_2372928, baseEnd_2372928] using wordTrace_append hprefix tailTrace_2372928
  have hstable : (prefixWord ++ tailWord_2372928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372928).length < 2 ^ (prefixWord ++ tailWord_2372928).sum := by decide
  have hdescent : baseEnd_2372928 < baseStart_2372928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372975 : List Nat := [1, 1, 2, 1, 3, 1, 3, 6, 4]
def baseStart_2372975 : Nat := 118140960795 + 2372975 * 2 ^ 59
def prefixEnd_2372975 : Nat := 4983230072969 + 3 ^ 40 * 2372975 * 2
def baseEnd_2372975 : Nat := 270772612467324101799865

theorem tailTrace_2372975 : CollatzResearch.WordTrace tailWord_2372975 prefixEnd_2372975 270772612467324101799865 := by
  unfold tailWord_2372975
  simp only [CollatzResearch.WordTrace]
  refine ⟨86549508578124321709768379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57699672385416214473178919 86549508578124321709768379)
  ·
    refine ⟨129824262867186482564652569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86549508578124321709768379 129824262867186482564652569)
    ·
      refine ⟨97368197150389861923489427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129824262867186482564652569 97368197150389861923489427)
      ·
        refine ⟨146052295725584792885234141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97368197150389861923489427 146052295725584792885234141)
        ·
          refine ⟨54769610897094297331962803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146052295725584792885234141 54769610897094297331962803)
          ·
            refine ⟨82154416345641445997944205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54769610897094297331962803 82154416345641445997944205)
            ·
              refine ⟨30807906129615542249229077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82154416345641445997944205 30807906129615542249229077)
              ·
                refine ⟨1444120599825728542932613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30807906129615542249229077 1444120599825728542932613)
                ·
                  refine ⟨270772612467324101799865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1444120599825728542932613 270772612467324101799865)
                  ·
                    rfl

theorem cell22_2372975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 4].length) (baseStart_2372975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372975 prefixEnd_2372975 := by exact prefixLift 2372975
  have htrace : WordTrace (prefixWord ++ tailWord_2372975) baseStart_2372975 baseEnd_2372975 := by
    simpa [prefixWord, tailWord_2372975, baseEnd_2372975] using wordTrace_append hprefix tailTrace_2372975
  have hstable : (prefixWord ++ tailWord_2372975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372975).length < 2 ^ (prefixWord ++ tailWord_2372975).sum := by decide
  have hdescent : baseEnd_2372975 < baseStart_2372975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372988 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 3, 6]
def baseStart_2372988 : Nat := 118140960795 + 2372988 * 2 ^ 59
def prefixEnd_2372988 : Nat := 4983230072969 + 3 ^ 40 * 2372988 * 2
def baseEnd_2372988 : Nat := 812322287567644604824555

theorem tailTrace_2372988 : CollatzResearch.WordTrace tailWord_2372988 prefixEnd_2372988 812322287567644604824555 := by
  unfold tailWord_2372988
  simp only [CollatzResearch.WordTrace]
  refine ⟨43274991363538612464995809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57699988484718149953327745 43274991363538612464995809)
  ·
    refine ⟨32456243522653959348746857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43274991363538612464995809 32456243522653959348746857)
    ·
      refine ⟨24342182641990469511560143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32456243522653959348746857 24342182641990469511560143)
      ·
        refine ⟨36513273962985704267340215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24342182641990469511560143 36513273962985704267340215)
        ·
          refine ⟨54769910944478556401010323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36513273962985704267340215 54769910944478556401010323)
          ·
            refine ⟨82154866416717834601515485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54769910944478556401010323 82154866416717834601515485)
            ·
              refine ⟨30808074906269187975568307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82154866416717834601515485 30808074906269187975568307)
              ·
                refine ⟨46212112359403781963352461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30808074906269187975568307 46212112359403781963352461)
                ·
                  refine ⟨17329542134776418236257173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46212112359403781963352461 17329542134776418236257173)
                  ·
                    refine ⟨812322287567644604824555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17329542134776418236257173 812322287567644604824555)
                    ·
                      rfl

theorem cell22_2372988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_2372988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372988 prefixEnd_2372988 := by exact prefixLift 2372988
  have htrace : WordTrace (prefixWord ++ tailWord_2372988) baseStart_2372988 baseEnd_2372988 := by
    simpa [prefixWord, tailWord_2372988, baseEnd_2372988] using wordTrace_append hprefix tailTrace_2372988
  have hstable : (prefixWord ++ tailWord_2372988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372988).length < 2 ^ (prefixWord ++ tailWord_2372988).sum := by decide
  have hdescent : baseEnd_2372988 < baseStart_2372988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2372994 : List Nat := [3, 4, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_2372994 : Nat := 118140960795 + 2372994 * 2 ^ 59
def prefixEnd_2372994 : Nat := 4983230072969 + 3 ^ 40 * 2372994 * 2
def baseEnd_2372994 : Nat := 812324341490262589174537

theorem tailTrace_2372994 : CollatzResearch.WordTrace tailWord_2372994 prefixEnd_2372994 812324341490262589174537 := by
  unfold tailWord_2372994
  simp only [CollatzResearch.WordTrace]
  refine ⟨21637550391263871988677509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57700134376703658636473357 21637550391263871988677509)
  ·
    refine ⟨4057040698361975997877033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21637550391263871988677509 4057040698361975997877033)
    ·
      refine ⟨3042780523771481998407775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4057040698361975997877033 3042780523771481998407775)
      ·
        refine ⟨4564170785657222997611663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3042780523771481998407775 4564170785657222997611663)
        ·
          refine ⟨6846256178485834496417495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4564170785657222997611663 6846256178485834496417495)
          ·
            refine ⟨10269384267728751744626243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6846256178485834496417495 10269384267728751744626243)
            ·
              refine ⟨15404076401593127616939365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10269384267728751744626243 15404076401593127616939365)
              ·
                refine ⟨2888264325298711428176131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15404076401593127616939365 2888264325298711428176131)
                ·
                  refine ⟨4332396487948067142264197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2888264325298711428176131 4332396487948067142264197)
                  ·
                    refine ⟨812324341490262589174537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4332396487948067142264197 812324341490262589174537)
                    ·
                      rfl

theorem cell22_2372994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_2372994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2372994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2372994 prefixEnd_2372994 := by exact prefixLift 2372994
  have htrace : WordTrace (prefixWord ++ tailWord_2372994) baseStart_2372994 baseEnd_2372994 := by
    simpa [prefixWord, tailWord_2372994, baseEnd_2372994] using wordTrace_append hprefix tailTrace_2372994
  have hstable : (prefixWord ++ tailWord_2372994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2372994).length < 2 ^ (prefixWord ++ tailWord_2372994).sum := by decide
  have hdescent : baseEnd_2372994 < baseStart_2372994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2372994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373003 : List Nat := [1, 1, 1, 1, 4, 3, 3, 8]
def baseStart_2373003 : Nat := 118140960795 + 2373003 * 2 ^ 59
def prefixEnd_2373003 : Nat := 4983230072969 + 3 ^ 40 * 2373003 * 2
def baseEnd_2373003 : Nat := 90258602486021062855501

theorem tailTrace_2373003 : CollatzResearch.WordTrace tailWord_2373003 prefixEnd_2373003 90258602486021062855501 := by
  unfold tailWord_2373003
  simp only [CollatzResearch.WordTrace]
  refine ⟨86550529822022882491787663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57700353214681921661191775 86550529822022882491787663)
  ·
    refine ⟨129825794733034323737681495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86550529822022882491787663 129825794733034323737681495)
    ·
      refine ⟨194738692099551485606522243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129825794733034323737681495 194738692099551485606522243)
      ·
        refine ⟨292108038149327228409783365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194738692099551485606522243 292108038149327228409783365)
        ·
          refine ⟨54770257152998855326834381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 292108038149327228409783365 54770257152998855326834381)
          ·
            refine ⟨20538846432374570747562893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54770257152998855326834381 20538846432374570747562893)
            ·
              refine ⟨7702067412140464030336085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20538846432374570747562893 7702067412140464030336085)
              ·
                refine ⟨90258602486021062855501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7702067412140464030336085 90258602486021062855501)
                ·
                  rfl

theorem cell22_2373003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 8].length) (baseStart_2373003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373003 prefixEnd_2373003 := by exact prefixLift 2373003
  have htrace : WordTrace (prefixWord ++ tailWord_2373003) baseStart_2373003 baseEnd_2373003 := by
    simpa [prefixWord, tailWord_2373003, baseEnd_2373003] using wordTrace_append hprefix tailTrace_2373003
  have hstable : (prefixWord ++ tailWord_2373003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373003).length < 2 ^ (prefixWord ++ tailWord_2373003).sum := by decide
  have hdescent : baseEnd_2373003 < baseStart_2373003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373037 : List Nat := [1, 5, 2, 2, 1, 2, 2, 7]
def baseStart_2373037 : Nat := 118140960795 + 2373037 * 2 ^ 59
def prefixEnd_2373037 : Nat := 4983230072969 + 3 ^ 40 * 2373037 * 2
def baseEnd_2373037 : Nat := 90259895696558312261045

theorem tailTrace_2373037 : CollatzResearch.WordTrace tailWord_2373037 prefixEnd_2373037 90259895696558312261045 := by
  unfold tailWord_2373037
  simp only [CollatzResearch.WordTrace]
  refine ⟨86551769903899706298525365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57701179935933137532350243 86551769903899706298525365)
  ·
    refine ⟨8114228428490597465486753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86551769903899706298525365 8114228428490597465486753)
    ·
      refine ⟨6085671321367948099115065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8114228428490597465486753 6085671321367948099115065)
      ·
        refine ⟨4564253491025961074336299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6085671321367948099115065 4564253491025961074336299)
        ·
          refine ⟨6846380236538941611504449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4564253491025961074336299 6846380236538941611504449)
          ·
            refine ⟨5134785177404206208628337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6846380236538941611504449 5134785177404206208628337)
            ·
              refine ⟨3851088883053154656471253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5134785177404206208628337 3851088883053154656471253)
              ·
                refine ⟨90259895696558312261045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3851088883053154656471253 90259895696558312261045)
                ·
                  rfl

theorem cell22_2373037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 7].length) (baseStart_2373037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373037 prefixEnd_2373037 := by exact prefixLift 2373037
  have htrace : WordTrace (prefixWord ++ tailWord_2373037) baseStart_2373037 baseEnd_2373037 := by
    simpa [prefixWord, tailWord_2373037, baseEnd_2373037] using wordTrace_append hprefix tailTrace_2373037
  have hstable : (prefixWord ++ tailWord_2373037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373037).length < 2 ^ (prefixWord ++ tailWord_2373037).sum := by decide
  have hdescent : baseEnd_2373037 < baseStart_2373037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373058 : List Nat := [3, 5, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2373058 : Nat := 118140960795 + 2373058 * 2 ^ 59
def prefixEnd_2373058 : Nat := 4983230072969 + 3 ^ 40 * 2373058 * 2
def baseEnd_2373058 : Nat := 812346249998187755574341

theorem tailTrace_2373058 : CollatzResearch.WordTrace tailWord_2373058 prefixEnd_2373058 812346249998187755574341 := by
  unfold tailWord_2373058
  simp only [CollatzResearch.WordTrace]
  refine ⟨21638133959205906721259957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57701690557882417923359885 21638133959205906721259957)
  ·
    refine ⟨2028575058675553755118121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21638133959205906721259957 2028575058675553755118121)
    ·
      refine ⟨1521431294006665316338591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2028575058675553755118121 1521431294006665316338591)
      ·
        refine ⟨2282146941009997974507887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1521431294006665316338591 2282146941009997974507887)
        ·
          refine ⟨3423220411514996961761831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2282146941009997974507887 3423220411514996961761831)
          ·
            refine ⟨5134830617272495442642747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3423220411514996961761831 5134830617272495442642747)
            ·
              refine ⟨7702245925908743163964121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5134830617272495442642747 7702245925908743163964121)
              ·
                refine ⟨5776684444431557372973091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7702245925908743163964121 5776684444431557372973091)
                ·
                  refine ⟨8665026666647336059459637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5776684444431557372973091 8665026666647336059459637)
                  ·
                    refine ⟨812346249998187755574341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8665026666647336059459637 812346249998187755574341)
                    ·
                      rfl

theorem cell22_2373058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2373058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373058 prefixEnd_2373058 := by exact prefixLift 2373058
  have htrace : WordTrace (prefixWord ++ tailWord_2373058) baseStart_2373058 baseEnd_2373058 := by
    simpa [prefixWord, tailWord_2373058, baseEnd_2373058] using wordTrace_append hprefix tailTrace_2373058
  have hstable : (prefixWord ++ tailWord_2373058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373058).length < 2 ^ (prefixWord ++ tailWord_2373058).sum := by decide
  have hdescent : baseEnd_2373058 < baseStart_2373058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373082 : List Nat := [3, 1, 1, 2, 3, 3, 2, 2, 5]
def baseStart_2373082 : Nat := 118140960795 + 2373082 * 2 ^ 59
def prefixEnd_2373082 : Nat := 4983230072969 + 3 ^ 40 * 2373082 * 2
def baseEnd_2373082 : Nat := 270784821896219897658089

theorem tailTrace_2373082 : CollatzResearch.WordTrace tailWord_2373082 prefixEnd_2373082 270784821896219897658089 := by
  unfold tailWord_2373082
  simp only [CollatzResearch.WordTrace]
  refine ⟨21638352797184169745978375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57702274125824452655942333 21638352797184169745978375)
  ·
    refine ⟨32457529195776254618967563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21638352797184169745978375 32457529195776254618967563)
    ·
      refine ⟨48686293793664381928451345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32457529195776254618967563 48686293793664381928451345)
      ·
        refine ⟨36514720345248286446338509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48686293793664381928451345 36514720345248286446338509)
        ·
          refine ⟨13693020129468107417376941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36514720345248286446338509 13693020129468107417376941)
          ·
            refine ⟨5134882548550540281516353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13693020129468107417376941 5134882548550540281516353)
            ·
              refine ⟨3851161911412905211137265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5134882548550540281516353 3851161911412905211137265)
              ·
                refine ⟨2888371433559678908352949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3851161911412905211137265 2888371433559678908352949)
                ·
                  refine ⟨270784821896219897658089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2888371433559678908352949 270784821896219897658089)
                  ·
                    rfl

theorem cell22_2373082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_2373082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373082 prefixEnd_2373082 := by exact prefixLift 2373082
  have htrace : WordTrace (prefixWord ++ tailWord_2373082) baseStart_2373082 baseEnd_2373082 := by
    simpa [prefixWord, tailWord_2373082, baseEnd_2373082] using wordTrace_append hprefix tailTrace_2373082
  have hstable : (prefixWord ++ tailWord_2373082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373082).length < 2 ^ (prefixWord ++ tailWord_2373082).sum := by decide
  have hdescent : baseEnd_2373082 < baseStart_2373082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373133 : List Nat := [1, 7, 1, 1, 2, 2, 1, 2, 5]
def baseStart_2373133 : Nat := 118140960795 + 2373133 * 2 ^ 59
def prefixEnd_2373133 : Nat := 4983230072969 + 3 ^ 40 * 2373133 * 2
def baseEnd_2373133 : Nat := 270790641343637519983037

theorem tailTrace_2373133 : CollatzResearch.WordTrace tailWord_2373133 prefixEnd_2373133 270790641343637519983037 := by
  unfold tailWord_2373133
  simp only [CollatzResearch.WordTrace]
  refine ⟨86555271311551914694020053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57703514207701276462680035 86555271311551914694020053)
  ·
    refine ⟨2028639171364498000641095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 86555271311551914694020053 2028639171364498000641095)
    ·
      refine ⟨3042958757046747000961643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2028639171364498000641095 3042958757046747000961643)
      ·
        refine ⟨4564438135570120501442465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3042958757046747000961643 4564438135570120501442465)
        ·
          refine ⟨3423328601677590376081849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4564438135570120501442465 3423328601677590376081849)
          ·
            refine ⟨2567496451258192782061387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3423328601677590376081849 2567496451258192782061387)
            ·
              refine ⟨3851244676887289173092081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2567496451258192782061387 3851244676887289173092081)
              ·
                refine ⟨2888433507665466879819061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3851244676887289173092081 2888433507665466879819061)
                ·
                  refine ⟨270790641343637519983037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2888433507665466879819061 270790641343637519983037)
                  ·
                    rfl

theorem cell22_2373133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_2373133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373133 prefixEnd_2373133 := by exact prefixLift 2373133
  have htrace : WordTrace (prefixWord ++ tailWord_2373133) baseStart_2373133 baseEnd_2373133 := by
    simpa [prefixWord, tailWord_2373133, baseEnd_2373133] using wordTrace_append hprefix tailTrace_2373133
  have hstable : (prefixWord ++ tailWord_2373133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373133).length < 2 ^ (prefixWord ++ tailWord_2373133).sum := by decide
  have hdescent : baseEnd_2373133 < baseStart_2373133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373150 : List Nat := [4, 3, 3, 1, 1, 1, 3, 1, 5]
def baseStart_2373150 : Nat := 118140960795 + 2373150 * 2 ^ 59
def prefixEnd_2373150 : Nat := 4983230072969 + 3 ^ 40 * 2373150 * 2
def baseEnd_2373150 : Nat := 270792581159443394091353

theorem tailTrace_2373150 : CollatzResearch.WordTrace tailWord_2373150 prefixEnd_2373150 270792581159443394091353 := by
  unfold tailWord_2373150
  simp only [CollatzResearch.WordTrace]
  refine ⟨10819486419061290824673613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57703927568326884398259269 10819486419061290824673613)
  ·
    refine ⟨4057307407147984059252605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10819486419061290824673613 4057307407147984059252605)
    ·
      refine ⟨1521490277680494022219727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4057307407147984059252605 1521490277680494022219727)
      ·
        refine ⟨2282235416520741033329591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1521490277680494022219727 2282235416520741033329591)
        ·
          refine ⟨3423353124781111549994387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2282235416520741033329591 3423353124781111549994387)
          ·
            refine ⟨5135029687171667324991581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3423353124781111549994387 5135029687171667324991581)
            ·
              refine ⟨1925636132689375246871843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5135029687171667324991581 1925636132689375246871843)
              ·
                refine ⟨2888454199034062870307765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1925636132689375246871843 2888454199034062870307765)
                ·
                  refine ⟨270792581159443394091353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2888454199034062870307765 270792581159443394091353)
                  ·
                    rfl

theorem cell22_2373150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_2373150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373150 prefixEnd_2373150 := by exact prefixLift 2373150
  have htrace : WordTrace (prefixWord ++ tailWord_2373150) baseStart_2373150 baseEnd_2373150 := by
    simpa [prefixWord, tailWord_2373150, baseEnd_2373150] using wordTrace_append hprefix tailTrace_2373150
  have hstable : (prefixWord ++ tailWord_2373150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373150).length < 2 ^ (prefixWord ++ tailWord_2373150).sum := by decide
  have hdescent : baseEnd_2373150 < baseStart_2373150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373170 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_2373170 : Nat := 118140960795 + 2373170 * 2 ^ 59
def prefixEnd_2373170 : Nat := 4983230072969 + 3 ^ 40 * 2373170 * 2
def baseEnd_2373170 : Nat := 812384589887056796773997

theorem tailTrace_2373170 : CollatzResearch.WordTrace tailWord_2373170 prefixEnd_2373170 812384589887056796773997 := by
  unfold tailWord_2373170
  simp only [CollatzResearch.WordTrace]
  refine ⟨21639155203104467503279241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57704413874945246675411309 21639155203104467503279241)
  ·
    refine ⟨16229366402328350627459431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21639155203104467503279241 16229366402328350627459431)
    ·
      refine ⟨24344049603492525941189147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16229366402328350627459431 24344049603492525941189147)
      ·
        refine ⟨36516074405238788911783721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24344049603492525941189147 36516074405238788911783721)
        ·
          refine ⟨27387055803929091683837791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36516074405238788911783721 27387055803929091683837791)
          ·
            refine ⟨41080583705893637525756687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27387055803929091683837791 41080583705893637525756687)
            ·
              refine ⟨61620875558840456288635031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41080583705893637525756687 61620875558840456288635031)
              ·
                refine ⟨92431313338260684432952547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61620875558840456288635031 92431313338260684432952547)
                ·
                  refine ⟨138646970007391026649428821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92431313338260684432952547 138646970007391026649428821)
                  ·
                    refine ⟨812384589887056796773997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 138646970007391026649428821 812384589887056796773997)
                    ·
                      rfl

theorem cell22_2373170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_2373170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373170 prefixEnd_2373170 := by exact prefixLift 2373170
  have htrace : WordTrace (prefixWord ++ tailWord_2373170) baseStart_2373170 baseEnd_2373170 := by
    simpa [prefixWord, tailWord_2373170, baseEnd_2373170] using wordTrace_append hprefix tailTrace_2373170
  have hstable : (prefixWord ++ tailWord_2373170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373170).length < 2 ^ (prefixWord ++ tailWord_2373170).sum := by decide
  have hdescent : baseEnd_2373170 < baseStart_2373170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373200 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 7]
def baseStart_2373200 : Nat := 118140960795 + 2373200 * 2 ^ 59
def prefixEnd_2373200 : Nat := 4983230072969 + 3 ^ 40 * 2373200 * 2
def baseEnd_2373200 : Nat := 270798286500048906174635

theorem tailTrace_2373200 : CollatzResearch.WordTrace tailWord_2373200 prefixEnd_2373200 270798286500048906174635 := by
  unfold tailWord_2373200
  simp only [CollatzResearch.WordTrace]
  refine ⟨43278857501154592568354527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57705143334872790091139369 43278857501154592568354527)
  ·
    refine ⟨64918286251731888852531791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43278857501154592568354527 64918286251731888852531791)
    ·
      refine ⟨97377429377597833278797687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64918286251731888852531791 97377429377597833278797687)
      ·
        refine ⟨146066144066396749918196531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97377429377597833278797687 146066144066396749918196531)
        ·
          refine ⟨219099216099595124877294797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146066144066396749918196531 219099216099595124877294797)
          ·
            refine ⟨82162206037348171828985549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219099216099595124877294797 82162206037348171828985549)
            ·
              refine ⟨30810827264005564435869581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82162206037348171828985549 30810827264005564435869581)
              ·
                refine ⟨11554060224002086663451093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30810827264005564435869581 11554060224002086663451093)
                ·
                  refine ⟨270798286500048906174635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11554060224002086663451093 270798286500048906174635)
                  ·
                    rfl

theorem cell22_2373200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 7].length) (baseStart_2373200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373200 prefixEnd_2373200 := by exact prefixLift 2373200
  have htrace : WordTrace (prefixWord ++ tailWord_2373200) baseStart_2373200 baseEnd_2373200 := by
    simpa [prefixWord, tailWord_2373200, baseEnd_2373200] using wordTrace_append hprefix tailTrace_2373200
  have hstable : (prefixWord ++ tailWord_2373200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373200).length < 2 ^ (prefixWord ++ tailWord_2373200).sum := by decide
  have hdescent : baseEnd_2373200 < baseStart_2373200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373217 : List Nat := [1, 2, 3, 1, 1, 3, 3, 3, 5]
def baseStart_2373217 : Nat := 118140960795 + 2373217 * 2 ^ 59
def prefixEnd_2373217 : Nat := 4983230072969 + 3 ^ 40 * 2373217 * 2
def baseEnd_2373217 : Nat := 270800226315854780282951

theorem tailTrace_2373217 : CollatzResearch.WordTrace tailWord_2373217 prefixEnd_2373217 270800226315854780282951 := by
  unfold tailWord_2373217
  simp only [CollatzResearch.WordTrace]
  refine ⟨86558335043247597040077905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57705556695498398026718603 86558335043247597040077905)
  ·
    refine ⟨64918751282435697780058429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86558335043247597040077905 64918751282435697780058429)
    ·
      refine ⟨24344531730913386667521911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64918751282435697780058429 24344531730913386667521911)
      ·
        refine ⟨36516797596370080001282867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24344531730913386667521911 36516797596370080001282867)
        ·
          refine ⟨54775196394555120001924301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36516797596370080001282867 54775196394555120001924301)
          ·
            refine ⟨20540698647958170000721613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54775196394555120001924301 20540698647958170000721613)
            ·
              refine ⟨7702761992984313750270605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20540698647958170000721613 7702761992984313750270605)
              ·
                refine ⟨2888535747369117656351477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7702761992984313750270605 2888535747369117656351477)
                ·
                  refine ⟨270800226315854780282951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2888535747369117656351477 270800226315854780282951)
                  ·
                    rfl

theorem cell22_2373217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 5].length) (baseStart_2373217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373217 prefixEnd_2373217 := by exact prefixLift 2373217
  have htrace : WordTrace (prefixWord ++ tailWord_2373217) baseStart_2373217 baseEnd_2373217 := by
    simpa [prefixWord, tailWord_2373217, baseEnd_2373217] using wordTrace_append hprefix tailTrace_2373217
  have hstable : (prefixWord ++ tailWord_2373217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373217).length < 2 ^ (prefixWord ++ tailWord_2373217).sum := by decide
  have hdescent : baseEnd_2373217 < baseStart_2373217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373341 : List Nat := [1, 4, 3, 3, 1, 1, 1, 8]
def baseStart_2373341 : Nat := 118140960795 + 2373341 * 2 ^ 59
def prefixEnd_2373341 : Nat := 4983230072969 + 3 ^ 40 * 2373341 * 2
def baseEnd_2373341 : Nat := 90271458520185483416497

theorem tailTrace_2373341 : CollatzResearch.WordTrace tailWord_2373341 prefixEnd_2373341 90271458520185483416497 := by
  unfold tailWord_2373341
  simp only [CollatzResearch.WordTrace]
  refine ⟨86562857694798366217591877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57708571796532244145061251 86562857694798366217591877)
  ·
    refine ⟨16230535817774693665798477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86562857694798366217591877 16230535817774693665798477)
    ·
      refine ⟨6086450931665510124674429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16230535817774693665798477 6086450931665510124674429)
      ·
        refine ⟨2282419099374566296752911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6086450931665510124674429 2282419099374566296752911)
        ·
          refine ⟨3423628649061849445129367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2282419099374566296752911 3423628649061849445129367)
          ·
            refine ⟨5135442973592774167694051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3423628649061849445129367 5135442973592774167694051)
            ·
              refine ⟨7703164460389161251541077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5135442973592774167694051 7703164460389161251541077)
              ·
                refine ⟨90271458520185483416497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7703164460389161251541077 90271458520185483416497)
                ·
                  rfl

theorem cell22_2373341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 8].length) (baseStart_2373341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373341 prefixEnd_2373341 := by exact prefixLift 2373341
  have htrace : WordTrace (prefixWord ++ tailWord_2373341) baseStart_2373341 baseEnd_2373341 := by
    simpa [prefixWord, tailWord_2373341, baseEnd_2373341] using wordTrace_append hprefix tailTrace_2373341
  have hstable : (prefixWord ++ tailWord_2373341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373341).length < 2 ^ (prefixWord ++ tailWord_2373341).sum := by decide
  have hdescent : baseEnd_2373341 < baseStart_2373341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373367 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 4, 5]
def baseStart_2373367 : Nat := 118140960795 + 2373367 * 2 ^ 59
def prefixEnd_2373367 : Nat := 4983230072969 + 3 ^ 40 * 2373367 * 2
def baseEnd_2373367 : Nat := 812452027013013949598393

theorem tailTrace_2373367 : CollatzResearch.WordTrace tailWord_2373367 prefixEnd_2373367 812452027013013949598393 := by
  unfold tailWord_2373367
  simp only [CollatzResearch.WordTrace]
  refine ⟨86563805992704172658038355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57709203995136115105358903 86563805992704172658038355)
  ·
    refine ⟨129845708989056258987057533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86563805992704172658038355 129845708989056258987057533)
    ·
      refine ⟨48692140870896097120146575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129845708989056258987057533 48692140870896097120146575)
      ·
        refine ⟨73038211306344145680219863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48692140870896097120146575 73038211306344145680219863)
        ·
          refine ⟨109557316959516218520329795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73038211306344145680219863 109557316959516218520329795)
          ·
            refine ⟨164335975439274327780494693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109557316959516218520329795 164335975439274327780494693)
            ·
              refine ⟨30812995394863936458842755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 164335975439274327780494693 30812995394863936458842755)
              ·
                refine ⟨46219493092295904688264133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30812995394863936458842755 46219493092295904688264133)
                ·
                  refine ⟨8666154954805482129049525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46219493092295904688264133 8666154954805482129049525)
                  ·
                    refine ⟨812452027013013949598393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8666154954805482129049525 812452027013013949598393)
                    ·
                      rfl

theorem cell22_2373367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_2373367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373367 prefixEnd_2373367 := by exact prefixLift 2373367
  have htrace : WordTrace (prefixWord ++ tailWord_2373367) baseStart_2373367 baseEnd_2373367 := by
    simpa [prefixWord, tailWord_2373367, baseEnd_2373367] using wordTrace_append hprefix tailTrace_2373367
  have hstable : (prefixWord ++ tailWord_2373367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373367).length < 2 ^ (prefixWord ++ tailWord_2373367).sum := by decide
  have hdescent : baseEnd_2373367 < baseStart_2373367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373386 : List Nat := [3, 1, 2, 2, 1, 3, 4, 1, 5]
def baseStart_2373386 : Nat := 118140960795 + 2373386 * 2 ^ 59
def prefixEnd_2373386 : Nat := 4983230072969 + 3 ^ 40 * 2373386 * 2
def baseEnd_2373386 : Nat := 270819510367101411124445

theorem tailTrace_2373386 : CollatzResearch.WordTrace tailWord_2373386 prefixEnd_2373386 270819510367101411124445 := by
  unfold tailWord_2373386
  simp only [CollatzResearch.WordTrace]
  refine ⟨21641124744908834725745003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57709665986423559268653341 21641124744908834725745003)
  ·
    refine ⟨32461687117363252088617505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21641124744908834725745003 32461687117363252088617505)
    ·
      refine ⟨24346265338022439066463129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32461687117363252088617505 24346265338022439066463129)
      ·
        refine ⟨18259699003516829299847347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24346265338022439066463129 18259699003516829299847347)
        ·
          refine ⟨27389548505275243949771021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18259699003516829299847347 27389548505275243949771021)
          ·
            refine ⟨10271080689478216481164133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27389548505275243949771021 10271080689478216481164133)
            ·
              refine ⟨1925827629277165590218275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10271080689478216481164133 1925827629277165590218275)
              ·
                refine ⟨2888741443915748385327413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1925827629277165590218275 2888741443915748385327413)
                ·
                  refine ⟨270819510367101411124445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2888741443915748385327413 270819510367101411124445)
                  ·
                    rfl

theorem cell22_2373386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 5].length) (baseStart_2373386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373386 prefixEnd_2373386 := by exact prefixLift 2373386
  have htrace : WordTrace (prefixWord ++ tailWord_2373386) baseStart_2373386 baseEnd_2373386 := by
    simpa [prefixWord, tailWord_2373386, baseEnd_2373386] using wordTrace_append hprefix tailTrace_2373386
  have hstable : (prefixWord ++ tailWord_2373386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373386).length < 2 ^ (prefixWord ++ tailWord_2373386).sum := by decide
  have hdescent : baseEnd_2373386 < baseStart_2373386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373461 : List Nat := [1, 3, 2, 2, 2, 2, 3, 1, 2, 4]
def baseStart_2373461 : Nat := 118140960795 + 2373461 * 2 ^ 59
def prefixEnd_2373461 : Nat := 4983230072969 + 3 ^ 40 * 2373461 * 2
def baseEnd_2373461 : Nat := 812484205134029037748105

theorem tailTrace_2373461 : CollatzResearch.WordTrace tailWord_2373461 prefixEnd_2373461 812484205134029037748105 := by
  unfold tailWord_2373461
  simp only [CollatzResearch.WordTrace]
  refine ⟨86567234454363626711960237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57711489636242417807973491 86567234454363626711960237)
  ·
    refine ⟨32462712920386360016985089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86567234454363626711960237 32462712920386360016985089)
    ·
      refine ⟨24347034690289770012738817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32462712920386360016985089 24347034690289770012738817)
      ·
        refine ⟨18260276017717327509554113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24347034690289770012738817 18260276017717327509554113)
        ·
          refine ⟨13695207013287995632165585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18260276017717327509554113 13695207013287995632165585)
          ·
            refine ⟨10271405259965996724124189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13695207013287995632165585 10271405259965996724124189)
            ·
              refine ⟨3851776972487248771546571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10271405259965996724124189 3851776972487248771546571)
              ·
                refine ⟨5777665458730873157319857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3851776972487248771546571 5777665458730873157319857)
                ·
                  refine ⟨4333249094048154867989893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5777665458730873157319857 4333249094048154867989893)
                  ·
                    refine ⟨812484205134029037748105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4333249094048154867989893 812484205134029037748105)
                    ·
                      rfl

theorem cell22_2373461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_2373461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373461 prefixEnd_2373461 := by exact prefixLift 2373461
  have htrace : WordTrace (prefixWord ++ tailWord_2373461) baseStart_2373461 baseEnd_2373461 := by
    simpa [prefixWord, tailWord_2373461, baseEnd_2373461] using wordTrace_append hprefix tailTrace_2373461
  have hstable : (prefixWord ++ tailWord_2373461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373461).length < 2 ^ (prefixWord ++ tailWord_2373461).sum := by decide
  have hdescent : baseEnd_2373461 < baseStart_2373461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373594 : List Nat := [3, 1, 1, 2, 15]
def baseStart_2373594 : Nat := 118140960795 + 2373594 * 2 ^ 59
def prefixEnd_2373594 : Nat := 4983230072969 + 3 ^ 40 * 2373594 * 2
def baseEnd_2373594 : Nat := 3343743760296547424579

theorem tailTrace_2373594 : CollatzResearch.WordTrace tailWord_2373594 prefixEnd_2373594 3343743760296547424579 := by
  unfold tailWord_2373594
  simp only [CollatzResearch.WordTrace]
  refine ⟨21643021340720447606637959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57714723575254526951034557 21643021340720447606637959)
  ·
    refine ⟨32464532011080671409956939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21643021340720447606637959 32464532011080671409956939)
    ·
      refine ⟨48696798016621007114935409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32464532011080671409956939 48696798016621007114935409)
      ·
        refine ⟨36522598512465755336201557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48696798016621007114935409 36522598512465755336201557)
        ·
          refine ⟨3343743760296547424579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 36522598512465755336201557 3343743760296547424579)
          ·
            rfl

theorem cell22_2373594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 15].length) (baseStart_2373594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373594 prefixEnd_2373594 := by exact prefixLift 2373594
  have htrace : WordTrace (prefixWord ++ tailWord_2373594) baseStart_2373594 baseEnd_2373594 := by
    simpa [prefixWord, tailWord_2373594, baseEnd_2373594] using wordTrace_append hprefix tailTrace_2373594
  have hstable : (prefixWord ++ tailWord_2373594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373594).length < 2 ^ (prefixWord ++ tailWord_2373594).sum := by decide
  have hdescent : baseEnd_2373594 < baseStart_2373594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373630 : List Nat := [4, 2, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_2373630 : Nat := 118140960795 + 2373630 * 2 ^ 59
def prefixEnd_2373630 : Nat := 4983230072969 + 3 ^ 40 * 2373630 * 2
def baseEnd_2373630 : Nat := 812542057287768930272587

theorem tailTrace_2373630 : CollatzResearch.WordTrace tailWord_2373630 prefixEnd_2373630 812542057287768930272587 := by
  unfold tailWord_2373630
  simp only [CollatzResearch.WordTrace]
  refine ⟨10821674798843921071857793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57715598927167579049908229 10821674798843921071857793)
  ·
    refine ⟨8116256099132940803893345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10821674798843921071857793 8116256099132940803893345)
    ·
      refine ⟨6087192074349705602920009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8116256099132940803893345 6087192074349705602920009)
      ·
        refine ⟨4565394055762279202190007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6087192074349705602920009 4565394055762279202190007)
        ·
          refine ⟨6848091083643418803285011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4565394055762279202190007 6848091083643418803285011)
          ·
            refine ⟨10272136625465128204927517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6848091083643418803285011 10272136625465128204927517)
            ·
              refine ⟨3852051234549423076847819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10272136625465128204927517 3852051234549423076847819)
              ·
                refine ⟨5778076851824134615271729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3852051234549423076847819 5778076851824134615271729)
                ·
                  refine ⟨4333557638868100961453797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5778076851824134615271729 4333557638868100961453797)
                  ·
                    refine ⟨812542057287768930272587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4333557638868100961453797 812542057287768930272587)
                    ·
                      rfl

theorem cell22_2373630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_2373630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373630 prefixEnd_2373630 := by exact prefixLift 2373630
  have htrace : WordTrace (prefixWord ++ tailWord_2373630) baseStart_2373630 baseEnd_2373630 := by
    simpa [prefixWord, tailWord_2373630, baseEnd_2373630] using wordTrace_append hprefix tailTrace_2373630
  have hstable : (prefixWord ++ tailWord_2373630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373630).length < 2 ^ (prefixWord ++ tailWord_2373630).sum := by decide
  have hdescent : baseEnd_2373630 < baseStart_2373630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373656 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 7]
def baseStart_2373656 : Nat := 118140960795 + 2373656 * 2 ^ 59
def prefixEnd_2373656 : Nat := 4983230072969 + 3 ^ 40 * 2373656 * 2
def baseEnd_2373656 : Nat := 270850319206371176374169

theorem tailTrace_2373656 : CollatzResearch.WordTrace tailWord_2373656 prefixEnd_2373656 270850319206371176374169 := by
  unfold tailWord_2373656
  simp only [CollatzResearch.WordTrace]
  refine ⟨43287173344328587507654411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57716231125771450010205881 43287173344328587507654411)
  ·
    refine ⟨64930760016492881261481617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43287173344328587507654411 64930760016492881261481617)
    ·
      refine ⟨48698070012369660946111213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64930760016492881261481617 48698070012369660946111213)
      ·
        refine ⟨18261776254638622854791705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48698070012369660946111213 18261776254638622854791705)
        ·
          refine ⟨13696332190978967141093779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18261776254638622854791705 13696332190978967141093779)
          ·
            refine ⟨20544498286468450711640669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13696332190978967141093779 20544498286468450711640669)
            ·
              refine ⟨7704186857425669016865251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20544498286468450711640669 7704186857425669016865251)
              ·
                refine ⟨11556280286138503525297877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7704186857425669016865251 11556280286138503525297877)
                ·
                  refine ⟨270850319206371176374169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11556280286138503525297877 270850319206371176374169)
                  ·
                    rfl

theorem cell22_2373656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 7].length) (baseStart_2373656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373656 prefixEnd_2373656 := by exact prefixLift 2373656
  have htrace : WordTrace (prefixWord ++ tailWord_2373656) baseStart_2373656 baseEnd_2373656 := by
    simpa [prefixWord, tailWord_2373656, baseEnd_2373656] using wordTrace_append hprefix tailTrace_2373656
  have hstable : (prefixWord ++ tailWord_2373656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373656).length < 2 ^ (prefixWord ++ tailWord_2373656).sum := by decide
  have hdescent : baseEnd_2373656 < baseStart_2373656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373660 : List Nat := [2, 2, 3, 1, 3, 2, 2, 1, 3, 3]
def baseStart_2373660 : Nat := 118140960795 + 2373660 * 2 ^ 59
def prefixEnd_2373660 : Nat := 4983230072969 + 3 ^ 40 * 2373660 * 2
def baseEnd_2373660 : Nat := 812552326900858852022495

theorem tailTrace_2373660 : CollatzResearch.WordTrace tailWord_2373660 prefixEnd_2373660 812552326900858852022495 := by
  unfold tailWord_2373660
  simp only [CollatzResearch.WordTrace]
  refine ⟨43287246290321341849227217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57716328387095122465636289 43287246290321341849227217)
  ·
    refine ⟨32465434717741006386920413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43287246290321341849227217 32465434717741006386920413)
    ·
      refine ⟨12174538019152877395095155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32465434717741006386920413 12174538019152877395095155)
      ·
        refine ⟨18261807028729316092642733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12174538019152877395095155 18261807028729316092642733)
        ·
          refine ⟨6848177635773493534741025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18261807028729316092642733 6848177635773493534741025)
          ·
            refine ⟨5136133226830120151055769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6848177635773493534741025 5136133226830120151055769)
            ·
              refine ⟨3852099920122590113291827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5136133226830120151055769 3852099920122590113291827)
              ·
                refine ⟨5778149880183885169937741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3852099920122590113291827 5778149880183885169937741)
                ·
                  refine ⟨2166806205068956938726653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5778149880183885169937741 2166806205068956938726653)
                  ·
                    refine ⟨812552326900858852022495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2166806205068956938726653 812552326900858852022495)
                    ·
                      rfl

theorem cell22_2373660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_2373660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373660 prefixEnd_2373660 := by exact prefixLift 2373660
  have htrace : WordTrace (prefixWord ++ tailWord_2373660) baseStart_2373660 baseEnd_2373660 := by
    simpa [prefixWord, tailWord_2373660, baseEnd_2373660] using wordTrace_append hprefix tailTrace_2373660
  have hstable : (prefixWord ++ tailWord_2373660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373660).length < 2 ^ (prefixWord ++ tailWord_2373660).sum := by decide
  have hdescent : baseEnd_2373660 < baseStart_2373660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373703 : List Nat := [1, 1, 4, 1, 3, 1, 1, 5, 1, 4]
def baseStart_2373703 : Nat := 118140960795 + 2373703 * 2 ^ 59
def prefixEnd_2373703 : Nat := 4983230072969 + 3 ^ 40 * 2373703 * 2
def baseEnd_2373703 : Nat := 812567046679621073197363

theorem tailTrace_2373703 : CollatzResearch.WordTrace tailWord_2373703 prefixEnd_2373703 812567046679621073197363 := by
  unfold tailWord_2373703
  simp only [CollatzResearch.WordTrace]
  refine ⟨86576060919486902042269763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57717373946324601361513175 86576060919486902042269763)
  ·
    refine ⟨129864091379230353063404645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86576060919486902042269763 129864091379230353063404645)
    ·
      refine ⟨24349517133605691199388371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129864091379230353063404645 24349517133605691199388371)
      ·
        refine ⟨36524275700408536799082557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24349517133605691199388371 36524275700408536799082557)
        ·
          refine ⟨13696603387653201299655959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36524275700408536799082557 13696603387653201299655959)
          ·
            refine ⟨20544905081479801949483939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13696603387653201299655959 20544905081479801949483939)
            ·
              refine ⟨30817357622219702924225909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20544905081479801949483939 30817357622219702924225909)
              ·
                refine ⟨2889127277083097149146179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30817357622219702924225909 2889127277083097149146179)
                ·
                  refine ⟨4333690915624645723719269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2889127277083097149146179 4333690915624645723719269)
                  ·
                    refine ⟨812567046679621073197363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4333690915624645723719269 812567046679621073197363)
                    ·
                      rfl

theorem cell22_2373703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_2373703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373703 prefixEnd_2373703 := by exact prefixLift 2373703
  have htrace : WordTrace (prefixWord ++ tailWord_2373703) baseStart_2373703 baseEnd_2373703 := by
    simpa [prefixWord, tailWord_2373703, baseEnd_2373703] using wordTrace_append hprefix tailTrace_2373703
  have hstable : (prefixWord ++ tailWord_2373703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373703).length < 2 ^ (prefixWord ++ tailWord_2373703).sum := by decide
  have hdescent : baseEnd_2373703 < baseStart_2373703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373731 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 3, 6]
def baseStart_2373731 : Nat := 118140960795 + 2373731 * 2 ^ 59
def prefixEnd_2373731 : Nat := 4983230072969 + 3 ^ 40 * 2373731 * 2
def baseEnd_2373731 : Nat := 812576631651838333497277

theorem tailTrace_2373731 : CollatzResearch.WordTrace tailWord_2373731 prefixEnd_2373731 812576631651838333497277 := by
  unfold tailWord_2373731
  simp only [CollatzResearch.WordTrace]
  refine ⟨86577082163385462824289047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57718054775590308549526031 86577082163385462824289047)
  ·
    refine ⟨129865623245078194236433571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86577082163385462824289047 129865623245078194236433571)
    ·
      refine ⟨194798434867617291354650357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129865623245078194236433571 194798434867617291354650357)
      ·
        refine ⟨18262353268839121064498471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 194798434867617291354650357 18262353268839121064498471)
        ·
          refine ⟨27393529903258681596747707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18262353268839121064498471 27393529903258681596747707)
          ·
            refine ⟨41090294854888022395121561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27393529903258681596747707 41090294854888022395121561)
            ·
              refine ⟨30817721141166016796341171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41090294854888022395121561 30817721141166016796341171)
              ·
                refine ⟨46226581711749025194511757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30817721141166016796341171 46226581711749025194511757)
                ·
                  refine ⟨17334968141905884447941909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46226581711749025194511757 17334968141905884447941909)
                  ·
                    refine ⟨812576631651838333497277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17334968141905884447941909 812576631651838333497277)
                    ·
                      rfl

theorem cell22_2373731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 6].length) (baseStart_2373731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373731 prefixEnd_2373731 := by exact prefixLift 2373731
  have htrace : WordTrace (prefixWord ++ tailWord_2373731) baseStart_2373731 baseEnd_2373731 := by
    simpa [prefixWord, tailWord_2373731, baseEnd_2373731] using wordTrace_append hprefix tailTrace_2373731
  have hstable : (prefixWord ++ tailWord_2373731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373731).length < 2 ^ (prefixWord ++ tailWord_2373731).sum := by decide
  have hdescent : baseEnd_2373731 < baseStart_2373731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373750 : List Nat := [5, 1, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_2373750 : Nat := 118140960795 + 2373750 * 2 ^ 59
def prefixEnd_2373750 : Nat := 4983230072969 + 3 ^ 40 * 2373750 * 2
def baseEnd_2373750 : Nat := 812583135740128617272219

theorem tailTrace_2373750 : CollatzResearch.WordTrace tailWord_2373750 prefixEnd_2373750 812583135740128617272219 := by
  unfold tailWord_2373750
  simp only [CollatzResearch.WordTrace]
  refine ⟨5411110946894789316826919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57718516766877752712820469 5411110946894789316826919)
  ·
    refine ⟨8116666420342183975240379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5411110946894789316826919 8116666420342183975240379)
    ·
      refine ⟨12174999630513275962860569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8116666420342183975240379 12174999630513275962860569)
      ·
        refine ⟨9131249722884956972145427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12174999630513275962860569 9131249722884956972145427)
        ·
          refine ⟨13696874584327435458218141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9131249722884956972145427 13696874584327435458218141)
          ·
            refine ⟨5136327969122788296831803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13696874584327435458218141 5136327969122788296831803)
            ·
              refine ⟨7704491953684182445247705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5136327969122788296831803 7704491953684182445247705)
              ·
                refine ⟨5778368965263136833935779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7704491953684182445247705 5778368965263136833935779)
                ·
                  refine ⟨8667553447894705250903669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5778368965263136833935779 8667553447894705250903669)
                  ·
                    refine ⟨812583135740128617272219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8667553447894705250903669 812583135740128617272219)
                    ·
                      rfl

theorem cell22_2373750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_2373750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373750 prefixEnd_2373750 := by exact prefixLift 2373750
  have htrace : WordTrace (prefixWord ++ tailWord_2373750) baseStart_2373750 baseEnd_2373750 := by
    simpa [prefixWord, tailWord_2373750, baseEnd_2373750] using wordTrace_append hprefix tailTrace_2373750
  have hstable : (prefixWord ++ tailWord_2373750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373750).length < 2 ^ (prefixWord ++ tailWord_2373750).sum := by decide
  have hdescent : baseEnd_2373750 < baseStart_2373750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373776 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 1, 8]
def baseStart_2373776 : Nat := 118140960795 + 2373776 * 2 ^ 59
def prefixEnd_2373776 : Nat := 4983230072969 + 3 ^ 40 * 2373776 * 2
def baseEnd_2373776 : Nat := 812592036071473216122139

theorem tailTrace_2373776 : CollatzResearch.WordTrace tailWord_2373776 prefixEnd_2373776 812592036071473216122139 := by
  unfold tailWord_2373776
  simp only [CollatzResearch.WordTrace]
  refine ⟨43289361724111217754838591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57719148965481623673118121 43289361724111217754838591)
  ·
    refine ⟨64934042586166826632257887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43289361724111217754838591 64934042586166826632257887)
    ·
      refine ⟨97401063879250239948386831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64934042586166826632257887 97401063879250239948386831)
      ·
        refine ⟨146101595818875359922580247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97401063879250239948386831 146101595818875359922580247)
        ·
          refine ⟨219152393728313039883870371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146101595818875359922580247 219152393728313039883870371)
          ·
            refine ⟨328728590592469559825805557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219152393728313039883870371 328728590592469559825805557)
            ·
              refine ⟨30818305368044021233669271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 328728590592469559825805557 30818305368044021233669271)
              ·
                refine ⟨46227458052066031850503907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30818305368044021233669271 46227458052066031850503907)
                ·
                  refine ⟨69341187078099047775755861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46227458052066031850503907 69341187078099047775755861)
                  ·
                    refine ⟨812592036071473216122139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69341187078099047775755861 812592036071473216122139)
                    ·
                      rfl

theorem cell22_2373776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_2373776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373776 prefixEnd_2373776 := by exact prefixLift 2373776
  have htrace : WordTrace (prefixWord ++ tailWord_2373776) baseStart_2373776 baseEnd_2373776 := by
    simpa [prefixWord, tailWord_2373776, baseEnd_2373776] using wordTrace_append hprefix tailTrace_2373776
  have hstable : (prefixWord ++ tailWord_2373776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373776).length < 2 ^ (prefixWord ++ tailWord_2373776).sum := by decide
  have hdescent : baseEnd_2373776 < baseStart_2373776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373799 : List Nat := [1, 1, 6, 2, 3, 1, 1, 1, 2, 4]
def baseStart_2373799 : Nat := 118140960795 + 2373799 * 2 ^ 59
def prefixEnd_2373799 : Nat := 4983230072969 + 3 ^ 40 * 2373799 * 2
def baseEnd_2373799 : Nat := 812599909441508822797069

theorem tailTrace_2373799 : CollatzResearch.WordTrace tailWord_2373799 prefixEnd_2373799 812599909441508822797069 := by
  unfold tailWord_2373799
  simp only [CollatzResearch.WordTrace]
  refine ⟨86579562327139110437764451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57719708218092740291842967 86579562327139110437764451)
  ·
    refine ⟨129869343490708665656646677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86579562327139110437764451 129869343490708665656646677)
    ·
      refine ⟨6087625476126968702655313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 129869343490708665656646677 6087625476126968702655313)
      ·
        refine ⟨4565719107095226526991485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6087625476126968702655313 4565719107095226526991485)
        ·
          refine ⟨1712144665160709947621807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4565719107095226526991485 1712144665160709947621807)
          ·
            refine ⟨2568216997741064921432711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1712144665160709947621807 2568216997741064921432711)
            ·
              refine ⟨3852325496611597382149067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2568216997741064921432711 3852325496611597382149067)
              ·
                refine ⟨5778488244917396073223601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3852325496611597382149067 5778488244917396073223601)
                ·
                  refine ⟨4333866183688047054917701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5778488244917396073223601 4333866183688047054917701)
                  ·
                    refine ⟨812599909441508822797069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4333866183688047054917701 812599909441508822797069)
                    ·
                      rfl

theorem cell22_2373799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_2373799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373799 prefixEnd_2373799 := by exact prefixLift 2373799
  have htrace : WordTrace (prefixWord ++ tailWord_2373799) baseStart_2373799 baseEnd_2373799 := by
    simpa [prefixWord, tailWord_2373799, baseEnd_2373799] using wordTrace_append hprefix tailTrace_2373799
  have hstable : (prefixWord ++ tailWord_2373799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373799).length < 2 ^ (prefixWord ++ tailWord_2373799).sum := by decide
  have hdescent : baseEnd_2373799 < baseStart_2373799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373842 : List Nat := [3, 2, 2, 2, 1, 3, 3, 1, 5]
def baseStart_2373842 : Nat := 118140960795 + 2373842 * 2 ^ 59
def prefixEnd_2373842 : Nat := 4983230072969 + 3 ^ 40 * 2373842 * 2
def baseEnd_2373842 : Nat := 270871543073423681323979

theorem tailTrace_2373842 : CollatzResearch.WordTrace tailWord_2373842 prefixEnd_2373842 270871543073423681323979 := by
  unfold tailWord_2373842
  simp only [CollatzResearch.WordTrace]
  refine ⟨21645282666495832195394945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57720753777322219187719853 21645282666495832195394945)
  ·
    refine ⟨16233961999871874146546209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21645282666495832195394945 16233961999871874146546209)
    ·
      refine ⟨12175471499903905609909657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16233961999871874146546209 12175471499903905609909657)
      ·
        refine ⟨9131603624927929207432243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12175471499903905609909657 9131603624927929207432243)
        ·
          refine ⟨13697405437391893811148365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9131603624927929207432243 13697405437391893811148365)
          ·
            refine ⟨5136527039021960179180637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13697405437391893811148365 5136527039021960179180637)
            ·
              refine ⟨1926197639633235067192739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5136527039021960179180637 1926197639633235067192739)
              ·
                refine ⟨2889296459449852600789109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1926197639633235067192739 2889296459449852600789109)
                ·
                  refine ⟨270871543073423681323979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2889296459449852600789109 270871543073423681323979)
                  ·
                    rfl

theorem cell22_2373842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_2373842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373842 prefixEnd_2373842 := by exact prefixLift 2373842
  have htrace : WordTrace (prefixWord ++ tailWord_2373842) baseStart_2373842 baseEnd_2373842 := by
    simpa [prefixWord, tailWord_2373842, baseEnd_2373842] using wordTrace_append hprefix tailTrace_2373842
  have hstable : (prefixWord ++ tailWord_2373842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373842).length < 2 ^ (prefixWord ++ tailWord_2373842).sum := by decide
  have hdescent : baseEnd_2373842 < baseStart_2373842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373868 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 3, 5]
def baseStart_2373868 : Nat := 118140960795 + 2373868 * 2 ^ 59
def prefixEnd_2373868 : Nat := 4983230072969 + 3 ^ 40 * 2373868 * 2
def baseEnd_2373868 : Nat := 812623529551615642821857

theorem tailTrace_2373868 : CollatzResearch.WordTrace tailWord_2373868 prefixEnd_2373868 812623529551615642821857 := by
  unfold tailWord_2373868
  simp only [CollatzResearch.WordTrace]
  refine ⟨43291039481944567611013129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57721385975926090148017505 43291039481944567611013129)
  ·
    refine ⟨32468279611458425708259847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43291039481944567611013129 32468279611458425708259847)
    ·
      refine ⟨48702419417187638562389771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32468279611458425708259847 48702419417187638562389771)
      ·
        refine ⟨73053629125781457843584657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48702419417187638562389771 73053629125781457843584657)
        ·
          refine ⟨54790221844336093382688493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73053629125781457843584657 54790221844336093382688493)
          ·
            refine ⟨20546333191626035018508185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54790221844336093382688493 20546333191626035018508185)
            ·
              refine ⟨15409749893719526263881139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20546333191626035018508185 15409749893719526263881139)
              ·
                refine ⟨23114624840579289395821709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15409749893719526263881139 23114624840579289395821709)
                ·
                  refine ⟨8667984315217233523433141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23114624840579289395821709 8667984315217233523433141)
                  ·
                    refine ⟨812623529551615642821857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8667984315217233523433141 812623529551615642821857)
                    ·
                      rfl

theorem cell22_2373868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_2373868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373868 prefixEnd_2373868 := by exact prefixLift 2373868
  have htrace : WordTrace (prefixWord ++ tailWord_2373868) baseStart_2373868 baseEnd_2373868 := by
    simpa [prefixWord, tailWord_2373868, baseEnd_2373868] using wordTrace_append hprefix tailTrace_2373868
  have hstable : (prefixWord ++ tailWord_2373868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373868).length < 2 ^ (prefixWord ++ tailWord_2373868).sum := by decide
  have hdescent : baseEnd_2373868 < baseStart_2373868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373887 : List Nat := [1, 1, 2, 2, 1, 4, 5, 2, 4]
def baseStart_2373887 : Nat := 118140960795 + 2373887 * 2 ^ 59
def prefixEnd_2373887 : Nat := 4983230072969 + 3 ^ 40 * 2373887 * 2
def baseEnd_2373887 : Nat := 270876677879968642198933

theorem tailTrace_2373887 : CollatzResearch.WordTrace tailWord_2373887 prefixEnd_2373887 270876677879968642198933 := by
  unfold tailWord_2373887
  simp only [CollatzResearch.WordTrace]
  refine ⟨86582771950820301466967915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57721847967213534311311943 86582771950820301466967915)
  ·
    refine ⟨129874157926230452200451873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86582771950820301466967915 129874157926230452200451873)
    ·
      refine ⟨97405618444672839150338905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129874157926230452200451873 97405618444672839150338905)
      ·
        refine ⟨73054213833504629362754179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97405618444672839150338905 73054213833504629362754179)
        ·
          refine ⟨109581320750256944044131269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73054213833504629362754179 109581320750256944044131269)
          ·
            refine ⟨20546497640673177008274613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109581320750256944044131269 20546497640673177008274613)
            ·
              refine ⟨1926234153813110344525745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20546497640673177008274613 1926234153813110344525745)
              ·
                refine ⟨1444675615359832758394309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1926234153813110344525745 1444675615359832758394309)
                ·
                  refine ⟨270876677879968642198933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1444675615359832758394309 270876677879968642198933)
                  ·
                    rfl

theorem cell22_2373887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 4].length) (baseStart_2373887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373887 prefixEnd_2373887 := by exact prefixLift 2373887
  have htrace : WordTrace (prefixWord ++ tailWord_2373887) baseStart_2373887 baseEnd_2373887 := by
    simpa [prefixWord, tailWord_2373887, baseEnd_2373887] using wordTrace_append hprefix tailTrace_2373887
  have hstable : (prefixWord ++ tailWord_2373887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373887).length < 2 ^ (prefixWord ++ tailWord_2373887).sum := by decide
  have hdescent : baseEnd_2373887 < baseStart_2373887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373898 : List Nat := [3, 1, 2, 2, 1, 1, 3, 9]
def baseStart_2373898 : Nat := 118140960795 + 2373898 * 2 ^ 59
def prefixEnd_2373898 : Nat := 4983230072969 + 3 ^ 40 * 2373898 * 2
def baseEnd_2373898 : Nat := 90292644351633951619085

theorem tailTrace_2373898 : CollatzResearch.WordTrace tailWord_2373898 prefixEnd_2373898 90292644351633951619085 := by
  unfold tailWord_2373898
  simp only [CollatzResearch.WordTrace]
  refine ⟨21645793288445112586404587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57722115435853633563745565 21645793288445112586404587)
  ·
    refine ⟨32468689932667668879606881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21645793288445112586404587 32468689932667668879606881)
    ·
      refine ⟨24351517449500751659705161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32468689932667668879606881 24351517449500751659705161)
      ·
        refine ⟨18263638087125563744778871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24351517449500751659705161 18263638087125563744778871)
        ·
          refine ⟨27395457130688345617168307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18263638087125563744778871 27395457130688345617168307)
          ·
            refine ⟨41093185696032518425752461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27395457130688345617168307 41093185696032518425752461)
            ·
              refine ⟨15409944636012194409657173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41093185696032518425752461 15409944636012194409657173)
              ·
                refine ⟨90292644351633951619085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15409944636012194409657173 90292644351633951619085)
                ·
                  rfl

theorem cell22_2373898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 9].length) (baseStart_2373898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373898 prefixEnd_2373898 := by exact prefixLift 2373898
  have htrace : WordTrace (prefixWord ++ tailWord_2373898) baseStart_2373898 baseEnd_2373898 := by
    simpa [prefixWord, tailWord_2373898, baseEnd_2373898] using wordTrace_append hprefix tailTrace_2373898
  have hstable : (prefixWord ++ tailWord_2373898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373898).length < 2 ^ (prefixWord ++ tailWord_2373898).sum := by decide
  have hdescent : baseEnd_2373898 < baseStart_2373898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373902 : List Nat := [4, 1, 1, 2, 1, 2, 3, 3, 2, 3]
def baseStart_2373902 : Nat := 118140960795 + 2373902 * 2 ^ 59
def prefixEnd_2373902 : Nat := 4983230072969 + 3 ^ 40 * 2373902 * 2
def baseEnd_2373902 : Nat := 812635168446450887471753

theorem tailTrace_2373902 : CollatzResearch.WordTrace tailWord_2373902 prefixEnd_2373902 812635168446450887471753 := by
  unfold tailWord_2373902
  simp only [CollatzResearch.WordTrace]
  refine ⟨10822914880720744878595495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57722212697177306019175973 10822914880720744878595495)
  ·
    refine ⟨16234372321081117317893243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10822914880720744878595495 16234372321081117317893243)
    ·
      refine ⟨24351558481621675976839865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16234372321081117317893243 24351558481621675976839865)
      ·
        refine ⟨18263668861216256982629899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24351558481621675976839865 18263668861216256982629899)
        ·
          refine ⟨27395503291824385473944849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18263668861216256982629899 27395503291824385473944849)
          ·
            refine ⟨20546627468868289105458637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27395503291824385473944849 20546627468868289105458637)
            ·
              refine ⟨7704985300825608414546989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20546627468868289105458637 7704985300825608414546989)
              ·
                refine ⟨2889369487809603155455121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7704985300825608414546989 2889369487809603155455121)
                ·
                  refine ⟨2167027115857202366591341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2889369487809603155455121 2167027115857202366591341)
                  ·
                    refine ⟨812635168446450887471753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2167027115857202366591341 812635168446450887471753)
                    ·
                      rfl

theorem cell22_2373902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_2373902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373902 prefixEnd_2373902 := by exact prefixLift 2373902
  have htrace : WordTrace (prefixWord ++ tailWord_2373902) baseStart_2373902 baseEnd_2373902 := by
    simpa [prefixWord, tailWord_2373902, baseEnd_2373902] using wordTrace_append hprefix tailTrace_2373902
  have hstable : (prefixWord ++ tailWord_2373902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373902).length < 2 ^ (prefixWord ++ tailWord_2373902).sum := by decide
  have hdescent : baseEnd_2373902 < baseStart_2373902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373943 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 7]
def baseStart_2373943 : Nat := 118140960795 + 2373943 * 2 ^ 59
def prefixEnd_2373943 : Nat := 4983230072969 + 3 ^ 40 * 2373943 * 2
def baseEnd_2373943 : Nat := 270883067861446815732209

theorem tailTrace_2373943 : CollatzResearch.WordTrace tailWord_2373943 prefixEnd_2373943 270883067861446815732209 := by
  unfold tailWord_2373943
  simp only [CollatzResearch.WordTrace]
  refine ⟨86584814438617423031006483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57723209625744948687337655 86584814438617423031006483)
  ·
    refine ⟨129877221657926134546509725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86584814438617423031006483 129877221657926134546509725)
    ·
      refine ⟨48703958121722300454941147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129877221657926134546509725 48703958121722300454941147)
      ·
        refine ⟨73055937182583450682411721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48703958121722300454941147 73055937182583450682411721)
        ·
          refine ⟨54791952886937588011808791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73055937182583450682411721 54791952886937588011808791)
          ·
            refine ⟨82187929330406382017713187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54791952886937588011808791 82187929330406382017713187)
            ·
              refine ⟨123281893995609573026569781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82187929330406382017713187 123281893995609573026569781)
              ·
                refine ⟨11557677562088397471240917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123281893995609573026569781 11557677562088397471240917)
                ·
                  refine ⟨270883067861446815732209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11557677562088397471240917 270883067861446815732209)
                  ·
                    rfl

theorem cell22_2373943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 7].length) (baseStart_2373943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373943 prefixEnd_2373943 := by exact prefixLift 2373943
  have htrace : WordTrace (prefixWord ++ tailWord_2373943) baseStart_2373943 baseEnd_2373943 := by
    simpa [prefixWord, tailWord_2373943, baseEnd_2373943] using wordTrace_append hprefix tailTrace_2373943
  have hstable : (prefixWord ++ tailWord_2373943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373943).length < 2 ^ (prefixWord ++ tailWord_2373943).sum := by decide
  have hdescent : baseEnd_2373943 < baseStart_2373943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373945 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 2, 6]
def baseStart_2373945 : Nat := 118140960795 + 2373945 * 2 ^ 59
def prefixEnd_2373945 : Nat := 4983230072969 + 3 ^ 40 * 2373945 * 2
def baseEnd_2373945 : Nat := 812649888225213108646621

theorem tailTrace_2373945 : CollatzResearch.WordTrace tailWord_2373945 prefixEnd_2373945 812649888225213108646621 := by
  unfold tailWord_2373945
  simp only [CollatzResearch.WordTrace]
  refine ⟨86584887384610177372579289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57723258256406784915052859 86584887384610177372579289)
  ·
    refine ⟨64938665538457633029434467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86584887384610177372579289 64938665538457633029434467)
    ·
      refine ⟨97407998307686449544151701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64938665538457633029434467 97407998307686449544151701)
      ·
        refine ⟨4565999920672802322382111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 97407998307686449544151701 4565999920672802322382111)
        ·
          refine ⟨6848999881009203483573167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4565999920672802322382111 6848999881009203483573167)
          ·
            refine ⟨10273499821513805225359751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6848999881009203483573167 10273499821513805225359751)
            ·
              refine ⟨15410249732270707838039627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10273499821513805225359751 15410249732270707838039627)
              ·
                refine ⟨23115374598406061757059441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15410249732270707838039627 23115374598406061757059441)
                ·
                  refine ⟨17336530948804546317794581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23115374598406061757059441 17336530948804546317794581)
                  ·
                    refine ⟨812649888225213108646621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17336530948804546317794581 812649888225213108646621)
                    ·
                      rfl

theorem cell22_2373945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 6].length) (baseStart_2373945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373945 prefixEnd_2373945 := by exact prefixLift 2373945
  have htrace : WordTrace (prefixWord ++ tailWord_2373945) baseStart_2373945 baseEnd_2373945 := by
    simpa [prefixWord, tailWord_2373945, baseEnd_2373945] using wordTrace_append hprefix tailTrace_2373945
  have hstable : (prefixWord ++ tailWord_2373945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373945).length < 2 ^ (prefixWord ++ tailWord_2373945).sum := by decide
  have hdescent : baseEnd_2373945 < baseStart_2373945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373960 : List Nat := [2, 1, 3, 1, 1, 2, 4, 3, 5]
def baseStart_2373960 : Nat := 118140960795 + 2373960 * 2 ^ 59
def prefixEnd_2373960 : Nat := 4983230072969 + 3 ^ 40 * 2373960 * 2
def baseEnd_2373960 : Nat := 270885007677252689840525

theorem tailTrace_2373960 : CollatzResearch.WordTrace tailWord_2373960 prefixEnd_2373960 270885007677252689840525 := by
  unfold tailWord_2373960
  simp only [CollatzResearch.WordTrace]
  refine ⟨43292717239777917467187667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57723622986370556622916889 43292717239777917467187667)
  ·
    refine ⟨64939075859666876200781501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43292717239777917467187667 64939075859666876200781501)
    ·
      refine ⟨24352153447375078575293063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64939075859666876200781501 24352153447375078575293063)
      ·
        refine ⟨36528230171062617862939595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24352153447375078575293063 36528230171062617862939595)
        ·
          refine ⟨54792345256593926794409393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36528230171062617862939595 54792345256593926794409393)
          ·
            refine ⟨41094258942445445095807045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54792345256593926794409393 41094258942445445095807045)
            ·
              refine ⟨7705173551708520955463821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41094258942445445095807045 7705173551708520955463821)
              ·
                refine ⟨2889440081890695358298933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7705173551708520955463821 2889440081890695358298933)
                ·
                  refine ⟨270885007677252689840525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2889440081890695358298933 270885007677252689840525)
                  ·
                    rfl

theorem cell22_2373960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 5].length) (baseStart_2373960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373960 prefixEnd_2373960 := by exact prefixLift 2373960
  have htrace : WordTrace (prefixWord ++ tailWord_2373960) baseStart_2373960 baseEnd_2373960 := by
    simpa [prefixWord, tailWord_2373960, baseEnd_2373960] using wordTrace_append hprefix tailTrace_2373960
  have hstable : (prefixWord ++ tailWord_2373960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373960).length < 2 ^ (prefixWord ++ tailWord_2373960).sum := by decide
  have hdescent : baseEnd_2373960 < baseStart_2373960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2373994 : List Nat := [3, 1, 3, 3, 1, 3, 1, 2, 5]
def baseStart_2373994 : Nat := 118140960795 + 2373994 * 2 ^ 59
def prefixEnd_2373994 : Nat := 4983230072969 + 3 ^ 40 * 2373994 * 2
def baseEnd_2373994 : Nat := 270888887308864438057157

theorem tailTrace_2373994 : CollatzResearch.WordTrace tailWord_2373994 prefixEnd_2373994 270888887308864438057157 := by
  unfold tailWord_2373994
  simp only [CollatzResearch.WordTrace]
  refine ⟨21646668640358164685278259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57724449707621772494075357 21646668640358164685278259)
  ·
    refine ⟨32470002960537247027917389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21646668640358164685278259 32470002960537247027917389)
    ·
      refine ⟨12176251110201467635469021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32470002960537247027917389 12176251110201467635469021)
      ·
        refine ⟨4566094166325550363300883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12176251110201467635469021 4566094166325550363300883)
        ·
          refine ⟨6849141249488325544951325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4566094166325550363300883 6849141249488325544951325)
          ·
            refine ⟨2568427968558122079356747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6849141249488325544951325 2568427968558122079356747)
            ·
              refine ⟨3852641952837183119035121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2568427968558122079356747 3852641952837183119035121)
              ·
                refine ⟨2889481464627887339276341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3852641952837183119035121 2889481464627887339276341)
                ·
                  refine ⟨270888887308864438057157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2889481464627887339276341 270888887308864438057157)
                  ·
                    rfl

theorem cell22_2373994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 5].length) (baseStart_2373994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2373994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2373994 prefixEnd_2373994 := by exact prefixLift 2373994
  have htrace : WordTrace (prefixWord ++ tailWord_2373994) baseStart_2373994 baseEnd_2373994 := by
    simpa [prefixWord, tailWord_2373994, baseEnd_2373994] using wordTrace_append hprefix tailTrace_2373994
  have hstable : (prefixWord ++ tailWord_2373994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2373994).length < 2 ^ (prefixWord ++ tailWord_2373994).sum := by decide
  have hdescent : baseEnd_2373994 < baseStart_2373994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2373994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374071 : List Nat := [1, 1, 3, 1, 3, 5, 2, 1, 2, 3]
def baseStart_2374071 : Nat := 118140960795 + 2374071 * 2 ^ 59
def prefixEnd_2374071 : Nat := 4983230072969 + 3 ^ 40 * 2374071 * 2
def baseEnd_2374071 : Nat := 812693020600190779996235

theorem tailTrace_2374071 : CollatzResearch.WordTrace tailWord_2374071 prefixEnd_2374071 812693020600190779996235 := by
  unfold tailWord_2374071
  simp only [CollatzResearch.WordTrace]
  refine ⟨86589482982153700891666067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57726321988102467261110711 86589482982153700891666067)
  ·
    refine ⟨129884224473230551337499101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86589482982153700891666067 129884224473230551337499101)
    ·
      refine ⟨48706584177461456751562163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129884224473230551337499101 48706584177461456751562163)
      ·
        refine ⟨73059876266192185127343245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48706584177461456751562163 73059876266192185127343245)
        ·
          refine ⟨27397453599822069422753717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73059876266192185127343245 27397453599822069422753717)
          ·
            refine ⟨2568511274983319008383161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27397453599822069422753717 2568511274983319008383161)
            ·
              refine ⟨1926383456237489256287371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2568511274983319008383161 1926383456237489256287371)
              ·
                refine ⟨2889575184356233884431057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1926383456237489256287371 2889575184356233884431057)
                ·
                  refine ⟨2167181388267175413323293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2889575184356233884431057 2167181388267175413323293)
                  ·
                    refine ⟨812693020600190779996235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2167181388267175413323293 812693020600190779996235)
                    ·
                      rfl

theorem cell22_2374071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 2, 3].length) (baseStart_2374071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2374071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2374071 prefixEnd_2374071 := by exact prefixLift 2374071
  have htrace : WordTrace (prefixWord ++ tailWord_2374071) baseStart_2374071 baseEnd_2374071 := by
    simpa [prefixWord, tailWord_2374071, baseEnd_2374071] using wordTrace_append hprefix tailTrace_2374071
  have hstable : (prefixWord ++ tailWord_2374071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374071).length < 2 ^ (prefixWord ++ tailWord_2374071).sum := by decide
  have hdescent : baseEnd_2374071 < baseStart_2374071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374112 : List Nat := [2, 1, 1, 3, 1, 1, 6, 2, 5]
def baseStart_2374112 : Nat := 118140960795 + 2374112 * 2 ^ 59
def prefixEnd_2374112 : Nat := 4983230072969 + 3 ^ 40 * 2374112 * 2
def baseEnd_2374112 : Nat := 270902351912693446573703

theorem tailTrace_2374112 : CollatzResearch.WordTrace tailWord_2374112 prefixEnd_2374112 270902351912693446573703 := by
  unfold tailWord_2374112
  simp only [CollatzResearch.WordTrace]
  refine ⟨43295489187502582446954295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57727318916670109929272393 43295489187502582446954295)
  ·
    refine ⟨64943233781253873670431443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43295489187502582446954295 64943233781253873670431443)
    ·
      refine ⟨97414850671880810505647165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64943233781253873670431443 97414850671880810505647165)
      ·
        refine ⟨36530569001955303939617687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97414850671880810505647165 36530569001955303939617687)
        ·
          refine ⟨54795853502932955909426531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36530569001955303939617687 54795853502932955909426531)
          ·
            refine ⟨82193780254399433864139797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54795853502932955909426531 82193780254399433864139797)
            ·
              refine ⟨3852833449424973462381553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82193780254399433864139797 3852833449424973462381553)
              ·
                refine ⟨2889625087068730096786165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3852833449424973462381553 2889625087068730096786165)
                ·
                  refine ⟨270902351912693446573703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2889625087068730096786165 270902351912693446573703)
                  ·
                    rfl

theorem cell22_2374112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 5].length) (baseStart_2374112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2374112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2374112 prefixEnd_2374112 := by exact prefixLift 2374112
  have htrace : WordTrace (prefixWord ++ tailWord_2374112) baseStart_2374112 baseEnd_2374112 := by
    simpa [prefixWord, tailWord_2374112, baseEnd_2374112] using wordTrace_append hprefix tailTrace_2374112
  have hstable : (prefixWord ++ tailWord_2374112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374112).length < 2 ^ (prefixWord ++ tailWord_2374112).sum := by decide
  have hdescent : baseEnd_2374112 < baseStart_2374112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374202 : List Nat := [3, 1, 1, 1, 3, 4, 1, 8]
def baseStart_2374202 : Nat := 118140960795 + 2374202 * 2 ^ 59
def prefixEnd_2374202 : Nat := 4983230072969 + 3 ^ 40 * 2374202 * 2
def baseEnd_2374202 : Nat := 90304207175261122774537

theorem tailTrace_2374202 : CollatzResearch.WordTrace tailWord_2374202 prefixEnd_2374202 90304207175261122774537 := by
  unfold tailWord_2374202
  simp only [CollatzResearch.WordTrace]
  refine ⟨21648565236169777566171215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57729507296452740176456573 21648565236169777566171215)
  ·
    refine ⟨32472847854254666349256823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21648565236169777566171215 32472847854254666349256823)
    ·
      refine ⟨48709271781381999523885235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32472847854254666349256823 48709271781381999523885235)
      ·
        refine ⟨73063907672072999285827853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48709271781381999523885235 73063907672072999285827853)
        ·
          refine ⟨27398965377027374732185445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73063907672072999285827853 27398965377027374732185445)
          ·
            refine ⟨5137306008192632762284771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27398965377027374732185445 5137306008192632762284771)
            ·
              refine ⟨7705959012288949143427157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5137306008192632762284771 7705959012288949143427157)
              ·
                refine ⟨90304207175261122774537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7705959012288949143427157 90304207175261122774537)
                ·
                  rfl

theorem cell22_2374202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 8].length) (baseStart_2374202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2374202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2374202 prefixEnd_2374202 := by exact prefixLift 2374202
  have htrace : WordTrace (prefixWord ++ tailWord_2374202) baseStart_2374202 baseEnd_2374202 := by
    simpa [prefixWord, tailWord_2374202, baseEnd_2374202] using wordTrace_append hprefix tailTrace_2374202
  have hstable : (prefixWord ++ tailWord_2374202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374202).length < 2 ^ (prefixWord ++ tailWord_2374202).sum := by decide
  have hdescent : baseEnd_2374202 < baseStart_2374202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374221 : List Nat := [1, 6, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_2374221 : Nat := 118140960795 + 2374221 * 2 ^ 59
def prefixEnd_2374221 : Nat := 4983230072969 + 3 ^ 40 * 2374221 * 2
def baseEnd_2374221 : Nat := 812744368665640388745775

theorem tailTrace_2374221 : CollatzResearch.WordTrace tailWord_2374221 prefixEnd_2374221 812744368665640388745775 := by
  unfold tailWord_2374221
  simp only [CollatzResearch.WordTrace]
  refine ⟨86594953931610276509626517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57729969287740184339751011 86594953931610276509626517)
  ·
    refine ⟨4059138465544231711388743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86594953931610276509626517 4059138465544231711388743)
    ·
      refine ⟨6088707698316347567083115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4059138465544231711388743 6088707698316347567083115)
      ·
        refine ⟨9133061547474521350624673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6088707698316347567083115 9133061547474521350624673)
        ·
          refine ⟨6849796160605891012968505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9133061547474521350624673 6849796160605891012968505)
          ·
            refine ⟨5137347120454418259726379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6849796160605891012968505 5137347120454418259726379)
            ·
              refine ⟨7706020680681627389589569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5137347120454418259726379 7706020680681627389589569)
              ·
                refine ⟨5779515510511220542192177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7706020680681627389589569 5779515510511220542192177)
                ·
                  refine ⟨4334636632883415406644133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5779515510511220542192177 4334636632883415406644133)
                  ·
                    refine ⟨812744368665640388745775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4334636632883415406644133 812744368665640388745775)
                    ·
                      rfl

theorem cell22_2374221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_2374221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2374221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2374221 prefixEnd_2374221 := by exact prefixLift 2374221
  have htrace : WordTrace (prefixWord ++ tailWord_2374221) baseStart_2374221 baseEnd_2374221 := by
    simpa [prefixWord, tailWord_2374221, baseEnd_2374221] using wordTrace_append hprefix tailTrace_2374221
  have hstable : (prefixWord ++ tailWord_2374221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374221).length < 2 ^ (prefixWord ++ tailWord_2374221).sum := by decide
  have hdescent : baseEnd_2374221 < baseStart_2374221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374371 : List Nat := [1, 1, 1, 7, 1, 1, 4, 6]
def baseStart_2374371 : Nat := 118140960795 + 2374371 * 2 ^ 59
def prefixEnd_2374371 : Nat := 4983230072969 + 3 ^ 40 * 2374371 * 2
def baseEnd_2374371 : Nat := 90310635192343333055035

theorem tailTrace_2374371 : CollatzResearch.WordTrace tailWord_2374371 prefixEnd_2374371 90310635192343333055035 := by
  unfold tailWord_2374371
  simp only [CollatzResearch.WordTrace]
  refine ⟨86600424881066852127586967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57733616587377901418391311 86600424881066852127586967)
  ·
    refine ⟨129900637321600278191380451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86600424881066852127586967 129900637321600278191380451)
    ·
      refine ⟨194850955982400417287070677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129900637321600278191380451 194850955982400417287070677)
      ·
        refine ⟨4566819280837509780165719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 194850955982400417287070677 4566819280837509780165719)
        ·
          refine ⟨6850228921256264670248579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4566819280837509780165719 6850228921256264670248579)
          ·
            refine ⟨10275343381884397005372869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6850228921256264670248579 10275343381884397005372869)
            ·
              refine ⟨1926626884103324438507413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10275343381884397005372869 1926626884103324438507413)
              ·
                refine ⟨90310635192343333055035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1926626884103324438507413 90310635192343333055035)
                ·
                  rfl

theorem cell22_2374371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 6].length) (baseStart_2374371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2374371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2374371 prefixEnd_2374371 := by exact prefixLift 2374371
  have htrace : WordTrace (prefixWord ++ tailWord_2374371) baseStart_2374371 baseEnd_2374371 := by
    simpa [prefixWord, tailWord_2374371, baseEnd_2374371] using wordTrace_append hprefix tailTrace_2374371
  have hstable : (prefixWord ++ tailWord_2374371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374371).length < 2 ^ (prefixWord ++ tailWord_2374371).sum := by decide
  have hdescent : baseEnd_2374371 < baseStart_2374371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374399 : List Nat := [1, 1, 2, 2, 1, 3, 1, 6, 5]
def baseStart_2374399 : Nat := 118140960795 + 2374399 * 2 ^ 59
def prefixEnd_2374399 : Nat := 4983230072969 + 3 ^ 40 * 2374399 * 2
def baseEnd_2374399 : Nat := 270935100567769085931743

theorem tailTrace_2374399 : CollatzResearch.WordTrace tailWord_2374399 prefixEnd_2374399 270935100567769085931743 := by
  unfold tailWord_2374399
  simp only [CollatzResearch.WordTrace]
  refine ⟨86601446124965412909606251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57734297416643608606404167 86601446124965412909606251)
  ·
    refine ⟨129902169187448119364409377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86601446124965412909606251 129902169187448119364409377)
    ·
      refine ⟨97426626890586089523307033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129902169187448119364409377 97426626890586089523307033)
      ·
        refine ⟨73069970167939567142480275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97426626890586089523307033 73069970167939567142480275)
        ·
          refine ⟨109604955251909350713720413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73069970167939567142480275 109604955251909350713720413)
          ·
            refine ⟨41101858219466006517645155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109604955251909350713720413 41101858219466006517645155)
            ·
              refine ⟨61652787329199009776467733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41101858219466006517645155 61652787329199009776467733)
              ·
                refine ⟨2889974406056203583271925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61652787329199009776467733 2889974406056203583271925)
                ·
                  refine ⟨270935100567769085931743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2889974406056203583271925 270935100567769085931743)
                  ·
                    rfl

theorem cell22_2374399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 5].length) (baseStart_2374399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2374399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2374399 prefixEnd_2374399 := by exact prefixLift 2374399
  have htrace : WordTrace (prefixWord ++ tailWord_2374399) baseStart_2374399 baseEnd_2374399 := by
    simpa [prefixWord, tailWord_2374399, baseEnd_2374399] using wordTrace_append hprefix tailTrace_2374399
  have hstable : (prefixWord ++ tailWord_2374399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374399).length < 2 ^ (prefixWord ++ tailWord_2374399).sum := by decide
  have hdescent : baseEnd_2374399 < baseStart_2374399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374414 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_2374414 : Nat := 118140960795 + 2374414 * 2 ^ 59
def prefixEnd_2374414 : Nat := 4983230072969 + 3 ^ 40 * 2374414 * 2
def baseEnd_2374414 : Nat := 812810436509852218670183

theorem tailTrace_2374414 : CollatzResearch.WordTrace tailWord_2374414 prefixEnd_2374414 812810436509852218670183 := by
  unfold tailWord_2374414
  simp only [CollatzResearch.WordTrace]
  refine ⟨10825249152488883808925287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57734662146607380314268197 10825249152488883808925287)
  ·
    refine ⟨16237873728733325713387931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10825249152488883808925287 16237873728733325713387931)
    ·
      refine ⟨24356810593099988570081897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16237873728733325713387931 24356810593099988570081897)
      ·
        refine ⟨18267607944824991427561423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24356810593099988570081897 18267607944824991427561423)
        ·
          refine ⟨27401411917237487141342135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18267607944824991427561423 27401411917237487141342135)
          ·
            refine ⟨41102117875856230712013203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27401411917237487141342135 41102117875856230712013203)
            ·
              refine ⟨61653176813784346068019805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41102117875856230712013203 61653176813784346068019805)
              ·
                refine ⟨23119941305169129775507427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61653176813784346068019805 23119941305169129775507427)
                ·
                  refine ⟨34679911957753694663261141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23119941305169129775507427 34679911957753694663261141)
                  ·
                    refine ⟨812810436509852218670183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34679911957753694663261141 812810436509852218670183)
                    ·
                      rfl

theorem cell22_2374414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_2374414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2374414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2374414 prefixEnd_2374414 := by exact prefixLift 2374414
  have htrace : WordTrace (prefixWord ++ tailWord_2374414) baseStart_2374414 baseEnd_2374414 := by
    simpa [prefixWord, tailWord_2374414, baseEnd_2374414] using wordTrace_append hprefix tailTrace_2374414
  have hstable : (prefixWord ++ tailWord_2374414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374414).length < 2 ^ (prefixWord ++ tailWord_2374414).sum := by decide
  have hdescent : baseEnd_2374414 < baseStart_2374414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374476 : List Nat := [2, 2, 1, 3, 3, 1, 1, 3, 1, 5]
def baseStart_2374476 : Nat := 118140960795 + 2374476 * 2 ^ 59
def prefixEnd_2374476 : Nat := 4983230072969 + 3 ^ 40 * 2374476 * 2
def baseEnd_2374476 : Nat := 812831660376904723619993

theorem tailTrace_2374476 : CollatzResearch.WordTrace tailWord_2374476 prefixEnd_2374476 812831660376904723619993 := by
  unfold tailWord_2374476
  simp only [CollatzResearch.WordTrace]
  refine ⟨43302127272843227530079641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57736169697124303373439521 43302127272843227530079641)
  ·
    refine ⟨32476595454632420647559731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43302127272843227530079641 32476595454632420647559731)
    ·
      refine ⟨48714893181948630971339597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32476595454632420647559731 48714893181948630971339597)
      ·
        refine ⟨18268084943230736614252349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48714893181948630971339597 18268084943230736614252349)
        ·
          refine ⟨6850531853711526230344631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18268084943230736614252349 6850531853711526230344631)
          ·
            refine ⟨10275797780567289345516947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6850531853711526230344631 10275797780567289345516947)
            ·
              refine ⟨15413696670850934018275421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10275797780567289345516947 15413696670850934018275421)
              ·
                refine ⟨5780136251569100256853283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15413696670850934018275421 5780136251569100256853283)
                ·
                  refine ⟨8670204377353650385279925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5780136251569100256853283 8670204377353650385279925)
                  ·
                    refine ⟨812831660376904723619993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8670204377353650385279925 812831660376904723619993)
                    ·
                      rfl

theorem cell22_2374476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_2374476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2374476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2374476 prefixEnd_2374476 := by exact prefixLift 2374476
  have htrace : WordTrace (prefixWord ++ tailWord_2374476) baseStart_2374476 baseEnd_2374476 := by
    simpa [prefixWord, tailWord_2374476, baseEnd_2374476] using wordTrace_append hprefix tailTrace_2374476
  have hstable : (prefixWord ++ tailWord_2374476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374476).length < 2 ^ (prefixWord ++ tailWord_2374476).sum := by decide
  have hdescent : baseEnd_2374476 < baseStart_2374476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374510 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 4, 3]
def baseStart_2374510 : Nat := 118140960795 + 2374510 * 2 ^ 59
def prefixEnd_2374510 : Nat := 4983230072969 + 3 ^ 40 * 2374510 * 2
def baseEnd_2374510 : Nat := 812843299271739968269889

theorem tailTrace_2374510 : CollatzResearch.WordTrace tailWord_2374510 prefixEnd_2374510 812843299271739968269889 := by
  unfold tailWord_2374510
  simp only [CollatzResearch.WordTrace]
  refine ⟨10825686828445409858362123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57736996418375519244597989 10825686828445409858362123)
  ·
    refine ⟨16238530242668114787543185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10825686828445409858362123 16238530242668114787543185)
    ·
      refine ⟨12178897682001086090657389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16238530242668114787543185 12178897682001086090657389)
      ·
        refine ⟨4567086630750407283996521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12178897682001086090657389 4567086630750407283996521)
        ·
          refine ⟨3425314973062805462997391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4567086630750407283996521 3425314973062805462997391)
          ·
            refine ⟨5137972459594208194496087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425314973062805462997391 5137972459594208194496087)
            ·
              refine ⟨7706958689391312291744131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5137972459594208194496087 7706958689391312291744131)
              ·
                refine ⟨11560438034086968437616197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7706958689391312291744131 11560438034086968437616197)
                ·
                  refine ⟨2167582131391306582053037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11560438034086968437616197 2167582131391306582053037)
                  ·
                    refine ⟨812843299271739968269889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2167582131391306582053037 812843299271739968269889)
                    ·
                      rfl

theorem cell22_2374510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_2374510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2374510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2374510 prefixEnd_2374510 := by exact prefixLift 2374510
  have htrace : WordTrace (prefixWord ++ tailWord_2374510) baseStart_2374510 baseEnd_2374510 := by
    simpa [prefixWord, tailWord_2374510, baseEnd_2374510] using wordTrace_append hprefix tailTrace_2374510
  have hstable : (prefixWord ++ tailWord_2374510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374510).length < 2 ^ (prefixWord ++ tailWord_2374510).sum := by decide
  have hdescent : baseEnd_2374510 < baseStart_2374510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374519 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 1, 8]
def baseStart_2374519 : Nat := 118140960795 + 2374519 * 2 ^ 59
def prefixEnd_2374519 : Nat := 4983230072969 + 3 ^ 40 * 2374519 * 2
def baseEnd_2374519 : Nat := 812846380155666944794861

theorem tailTrace_2374519 : CollatzResearch.WordTrace tailWord_2374519 prefixEnd_2374519 812846380155666944794861 := by
  unfold tailWord_2374519
  simp only [CollatzResearch.WordTrace]
  refine ⟨86605822884530673403974611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57737215256353782269316407 86605822884530673403974611)
  ·
    refine ⟨129908734326796010105961917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86605822884530673403974611 129908734326796010105961917)
    ·
      refine ⟨48715775372548503789735719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129908734326796010105961917 48715775372548503789735719)
      ·
        refine ⟨73073663058822755684603579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48715775372548503789735719 73073663058822755684603579)
        ·
          refine ⟨109610494588234133526905369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73073663058822755684603579 109610494588234133526905369)
          ·
            refine ⟨82207870941175600145179027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109610494588234133526905369 82207870941175600145179027)
            ·
              refine ⟨123311806411763400217768541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82207870941175600145179027 123311806411763400217768541)
              ·
                refine ⟨46241927404411275081663203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123311806411763400217768541 46241927404411275081663203)
                ·
                  refine ⟨69362891106616912622494805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46241927404411275081663203 69362891106616912622494805)
                  ·
                    refine ⟨812846380155666944794861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69362891106616912622494805 812846380155666944794861)
                    ·
                      rfl

theorem cell22_2374519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_2374519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2374519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2374519 prefixEnd_2374519 := by exact prefixLift 2374519
  have htrace : WordTrace (prefixWord ++ tailWord_2374519) baseStart_2374519 baseEnd_2374519 := by
    simpa [prefixWord, tailWord_2374519, baseEnd_2374519] using wordTrace_append hprefix tailTrace_2374519
  have hstable : (prefixWord ++ tailWord_2374519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374519).length < 2 ^ (prefixWord ++ tailWord_2374519).sum := by decide
  have hdescent : baseEnd_2374519 < baseStart_2374519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374585 : List Nat := [1, 2, 1, 4, 2, 4, 2, 1, 5]
def baseStart_2374585 : Nat := 118140960795 + 2374585 * 2 ^ 59
def prefixEnd_2374585 : Nat := 4983230072969 + 3 ^ 40 * 2374585 * 2
def baseEnd_2374585 : Nat := 270956324434821590881553

theorem tailTrace_2374585 : CollatzResearch.WordTrace tailWord_2374585 prefixEnd_2374585 270956324434821590881553 := by
  unfold tailWord_2374585
  simp only [CollatzResearch.WordTrace]
  refine ⟨86608230102291566675877209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57738820068194377783918139 86608230102291566675877209)
  ·
    refine ⟨64956172576718675006907907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86608230102291566675877209 64956172576718675006907907)
    ·
      refine ⟨97434258865078012510361861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64956172576718675006907907 97434258865078012510361861)
      ·
        refine ⟨18268923537202127345692849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97434258865078012510361861 18268923537202127345692849)
        ·
          refine ⟨13701692652901595509269637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18268923537202127345692849 13701692652901595509269637)
          ·
            refine ⟨2569067372419049157988057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13701692652901595509269637 2569067372419049157988057)
            ·
              refine ⟨1926800529314286868491043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2569067372419049157988057 1926800529314286868491043)
              ·
                refine ⟨2890200793971430302736565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1926800529314286868491043 2890200793971430302736565)
                ·
                  refine ⟨270956324434821590881553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2890200793971430302736565 270956324434821590881553)
                  ·
                    rfl

theorem cell22_2374585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 5].length) (baseStart_2374585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2374585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2374585 prefixEnd_2374585 := by exact prefixLift 2374585
  have htrace : WordTrace (prefixWord ++ tailWord_2374585) baseStart_2374585 baseEnd_2374585 := by
    simpa [prefixWord, tailWord_2374585, baseEnd_2374585] using wordTrace_append hprefix tailTrace_2374585
  have hstable : (prefixWord ++ tailWord_2374585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374585).length < 2 ^ (prefixWord ++ tailWord_2374585).sum := by decide
  have hdescent : baseEnd_2374585 < baseStart_2374585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374690 : List Nat := [3, 3, 1, 1, 1, 3, 1, 3, 3, 3]
def baseStart_2374690 : Nat := 118140960795 + 2374690 * 2 ^ 59
def prefixEnd_2374690 : Nat := 4983230072969 + 3 ^ 40 * 2374690 * 2
def baseEnd_2374690 : Nat := 812904916950279498769337

theorem tailTrace_2374690 : CollatzResearch.WordTrace tailWord_2374690 prefixEnd_2374690 812904916950279498769337 := by
  unfold tailWord_2374690
  simp only [CollatzResearch.WordTrace]
  refine ⟨21653014941727792402112381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57741373177940779738966349 21653014941727792402112381)
  ·
    refine ⟨8119880603147922150792143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21653014941727792402112381 8119880603147922150792143)
    ·
      refine ⟨12179820904721883226188215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8119880603147922150792143 12179820904721883226188215)
      ·
        refine ⟨18269731357082824839282323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12179820904721883226188215 18269731357082824839282323)
        ·
          refine ⟨27404597035624237258923485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18269731357082824839282323 27404597035624237258923485)
          ·
            refine ⟨10276723888359088972096307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27404597035624237258923485 10276723888359088972096307)
            ·
              refine ⟨15415085832538633458144461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10276723888359088972096307 15415085832538633458144461)
              ·
                refine ⟨5780657187201987546804173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15415085832538633458144461 5780657187201987546804173)
                ·
                  refine ⟨2167746445200745330051565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5780657187201987546804173 2167746445200745330051565)
                  ·
                    refine ⟨812904916950279498769337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2167746445200745330051565 812904916950279498769337)
                    ·
                      rfl

theorem cell22_2374690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_2374690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2374690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2374690 prefixEnd_2374690 := by exact prefixLift 2374690
  have htrace : WordTrace (prefixWord ++ tailWord_2374690) baseStart_2374690 baseEnd_2374690 := by
    simpa [prefixWord, tailWord_2374690, baseEnd_2374690] using wordTrace_append hprefix tailTrace_2374690
  have hstable : (prefixWord ++ tailWord_2374690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374690).length < 2 ^ (prefixWord ++ tailWord_2374690).sum := by decide
  have hdescent : baseEnd_2374690 < baseStart_2374690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374754 : List Nat := [3, 3, 2, 2, 1, 3, 2, 1, 5]
def baseStart_2374754 : Nat := 118140960795 + 2374754 * 2 ^ 59
def prefixEnd_2374754 : Nat := 4983230072969 + 3 ^ 40 * 2374754 * 2
def baseEnd_2374754 : Nat := 270975608486068221723047

theorem tailTrace_2374754 : CollatzResearch.WordTrace tailWord_2374754 prefixEnd_2374754 270975608486068221723047 := by
  unfold tailWord_2374754
  simp only [CollatzResearch.WordTrace]
  refine ⟨21653598509669827134694829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57742929359119539025852877 21653598509669827134694829)
  ·
    refine ⟨8120099441126185175510561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21653598509669827134694829 8120099441126185175510561)
    ·
      refine ⟨6090074580844638881632921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8120099441126185175510561 6090074580844638881632921)
      ·
        refine ⟨4567555935633479161224691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6090074580844638881632921 4567555935633479161224691)
        ·
          refine ⟨6851333903450218741837037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4567555935633479161224691 6851333903450218741837037)
          ·
            refine ⟨2569250213793832028188889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6851333903450218741837037 2569250213793832028188889)
            ·
              refine ⟨1926937660345374021141667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2569250213793832028188889 1926937660345374021141667)
              ·
                refine ⟨2890406490518061031712501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1926937660345374021141667 2890406490518061031712501)
                ·
                  refine ⟨270975608486068221723047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2890406490518061031712501 270975608486068221723047)
                  ·
                    rfl

theorem cell22_2374754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_2374754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2374754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2374754 prefixEnd_2374754 := by exact prefixLift 2374754
  have htrace : WordTrace (prefixWord ++ tailWord_2374754) baseStart_2374754 baseEnd_2374754 := by
    simpa [prefixWord, tailWord_2374754, baseEnd_2374754] using wordTrace_append hprefix tailTrace_2374754
  have hstable : (prefixWord ++ tailWord_2374754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374754).length < 2 ^ (prefixWord ++ tailWord_2374754).sum := by decide
  have hdescent : baseEnd_2374754 < baseStart_2374754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374810 : List Nat := [3, 1, 1, 5, 1, 1, 3, 7]
def baseStart_2374810 : Nat := 118140960795 + 2374810 * 2 ^ 59
def prefixEnd_2374810 : Nat := 4983230072969 + 3 ^ 40 * 2374810 * 2
def baseEnd_2374810 : Nat := 90327332822515465085441

theorem tailTrace_2374810 : CollatzResearch.WordTrace tailWord_2374810 prefixEnd_2374810 90327332822515465085441 := by
  unfold tailWord_2374810
  simp only [CollatzResearch.WordTrace]
  refine ⟨21654109131619107525704471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57744291017650953401878589 21654109131619107525704471)
  ·
    refine ⟨32481163697428661288556707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21654109131619107525704471 32481163697428661288556707)
    ·
      refine ⟨48721745546142991932835061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32481163697428661288556707 48721745546142991932835061)
      ·
        refine ⟨4567663644950905493703287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48721745546142991932835061 4567663644950905493703287)
        ·
          refine ⟨6851495467426358240554931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4567663644950905493703287 6851495467426358240554931)
          ·
            refine ⟨10277243201139537360832397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6851495467426358240554931 10277243201139537360832397)
            ·
              refine ⟨3853966200427326510312149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10277243201139537360832397 3853966200427326510312149)
              ·
                refine ⟨90327332822515465085441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3853966200427326510312149 90327332822515465085441)
                ·
                  rfl

theorem cell22_2374810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 7].length) (baseStart_2374810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2374810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2374810 prefixEnd_2374810 := by exact prefixLift 2374810
  have htrace : WordTrace (prefixWord ++ tailWord_2374810) baseStart_2374810 baseEnd_2374810 := by
    simpa [prefixWord, tailWord_2374810, baseEnd_2374810] using wordTrace_append hprefix tailTrace_2374810
  have hstable : (prefixWord ++ tailWord_2374810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374810).length < 2 ^ (prefixWord ++ tailWord_2374810).sum := by decide
  have hdescent : baseEnd_2374810 < baseStart_2374810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374814 : List Nat := [4, 3, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_2374814 : Nat := 118140960795 + 2374814 * 2 ^ 59
def prefixEnd_2374814 : Nat := 4983230072969 + 3 ^ 40 * 2374814 * 2
def baseEnd_2374814 : Nat := 812947364684384508668957

theorem tailTrace_2374814 : CollatzResearch.WordTrace tailWord_2374814 prefixEnd_2374814 812947364684384508668957 := by
  unfold tailWord_2374814
  simp only [CollatzResearch.WordTrace]
  refine ⟨10827072802307742348245437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57744388278974625857308997 10827072802307742348245437)
  ·
    refine ⟨4060152300865403380592039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10827072802307742348245437 4060152300865403380592039)
    ·
      refine ⟨6090228451298105070888059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4060152300865403380592039 6090228451298105070888059)
      ·
        refine ⟨9135342676947157606332089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6090228451298105070888059 9135342676947157606332089)
        ·
          refine ⟨6851507007710368204749067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9135342676947157606332089 6851507007710368204749067)
          ·
            refine ⟨10277260511565552307123601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6851507007710368204749067 10277260511565552307123601)
            ·
              refine ⟨7707945383674164230342701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10277260511565552307123601 7707945383674164230342701)
              ·
                refine ⟨2890479518877811586378513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7707945383674164230342701 2890479518877811586378513)
                ·
                  refine ⟨2167859639158358689783885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2890479518877811586378513 2167859639158358689783885)
                  ·
                    refine ⟨812947364684384508668957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2167859639158358689783885 812947364684384508668957)
                    ·
                      rfl

theorem cell22_2374814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_2374814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2374814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2374814 prefixEnd_2374814 := by exact prefixLift 2374814
  have htrace : WordTrace (prefixWord ++ tailWord_2374814) baseStart_2374814 baseEnd_2374814 := by
    simpa [prefixWord, tailWord_2374814, baseEnd_2374814] using wordTrace_append hprefix tailTrace_2374814
  have hstable : (prefixWord ++ tailWord_2374814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374814).length < 2 ^ (prefixWord ++ tailWord_2374814).sum := by decide
  have hdescent : baseEnd_2374814 < baseStart_2374814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374829 : List Nat := [1, 5, 2, 1, 3, 2, 1, 1, 2, 4]
def baseStart_2374829 : Nat := 118140960795 + 2374829 * 2 ^ 59
def prefixEnd_2374829 : Nat := 4983230072969 + 3 ^ 40 * 2374829 * 2
def baseEnd_2374829 : Nat := 812952499490929469543911

theorem tailTrace_2374829 : CollatzResearch.WordTrace tailWord_2374829 prefixEnd_2374829 812952499490929469543911 := by
  unfold tailWord_2374829
  simp only [CollatzResearch.WordTrace]
  refine ⟨86617129513407596347759541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57744753008938397565173027 86617129513407596347759541)
  ·
    refine ⟨8120355891881962157602457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86617129513407596347759541 8120355891881962157602457)
    ·
      refine ⟨6090266918911471618201843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8120355891881962157602457 6090266918911471618201843)
      ·
        refine ⟨9135400378367207427302765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6090266918911471618201843 9135400378367207427302765)
        ·
          refine ⟨3425775141887702785238537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9135400378367207427302765 3425775141887702785238537)
          ·
            refine ⟨2569331356415777088928903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3425775141887702785238537 2569331356415777088928903)
            ·
              refine ⟨3853997034623665633393355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2569331356415777088928903 3853997034623665633393355)
              ·
                refine ⟨5780995551935498450090033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3853997034623665633393355 5780995551935498450090033)
                ·
                  refine ⟨4335746663951623837567525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5780995551935498450090033 4335746663951623837567525)
                  ·
                    refine ⟨812952499490929469543911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4335746663951623837567525 812952499490929469543911)
                    ·
                      rfl

theorem cell22_2374829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_2374829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2374829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2374829 prefixEnd_2374829 := by exact prefixLift 2374829
  have htrace : WordTrace (prefixWord ++ tailWord_2374829) baseStart_2374829 baseEnd_2374829 := by
    simpa [prefixWord, tailWord_2374829, baseEnd_2374829] using wordTrace_append hprefix tailTrace_2374829
  have hstable : (prefixWord ++ tailWord_2374829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374829).length < 2 ^ (prefixWord ++ tailWord_2374829).sum := by decide
  have hdescent : baseEnd_2374829 < baseStart_2374829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374947 : List Nat := [1, 1, 1, 4, 2, 4, 2, 1, 2, 4]
def baseStart_2374947 : Nat := 118140960795 + 2374947 * 2 ^ 59
def prefixEnd_2374947 : Nat := 4983230072969 + 3 ^ 40 * 2374947 * 2
def baseEnd_2374947 : Nat := 812992893302416495093549

theorem tailTrace_2374947 : CollatzResearch.WordTrace tailWord_2374947 prefixEnd_2374947 812992893302416495093549 := by
  unfold tailWord_2374947
  simp only [CollatzResearch.WordTrace]
  refine ⟨86621433326980102500555095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57747622217986735000370063 86621433326980102500555095)
  ·
    refine ⟨129932149990470153750832643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86621433326980102500555095 129932149990470153750832643)
    ·
      refine ⟨194898224985705230626248965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129932149990470153750832643 194898224985705230626248965)
      ·
        refine ⟨36543417184819730742421681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194898224985705230626248965 36543417184819730742421681)
        ·
          refine ⟨27407562888614798056816261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36543417184819730742421681 27407562888614798056816261)
          ·
            refine ⟨5138918041615274635653049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27407562888614798056816261 5138918041615274635653049)
            ·
              refine ⟨3854188531211455976739787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5138918041615274635653049 3854188531211455976739787)
              ·
                refine ⟨5781282796817183965109681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3854188531211455976739787 5781282796817183965109681)
                ·
                  refine ⟨4335962097612887973832261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5781282796817183965109681 4335962097612887973832261)
                  ·
                    refine ⟨812992893302416495093549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4335962097612887973832261 812992893302416495093549)
                    ·
                      rfl

theorem cell22_2374947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 4].length) (baseStart_2374947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2374947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2374947 prefixEnd_2374947 := by exact prefixLift 2374947
  have htrace : WordTrace (prefixWord ++ tailWord_2374947) baseStart_2374947 baseEnd_2374947 := by
    simpa [prefixWord, tailWord_2374947, baseEnd_2374947] using wordTrace_append hprefix tailTrace_2374947
  have hstable : (prefixWord ++ tailWord_2374947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374947).length < 2 ^ (prefixWord ++ tailWord_2374947).sum := by decide
  have hdescent : baseEnd_2374947 < baseStart_2374947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374975 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 2, 6]
def baseStart_2374975 : Nat := 118140960795 + 2374975 * 2 ^ 59
def prefixEnd_2374975 : Nat := 4983230072969 + 3 ^ 40 * 2374975 * 2
def baseEnd_2374975 : Nat := 813002478274633755393463

theorem tailTrace_2374975 : CollatzResearch.WordTrace tailWord_2374975 prefixEnd_2374975 813002478274633755393463 := by
  unfold tailWord_2374975
  simp only [CollatzResearch.WordTrace]
  refine ⟨86622454570878663282574379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57748303047252442188382919 86622454570878663282574379)
  ·
    refine ⟨129933681856317994923861569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86622454570878663282574379 129933681856317994923861569)
    ·
      refine ⟨97450261392238496192896177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129933681856317994923861569 97450261392238496192896177)
      ·
        refine ⟨73087696044178872144672133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97450261392238496192896177 73087696044178872144672133)
        ·
          refine ⟨13703943008283538527126025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73087696044178872144672133 13703943008283538527126025)
          ·
            refine ⟨10277957256212653895344519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13703943008283538527126025 10277957256212653895344519)
            ·
              refine ⟨15416935884318980843016779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10277957256212653895344519 15416935884318980843016779)
              ·
                refine ⟨23125403826478471264525169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15416935884318980843016779 23125403826478471264525169)
                ·
                  refine ⟨17344052869858853448393877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23125403826478471264525169 17344052869858853448393877)
                  ·
                    refine ⟨813002478274633755393463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17344052869858853448393877 813002478274633755393463)
                    ·
                      rfl

theorem cell22_2374975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_2374975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2374975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2374975 prefixEnd_2374975 := by exact prefixLift 2374975
  have htrace : WordTrace (prefixWord ++ tailWord_2374975) baseStart_2374975 baseEnd_2374975 := by
    simpa [prefixWord, tailWord_2374975, baseEnd_2374975] using wordTrace_append hprefix tailTrace_2374975
  have hstable : (prefixWord ++ tailWord_2374975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374975).length < 2 ^ (prefixWord ++ tailWord_2374975).sum := by decide
  have hdescent : baseEnd_2374975 < baseStart_2374975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2374998 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_2374998 : Nat := 118140960795 + 2374998 * 2 ^ 59
def prefixEnd_2374998 : Nat := 4983230072969 + 3 ^ 40 * 2374998 * 2
def baseEnd_2374998 : Nat := 813010351644669362068393

theorem tailTrace_2374998 : CollatzResearch.WordTrace tailWord_2374998 prefixEnd_2374998 813010351644669362068393 := by
  unfold tailWord_2374998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5413955840612208638166353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57748862299863558807107765 5413955840612208638166353)
  ·
    refine ⟨4060466880459156478624765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5413955840612208638166353 4060466880459156478624765)
    ·
      refine ⟨1522675080172183679484287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4060466880459156478624765 1522675080172183679484287)
      ·
        refine ⟨2284012620258275519226431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1522675080172183679484287 2284012620258275519226431)
        ·
          refine ⟨3426018930387413278839647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2284012620258275519226431 3426018930387413278839647)
          ·
            refine ⟨5139028395581119918259471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3426018930387413278839647 5139028395581119918259471)
            ·
              refine ⟨7708542593371679877389207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5139028395581119918259471 7708542593371679877389207)
              ·
                refine ⟨11562813890057519816083811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7708542593371679877389207 11562813890057519816083811)
                ·
                  refine ⟨17344220835086279724125717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11562813890057519816083811 17344220835086279724125717)
                  ·
                    refine ⟨813010351644669362068393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17344220835086279724125717 813010351644669362068393)
                    ·
                      rfl

theorem cell22_2374998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_2374998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2374998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2374998 prefixEnd_2374998 := by exact prefixLift 2374998
  have htrace : WordTrace (prefixWord ++ tailWord_2374998) baseStart_2374998 baseEnd_2374998 := by
    simpa [prefixWord, tailWord_2374998, baseEnd_2374998] using wordTrace_append hprefix tailTrace_2374998
  have hstable : (prefixWord ++ tailWord_2374998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2374998).length < 2 ^ (prefixWord ++ tailWord_2374998).sum := by decide
  have hdescent : baseEnd_2374998 < baseStart_2374998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2374998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375011 : List Nat := [1, 1, 1, 5, 2, 3, 2, 3, 1, 3]
def baseStart_2375011 : Nat := 118140960795 + 2375011 * 2 ^ 59
def prefixEnd_2375011 : Nat := 4983230072969 + 3 ^ 40 * 2375011 * 2
def baseEnd_2375011 : Nat := 813014801810341661493353

theorem tailTrace_2375011 : CollatzResearch.WordTrace tailWord_2375011 prefixEnd_2375011 813014801810341661493353 := by
  unfold tailWord_2375011
  simp only [CollatzResearch.WordTrace]
  refine ⟨86623767598748241430884887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57749178399165494287256591 86623767598748241430884887)
  ·
    refine ⟨129935651398122362146327331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86623767598748241430884887 129935651398122362146327331)
    ·
      refine ⟨194903477097183543219490997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129935651398122362146327331 194903477097183543219490997)
      ·
        refine ⟨18272200977860957176827281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 194903477097183543219490997 18272200977860957176827281)
        ·
          refine ⟨13704150733395717882620461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18272200977860957176827281 13704150733395717882620461)
          ·
            refine ⟨5139056525023394205982673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13704150733395717882620461 5139056525023394205982673)
            ·
              refine ⟨3854292393767545654487005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5139056525023394205982673 3854292393767545654487005)
              ·
                refine ⟨1445359647662829620432627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3854292393767545654487005 1445359647662829620432627)
                ·
                  refine ⟨2168039471494244430648941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1445359647662829620432627 2168039471494244430648941)
                  ·
                    refine ⟨813014801810341661493353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2168039471494244430648941 813014801810341661493353)
                    ·
                      rfl

theorem cell22_2375011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 1, 3].length) (baseStart_2375011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2375011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2375011 prefixEnd_2375011 := by exact prefixLift 2375011
  have htrace : WordTrace (prefixWord ++ tailWord_2375011) baseStart_2375011 baseEnd_2375011 := by
    simpa [prefixWord, tailWord_2375011, baseEnd_2375011] using wordTrace_append hprefix tailTrace_2375011
  have hstable : (prefixWord ++ tailWord_2375011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375011).length < 2 ^ (prefixWord ++ tailWord_2375011).sum := by decide
  have hdescent : baseEnd_2375011 < baseStart_2375011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375041 : List Nat := [1, 2, 4, 3, 2, 1, 3, 1, 5]
def baseStart_2375041 : Nat := 118140960795 + 2375041 * 2 ^ 59
def prefixEnd_2375041 : Nat := 4983230072969 + 3 ^ 40 * 2375041 * 2
def baseEnd_2375041 : Nat := 271008357141143861081087

theorem tailTrace_2375041 : CollatzResearch.WordTrace tailWord_2375041 prefixEnd_2375041 271008357141143861081087 := by
  unfold tailWord_2375041
  simp only [CollatzResearch.WordTrace]
  refine ⟨86624861788639556554476977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57749907859093037702984651 86624861788639556554476977)
  ·
    refine ⟨64968646341479667415857733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86624861788639556554476977 64968646341479667415857733)
    ·
      refine ⟨12181621189027437640473325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64968646341479667415857733 12181621189027437640473325)
      ·
        refine ⟨4568107945885289115177497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12181621189027437640473325 4568107945885289115177497)
        ·
          refine ⟨3426080959413966836383123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4568107945885289115177497 3426080959413966836383123)
          ·
            refine ⟨5139121439120950254574685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3426080959413966836383123 5139121439120950254574685)
            ·
              refine ⟨1927170539670356345465507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5139121439120950254574685 1927170539670356345465507)
              ·
                refine ⟨2890755809505534518198261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1927170539670356345465507 2890755809505534518198261)
                ·
                  refine ⟨271008357141143861081087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2890755809505534518198261 271008357141143861081087)
                  ·
                    rfl

theorem cell22_2375041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 5].length) (baseStart_2375041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2375041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2375041 prefixEnd_2375041 := by exact prefixLift 2375041
  have htrace : WordTrace (prefixWord ++ tailWord_2375041) baseStart_2375041 baseEnd_2375041 := by
    simpa [prefixWord, tailWord_2375041, baseEnd_2375041] using wordTrace_append hprefix tailTrace_2375041
  have hstable : (prefixWord ++ tailWord_2375041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375041).length < 2 ^ (prefixWord ++ tailWord_2375041).sum := by decide
  have hdescent : baseEnd_2375041 < baseStart_2375041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375219 : List Nat := [1, 1, 1, 2, 4, 3, 3, 1, 1, 5]
def baseStart_2375219 : Nat := 118140960795 + 2375219 * 2 ^ 59
def prefixEnd_2375219 : Nat := 4983230072969 + 3 ^ 40 * 2375219 * 2
def baseEnd_2375219 : Nat := 813086004461098452292715

theorem tailTrace_2375219 : CollatzResearch.WordTrace tailWord_2375219 prefixEnd_2375219 813086004461098452292715 := by
  unfold tailWord_2375219
  simp only [CollatzResearch.WordTrace]
  refine ⟨86631353981994692954456711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57754235987996461969637807 86631353981994692954456711)
  ·
    refine ⟨129947030972992039431685067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86631353981994692954456711 129947030972992039431685067)
    ·
      refine ⟨194920546459488059147527601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129947030972992039431685067 194920546459488059147527601)
      ·
        refine ⟨146190409844616044360645701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194920546459488059147527601 146190409844616044360645701)
        ·
          refine ⟨27410701845865508317621069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146190409844616044360645701 27410701845865508317621069)
          ·
            refine ⟨10279013192199565619107901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27410701845865508317621069 10279013192199565619107901)
            ·
              refine ⟨3854629947074837107165463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10279013192199565619107901 3854629947074837107165463)
              ·
                refine ⟨5781944920612255660748195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3854629947074837107165463 5781944920612255660748195)
                ·
                  refine ⟨8672917380918383491122293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5781944920612255660748195 8672917380918383491122293)
                  ·
                    refine ⟨813086004461098452292715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8672917380918383491122293 813086004461098452292715)
                    ·
                      rfl

theorem cell22_2375219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 5].length) (baseStart_2375219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2375219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2375219 prefixEnd_2375219 := by exact prefixLift 2375219
  have htrace : WordTrace (prefixWord ++ tailWord_2375219) baseStart_2375219 baseEnd_2375219 := by
    simpa [prefixWord, tailWord_2375219, baseEnd_2375219] using wordTrace_append hprefix tailTrace_2375219
  have hstable : (prefixWord ++ tailWord_2375219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375219).length < 2 ^ (prefixWord ++ tailWord_2375219).sum := by decide
  have hdescent : baseEnd_2375219 < baseStart_2375219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375326 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_2375326 : Nat := 118140960795 + 2375326 * 2 ^ 59
def prefixEnd_2375326 : Nat := 4983230072969 + 3 ^ 40 * 2375326 * 2
def baseEnd_2375326 : Nat := 813122632747785839867387

theorem tailTrace_2375326 : CollatzResearch.WordTrace tailWord_2375326 prefixEnd_2375326 813122632747785839867387 := by
  unfold tailWord_2375326
  simp only [CollatzResearch.WordTrace]
  refine ⟨10829407074075881278575229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57756837728404700152401221 10829407074075881278575229)
  ·
    refine ⟨4061027652778455479465711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10829407074075881278575229 4061027652778455479465711)
    ·
      refine ⟨6091541479167683219198567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4061027652778455479465711 6091541479167683219198567)
      ·
        refine ⟨9137312218751524828797851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6091541479167683219198567 9137312218751524828797851)
        ·
          refine ⟨13705968328127287243196777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9137312218751524828797851 13705968328127287243196777)
          ·
            refine ⟨10279476246095465432397583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13705968328127287243196777 10279476246095465432397583)
            ·
              refine ⟨15419214369143198148596375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10279476246095465432397583 15419214369143198148596375)
              ·
                refine ⟨23128821553714797222894563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15419214369143198148596375 23128821553714797222894563)
                ·
                  refine ⟨34693232330572195834341845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23128821553714797222894563 34693232330572195834341845)
                  ·
                    refine ⟨813122632747785839867387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34693232330572195834341845 813122632747785839867387)
                    ·
                      rfl

theorem cell22_2375326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_2375326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2375326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2375326 prefixEnd_2375326 := by exact prefixLift 2375326
  have htrace : WordTrace (prefixWord ++ tailWord_2375326) baseStart_2375326 baseEnd_2375326 := by
    simpa [prefixWord, tailWord_2375326, baseEnd_2375326] using wordTrace_append hprefix tailTrace_2375326
  have hstable : (prefixWord ++ tailWord_2375326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375326).length < 2 ^ (prefixWord ++ tailWord_2375326).sum := by decide
  have hdescent : baseEnd_2375326 < baseStart_2375326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375341 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_2375341 : Nat := 118140960795 + 2375341 * 2 ^ 59
def prefixEnd_2375341 : Nat := 4983230072969 + 3 ^ 40 * 2375341 * 2
def baseEnd_2375341 : Nat := 813127767554330800742341

theorem tailTrace_2375341 : CollatzResearch.WordTrace tailWord_2375341 prefixEnd_2375341 813127767554330800742341 := by
  unfold tailWord_2375341
  simp only [CollatzResearch.WordTrace]
  refine ⟨86635803687552707790397877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57757202458368471860265251 86635803687552707790397877)
  ·
    refine ⟨8122106595708066355349801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86635803687552707790397877 8122106595708066355349801)
    ·
      refine ⟨6091579946781049766512351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8122106595708066355349801 6091579946781049766512351)
      ·
        refine ⟨9137369920171574649768527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6091579946781049766512351 9137369920171574649768527)
        ·
          refine ⟨13706054880257361974652791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9137369920171574649768527 13706054880257361974652791)
          ·
            refine ⟨20559082320386042961979187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13706054880257361974652791 20559082320386042961979187)
            ·
              refine ⟨30838623480579064442968781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20559082320386042961979187 30838623480579064442968781)
              ·
                refine ⟨11564483805217149166113293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30838623480579064442968781 11564483805217149166113293)
                ·
                  refine ⟨4336681426956430937292485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11564483805217149166113293 4336681426956430937292485)
                  ·
                    refine ⟨813127767554330800742341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4336681426956430937292485 813127767554330800742341)
                    ·
                      rfl

theorem cell22_2375341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_2375341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2375341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2375341 prefixEnd_2375341 := by exact prefixLift 2375341
  have htrace : WordTrace (prefixWord ++ tailWord_2375341) baseStart_2375341 baseEnd_2375341 := by
    simpa [prefixWord, tailWord_2375341, baseEnd_2375341] using wordTrace_append hprefix tailTrace_2375341
  have hstable : (prefixWord ++ tailWord_2375341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375341).length < 2 ^ (prefixWord ++ tailWord_2375341).sum := by decide
  have hdescent : baseEnd_2375341 < baseStart_2375341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375358 : List Nat := [4, 2, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_2375358 : Nat := 118140960795 + 2375358 * 2 ^ 59
def prefixEnd_2375358 : Nat := 4983230072969 + 3 ^ 40 * 2375358 * 2
def baseEnd_2375358 : Nat := 813133587001748423067289

theorem tailTrace_2375358 : CollatzResearch.WordTrace tailWord_2375358 prefixEnd_2375358 813133587001748423067289 := by
  unfold tailWord_2375358
  simp only [CollatzResearch.WordTrace]
  refine ⟨10829552966061389961720841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57757615818994079795844485 10829552966061389961720841)
  ·
    refine ⟨8122164724546042471290631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10829552966061389961720841 8122164724546042471290631)
    ·
      refine ⟨12183247086819063706935947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8122164724546042471290631 12183247086819063706935947)
      ·
        refine ⟨18274870630228595560403921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12183247086819063706935947 18274870630228595560403921)
        ·
          refine ⟨13706152972671446670302941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18274870630228595560403921 13706152972671446670302941)
          ·
            refine ⟨5139807364751792501363603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13706152972671446670302941 5139807364751792501363603)
            ·
              refine ⟨7709711047127688752045405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5139807364751792501363603 7709711047127688752045405)
              ·
                refine ⟨2891141642672883282017027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7709711047127688752045405 2891141642672883282017027)
                ·
                  refine ⟨4336712464009324923025541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2891141642672883282017027 4336712464009324923025541)
                  ·
                    refine ⟨813133587001748423067289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4336712464009324923025541 813133587001748423067289)
                    ·
                      rfl

theorem cell22_2375358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_2375358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2375358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2375358 prefixEnd_2375358 := by exact prefixLift 2375358
  have htrace : WordTrace (prefixWord ++ tailWord_2375358) baseStart_2375358 baseEnd_2375358 := by
    simpa [prefixWord, tailWord_2375358, baseEnd_2375358] using wordTrace_append hprefix tailTrace_2375358
  have hstable : (prefixWord ++ tailWord_2375358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375358).length < 2 ^ (prefixWord ++ tailWord_2375358).sum := by decide
  have hdescent : baseEnd_2375358 < baseStart_2375358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375373 : List Nat := [1, 6, 2, 1, 1, 1, 1, 3, 6]
def baseStart_2375373 : Nat := 118140960795 + 2375373 * 2 ^ 59
def prefixEnd_2375373 : Nat := 4983230072969 + 3 ^ 40 * 2375373 * 2
def baseEnd_2375373 : Nat := 271046240602764461314081

theorem tailTrace_2375373 : CollatzResearch.WordTrace tailWord_2375373 prefixEnd_2375373 271046240602764461314081 := by
  unfold tailWord_2375373
  simp only [CollatzResearch.WordTrace]
  refine ⟨86636970823436777255562773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57757980548957851503708515 86636970823436777255562773)
  ·
    refine ⟨4061108007348598933854505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86636970823436777255562773 4061108007348598933854505)
    ·
      refine ⟨3045831005511449200390879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4061108007348598933854505 3045831005511449200390879)
      ·
        refine ⟨4568746508267173800586319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3045831005511449200390879 4568746508267173800586319)
        ·
          refine ⟨6853119762400760700879479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4568746508267173800586319 6853119762400760700879479)
          ·
            refine ⟨10279679643601141051319219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6853119762400760700879479 10279679643601141051319219)
            ·
              refine ⟨15419519465401711576978829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10279679643601141051319219 15419519465401711576978829)
              ·
                refine ⟨5782319799525641841367061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15419519465401711576978829 5782319799525641841367061)
                ·
                  refine ⟨271046240602764461314081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5782319799525641841367061 271046240602764461314081)
                  ·
                    rfl

theorem cell22_2375373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_2375373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2375373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2375373 prefixEnd_2375373 := by exact prefixLift 2375373
  have htrace : WordTrace (prefixWord ++ tailWord_2375373) baseStart_2375373 baseEnd_2375373 := by
    simpa [prefixWord, tailWord_2375373, baseEnd_2375373] using wordTrace_append hprefix tailTrace_2375373
  have hstable : (prefixWord ++ tailWord_2375373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375373).length < 2 ^ (prefixWord ++ tailWord_2375373).sum := by decide
  have hdescent : baseEnd_2375373 < baseStart_2375373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375384 : List Nat := [2, 1, 2, 2, 3, 1, 2, 9]
def baseStart_2375384 : Nat := 118140960795 + 2375384 * 2 ^ 59
def prefixEnd_2375384 : Nat := 4983230072969 + 3 ^ 40 * 2375384 * 2
def baseEnd_2375384 : Nat := 90349165259232557990801

theorem tailTrace_2375384 : CollatzResearch.WordTrace tailWord_2375384 prefixEnd_2375384 90349165259232557990801 := by
  unfold tailWord_2375384
  simp only [CollatzResearch.WordTrace]
  refine ⟨43318686013198463067106603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57758248017597950756142137 43318686013198463067106603)
  ·
    refine ⟨64978029019797694600659905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43318686013198463067106603 64978029019797694600659905)
    ·
      refine ⟨48733521764848270950494929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64978029019797694600659905 48733521764848270950494929)
      ·
        refine ⟨36550141323636203212871197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48733521764848270950494929 36550141323636203212871197)
        ·
          refine ⟨13706302996363576204826699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36550141323636203212871197 13706302996363576204826699)
          ·
            refine ⟨20559454494545364307240049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13706302996363576204826699 20559454494545364307240049)
            ·
              refine ⟨15419590870909023230430037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20559454494545364307240049 15419590870909023230430037)
              ·
                refine ⟨90349165259232557990801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15419590870909023230430037 90349165259232557990801)
                ·
                  rfl

theorem cell22_2375384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 9].length) (baseStart_2375384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2375384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2375384 prefixEnd_2375384 := by exact prefixLift 2375384
  have htrace : WordTrace (prefixWord ++ tailWord_2375384) baseStart_2375384 baseEnd_2375384 := by
    simpa [prefixWord, tailWord_2375384, baseEnd_2375384] using wordTrace_append hprefix tailTrace_2375384
  have hstable : (prefixWord ++ tailWord_2375384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375384).length < 2 ^ (prefixWord ++ tailWord_2375384).sum := by decide
  have hdescent : baseEnd_2375384 < baseStart_2375384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375508 : List Nat := [2, 4, 1, 1, 3, 2, 1, 2, 6]
def baseStart_2375508 : Nat := 118140960795 + 2375508 * 2 ^ 59
def prefixEnd_2375508 : Nat := 4983230072969 + 3 ^ 40 * 2375508 * 2
def baseEnd_2375508 : Nat := 271061645022399343938943

theorem tailTrace_2375508 : CollatzResearch.WordTrace tailWord_2375508 prefixEnd_2375508 271061645022399343938943 := by
  unfold tailWord_2375508
  simp only [CollatzResearch.WordTrace]
  refine ⟨43320947338973847655863589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57761263118631796874484785 43320947338973847655863589)
  ·
    refine ⟨8122677626057596435474423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43320947338973847655863589 8122677626057596435474423)
    ·
      refine ⟨12184016439086394653211635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8122677626057596435474423 12184016439086394653211635)
      ·
        refine ⟨18276024658629591979817453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12184016439086394653211635 18276024658629591979817453)
        ·
          refine ⟨6853509246986096992431545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18276024658629591979817453 6853509246986096992431545)
          ·
            refine ⟨5140131935239572744323659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6853509246986096992431545 5140131935239572744323659)
            ·
              refine ⟨7710197902859359116485489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5140131935239572744323659 7710197902859359116485489)
              ·
                refine ⟨5782648427144519337364117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7710197902859359116485489 5782648427144519337364117)
                ·
                  refine ⟨271061645022399343938943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5782648427144519337364117 271061645022399343938943)
                  ·
                    rfl

theorem cell22_2375508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_2375508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2375508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2375508 prefixEnd_2375508 := by exact prefixLift 2375508
  have htrace : WordTrace (prefixWord ++ tailWord_2375508) baseStart_2375508 baseEnd_2375508 := by
    simpa [prefixWord, tailWord_2375508, baseEnd_2375508] using wordTrace_append hprefix tailTrace_2375508
  have hstable : (prefixWord ++ tailWord_2375508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375508).length < 2 ^ (prefixWord ++ tailWord_2375508).sum := by decide
  have hdescent : baseEnd_2375508 < baseStart_2375508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375521 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 1, 6]
def baseStart_2375521 : Nat := 118140960795 + 2375521 * 2 ^ 59
def prefixEnd_2375521 : Nat := 4983230072969 + 3 ^ 40 * 2375521 * 2
def baseEnd_2375521 : Nat := 813189385232870331241789

theorem tailTrace_2375521 : CollatzResearch.WordTrace tailWord_2375521 prefixEnd_2375521 813189385232870331241789 := by
  unfold tailWord_2375521
  simp only [CollatzResearch.WordTrace]
  refine ⟨86642368826900598531950417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57761579217933732354633611 86642368826900598531950417)
  ·
    refine ⟨64981776620175448898962813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86642368826900598531950417 64981776620175448898962813)
    ·
      refine ⟨24368166232565793337111055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64981776620175448898962813 24368166232565793337111055)
      ·
        refine ⟨36552249348848690005666583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24368166232565793337111055 36552249348848690005666583)
        ·
          refine ⟨54828374023273035008499875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36552249348848690005666583 54828374023273035008499875)
          ·
            refine ⟨82242561034909552512749813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54828374023273035008499875 82242561034909552512749813)
            ·
              refine ⟨7710240097022770548070295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82242561034909552512749813 7710240097022770548070295)
              ·
                refine ⟨11565360145534155822105443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7710240097022770548070295 11565360145534155822105443)
                ·
                  refine ⟨17348040218301233733158165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11565360145534155822105443 17348040218301233733158165)
                  ·
                    refine ⟨813189385232870331241789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17348040218301233733158165 813189385232870331241789)
                    ·
                      rfl

theorem cell22_2375521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_2375521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2375521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2375521 prefixEnd_2375521 := by exact prefixLift 2375521
  have htrace : WordTrace (prefixWord ++ tailWord_2375521) baseStart_2375521 baseEnd_2375521 := by
    simpa [prefixWord, tailWord_2375521, baseEnd_2375521] using wordTrace_append hprefix tailTrace_2375521
  have hstable : (prefixWord ++ tailWord_2375521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375521).length < 2 ^ (prefixWord ++ tailWord_2375521).sum := by decide
  have hdescent : baseEnd_2375521 < baseStart_2375521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375570 : List Nat := [3, 2, 3, 2, 1, 1, 4, 6]
def baseStart_2375570 : Nat := 118140960795 + 2375570 * 2 ^ 59
def prefixEnd_2375570 : Nat := 4983230072969 + 3 ^ 40 * 2375570 * 2
def baseEnd_2375570 : Nat := 90356239881583392974071

theorem tailTrace_2375570 : CollatzResearch.WordTrace tailWord_2375570 prefixEnd_2375570 90356239881583392974071 := by
  unfold tailWord_2375570
  simp only [CollatzResearch.WordTrace]
  refine ⟨21661039000930769975121041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57762770669148719933656109 21661039000930769975121041)
  ·
    refine ⟨16245779250698077481340781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21661039000930769975121041 16245779250698077481340781)
    ·
      refine ⟨6092167219011779055502793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16245779250698077481340781 6092167219011779055502793)
      ·
        refine ⟨4569125414258834291627095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6092167219011779055502793 4569125414258834291627095)
        ·
          refine ⟨6853688121388251437440643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4569125414258834291627095 6853688121388251437440643)
          ·
            refine ⟨10280532182082377156160965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6853688121388251437440643 10280532182082377156160965)
            ·
              refine ⟨1927599784140445716780181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10280532182082377156160965 1927599784140445716780181)
              ·
                refine ⟨90356239881583392974071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1927599784140445716780181 90356239881583392974071)
                ·
                  rfl

theorem cell22_2375570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 6].length) (baseStart_2375570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2375570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2375570 prefixEnd_2375570 := by exact prefixLift 2375570
  have htrace : WordTrace (prefixWord ++ tailWord_2375570) baseStart_2375570 baseEnd_2375570 := by
    simpa [prefixWord, tailWord_2375570, baseEnd_2375570] using wordTrace_append hprefix tailTrace_2375570
  have hstable : (prefixWord ++ tailWord_2375570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375570).length < 2 ^ (prefixWord ++ tailWord_2375570).sum := by decide
  have hdescent : baseEnd_2375570 < baseStart_2375570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375658 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 3, 5]
def baseStart_2375658 : Nat := 118140960795 + 2375658 * 2 ^ 59
def prefixEnd_2375658 : Nat := 4983230072969 + 3 ^ 40 * 2375658 * 2
def baseEnd_2375658 : Nat := 813236283132647640566369

theorem tailTrace_2375658 : CollatzResearch.WordTrace tailWord_2375658 prefixEnd_2375658 813236283132647640566369 := by
  unfold tailWord_2375658
  simp only [CollatzResearch.WordTrace]
  refine ⟨21661841406851067732421907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57764910418269513953125085 21661841406851067732421907)
  ·
    refine ⟨32492762110276601598632861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21661841406851067732421907 32492762110276601598632861)
    ·
      refine ⟨12184785791353725599487323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32492762110276601598632861 12184785791353725599487323)
      ·
        refine ⟨18277178687030588399230985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12184785791353725599487323 18277178687030588399230985)
        ·
          refine ⟨13707884015272941299423239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18277178687030588399230985 13707884015272941299423239)
          ·
            refine ⟨20561826022909411949134859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13707884015272941299423239 20561826022909411949134859)
            ·
              refine ⟨30842739034364117923702289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20561826022909411949134859 30842739034364117923702289)
              ·
                refine ⟨23132054275773088442776717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30842739034364117923702289 23132054275773088442776717)
                ·
                  refine ⟨8674520353414908166041269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23132054275773088442776717 8674520353414908166041269)
                  ·
                    refine ⟨813236283132647640566369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8674520353414908166041269 813236283132647640566369)
                    ·
                      rfl

theorem cell22_2375658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_2375658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2375658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2375658 prefixEnd_2375658 := by exact prefixLift 2375658
  have htrace : WordTrace (prefixWord ++ tailWord_2375658) baseStart_2375658 baseEnd_2375658 := by
    simpa [prefixWord, tailWord_2375658, baseEnd_2375658] using wordTrace_append hprefix tailTrace_2375658
  have hstable : (prefixWord ++ tailWord_2375658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375658).length < 2 ^ (prefixWord ++ tailWord_2375658).sum := by decide
  have hdescent : baseEnd_2375658 < baseStart_2375658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375675 : List Nat := [1, 1, 1, 1, 1, 3, 6, 3, 2, 3]
def baseStart_2375675 : Nat := 118140960795 + 2375675 * 2 ^ 59
def prefixEnd_2375675 : Nat := 4983230072969 + 3 ^ 40 * 2375675 * 2
def baseEnd_2375675 : Nat := 813242102580065262891317

theorem tailTrace_2375675 : CollatzResearch.WordTrace tailWord_2375675 prefixEnd_2375675 813242102580065262891317 := by
  unfold tailWord_2375675
  simp only [CollatzResearch.WordTrace]
  refine ⟨86647985668342682833056479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57765323778895121888704319 86647985668342682833056479)
  ·
    refine ⟨129971978502514024249584719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86647985668342682833056479 129971978502514024249584719)
    ·
      refine ⟨194957967753771036374377079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129971978502514024249584719 194957967753771036374377079)
      ·
        refine ⟨292436951630656554561565619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194957967753771036374377079 292436951630656554561565619)
        ·
          refine ⟨438655427445984831842348429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292436951630656554561565619 438655427445984831842348429)
          ·
            refine ⟨164495785292244311940880661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 438655427445984831842348429 164495785292244311940880661)
            ·
              refine ⟨7710739935573952122228781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 164495785292244311940880661 7710739935573952122228781)
              ·
                refine ⟨2891527475840232045835793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7710739935573952122228781 2891527475840232045835793)
                ·
                  refine ⟨2168645606880174034376845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2891527475840232045835793 2168645606880174034376845)
                  ·
                    refine ⟨813242102580065262891317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2168645606880174034376845 813242102580065262891317)
                    ·
                      rfl

theorem cell22_2375675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 3].length) (baseStart_2375675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2375675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2375675 prefixEnd_2375675 := by exact prefixLift 2375675
  have htrace : WordTrace (prefixWord ++ tailWord_2375675) baseStart_2375675 baseEnd_2375675 := by
    simpa [prefixWord, tailWord_2375675, baseEnd_2375675] using wordTrace_append hprefix tailTrace_2375675
  have hstable : (prefixWord ++ tailWord_2375675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375675).length < 2 ^ (prefixWord ++ tailWord_2375675).sum := by decide
  have hdescent : baseEnd_2375675 < baseStart_2375675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375690 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 1, 6]
def baseStart_2375690 : Nat := 118140960795 + 2375690 * 2 ^ 59
def prefixEnd_2375690 : Nat := 4983230072969 + 3 ^ 40 * 2375690 * 2
def baseEnd_2375690 : Nat := 813247237386610223766271

theorem tailTrace_2375690 : CollatzResearch.WordTrace tailWord_2375690 prefixEnd_2375690 813247237386610223766271 := by
  unfold tailWord_2375690
  simp only [CollatzResearch.WordTrace]
  refine ⟨21662133190822085098713131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57765688508858893596568349 21662133190822085098713131)
  ·
    refine ⟨32493199786233127648069697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21662133190822085098713131 32493199786233127648069697)
    ·
      refine ⟨24369899839674845736052273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32493199786233127648069697 24369899839674845736052273)
      ·
        refine ⟨18277424879756134302039205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24369899839674845736052273 18277424879756134302039205)
        ·
          refine ⟨3427017164954275181632351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18277424879756134302039205 3427017164954275181632351)
          ·
            refine ⟨5140525747431412772448527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3427017164954275181632351 5140525747431412772448527)
            ·
              refine ⟨7710788621147119158672791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5140525747431412772448527 7710788621147119158672791)
              ·
                refine ⟨11566182931720678738009187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7710788621147119158672791 11566182931720678738009187)
                ·
                  refine ⟨17349274397581018107013781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11566182931720678738009187 17349274397581018107013781)
                  ·
                    refine ⟨813247237386610223766271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17349274397581018107013781 813247237386610223766271)
                    ·
                      rfl

theorem cell22_2375690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_2375690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2375690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2375690 prefixEnd_2375690 := by exact prefixLift 2375690
  have htrace : WordTrace (prefixWord ++ tailWord_2375690) baseStart_2375690 baseEnd_2375690 := by
    simpa [prefixWord, tailWord_2375690, baseEnd_2375690] using wordTrace_append hprefix tailTrace_2375690
  have hstable : (prefixWord ++ tailWord_2375690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375690).length < 2 ^ (prefixWord ++ tailWord_2375690).sum := by decide
  have hdescent : baseEnd_2375690 < baseStart_2375690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375709 : List Nat := [1, 4, 2, 2, 2, 3, 1, 2, 2, 3]
def baseStart_2375709 : Nat := 118140960795 + 2375709 * 2 ^ 59
def prefixEnd_2375709 : Nat := 4983230072969 + 3 ^ 40 * 2375709 * 2
def baseEnd_2375709 : Nat := 813253741474900507541213

theorem tailTrace_2375709 : CollatzResearch.WordTrace tailWord_2375709 prefixEnd_2375709 813253741474900507541213 := by
  unfold tailWord_2375709
  simp only [CollatzResearch.WordTrace]
  refine ⟨86649225750219506639794181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57766150500146337759862787 86649225750219506639794181)
  ·
    refine ⟨16246729828166157494961409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86649225750219506639794181 16246729828166157494961409)
    ·
      refine ⟨12185047371124618121221057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16246729828166157494961409 12185047371124618121221057)
      ·
        refine ⟨9138785528343463590915793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12185047371124618121221057 9138785528343463590915793)
        ·
          refine ⟨6854089146257597693186845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9138785528343463590915793 6854089146257597693186845)
          ·
            refine ⟨2570283429846599134945067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6854089146257597693186845 2570283429846599134945067)
            ·
              refine ⟨3855425144769898702417601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2570283429846599134945067 3855425144769898702417601)
              ·
                refine ⟨2891568858577424026813201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3855425144769898702417601 2891568858577424026813201)
                ·
                  refine ⟨2168676643933068020109901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2891568858577424026813201 2168676643933068020109901)
                  ·
                    refine ⟨813253741474900507541213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2168676643933068020109901 813253741474900507541213)
                    ·
                      rfl

theorem cell22_2375709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_2375709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2375709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2375709 prefixEnd_2375709 := by exact prefixLift 2375709
  have htrace : WordTrace (prefixWord ++ tailWord_2375709) baseStart_2375709 baseEnd_2375709 := by
    simpa [prefixWord, tailWord_2375709, baseEnd_2375709] using wordTrace_append hprefix tailTrace_2375709
  have hstable : (prefixWord ++ tailWord_2375709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375709).length < 2 ^ (prefixWord ++ tailWord_2375709).sum := by decide
  have hdescent : baseEnd_2375709 < baseStart_2375709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375812 : List Nat := [2, 3, 2, 1, 2, 1, 2, 5, 4]
def baseStart_2375812 : Nat := 118140960795 + 2375812 * 2 ^ 59
def prefixEnd_2375812 : Nat := 4983230072969 + 3 ^ 40 * 2375812 * 2
def baseEnd_2375812 : Nat := 271096333493280857405299

theorem tailTrace_2375812 : CollatzResearch.WordTrace tailWord_2375812 prefixEnd_2375812 271096333493280857405299 := by
  unfold tailWord_2375812
  simp only [CollatzResearch.WordTrace]
  refine ⟨43326491234423177615396845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57768654979230903487195793 43326491234423177615396845)
  ·
    refine ⟨16247434212908691605773817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43326491234423177615396845 16247434212908691605773817)
    ·
      refine ⟨12185575659681518704330363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16247434212908691605773817 12185575659681518704330363)
      ·
        refine ⟨18278363489522278056495545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12185575659681518704330363 18278363489522278056495545)
        ·
          refine ⟨13708772617141708542371659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18278363489522278056495545 13708772617141708542371659)
          ·
            refine ⟨20563158925712562813557489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13708772617141708542371659 20563158925712562813557489)
            ·
              refine ⟨15422369194284422110168117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20563158925712562813557489 15422369194284422110168117)
              ·
                refine ⟨1445847111964164572828261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15422369194284422110168117 1445847111964164572828261)
                ·
                  refine ⟨271096333493280857405299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1445847111964164572828261 271096333493280857405299)
                  ·
                    rfl

theorem cell22_2375812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_2375812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2375812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2375812 prefixEnd_2375812 := by exact prefixLift 2375812
  have htrace : WordTrace (prefixWord ++ tailWord_2375812) baseStart_2375812 baseEnd_2375812 := by
    simpa [prefixWord, tailWord_2375812, baseEnd_2375812] using wordTrace_append hprefix tailTrace_2375812
  have hstable : (prefixWord ++ tailWord_2375812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375812).length < 2 ^ (prefixWord ++ tailWord_2375812).sum := by decide
  have hdescent : baseEnd_2375812 < baseStart_2375812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375840 : List Nat := [2, 1, 1, 4, 2, 2, 3, 7]
def baseStart_2375840 : Nat := 118140960795 + 2375840 * 2 ^ 59
def prefixEnd_2375840 : Nat := 4983230072969 + 3 ^ 40 * 2375840 * 2
def baseEnd_2375840 : Nat := 90366509494673314723979

theorem tailTrace_2375840 : CollatzResearch.WordTrace tailWord_2375840 prefixEnd_2375840 90366509494673314723979 := by
  unfold tailWord_2375840
  simp only [CollatzResearch.WordTrace]
  refine ⟨43327001856372458006406487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57769335808496610675208649 43327001856372458006406487)
  ·
    refine ⟨64990502784558687009609731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43327001856372458006406487 64990502784558687009609731)
    ·
      refine ⟨97485754176838030514414597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64990502784558687009609731 97485754176838030514414597)
      ·
        refine ⟨18278578908157130721452737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97485754176838030514414597 18278578908157130721452737)
        ·
          refine ⟨13708934181117848041089553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18278578908157130721452737 13708934181117848041089553)
          ·
            refine ⟨10281700635838386030817165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13708934181117848041089553 10281700635838386030817165)
            ·
              refine ⟨3855637738439394761556437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10281700635838386030817165 3855637738439394761556437)
              ·
                refine ⟨90366509494673314723979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3855637738439394761556437 90366509494673314723979)
                ·
                  rfl

theorem cell22_2375840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 7].length) (baseStart_2375840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2375840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2375840 prefixEnd_2375840 := by exact prefixLift 2375840
  have htrace : WordTrace (prefixWord ++ tailWord_2375840) baseStart_2375840 baseEnd_2375840 := by
    simpa [prefixWord, tailWord_2375840, baseEnd_2375840] using wordTrace_append hprefix tailTrace_2375840
  have hstable : (prefixWord ++ tailWord_2375840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375840).length < 2 ^ (prefixWord ++ tailWord_2375840).sum := by decide
  have hdescent : baseEnd_2375840 < baseStart_2375840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375874 : List Nat := [3, 5, 1, 1, 1, 2, 9]
def baseStart_2375874 : Nat := 118140960795 + 2375874 * 2 ^ 59
def prefixEnd_2375874 : Nat := 4983230072969 + 3 ^ 40 * 2375874 * 2
def baseEnd_2375874 : Nat := 30122600901736854709841

theorem tailTrace_2375874 : CollatzResearch.WordTrace tailWord_2375874 prefixEnd_2375874 30122600901736854709841 := by
  unfold tailWord_2375874
  simp only [CollatzResearch.WordTrace]
  refine ⟨21663810948655434954887669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57770162529747826546367117 21663810948655434954887669)
  ·
    refine ⟨2030982276436447027020719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21663810948655434954887669 2030982276436447027020719)
    ·
      refine ⟨3046473414654670540531079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2030982276436447027020719 3046473414654670540531079)
      ·
        refine ⟨4569710121982005810796619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3046473414654670540531079 4569710121982005810796619)
        ·
          refine ⟨6854565182973008716194929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4569710121982005810796619 6854565182973008716194929)
          ·
            refine ⟨5140923887229756537146197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6854565182973008716194929 5140923887229756537146197)
            ·
              refine ⟨30122600901736854709841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5140923887229756537146197 30122600901736854709841)
              ·
                rfl

theorem cell22_2375874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 9].length) (baseStart_2375874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2375874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2375874 prefixEnd_2375874 := by exact prefixLift 2375874
  have htrace : WordTrace (prefixWord ++ tailWord_2375874) baseStart_2375874 baseEnd_2375874 := by
    simpa [prefixWord, tailWord_2375874, baseEnd_2375874] using wordTrace_append hprefix tailTrace_2375874
  have hstable : (prefixWord ++ tailWord_2375874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375874).length < 2 ^ (prefixWord ++ tailWord_2375874).sum := by decide
  have hdescent : baseEnd_2375874 < baseStart_2375874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375889 : List Nat := [1, 2, 2, 1, 2, 2, 4, 4, 1, 3]
def baseStart_2375889 : Nat := 118140960795 + 2375889 * 2 ^ 59
def prefixEnd_2375889 : Nat := 4983230072969 + 3 ^ 40 * 2375889 * 2
def baseEnd_2375889 : Nat := 813315359153440038040661

theorem tailTrace_2375889 : CollatzResearch.WordTrace tailWord_2375889 prefixEnd_2375889 813315359153440038040661 := by
  unfold tailWord_2375889
  simp only [CollatzResearch.WordTrace]
  refine ⟨86655790889567397381346721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57770527259711598254231147 86655790889567397381346721)
  ·
    refine ⟨64991843167175548036010041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86655790889567397381346721 64991843167175548036010041)
    ·
      refine ⟨48743882375381661027007531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64991843167175548036010041 48743882375381661027007531)
      ·
        refine ⟨73115823563072491540511297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48743882375381661027007531 73115823563072491540511297)
        ·
          refine ⟨54836867672304368655383473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73115823563072491540511297 54836867672304368655383473)
          ·
            refine ⟨41127650754228276491537605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54836867672304368655383473 41127650754228276491537605)
            ·
              refine ⟨7711434516417801842163301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41127650754228276491537605 7711434516417801842163301)
              ·
                refine ⟨1445893971828337845405619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7711434516417801842163301 1445893971828337845405619)
                ·
                  refine ⟨2168840957742506768108429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1445893971828337845405619 2168840957742506768108429)
                  ·
                    refine ⟨813315359153440038040661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2168840957742506768108429 813315359153440038040661)
                    ·
                      rfl

theorem cell22_2375889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 1, 3].length) (baseStart_2375889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2375889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2375889 prefixEnd_2375889 := by exact prefixLift 2375889
  have htrace : WordTrace (prefixWord ++ tailWord_2375889) baseStart_2375889 baseEnd_2375889 := by
    simpa [prefixWord, tailWord_2375889, baseEnd_2375889] using wordTrace_append hprefix tailTrace_2375889
  have hstable : (prefixWord ++ tailWord_2375889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375889).length < 2 ^ (prefixWord ++ tailWord_2375889).sum := by decide
  have hdescent : baseEnd_2375889 < baseStart_2375889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375966 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2375966 : Nat := 118140960795 + 2375966 * 2 ^ 59
def prefixEnd_2375966 : Nat := 4983230072969 + 3 ^ 40 * 2375966 * 2
def baseEnd_2375966 : Nat := 813341717827037503865425

theorem tailTrace_2375966 : CollatzResearch.WordTrace tailWord_2375966 prefixEnd_2375966 813341717827037503865425 := by
  unfold tailWord_2375966
  simp only [CollatzResearch.WordTrace]
  refine ⟨10832324913786054941487469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57772399540192293021266501 10832324913786054941487469)
  ·
    refine ⟨4062121842669770603057801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10832324913786054941487469 4062121842669770603057801)
    ·
      refine ⟨3046591382002327952293351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4062121842669770603057801 3046591382002327952293351)
      ·
        refine ⟨4569887073003491928440027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3046591382002327952293351 4569887073003491928440027)
        ·
          refine ⟨6854830609505237892660041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4569887073003491928440027 6854830609505237892660041)
          ·
            refine ⟨5141122957128928419495031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6854830609505237892660041 5141122957128928419495031)
            ·
              refine ⟨7711684435693392629242547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5141122957128928419495031 7711684435693392629242547)
              ·
                refine ⟨11567526653540088943863821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7711684435693392629242547 11567526653540088943863821)
                ·
                  refine ⟨4337822495077533353948933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11567526653540088943863821 4337822495077533353948933)
                  ·
                    refine ⟨813341717827037503865425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4337822495077533353948933 813341717827037503865425)
                    ·
                      rfl

theorem cell22_2375966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2375966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2375966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2375966 prefixEnd_2375966 := by exact prefixLift 2375966
  have htrace : WordTrace (prefixWord ++ tailWord_2375966) baseStart_2375966 baseEnd_2375966 := by
    simpa [prefixWord, tailWord_2375966, baseEnd_2375966] using wordTrace_append hprefix tailTrace_2375966
  have hstable : (prefixWord ++ tailWord_2375966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375966).length < 2 ^ (prefixWord ++ tailWord_2375966).sum := by decide
  have hdescent : baseEnd_2375966 < baseStart_2375966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2375998 : List Nat := [4, 2, 1, 2, 1, 4, 2, 2, 4]
def baseStart_2375998 : Nat := 118140960795 + 2375998 * 2 ^ 59
def prefixEnd_2375998 : Nat := 4983230072969 + 3 ^ 40 * 2375998 * 2
def baseEnd_2375998 : Nat := 271117557360333362355109

theorem tailTrace_2375998 : CollatzResearch.WordTrace tailWord_2375998 prefixEnd_2375998 271117557360333362355109 := by
  unfold tailWord_2375998
  simp only [CollatzResearch.WordTrace]
  refine ⟨10832470805771563624633081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57773177630781672664709765 10832470805771563624633081)
  ·
    refine ⟨8124353104328672718474811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10832470805771563624633081 8124353104328672718474811)
    ·
      refine ⟨12186529656493009077712217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8124353104328672718474811 12186529656493009077712217)
      ·
        refine ⟨9139897242369756808284163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12186529656493009077712217 9139897242369756808284163)
        ·
          refine ⟨13709845863554635212426245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9139897242369756808284163 13709845863554635212426245)
          ·
            refine ⟨2570596099416494102329921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13709845863554635212426245 2570596099416494102329921)
            ·
              refine ⟨1927947074562370576747441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2570596099416494102329921 1927947074562370576747441)
              ·
                refine ⟨1445960305921777932560581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1927947074562370576747441 1445960305921777932560581)
                ·
                  refine ⟨271117557360333362355109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1445960305921777932560581 271117557360333362355109)
                  ·
                    rfl

theorem cell22_2375998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_2375998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2375998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2375998 prefixEnd_2375998 := by exact prefixLift 2375998
  have htrace : WordTrace (prefixWord ++ tailWord_2375998) baseStart_2375998 baseEnd_2375998 := by
    simpa [prefixWord, tailWord_2375998, baseEnd_2375998] using wordTrace_append hprefix tailTrace_2375998
  have hstable : (prefixWord ++ tailWord_2375998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2375998).length < 2 ^ (prefixWord ++ tailWord_2375998).sum := by decide
  have hdescent : baseEnd_2375998 < baseStart_2375998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2375998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376028 : List Nat := [2, 2, 4, 3, 1, 2, 1, 1, 2, 4]
def baseStart_2376028 : Nat := 118140960795 + 2376028 * 2 ^ 59
def prefixEnd_2376028 : Nat := 4983230072969 + 3 ^ 40 * 2376028 * 2
def baseEnd_2376028 : Nat := 813362941694090008815235

theorem tailTrace_2376028 : CollatzResearch.WordTrace tailWord_2376028 prefixEnd_2376028 813362941694090008815235 := by
  unfold tailWord_2376028
  simp only [CollatzResearch.WordTrace]
  refine ⟨43330430318031912060328369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57773907090709216080437825 43330430318031912060328369)
  ·
    refine ⟨32497822738523934045246277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43330430318031912060328369 32497822738523934045246277)
    ·
      refine ⟨6093341763473237633483677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32497822738523934045246277 6093341763473237633483677)
      ·
        refine ⟨2285003161302464112556379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6093341763473237633483677 2285003161302464112556379)
        ·
          refine ⟨3427504741953696168834569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2285003161302464112556379 3427504741953696168834569)
          ·
            refine ⟨2570628556465272126625927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3427504741953696168834569 2570628556465272126625927)
            ·
              refine ⟨3855942834697908189938891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2570628556465272126625927 3855942834697908189938891)
              ·
                refine ⟨5783914252046862284908337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3855942834697908189938891 5783914252046862284908337)
                ·
                  refine ⟨4337935689035146713681253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5783914252046862284908337 4337935689035146713681253)
                  ·
                    refine ⟨813362941694090008815235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4337935689035146713681253 813362941694090008815235)
                    ·
                      rfl

theorem cell22_2376028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_2376028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376028 prefixEnd_2376028 := by exact prefixLift 2376028
  have htrace : WordTrace (prefixWord ++ tailWord_2376028) baseStart_2376028 baseEnd_2376028 := by
    simpa [prefixWord, tailWord_2376028, baseEnd_2376028] using wordTrace_append hprefix tailTrace_2376028
  have hstable : (prefixWord ++ tailWord_2376028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376028).length < 2 ^ (prefixWord ++ tailWord_2376028).sum := by decide
  have hdescent : baseEnd_2376028 < baseStart_2376028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376041 : List Nat := [1, 2, 1, 1, 1, 3, 6, 3, 1, 3]
def baseStart_2376041 : Nat := 118140960795 + 2376041 * 2 ^ 59
def prefixEnd_2376041 : Nat := 4983230072969 + 3 ^ 40 * 2376041 * 2
def baseEnd_2376041 : Nat := 813367391859762308240195

theorem tailTrace_2376041 : CollatzResearch.WordTrace tailWord_2376041 prefixEnd_2376041 813367391859762308240195 := by
  unfold tailWord_2376041
  simp only [CollatzResearch.WordTrace]
  refine ⟨86661334785016727340879977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57774223190011151560586651 86661334785016727340879977)
  ·
    refine ⟨64996001088762545505659983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86661334785016727340879977 64996001088762545505659983)
    ·
      refine ⟨97494001633143818258489975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64996001088762545505659983 97494001633143818258489975)
      ·
        refine ⟨146241002449715727387734963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97494001633143818258489975 146241002449715727387734963)
        ·
          refine ⟨219361503674573591081602445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146241002449715727387734963 219361503674573591081602445)
          ·
            refine ⟨82260563877965096655600917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219361503674573591081602445 82260563877965096655600917)
            ·
              refine ⟨3855963931779613905731293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82260563877965096655600917 3855963931779613905731293)
              ·
                refine ⟨1445986474417355214649235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3855963931779613905731293 1445986474417355214649235)
                ·
                  refine ⟨2168979711626032821973853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1445986474417355214649235 2168979711626032821973853)
                  ·
                    refine ⟨813367391859762308240195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2168979711626032821973853 813367391859762308240195)
                    ·
                      rfl

theorem cell22_2376041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 1, 3].length) (baseStart_2376041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376041 prefixEnd_2376041 := by exact prefixLift 2376041
  have htrace : WordTrace (prefixWord ++ tailWord_2376041) baseStart_2376041 baseEnd_2376041 := by
    simpa [prefixWord, tailWord_2376041, baseEnd_2376041] using wordTrace_append hprefix tailTrace_2376041
  have hstable : (prefixWord ++ tailWord_2376041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376041).length < 2 ^ (prefixWord ++ tailWord_2376041).sum := by decide
  have hdescent : baseEnd_2376041 < baseStart_2376041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376114 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 4, 3]
def baseStart_2376114 : Nat := 118140960795 + 2376114 * 2 ^ 59
def prefixEnd_2376114 : Nat := 4983230072969 + 3 ^ 40 * 2376114 * 2
def baseEnd_2376114 : Nat := 813392381251614451164971

theorem tailTrace_2376114 : CollatzResearch.WordTrace tailWord_2376114 prefixEnd_2376114 813392381251614451164971 := by
  unfold tailWord_2376114
  simp only [CollatzResearch.WordTrace]
  refine ⟨21665999328438065202071849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57775998209168173872191597 21665999328438065202071849)
  ·
    refine ⟨16249499496328548901553887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21665999328438065202071849 16249499496328548901553887)
    ·
      refine ⟨24374249244492823352330831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16249499496328548901553887 24374249244492823352330831)
      ·
        refine ⟨36561373866739235028496247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24374249244492823352330831 36561373866739235028496247)
        ·
          refine ⟨54842060800108852542744371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36561373866739235028496247 54842060800108852542744371)
          ·
            refine ⟨82263091200163278814116557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54842060800108852542744371 82263091200163278814116557)
            ·
              refine ⟨30848659200061229555293709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82263091200163278814116557 30848659200061229555293709)
              ·
                refine ⟨11568247200022961083235141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30848659200061229555293709 11568247200022961083235141)
                ·
                  refine ⟨2169046350004305203106589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11568247200022961083235141 2169046350004305203106589)
                  ·
                    refine ⟨813392381251614451164971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2169046350004305203106589 813392381251614451164971)
                    ·
                      rfl

theorem cell22_2376114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_2376114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376114 prefixEnd_2376114 := by exact prefixLift 2376114
  have htrace : WordTrace (prefixWord ++ tailWord_2376114) baseStart_2376114 baseEnd_2376114 := by
    simpa [prefixWord, tailWord_2376114, baseEnd_2376114] using wordTrace_append hprefix tailTrace_2376114
  have hstable : (prefixWord ++ tailWord_2376114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376114).length < 2 ^ (prefixWord ++ tailWord_2376114).sum := by decide
  have hdescent : baseEnd_2376114 < baseStart_2376114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376174 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_2376174 : Nat := 118140960795 + 2376174 * 2 ^ 59
def prefixEnd_2376174 : Nat := 4983230072969 + 3 ^ 40 * 2376174 * 2
def baseEnd_2376174 : Nat := 813412920477794294664787

theorem tailTrace_2376174 : CollatzResearch.WordTrace tailWord_2376174 prefixEnd_2376174 813412920477794294664787 := by
  unfold tailWord_2376174
  simp only [CollatzResearch.WordTrace]
  refine ⟨10833273211691861381933947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57777457129023260703647717 10833273211691861381933947)
  ·
    refine ⟨16249909817537792072900921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10833273211691861381933947 16249909817537792072900921)
    ·
      refine ⟨12187432363153344054675691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16249909817537792072900921 12187432363153344054675691)
      ·
        refine ⟨18281148544730016082013537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12187432363153344054675691 18281148544730016082013537)
        ·
          refine ⟨13710861408547512061510153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18281148544730016082013537 13710861408547512061510153)
          ·
            refine ⟨10283146056410634046132615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13710861408547512061510153 10283146056410634046132615)
            ·
              refine ⟨15424719084615951069198923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10283146056410634046132615 15424719084615951069198923)
              ·
                refine ⟨23137078626923926603798385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15424719084615951069198923 23137078626923926603798385)
                ·
                  refine ⟨17352808970192944952848789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23137078626923926603798385 17352808970192944952848789)
                  ·
                    refine ⟨813412920477794294664787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17352808970192944952848789 813412920477794294664787)
                    ·
                      rfl

theorem cell22_2376174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_2376174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376174 prefixEnd_2376174 := by exact prefixLift 2376174
  have htrace : WordTrace (prefixWord ++ tailWord_2376174) baseStart_2376174 baseEnd_2376174 := by
    simpa [prefixWord, tailWord_2376174, baseEnd_2376174] using wordTrace_append hprefix tailTrace_2376174
  have hstable : (prefixWord ++ tailWord_2376174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376174).length < 2 ^ (prefixWord ++ tailWord_2376174).sum := by decide
  have hdescent : baseEnd_2376174 < baseStart_2376174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376178 : List Nat := [3, 2, 1, 4, 3, 1, 1, 7]
def baseStart_2376178 : Nat := 118140960795 + 2376178 * 2 ^ 59
def prefixEnd_2376178 : Nat := 4983230072969 + 3 ^ 40 * 2376178 * 2
def baseEnd_2376178 : Nat := 90379365528837735284975

theorem tailTrace_2376178 : CollatzResearch.WordTrace tailWord_2376178 prefixEnd_2376178 90379365528837735284975 := by
  unfold tailWord_2376178
  simp only [CollatzResearch.WordTrace]
  refine ⟨21666582896380099934654297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57777554390346933159078125 21666582896380099934654297)
  ·
    refine ⟨16249937172285074950990723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21666582896380099934654297 16249937172285074950990723)
    ·
      refine ⟨24374905758427612426486085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16249937172285074950990723 24374905758427612426486085)
      ·
        refine ⟨4570294829705177329966141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24374905758427612426486085 4570294829705177329966141)
        ·
          refine ⟨1713860561139441498737303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4570294829705177329966141 1713860561139441498737303)
          ·
            refine ⟨2570790841709162248105955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1713860561139441498737303 2570790841709162248105955)
            ·
              refine ⟨3856186262563743372158933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2570790841709162248105955 3856186262563743372158933)
              ·
                refine ⟨90379365528837735284975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3856186262563743372158933 90379365528837735284975)
                ·
                  rfl

theorem cell22_2376178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 7].length) (baseStart_2376178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376178 prefixEnd_2376178 := by exact prefixLift 2376178
  have htrace : WordTrace (prefixWord ++ tailWord_2376178) baseStart_2376178 baseEnd_2376178 := by
    simpa [prefixWord, tailWord_2376178, baseEnd_2376178] using wordTrace_append hprefix tailTrace_2376178
  have hstable : (prefixWord ++ tailWord_2376178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376178).length < 2 ^ (prefixWord ++ tailWord_2376178).sum := by decide
  have hdescent : baseEnd_2376178 < baseStart_2376178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376189 : List Nat := [1, 4, 1, 1, 1, 3, 1, 5, 5]
def baseStart_2376189 : Nat := 118140960795 + 2376189 * 2 ^ 59
def prefixEnd_2376189 : Nat := 4983230072969 + 3 ^ 40 * 2376189 * 2
def baseEnd_2376189 : Nat := 271139351761446418513247

theorem tailTrace_2376189 : CollatzResearch.WordTrace tailWord_2376189 prefixEnd_2376189 271139351761446418513247 := by
  unfold tailWord_2376189
  simp only [CollatzResearch.WordTrace]
  refine ⟨86666732788480548617267621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57777821858987032411511747 86666732788480548617267621)
  ·
    refine ⟨16250012397840102865737679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86666732788480548617267621 16250012397840102865737679)
    ·
      refine ⟨24375018596760154298606519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16250012397840102865737679 24375018596760154298606519)
      ·
        refine ⟨36562527895140231447909779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24375018596760154298606519 36562527895140231447909779)
        ·
          refine ⟨54843791842710347171864669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36562527895140231447909779 54843791842710347171864669)
          ·
            refine ⟨20566421941016380189449251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54843791842710347171864669 20566421941016380189449251)
            ·
              refine ⟨30849632911524570284173877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20566421941016380189449251 30849632911524570284173877)
              ·
                refine ⟨2892153085455428464141301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30849632911524570284173877 2892153085455428464141301)
                ·
                  refine ⟨271139351761446418513247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2892153085455428464141301 271139351761446418513247)
                  ·
                    rfl

theorem cell22_2376189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_2376189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376189 prefixEnd_2376189 := by exact prefixLift 2376189
  have htrace : WordTrace (prefixWord ++ tailWord_2376189) baseStart_2376189 baseEnd_2376189 := by
    simpa [prefixWord, tailWord_2376189, baseEnd_2376189] using wordTrace_append hprefix tailTrace_2376189
  have hstable : (prefixWord ++ tailWord_2376189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376189).length < 2 ^ (prefixWord ++ tailWord_2376189).sum := by decide
  have hdescent : baseEnd_2376189 < baseStart_2376189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376253 : List Nat := [1, 4, 1, 3, 2, 2, 2, 2, 1, 4]
def baseStart_2376253 : Nat := 118140960795 + 2376253 * 2 ^ 59
def prefixEnd_2376253 : Nat := 4983230072969 + 3 ^ 40 * 2376253 * 2
def baseEnd_2376253 : Nat := 813439963792264421939545

theorem tailTrace_2376253 : CollatzResearch.WordTrace tailWord_2376253 prefixEnd_2376253 813439963792264421939545 := by
  unfold tailWord_2376253
  simp only [CollatzResearch.WordTrace]
  refine ⟨86669067060248687547597413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57779378040165791698398275 86669067060248687547597413)
  ·
    refine ⟨16250450073796628915174515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86669067060248687547597413 16250450073796628915174515)
    ·
      refine ⟨24375675110694943372761773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16250450073796628915174515 24375675110694943372761773)
      ·
        refine ⟨9140878166510603764785665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24375675110694943372761773 9140878166510603764785665)
        ·
          refine ⟨6855658624882952823589249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9140878166510603764785665 6855658624882952823589249)
          ·
            refine ⟨5141743968662214617691937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6855658624882952823589249 5141743968662214617691937)
            ·
              refine ⟨3856307976496660963268953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5141743968662214617691937 3856307976496660963268953)
              ·
                refine ⟨2892230982372495722451715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3856307976496660963268953 2892230982372495722451715)
                ·
                  refine ⟨4338346473558743583677573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2892230982372495722451715 4338346473558743583677573)
                  ·
                    refine ⟨813439963792264421939545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4338346473558743583677573 813439963792264421939545)
                    ·
                      rfl

theorem cell22_2376253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_2376253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376253 prefixEnd_2376253 := by exact prefixLift 2376253
  have htrace : WordTrace (prefixWord ++ tailWord_2376253) baseStart_2376253 baseEnd_2376253 := by
    simpa [prefixWord, tailWord_2376253, baseEnd_2376253] using wordTrace_append hprefix tailTrace_2376253
  have hstable : (prefixWord ++ tailWord_2376253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376253).length < 2 ^ (prefixWord ++ tailWord_2376253).sum := by decide
  have hdescent : baseEnd_2376253 < baseStart_2376253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376264 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 6, 4]
def baseStart_2376264 : Nat := 118140960795 + 2376264 * 2 ^ 59
def prefixEnd_2376264 : Nat := 4983230072969 + 3 ^ 40 * 2376264 * 2
def baseEnd_2376264 : Nat := 813443729317064059914511

theorem tailTrace_2376264 : CollatzResearch.WordTrace tailWord_2376264 prefixEnd_2376264 813443729317064059914511 := by
  unfold tailWord_2376264
  simp only [CollatzResearch.WordTrace]
  refine ⟨43334734131604418213123923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57779645508805890950831897 43334734131604418213123923)
  ·
    refine ⟨65002101197406627319685885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43334734131604418213123923 65002101197406627319685885)
    ·
      refine ⟨24375787949027485244882207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65002101197406627319685885 24375787949027485244882207)
      ·
        refine ⟨36563681923541227867323311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24375787949027485244882207 36563681923541227867323311)
        ·
          refine ⟨54845522885311841800984967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36563681923541227867323311 54845522885311841800984967)
          ·
            refine ⟨82268284327967762701477451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54845522885311841800984967 82268284327967762701477451)
            ·
              refine ⟨123402426491951644052216177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82268284327967762701477451 123402426491951644052216177)
              ·
                refine ⟨92551819868963733039162133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123402426491951644052216177 92551819868963733039162133)
                ·
                  refine ⟨4338366556357674986210725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92551819868963733039162133 4338366556357674986210725)
                  ·
                    refine ⟨813443729317064059914511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4338366556357674986210725 813443729317064059914511)
                    ·
                      rfl

theorem cell22_2376264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_2376264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376264 prefixEnd_2376264 := by exact prefixLift 2376264
  have htrace : WordTrace (prefixWord ++ tailWord_2376264) baseStart_2376264 baseEnd_2376264 := by
    simpa [prefixWord, tailWord_2376264, baseEnd_2376264] using wordTrace_append hprefix tailTrace_2376264
  have hstable : (prefixWord ++ tailWord_2376264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376264).length < 2 ^ (prefixWord ++ tailWord_2376264).sum := by decide
  have hdescent : baseEnd_2376264 < baseStart_2376264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376266 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 4, 3]
def baseStart_2376266 : Nat := 118140960795 + 2376266 * 2 ^ 59
def prefixEnd_2376266 : Nat := 4983230072969 + 3 ^ 40 * 2376266 * 2
def baseEnd_2376266 : Nat := 813444413957936721364505

theorem tailTrace_2376266 : CollatzResearch.WordTrace tailWord_2376266 prefixEnd_2376266 813444413957936721364505 := by
  unfold tailWord_2376266
  simp only [CollatzResearch.WordTrace]
  refine ⟨21667385302300397691955163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57779694139467727178547101 21667385302300397691955163)
  ·
    refine ⟨32501077953450596537932745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21667385302300397691955163 32501077953450596537932745)
    ·
      refine ⟨24375808465087947403449559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32501077953450596537932745 24375808465087947403449559)
      ·
        refine ⟨36563712697631921105174339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24375808465087947403449559 36563712697631921105174339)
        ·
          refine ⟨54845569046447881657761509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36563712697631921105174339 54845569046447881657761509)
          ·
            refine ⟨10283544196208977810830283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54845569046447881657761509 10283544196208977810830283)
            ·
              refine ⟨15425316294313466716245425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10283544196208977810830283 15425316294313466716245425)
              ·
                refine ⟨11568987220735100037184069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15425316294313466716245425 11568987220735100037184069)
                ·
                  refine ⟨2169185103887831256972013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11568987220735100037184069 2169185103887831256972013)
                  ·
                    refine ⟨813444413957936721364505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2169185103887831256972013 813444413957936721364505)
                    ·
                      rfl

theorem cell22_2376266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_2376266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376266 prefixEnd_2376266 := by exact prefixLift 2376266
  have htrace : WordTrace (prefixWord ++ tailWord_2376266) baseStart_2376266 baseEnd_2376266 := by
    simpa [prefixWord, tailWord_2376266, baseEnd_2376266] using wordTrace_append hprefix tailTrace_2376266
  have hstable : (prefixWord ++ tailWord_2376266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376266).length < 2 ^ (prefixWord ++ tailWord_2376266).sum := by decide
  have hdescent : baseEnd_2376266 < baseStart_2376266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376311 : List Nat := [1, 1, 3, 1, 1, 3, 2, 4, 3, 3]
def baseStart_2376311 : Nat := 118140960795 + 2376311 * 2 ^ 59
def prefixEnd_2376311 : Nat := 4983230072969 + 3 ^ 40 * 2376311 * 2
def baseEnd_2376311 : Nat := 813459818377571603989367

theorem tailTrace_2376311 : CollatzResearch.WordTrace tailWord_2376311 prefixEnd_2376311 813459818377571603989367 := by
  unfold tailWord_2376311
  simp only [CollatzResearch.WordTrace]
  refine ⟨86671182494038563453208787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57780788329359042302139191 86671182494038563453208787)
  ·
    refine ⟨130006773741057845179813181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86671182494038563453208787 130006773741057845179813181)
    ·
      refine ⟨48752540152896691942429943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130006773741057845179813181 48752540152896691942429943)
      ·
        refine ⟨73128810229345037913644915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48752540152896691942429943 73128810229345037913644915)
        ·
          refine ⟨109693215344017556870467373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73128810229345037913644915 109693215344017556870467373)
          ·
            refine ⟨41134955754006583826425265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109693215344017556870467373 41134955754006583826425265)
            ·
              refine ⟨30851216815504937869818949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41134955754006583826425265 30851216815504937869818949)
              ·
                refine ⟨5784603152907175850591053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30851216815504937869818949 5784603152907175850591053)
                ·
                  refine ⟨2169226182340190943971645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5784603152907175850591053 2169226182340190943971645)
                  ·
                    refine ⟨813459818377571603989367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2169226182340190943971645 813459818377571603989367)
                    ·
                      rfl

theorem cell22_2376311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 3].length) (baseStart_2376311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376311 prefixEnd_2376311 := by exact prefixLift 2376311
  have htrace : WordTrace (prefixWord ++ tailWord_2376311) baseStart_2376311 baseEnd_2376311 := by
    simpa [prefixWord, tailWord_2376311, baseEnd_2376311] using wordTrace_append hprefix tailTrace_2376311
  have hstable : (prefixWord ++ tailWord_2376311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376311).length < 2 ^ (prefixWord ++ tailWord_2376311).sum := by decide
  have hdescent : baseEnd_2376311 < baseStart_2376311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376339 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 4, 5]
def baseStart_2376339 : Nat := 118140960795 + 2376339 * 2 ^ 59
def prefixEnd_2376339 : Nat := 4983230072969 + 3 ^ 40 * 2376339 * 2
def baseEnd_2376339 : Nat := 813469403349788864289281

theorem tailTrace_2376339 : CollatzResearch.WordTrace tailWord_2376339 prefixEnd_2376339 813469403349788864289281 := by
  unfold tailWord_2376339
  simp only [CollatzResearch.WordTrace]
  refine ⟨86672203737937124235228071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57781469158624749490152047 86672203737937124235228071)
  ·
    refine ⟨130008305606905686352842107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86672203737937124235228071 130008305606905686352842107)
    ·
      refine ⟨195012458410358529529263161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130008305606905686352842107 195012458410358529529263161)
      ·
        refine ⟨146259343807768897146947371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195012458410358529529263161 146259343807768897146947371)
        ·
          refine ⟨219389015711653345720421057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146259343807768897146947371 219389015711653345720421057)
          ·
            refine ⟨164541761783740009290315793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219389015711653345720421057 164541761783740009290315793)
            ·
              refine ⟨123406321337805006967736845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164541761783740009290315793 123406321337805006967736845)
              ·
                refine ⟨46277370501676877612901317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123406321337805006967736845 46277370501676877612901317)
                ·
                  refine ⟨8677006969064414552418997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46277370501676877612901317 8677006969064414552418997)
                  ·
                    refine ⟨813469403349788864289281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8677006969064414552418997 813469403349788864289281)
                    ·
                      rfl

theorem cell22_2376339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 5].length) (baseStart_2376339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376339 prefixEnd_2376339 := by exact prefixLift 2376339
  have htrace : WordTrace (prefixWord ++ tailWord_2376339) baseStart_2376339 baseEnd_2376339 := by
    simpa [prefixWord, tailWord_2376339, baseEnd_2376339] using wordTrace_append hprefix tailTrace_2376339
  have hstable : (prefixWord ++ tailWord_2376339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376339).length < 2 ^ (prefixWord ++ tailWord_2376339).sum := by decide
  have hdescent : baseEnd_2376339 < baseStart_2376339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376356 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 2, 5]
def baseStart_2376356 : Nat := 118140960795 + 2376356 * 2 ^ 59
def prefixEnd_2376356 : Nat := 4983230072969 + 3 ^ 40 * 2376356 * 2
def baseEnd_2376356 : Nat := 813475222797206486614229

theorem tailTrace_2376356 : CollatzResearch.WordTrace tailWord_2376356 prefixEnd_2376356 813475222797206486614229 := by
  unfold tailWord_2376356
  simp only [CollatzResearch.WordTrace]
  refine ⟨43336411889437768069298461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57781882519250357425731281 43336411889437768069298461)
  ·
    refine ⟨16251154458539163025986923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43336411889437768069298461 16251154458539163025986923)
    ·
      refine ⟨24376731687808744538980385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16251154458539163025986923 24376731687808744538980385)
      ·
        refine ⟨18282548765856558404235289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24376731687808744538980385 18282548765856558404235289)
        ·
          refine ⟨13711911574392418803176467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18282548765856558404235289 13711911574392418803176467)
          ·
            refine ⟨20567867361588628204764701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13711911574392418803176467 20567867361588628204764701)
            ·
              refine ⟨7712950260595735576786763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20567867361588628204764701 7712950260595735576786763)
              ·
                refine ⟨11569425390893603365180145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7712950260595735576786763 11569425390893603365180145)
                ·
                  refine ⟨8677069043170202523885109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11569425390893603365180145 8677069043170202523885109)
                  ·
                    refine ⟨813475222797206486614229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8677069043170202523885109 813475222797206486614229)
                    ·
                      rfl

theorem cell22_2376356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_2376356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376356 prefixEnd_2376356 := by exact prefixLift 2376356
  have htrace : WordTrace (prefixWord ++ tailWord_2376356) baseStart_2376356 baseEnd_2376356 := by
    simpa [prefixWord, tailWord_2376356, baseEnd_2376356] using wordTrace_append hprefix tailTrace_2376356
  have hstable : (prefixWord ++ tailWord_2376356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376356).length < 2 ^ (prefixWord ++ tailWord_2376356).sum := by decide
  have hdescent : baseEnd_2376356 < baseStart_2376356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376362 : List Nat := [3, 1, 5, 2, 1, 1, 1, 2, 3, 3]
def baseStart_2376362 : Nat := 118140960795 + 2376362 * 2 ^ 59
def prefixEnd_2376362 : Nat := 4983230072969 + 3 ^ 40 * 2376362 * 2
def baseEnd_2376362 : Nat := 813477276719824470964211

theorem tailTrace_2376362 : CollatzResearch.WordTrace tailWord_2376362 prefixEnd_2376362 813477276719824470964211 := by
  unfold tailWord_2376362
  simp only [CollatzResearch.WordTrace]
  refine ⟨21668260654213449790828835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57782028411235866108876893 21668260654213449790828835)
  ·
    refine ⟨32502390981320174686243253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21668260654213449790828835 32502390981320174686243253)
    ·
      refine ⟨3047099154498766376835305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32502390981320174686243253 3047099154498766376835305)
      ·
        refine ⟨2285324365874074782626479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3047099154498766376835305 2285324365874074782626479)
        ·
          refine ⟨3427986548811112173939719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2285324365874074782626479 3427986548811112173939719)
          ·
            refine ⟨5141979823216668260909579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3427986548811112173939719 5141979823216668260909579)
            ·
              refine ⟨7712969734825002391364369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5141979823216668260909579 7712969734825002391364369)
              ·
                refine ⟨5784727301118751793523277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7712969734825002391364369 5784727301118751793523277)
                ·
                  refine ⟨2169272737919531922571229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5784727301118751793523277 2169272737919531922571229)
                  ·
                    refine ⟨813477276719824470964211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2169272737919531922571229 813477276719824470964211)
                    ·
                      rfl

theorem cell22_2376362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_2376362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376362 prefixEnd_2376362 := by exact prefixLift 2376362
  have htrace : WordTrace (prefixWord ++ tailWord_2376362) baseStart_2376362 baseEnd_2376362 := by
    simpa [prefixWord, tailWord_2376362, baseEnd_2376362] using wordTrace_append hprefix tailTrace_2376362
  have hstable : (prefixWord ++ tailWord_2376362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376362).length < 2 ^ (prefixWord ++ tailWord_2376362).sum := by decide
  have hdescent : baseEnd_2376362 < baseStart_2376362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376371 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 3, 4]
def baseStart_2376371 : Nat := 118140960795 + 2376371 * 2 ^ 59
def prefixEnd_2376371 : Nat := 4983230072969 + 3 ^ 40 * 2376371 * 2
def baseEnd_2376371 : Nat := 813480357603751447489183

theorem tailTrace_2376371 : CollatzResearch.WordTrace tailWord_2376371 prefixEnd_2376371 813480357603751447489183 := by
  unfold tailWord_2376371
  simp only [CollatzResearch.WordTrace]
  refine ⟨86673370873821193700392967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57782247249214129133595311 86673370873821193700392967)
  ·
    refine ⟨130010056310731790550589451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86673370873821193700392967 130010056310731790550589451)
    ·
      refine ⟨195015084466097685825884177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130010056310731790550589451 195015084466097685825884177)
      ·
        refine ⟨146261313349573264369413133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195015084466097685825884177 146261313349573264369413133)
        ·
          refine ⟨54847992506089974138529925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146261313349573264369413133 54847992506089974138529925)
          ·
            refine ⟨10283998594891870150974361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54847992506089974138529925 10283998594891870150974361)
            ·
              refine ⟨7712998946168902613230771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10283998594891870150974361 7712998946168902613230771)
              ·
                refine ⟨11569498419253353919846157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7712998946168902613230771 11569498419253353919846157)
                ·
                  refine ⟨4338561907220007719942309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11569498419253353919846157 4338561907220007719942309)
                  ·
                    refine ⟨813480357603751447489183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4338561907220007719942309 813480357603751447489183)
                    ·
                      rfl

theorem cell22_2376371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 4].length) (baseStart_2376371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376371 prefixEnd_2376371 := by exact prefixLift 2376371
  have htrace : WordTrace (prefixWord ++ tailWord_2376371) baseStart_2376371 baseEnd_2376371 := by
    simpa [prefixWord, tailWord_2376371, baseEnd_2376371] using wordTrace_append hprefix tailTrace_2376371
  have hstable : (prefixWord ++ tailWord_2376371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376371).length < 2 ^ (prefixWord ++ tailWord_2376371).sum := by decide
  have hdescent : baseEnd_2376371 < baseStart_2376371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376431 : List Nat := [1, 1, 2, 1, 5, 3, 1, 8]
def baseStart_2376431 : Nat := 118140960795 + 2376431 * 2 ^ 59
def prefixEnd_2376431 : Nat := 4983230072969 + 3 ^ 40 * 2376431 * 2
def baseEnd_2376431 : Nat := 90388988536659032332111

theorem tailTrace_2376431 : CollatzResearch.WordTrace tailWord_2376431 prefixEnd_2376431 90388988536659032332111 := by
  unfold tailWord_2376431
  simp only [CollatzResearch.WordTrace]
  refine ⟨86675559253603823947577147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57783706169069215965051431 86675559253603823947577147)
  ·
    refine ⟨130013338880405735921365721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86675559253603823947577147 130013338880405735921365721)
    ·
      refine ⟨97510004160304301941024291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130013338880405735921365721 97510004160304301941024291)
      ·
        refine ⟨146265006240456452911536437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97510004160304301941024291 146265006240456452911536437)
        ·
          refine ⟨13712344335042792460456541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146265006240456452911536437 13712344335042792460456541)
          ·
            refine ⟨5142129125641047172671203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13712344335042792460456541 5142129125641047172671203)
            ·
              refine ⟨7713193688461570759006805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5142129125641047172671203 7713193688461570759006805)
              ·
                refine ⟨90388988536659032332111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7713193688461570759006805 90388988536659032332111)
                ·
                  rfl

theorem cell22_2376431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 8].length) (baseStart_2376431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376431 prefixEnd_2376431 := by exact prefixLift 2376431
  have htrace : WordTrace (prefixWord ++ tailWord_2376431) baseStart_2376431 baseEnd_2376431 := by
    simpa [prefixWord, tailWord_2376431, baseEnd_2376431] using wordTrace_append hprefix tailTrace_2376431
  have hstable : (prefixWord ++ tailWord_2376431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376431).length < 2 ^ (prefixWord ++ tailWord_2376431).sum := by decide
  have hdescent : baseEnd_2376431 < baseStart_2376431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376450 : List Nat := [3, 4, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_2376450 : Nat := 118140960795 + 2376450 * 2 ^ 59
def prefixEnd_2376450 : Nat := 4983230072969 + 3 ^ 40 * 2376450 * 2
def baseEnd_2376450 : Nat := 813507400918221574763941

theorem tailTrace_2376450 : CollatzResearch.WordTrace tailWord_2376450 prefixEnd_2376450 813507400918221574763941 := by
  unfold tailWord_2376450
  simp only [CollatzResearch.WordTrace]
  refine ⟨21669063060133747548129701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57784168160356660128345869 21669063060133747548129701)
  ·
    refine ⟨4062949323775077665274319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21669063060133747548129701 4062949323775077665274319)
    ·
      refine ⟨6094423985662616497911479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4062949323775077665274319 6094423985662616497911479)
      ·
        refine ⟨9141635978493924746867219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6094423985662616497911479 9141635978493924746867219)
        ·
          refine ⟨13712453967740887120300829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9141635978493924746867219 13712453967740887120300829)
          ·
            refine ⟨5142170237902832670112811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13712453967740887120300829 5142170237902832670112811)
            ·
              refine ⟨7713255356854249005169217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5142170237902832670112811 7713255356854249005169217)
              ·
                refine ⟨5784941517640686753876913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7713255356854249005169217 5784941517640686753876913)
                ·
                  refine ⟨4338706138230515065407685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5784941517640686753876913 4338706138230515065407685)
                  ·
                    refine ⟨813507400918221574763941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4338706138230515065407685 813507400918221574763941)
                    ·
                      rfl

theorem cell22_2376450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_2376450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376450 prefixEnd_2376450 := by exact prefixLift 2376450
  have htrace : WordTrace (prefixWord ++ tailWord_2376450) baseStart_2376450 baseEnd_2376450 := by
    simpa [prefixWord, tailWord_2376450, baseEnd_2376450] using wordTrace_append hprefix tailTrace_2376450
  have hstable : (prefixWord ++ tailWord_2376450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376450).length < 2 ^ (prefixWord ++ tailWord_2376450).sum := by decide
  have hdescent : baseEnd_2376450 < baseStart_2376450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376538 : List Nat := [3, 1, 1, 2, 1, 5, 1, 2, 6]
def baseStart_2376538 : Nat := 118140960795 + 2376538 * 2 ^ 59
def prefixEnd_2376538 : Nat := 4983230072969 + 3 ^ 40 * 2376538 * 2
def baseEnd_2376538 : Nat := 271179175038872892854557

theorem tailTrace_2376538 : CollatzResearch.WordTrace tailWord_2376538 prefixEnd_2376538 271179175038872892854557 := by
  unfold tailWord_2376538
  simp only [CollatzResearch.WordTrace]
  refine ⟨21669865466054045305430567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57786307909477454147814845 21669865466054045305430567)
  ·
    refine ⟨32504798199081067958145851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21669865466054045305430567 32504798199081067958145851)
    ·
      refine ⟨48757197298621601937218777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32504798199081067958145851 48757197298621601937218777)
      ·
        refine ⟨36567897973966201452914083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48757197298621601937218777 36567897973966201452914083)
        ·
          refine ⟨54851846960949302179371125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36567897973966201452914083 54851846960949302179371125)
          ·
            refine ⟨5142360652588997079316043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54851846960949302179371125 5142360652588997079316043)
            ·
              refine ⟨7713540978883495618974065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5142360652588997079316043 7713540978883495618974065)
              ·
                refine ⟨5785155734162621714230549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7713540978883495618974065 5785155734162621714230549)
                ·
                  refine ⟨271179175038872892854557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5785155734162621714230549 271179175038872892854557)
                  ·
                    rfl

theorem cell22_2376538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_2376538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376538 prefixEnd_2376538 := by exact prefixLift 2376538
  have htrace : WordTrace (prefixWord ++ tailWord_2376538) baseStart_2376538 baseEnd_2376538 := by
    simpa [prefixWord, tailWord_2376538, baseEnd_2376538] using wordTrace_append hprefix tailTrace_2376538
  have hstable : (prefixWord ++ tailWord_2376538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376538).length < 2 ^ (prefixWord ++ tailWord_2376538).sum := by decide
  have hdescent : baseEnd_2376538 < baseStart_2376538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376540 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 3, 4]
def baseStart_2376540 : Nat := 118140960795 + 2376540 * 2 ^ 59
def prefixEnd_2376540 : Nat := 4983230072969 + 3 ^ 40 * 2376540 * 2
def baseEnd_2376540 : Nat := 813538209757491340013665

theorem tailTrace_2376540 : CollatzResearch.WordTrace tailWord_2376540 prefixEnd_2376540 813538209757491340013665 := by
  unfold tailWord_2376540
  simp only [CollatzResearch.WordTrace]
  refine ⟨43339767405104467781647537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57786356540139290375530049 43339767405104467781647537)
  ·
    refine ⟨32504825553828350836235653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43339767405104467781647537 32504825553828350836235653)
    ·
      refine ⟨6094654791342815781794185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32504825553828350836235653 6094654791342815781794185)
      ·
        refine ⟨4570991093507111836345639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6094654791342815781794185 4570991093507111836345639)
        ·
          refine ⟨6856486640260667754518459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4570991093507111836345639 6856486640260667754518459)
          ·
            refine ⟨10284729960391001631777689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6856486640260667754518459 10284729960391001631777689)
            ·
              refine ⟨7713547470293251223833267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10284729960391001631777689 7713547470293251223833267)
              ·
                refine ⟨11570321205439876835749901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7713547470293251223833267 11570321205439876835749901)
                ·
                  refine ⟨4338870452039953813406213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11570321205439876835749901 4338870452039953813406213)
                  ·
                    refine ⟨813538209757491340013665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4338870452039953813406213 813538209757491340013665)
                    ·
                      rfl

theorem cell22_2376540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_2376540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376540 prefixEnd_2376540 := by exact prefixLift 2376540
  have htrace : WordTrace (prefixWord ++ tailWord_2376540) baseStart_2376540 baseEnd_2376540 := by
    simpa [prefixWord, tailWord_2376540, baseEnd_2376540] using wordTrace_append hprefix tailTrace_2376540
  have hstable : (prefixWord ++ tailWord_2376540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376540).length < 2 ^ (prefixWord ++ tailWord_2376540).sum := by decide
  have hdescent : baseEnd_2376540 < baseStart_2376540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376632 : List Nat := [2, 1, 2, 1, 2, 6, 1, 1, 3, 3]
def baseStart_2376632 : Nat := 118140960795 + 2376632 * 2 ^ 59
def prefixEnd_2376632 : Nat := 4983230072969 + 3 ^ 40 * 2376632 * 2
def baseEnd_2376632 : Nat := 813569703237633766713383

theorem tailTrace_2376632 : CollatzResearch.WordTrace tailWord_2376632 prefixEnd_2376632 813569703237633766713383 := by
  unfold tailWord_2376632
  simp only [CollatzResearch.WordTrace]
  refine ⟨43341445162937817637822075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57788593550583756850429433 43341445162937817637822075)
  ·
    refine ⟨65012167744406726456733113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43341445162937817637822075 65012167744406726456733113)
    ·
      refine ⟨48759125808305044842549835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65012167744406726456733113 48759125808305044842549835)
      ·
        refine ⟨73138688712457567263824753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48759125808305044842549835 73138688712457567263824753)
        ·
          refine ⟨54854016534343175447868565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73138688712457567263824753 54854016534343175447868565)
          ·
            refine ⟨2571282025047336349118839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 54854016534343175447868565 2571282025047336349118839)
            ·
              refine ⟨3856923037571004523678259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2571282025047336349118839 3856923037571004523678259)
              ·
                refine ⟨5785384556356506785517389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3856923037571004523678259 5785384556356506785517389)
                ·
                  refine ⟨2169519208633690044569021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5785384556356506785517389 2169519208633690044569021)
                  ·
                    refine ⟨813569703237633766713383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2169519208633690044569021 813569703237633766713383)
                    ·
                      rfl

theorem cell22_2376632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 3, 3].length) (baseStart_2376632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376632 prefixEnd_2376632 := by exact prefixLift 2376632
  have htrace : WordTrace (prefixWord ++ tailWord_2376632) baseStart_2376632 baseEnd_2376632 := by
    simpa [prefixWord, tailWord_2376632, baseEnd_2376632] using wordTrace_append hprefix tailTrace_2376632
  have hstable : (prefixWord ++ tailWord_2376632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376632).length < 2 ^ (prefixWord ++ tailWord_2376632).sum := by decide
  have hdescent : baseEnd_2376632 < baseStart_2376632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376688 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 5, 5]
def baseStart_2376688 : Nat := 118140960795 + 2376688 * 2 ^ 59
def prefixEnd_2376688 : Nat := 4983230072969 + 3 ^ 40 * 2376688 * 2
def baseEnd_2376688 : Nat := 813588873182068287313211

theorem tailTrace_2376688 : CollatzResearch.WordTrace tailWord_2376688 prefixEnd_2376688 813588873182068287313211 := by
  unfold tailWord_2376688
  simp only [CollatzResearch.WordTrace]
  refine ⟨43342466406836378419841359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57789955209115171226455145 43342466406836378419841359)
  ·
    refine ⟨65013699610254567629762039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43342466406836378419841359 65013699610254567629762039)
    ·
      refine ⟨97520549415381851444643059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65013699610254567629762039 97520549415381851444643059)
      ·
        refine ⟨146280824123072777166964589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97520549415381851444643059 146280824123072777166964589)
        ·
          refine ⟨54855309046152291437611721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146280824123072777166964589 54855309046152291437611721)
          ·
            refine ⟨41141481784614218578208791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54855309046152291437611721 41141481784614218578208791)
            ·
              refine ⟨61712222676921327867313187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41141481784614218578208791 61712222676921327867313187)
              ·
                refine ⟨92568334015381991800969781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61712222676921327867313187 92568334015381991800969781)
                ·
                  refine ⟨8678281313942061731340917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92568334015381991800969781 8678281313942061731340917)
                  ·
                    refine ⟨813588873182068287313211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8678281313942061731340917 813588873182068287313211)
                    ·
                      rfl

theorem cell22_2376688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_2376688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376688 prefixEnd_2376688 := by exact prefixLift 2376688
  have htrace : WordTrace (prefixWord ++ tailWord_2376688) baseStart_2376688 baseEnd_2376688 := by
    simpa [prefixWord, tailWord_2376688, baseEnd_2376688] using wordTrace_append hprefix tailTrace_2376688
  have hstable : (prefixWord ++ tailWord_2376688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376688).length < 2 ^ (prefixWord ++ tailWord_2376688).sum := by decide
  have hdescent : baseEnd_2376688 < baseStart_2376688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376705 : List Nat := [1, 2, 4, 1, 2, 2, 1, 3, 1, 5]
def baseStart_2376705 : Nat := 118140960795 + 2376705 * 2 ^ 59
def prefixEnd_2376705 : Nat := 4983230072969 + 3 ^ 40 * 2376705 * 2
def baseEnd_2376705 : Nat := 813594692629485909638159

theorem tailTrace_2376705 : CollatzResearch.WordTrace tailWord_2376705 prefixEnd_2376705 813594692629485909638159 := by
  unfold tailWord_2376705
  simp only [CollatzResearch.WordTrace]
  refine ⟨86685552854611168743051569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57790368569740779162034379 86685552854611168743051569)
  ·
    refine ⟨65014164640958376557288677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86685552854611168743051569 65014164640958376557288677)
    ·
      refine ⟨12190155870179695604491627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65014164640958376557288677 12190155870179695604491627)
      ·
        refine ⟨18285233805269543406737441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12190155870179695604491627 18285233805269543406737441)
        ·
          refine ⟨13713925353952157555053081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18285233805269543406737441 13713925353952157555053081)
          ·
            refine ⟨10285444015464118166289811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13713925353952157555053081 10285444015464118166289811)
            ·
              refine ⟨15428166023196177249434717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10285444015464118166289811 15428166023196177249434717)
              ·
                refine ⟨5785562258698566468538019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15428166023196177249434717 5785562258698566468538019)
                ·
                  refine ⟨8678343388047849702807029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5785562258698566468538019 8678343388047849702807029)
                  ·
                    refine ⟨813594692629485909638159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8678343388047849702807029 813594692629485909638159)
                    ·
                      rfl

theorem cell22_2376705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_2376705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376705 prefixEnd_2376705 := by exact prefixLift 2376705
  have htrace : WordTrace (prefixWord ++ tailWord_2376705) baseStart_2376705 baseEnd_2376705 := by
    simpa [prefixWord, tailWord_2376705, baseEnd_2376705] using wordTrace_append hprefix tailTrace_2376705
  have hstable : (prefixWord ++ tailWord_2376705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376705).length < 2 ^ (prefixWord ++ tailWord_2376705).sum := by decide
  have hdescent : baseEnd_2376705 < baseStart_2376705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376739 : List Nat := [1, 1, 1, 4, 3, 4, 1, 2, 2, 3]
def baseStart_2376739 : Nat := 118140960795 + 2376739 * 2 ^ 59
def prefixEnd_2376739 : Nat := 4983230072969 + 3 ^ 40 * 2376739 * 2
def baseEnd_2376739 : Nat := 813606331524321154288055

theorem tailTrace_2376739 : CollatzResearch.WordTrace tailWord_2376739 prefixEnd_2376739 813606331524321154288055 := by
  unfold tailWord_2376739
  simp only [CollatzResearch.WordTrace]
  refine ⟨86686792936487992549789271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57791195290991995033192847 86686792936487992549789271)
  ·
    refine ⟨130030189404731988824683907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86686792936487992549789271 130030189404731988824683907)
    ·
      refine ⟨195045284107097983237025861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130030189404731988824683907 195045284107097983237025861)
      ·
        refine ⟨36570990770080871856942349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195045284107097983237025861 36570990770080871856942349)
        ·
          refine ⟨13714121538780326946353381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36570990770080871856942349 13714121538780326946353381)
          ·
            refine ⟨2571397788521311302441259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13714121538780326946353381 2571397788521311302441259)
            ·
              refine ⟨3857096682781966953661889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2571397788521311302441259 3857096682781966953661889)
              ·
                refine ⟨2892822512086475215246417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3857096682781966953661889 2892822512086475215246417)
                ·
                  refine ⟨2169616884064856411434813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2892822512086475215246417 2169616884064856411434813)
                  ·
                    refine ⟨813606331524321154288055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2169616884064856411434813 813606331524321154288055)
                    ·
                      rfl

theorem cell22_2376739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 3].length) (baseStart_2376739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376739 prefixEnd_2376739 := by exact prefixLift 2376739
  have htrace : WordTrace (prefixWord ++ tailWord_2376739) baseStart_2376739 baseEnd_2376739 := by
    simpa [prefixWord, tailWord_2376739, baseEnd_2376739] using wordTrace_append hprefix tailTrace_2376739
  have hstable : (prefixWord ++ tailWord_2376739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376739).length < 2 ^ (prefixWord ++ tailWord_2376739).sum := by decide
  have hdescent : baseEnd_2376739 < baseStart_2376739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376763 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 11]
def baseStart_2376763 : Nat := 118140960795 + 2376763 * 2 ^ 59
def prefixEnd_2376763 : Nat := 4983230072969 + 3 ^ 40 * 2376763 * 2
def baseEnd_2376763 : Nat := 271204849071597697229327

theorem tailTrace_2376763 : CollatzResearch.WordTrace tailWord_2376763 prefixEnd_2376763 271204849071597697229327 := by
  unfold tailWord_2376763
  simp only [CollatzResearch.WordTrace]
  refine ⟨86687668288401044648662943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57791778858934029765775295 86687668288401044648662943)
  ·
    refine ⟨130031502432601566972994415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86687668288401044648662943 130031502432601566972994415)
    ·
      refine ⟨195047253648902350459491623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130031502432601566972994415 195047253648902350459491623)
      ·
        refine ⟨292570880473353525689237435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195047253648902350459491623 292570880473353525689237435)
        ·
          refine ⟨438856320710030288533856153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292570880473353525689237435 438856320710030288533856153)
          ·
            refine ⟨329142240532522716400392115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 438856320710030288533856153 329142240532522716400392115)
            ·
              refine ⟨493713360798784074600588173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329142240532522716400392115 493713360798784074600588173)
              ·
                refine ⟨185142510299544027975220565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 493713360798784074600588173 185142510299544027975220565)
                ·
                  refine ⟨271204849071597697229327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 185142510299544027975220565 271204849071597697229327)
                  ·
                    rfl

theorem cell22_2376763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 11].length) (baseStart_2376763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376763 prefixEnd_2376763 := by exact prefixLift 2376763
  have htrace : WordTrace (prefixWord ++ tailWord_2376763) baseStart_2376763 baseEnd_2376763 := by
    simpa [prefixWord, tailWord_2376763, baseEnd_2376763] using wordTrace_append hprefix tailTrace_2376763
  have hstable : (prefixWord ++ tailWord_2376763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376763).length < 2 ^ (prefixWord ++ tailWord_2376763).sum := by decide
  have hdescent : baseEnd_2376763 < baseStart_2376763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376769 : List Nat := [1, 2, 5, 1, 3, 2, 2, 6]
def baseStart_2376769 : Nat := 118140960795 + 2376769 * 2 ^ 59
def prefixEnd_2376769 : Nat := 4983230072969 + 3 ^ 40 * 2376769 * 2
def baseEnd_2376769 : Nat := 90401844570823452893107

theorem tailTrace_2376769 : CollatzResearch.WordTrace tailWord_2376769 prefixEnd_2376769 90401844570823452893107 := by
  unfold tailWord_2376769
  simp only [CollatzResearch.WordTrace]
  refine ⟨86687887126379307673381361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57791924750919538448920907 86687887126379307673381361)
  ·
    refine ⟨65015915344784480755036021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86687887126379307673381361 65015915344784480755036021)
    ·
      refine ⟨6095242063573545070784627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65015915344784480755036021 6095242063573545070784627)
      ·
        refine ⟨9142863095360317606176941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6095242063573545070784627 9142863095360317606176941)
        ·
          refine ⟨3428573660760119102316353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9142863095360317606176941 3428573660760119102316353)
          ·
            refine ⟨2571430245570089326737265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3428573660760119102316353 2571430245570089326737265)
            ·
              refine ⟨1928572684177566995052949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2571430245570089326737265 1928572684177566995052949)
              ·
                refine ⟨90401844570823452893107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1928572684177566995052949 90401844570823452893107)
                ·
                  rfl

theorem cell22_2376769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 6].length) (baseStart_2376769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376769 prefixEnd_2376769 := by exact prefixLift 2376769
  have htrace : WordTrace (prefixWord ++ tailWord_2376769) baseStart_2376769 baseEnd_2376769 := by
    simpa [prefixWord, tailWord_2376769, baseEnd_2376769] using wordTrace_append hprefix tailTrace_2376769
  have hstable : (prefixWord ++ tailWord_2376769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376769).length < 2 ^ (prefixWord ++ tailWord_2376769).sum := by decide
  have hdescent : baseEnd_2376769 < baseStart_2376769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376814 : List Nat := [4, 1, 2, 2, 1, 2, 4, 1, 5]
def baseStart_2376814 : Nat := 118140960795 + 2376814 * 2 ^ 59
def prefixEnd_2376814 : Nat := 4983230072969 + 3 ^ 40 * 2376814 * 2
def baseEnd_2376814 : Nat := 271210668519015319554275

theorem tailTrace_2376814 : CollatzResearch.WordTrace tailWord_2376814 prefixEnd_2376814 271210668519015319554275 := by
  unfold tailWord_2376814
  simp only [CollatzResearch.WordTrace]
  refine ⟨10836191051402035044846187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57793018940810853572512997 10836191051402035044846187)
  ·
    refine ⟨16254286577103052567269281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10836191051402035044846187 16254286577103052567269281)
    ·
      refine ⟨12190714932827289425451961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16254286577103052567269281 12190714932827289425451961)
      ·
        refine ⟨9143036199620467069088971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12190714932827289425451961 9143036199620467069088971)
        ·
          refine ⟨13714554299430700603633457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9143036199620467069088971 13714554299430700603633457)
          ·
            refine ⟨10285915724573025452725093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13714554299430700603633457 10285915724573025452725093)
            ·
              refine ⟨1928609198357442272385955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10285915724573025452725093 1928609198357442272385955)
              ·
                refine ⟨2892913797536163408578933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1928609198357442272385955 2892913797536163408578933)
                ·
                  refine ⟨271210668519015319554275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2892913797536163408578933 271210668519015319554275)
                  ·
                    rfl

theorem cell22_2376814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_2376814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376814 prefixEnd_2376814 := by exact prefixLift 2376814
  have htrace : WordTrace (prefixWord ++ tailWord_2376814) baseStart_2376814 baseEnd_2376814 := by
    simpa [prefixWord, tailWord_2376814, baseEnd_2376814] using wordTrace_append hprefix tailTrace_2376814
  have hstable : (prefixWord ++ tailWord_2376814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376814).length < 2 ^ (prefixWord ++ tailWord_2376814).sum := by decide
  have hdescent : baseEnd_2376814 < baseStart_2376814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376874 : List Nat := [3, 1, 5, 1, 1, 1, 1, 3, 1, 5]
def baseStart_2376874 : Nat := 118140960795 + 2376874 * 2 ^ 59
def prefixEnd_2376874 : Nat := 4983230072969 + 3 ^ 40 * 2376874 * 2
def baseEnd_2376874 : Nat := 813652544783225802162641

theorem tailTrace_2376874 : CollatzResearch.WordTrace tailWord_2376874 prefixEnd_2376874 813652544783225802162641 := by
  unfold tailWord_2376874
  simp only [CollatzResearch.WordTrace]
  refine ⟨21672929197749727651488419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57794477860665940403969117 21672929197749727651488419)
  ·
    refine ⟨32509393796624591477232629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21672929197749727651488419 32509393796624591477232629)
    ·
      refine ⟨3047755668433555450990559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32509393796624591477232629 3047755668433555450990559)
      ·
        refine ⟨4571633502650333176485839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3047755668433555450990559 4571633502650333176485839)
        ·
          refine ⟨6857450253975499764728759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4571633502650333176485839 6857450253975499764728759)
          ·
            refine ⟨10286175380963249647093139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6857450253975499764728759 10286175380963249647093139)
            ·
              refine ⟨15429263071444874470639709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10286175380963249647093139 15429263071444874470639709)
              ·
                refine ⟨5785973651791827926489891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15429263071444874470639709 5785973651791827926489891)
                ·
                  refine ⟨8678960477687741889734837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5785973651791827926489891 8678960477687741889734837)
                  ·
                    refine ⟨813652544783225802162641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8678960477687741889734837 813652544783225802162641)
                    ·
                      rfl

theorem cell22_2376874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_2376874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376874 prefixEnd_2376874 := by exact prefixLift 2376874
  have htrace : WordTrace (prefixWord ++ tailWord_2376874) baseStart_2376874 baseEnd_2376874 := by
    simpa [prefixWord, tailWord_2376874, baseEnd_2376874] using wordTrace_append hprefix tailTrace_2376874
  have hstable : (prefixWord ++ tailWord_2376874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376874).length < 2 ^ (prefixWord ++ tailWord_2376874).sum := by decide
  have hdescent : baseEnd_2376874 < baseStart_2376874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376887 : List Nat := [1, 1, 3, 1, 4, 1, 5, 6]
def baseStart_2376887 : Nat := 118140960795 + 2376887 * 2 ^ 59
def prefixEnd_2376887 : Nat := 4983230072969 + 3 ^ 40 * 2376887 * 2
def baseEnd_2376887 : Nat := 90406332772099789065289

theorem tailTrace_2376887 : CollatzResearch.WordTrace tailWord_2376887 prefixEnd_2376887 90406332772099789065289 := by
  unfold tailWord_2376887
  simp only [CollatzResearch.WordTrace]
  refine ⟨86692190939951813826176915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57794793959967875884117943 86692190939951813826176915)
  ·
    refine ⟨130038286409927720739265373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86692190939951813826176915 130038286409927720739265373)
    ·
      refine ⟨48764357403722895277224515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130038286409927720739265373 48764357403722895277224515)
      ·
        refine ⟨73146536105584342915836773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48764357403722895277224515 73146536105584342915836773)
        ·
          refine ⟨13714975519797064296719395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73146536105584342915836773 13714975519797064296719395)
          ·
            refine ⟨20572463279695596445079093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13714975519797064296719395 20572463279695596445079093)
            ·
              refine ⟨1928668432471462166726165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20572463279695596445079093 1928668432471462166726165)
              ·
                refine ⟨90406332772099789065289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1928668432471462166726165 90406332772099789065289)
                ·
                  rfl

theorem cell22_2376887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 6].length) (baseStart_2376887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376887 prefixEnd_2376887 := by exact prefixLift 2376887
  have htrace : WordTrace (prefixWord ++ tailWord_2376887) baseStart_2376887 baseEnd_2376887 := by
    simpa [prefixWord, tailWord_2376887, baseEnd_2376887] using wordTrace_append hprefix tailTrace_2376887
  have hstable : (prefixWord ++ tailWord_2376887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376887).length < 2 ^ (prefixWord ++ tailWord_2376887).sum := by decide
  have hdescent : baseEnd_2376887 < baseStart_2376887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376889 : List Nat := [1, 2, 1, 4, 1, 5, 1, 1, 2, 4]
def baseStart_2376889 : Nat := 118140960795 + 2376889 * 2 ^ 59
def prefixEnd_2376889 : Nat := 4983230072969 + 3 ^ 40 * 2376889 * 2
def baseEnd_2376889 : Nat := 813657679589770763037595

theorem tailTrace_2376889 : CollatzResearch.WordTrace tailWord_2376889 prefixEnd_2376889 813657679589770763037595 := by
  unfold tailWord_2376889
  simp only [CollatzResearch.WordTrace]
  refine ⟨86692263885944568167749721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57794842590629712111833147 86692263885944568167749721)
  ·
    refine ⟨65019197914458426125812291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86692263885944568167749721 65019197914458426125812291)
    ·
      refine ⟨97528796871687639188718437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65019197914458426125812291 97528796871687639188718437)
      ·
        refine ⟨18286649413441432347884707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97528796871687639188718437 18286649413441432347884707)
        ·
          refine ⟨27429974120162148521827061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18286649413441432347884707 27429974120162148521827061)
          ·
            refine ⟨2571560073765201423921287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27429974120162148521827061 2571560073765201423921287)
            ·
              refine ⟨3857340110647802135881931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2571560073765201423921287 3857340110647802135881931)
              ·
                refine ⟨5786010165971703203822897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3857340110647802135881931 5786010165971703203822897)
                ·
                  refine ⟨4339507624478777402867173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5786010165971703203822897 4339507624478777402867173)
                  ·
                    refine ⟨813657679589770763037595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4339507624478777402867173 813657679589770763037595)
                    ·
                      rfl

theorem cell22_2376889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 4].length) (baseStart_2376889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376889 prefixEnd_2376889 := by exact prefixLift 2376889
  have htrace : WordTrace (prefixWord ++ tailWord_2376889) baseStart_2376889 baseEnd_2376889 := by
    simpa [prefixWord, tailWord_2376889, baseEnd_2376889] using wordTrace_append hprefix tailTrace_2376889
  have hstable : (prefixWord ++ tailWord_2376889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376889).length < 2 ^ (prefixWord ++ tailWord_2376889).sum := by decide
  have hdescent : baseEnd_2376889 < baseStart_2376889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376915 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 7]
def baseStart_2376915 : Nat := 118140960795 + 2376915 * 2 ^ 59
def prefixEnd_2376915 : Nat := 4983230072969 + 3 ^ 40 * 2376915 * 2
def baseEnd_2376915 : Nat := 271222193307038453962505

theorem tailTrace_2376915 : CollatzResearch.WordTrace tailWord_2376915 prefixEnd_2376915 271222193307038453962505 := by
  unfold tailWord_2376915
  simp only [CollatzResearch.WordTrace]
  refine ⟨86693212183850374608196199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57795474789233583072130799 86693212183850374608196199)
  ·
    refine ⟨130039818275775561912294299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86693212183850374608196199 130039818275775561912294299)
    ·
      refine ⟨195059727413663342868441449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130039818275775561912294299 195059727413663342868441449)
      ·
        refine ⟨146294795560247507151331087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195059727413663342868441449 146294795560247507151331087)
        ·
          refine ⟨219442193340371260726996631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146294795560247507151331087 219442193340371260726996631)
          ·
            refine ⟨329163290010556891090494947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219442193340371260726996631 329163290010556891090494947)
            ·
              refine ⟨493744935015835336635742421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329163290010556891090494947 493744935015835336635742421)
              ·
                refine ⟨11572146914433640702400213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 493744935015835336635742421 11572146914433640702400213)
                ·
                  refine ⟨271222193307038453962505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11572146914433640702400213 271222193307038453962505)
                  ·
                    rfl

theorem cell22_2376915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 7].length) (baseStart_2376915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376915 prefixEnd_2376915 := by exact prefixLift 2376915
  have htrace : WordTrace (prefixWord ++ tailWord_2376915) baseStart_2376915 baseEnd_2376915 := by
    simpa [prefixWord, tailWord_2376915, baseEnd_2376915] using wordTrace_append hprefix tailTrace_2376915
  have hstable : (prefixWord ++ tailWord_2376915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376915).length < 2 ^ (prefixWord ++ tailWord_2376915).sum := by decide
  have hdescent : baseEnd_2376915 < baseStart_2376915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2376932 : List Nat := [2, 3, 1, 1, 1, 2, 2, 5, 5]
def baseStart_2376932 : Nat := 118140960795 + 2376932 * 2 ^ 59
def prefixEnd_2376932 : Nat := 4983230072969 + 3 ^ 40 * 2376932 * 2
def baseEnd_2376932 : Nat := 271224133122844328070821

theorem tailTrace_2376932 : CollatzResearch.WordTrace tailWord_2376932 prefixEnd_2376932 271224133122844328070821 := by
  unfold tailWord_2376932
  simp only [CollatzResearch.WordTrace]
  refine ⟨43346916112394393255782525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57795888149859191007710033 43346916112394393255782525)
  ·
    refine ⟨16255093542147897470918447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43346916112394393255782525 16255093542147897470918447)
    ·
      refine ⟨24382640313221846206377671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16255093542147897470918447 24382640313221846206377671)
      ·
        refine ⟨36573960469832769309566507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24382640313221846206377671 36573960469832769309566507)
        ·
          refine ⟨54860940704749153964349761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36573960469832769309566507 54860940704749153964349761)
          ·
            refine ⟨41145705528561865473262321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54860940704749153964349761 41145705528561865473262321)
            ·
              refine ⟨30859279146421399104946741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41145705528561865473262321 30859279146421399104946741)
              ·
                refine ⟨2893057419977006166088757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30859279146421399104946741 2893057419977006166088757)
                ·
                  refine ⟨271224133122844328070821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2893057419977006166088757 271224133122844328070821)
                  ·
                    rfl

theorem cell22_2376932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_2376932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2376932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2376932 prefixEnd_2376932 := by exact prefixLift 2376932
  have htrace : WordTrace (prefixWord ++ tailWord_2376932) baseStart_2376932 baseEnd_2376932 := by
    simpa [prefixWord, tailWord_2376932, baseEnd_2376932] using wordTrace_append hprefix tailTrace_2376932
  have hstable : (prefixWord ++ tailWord_2376932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2376932).length < 2 ^ (prefixWord ++ tailWord_2376932).sum := by decide
  have hdescent : baseEnd_2376932 < baseStart_2376932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2376932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377009 : List Nat := [1, 2, 2, 3, 3, 2, 1, 2, 1, 5]
def baseStart_2377009 : Nat := 118140960795 + 2377009 * 2 ^ 59
def prefixEnd_2377009 : Nat := 4983230072969 + 3 ^ 40 * 2377009 * 2
def baseEnd_2377009 : Nat := 813698758042130450037227

theorem tailTrace_2377009 : CollatzResearch.WordTrace tailWord_2377009 prefixEnd_2377009 813698758042130450037227 := by
  unfold tailWord_2377009
  simp only [CollatzResearch.WordTrace]
  refine ⟨86696640645509828662118081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57797760430339885774745387 86696640645509828662118081)
  ·
    refine ⟨65022480484132371496588561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86696640645509828662118081 65022480484132371496588561)
    ·
      refine ⟨48766860363099278622441421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65022480484132371496588561 48766860363099278622441421)
      ·
        refine ⟨18287572636162229483415533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48766860363099278622441421 18287572636162229483415533)
        ·
          refine ⟨6857839738560836056280825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18287572636162229483415533 6857839738560836056280825)
          ·
            refine ⟨5143379803920627042210619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6857839738560836056280825 5143379803920627042210619)
            ·
              refine ⟨7715069705880940563315929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5143379803920627042210619 7715069705880940563315929)
              ·
                refine ⟨5786302279410705422486947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7715069705880940563315929 5786302279410705422486947)
                ·
                  refine ⟨8679453419116058133730421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5786302279410705422486947 8679453419116058133730421)
                  ·
                    refine ⟨813698758042130450037227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8679453419116058133730421 813698758042130450037227)
                    ·
                      rfl

theorem cell22_2377009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_2377009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377009 prefixEnd_2377009 := by exact prefixLift 2377009
  have htrace : WordTrace (prefixWord ++ tailWord_2377009) baseStart_2377009 baseEnd_2377009 := by
    simpa [prefixWord, tailWord_2377009, baseEnd_2377009] using wordTrace_append hprefix tailTrace_2377009
  have hstable : (prefixWord ++ tailWord_2377009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377009).length < 2 ^ (prefixWord ++ tailWord_2377009).sum := by decide
  have hdescent : baseEnd_2377009 < baseStart_2377009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377028 : List Nat := [2, 3, 4, 1, 1, 2, 1, 4, 4]
def baseStart_2377028 : Nat := 118140960795 + 2377028 * 2 ^ 59
def prefixEnd_2377028 : Nat := 4983230072969 + 3 ^ 40 * 2377028 * 2
def baseEnd_2377028 : Nat := 271235087376806911270723

theorem tailTrace_2377028 : CollatzResearch.WordTrace tailWord_2377028 prefixEnd_2377028 271235087376806911270723 := by
  unfold tailWord_2377028
  simp only [CollatzResearch.WordTrace]
  refine ⟨43348666816220497453529869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57798222421627329938039825 43348666816220497453529869)
  ·
    refine ⟨16255750056082686545073701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43348666816220497453529869 16255750056082686545073701)
    ·
      refine ⟨3047953135515503727201319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16255750056082686545073701 3047953135515503727201319)
      ·
        refine ⟨4571929703273255590801979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3047953135515503727201319 4571929703273255590801979)
        ·
          refine ⟨6857894554909883386202969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4571929703273255590801979 6857894554909883386202969)
          ·
            refine ⟨5143420916182412539652227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6857894554909883386202969 5143420916182412539652227)
            ·
              refine ⟨7715131374273618809478341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5143420916182412539652227 7715131374273618809478341)
              ·
                refine ⟨1446587132676303526777189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7715131374273618809478341 1446587132676303526777189)
                ·
                  refine ⟨271235087376806911270723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1446587132676303526777189 271235087376806911270723)
                  ·
                    rfl

theorem cell22_2377028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_2377028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377028 prefixEnd_2377028 := by exact prefixLift 2377028
  have htrace : WordTrace (prefixWord ++ tailWord_2377028) baseStart_2377028 baseEnd_2377028 := by
    simpa [prefixWord, tailWord_2377028, baseEnd_2377028] using wordTrace_append hprefix tailTrace_2377028
  have hstable : (prefixWord ++ tailWord_2377028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377028).length < 2 ^ (prefixWord ++ tailWord_2377028).sum := by decide
  have hdescent : baseEnd_2377028 < baseStart_2377028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377082 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 3, 7]
def baseStart_2377082 : Nat := 118140960795 + 2377082 * 2 ^ 59
def prefixEnd_2377082 : Nat := 4983230072969 + 3 ^ 40 * 2377082 * 2
def baseEnd_2377082 : Nat := 813723747433982592962003

theorem tailTrace_2377082 : CollatzResearch.WordTrace tailWord_2377082 prefixEnd_2377082 813723747433982592962003 := by
  unfold tailWord_2377082
  simp only [CollatzResearch.WordTrace]
  refine ⟨21674825793561340532381375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57799535449496908086350333 21674825793561340532381375)
  ·
    refine ⟨32512238690342010798572063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21674825793561340532381375 32512238690342010798572063)
    ·
      refine ⟨48768358035513016197858095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32512238690342010798572063 48768358035513016197858095)
      ·
        refine ⟨73152537053269524296787143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48768358035513016197858095 73152537053269524296787143)
        ·
          refine ⟨109728805579904286445180715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73152537053269524296787143 109728805579904286445180715)
          ·
            refine ⟨164593208369856429667771073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109728805579904286445180715 164593208369856429667771073)
            ·
              refine ⟨123444906277392322250828305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164593208369856429667771073 123444906277392322250828305)
              ·
                refine ⟨92583679708044241688121229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123444906277392322250828305 92583679708044241688121229)
                ·
                  refine ⟨34718879890516590633045461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92583679708044241688121229 34718879890516590633045461)
                  ·
                    refine ⟨813723747433982592962003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34718879890516590633045461 813723747433982592962003)
                    ·
                      rfl

theorem cell22_2377082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_2377082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377082 prefixEnd_2377082 := by exact prefixLift 2377082
  have htrace : WordTrace (prefixWord ++ tailWord_2377082) baseStart_2377082 baseEnd_2377082 := by
    simpa [prefixWord, tailWord_2377082, baseEnd_2377082] using wordTrace_append hprefix tailTrace_2377082
  have hstable : (prefixWord ++ tailWord_2377082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377082).length < 2 ^ (prefixWord ++ tailWord_2377082).sum := by decide
  have hdescent : baseEnd_2377082 < baseStart_2377082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377159 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 4, 4]
def baseStart_2377159 : Nat := 118140960795 + 2377159 * 2 ^ 59
def prefixEnd_2377159 : Nat := 4983230072969 + 3 ^ 40 * 2377159 * 2
def baseEnd_2377159 : Nat := 813750106107580058786767

theorem tailTrace_2377159 : CollatzResearch.WordTrace tailWord_2377159 prefixEnd_2377159 813750106107580058786767 := by
  unfold tailWord_2377159
  simp only [CollatzResearch.WordTrace]
  refine ⟨86702111594966404280078531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57801407729977602853385687 86702111594966404280078531)
  ·
    refine ⟨130053167392449606420117797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86702111594966404280078531 130053167392449606420117797)
    ·
      refine ⟨24384968886084301203772087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130053167392449606420117797 24384968886084301203772087)
      ·
        refine ⟨36577453329126451805658131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24384968886084301203772087 36577453329126451805658131)
        ·
          refine ⟨54866179993689677708487197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36577453329126451805658131 54866179993689677708487197)
          ·
            refine ⟨20574817497633629140682699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54866179993689677708487197 20574817497633629140682699)
            ·
              refine ⟨30862226246450443711024049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20574817497633629140682699 30862226246450443711024049)
              ·
                refine ⟨23146669684837832783268037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30862226246450443711024049 23146669684837832783268037)
                ·
                  refine ⟨4340000565907093646862757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23146669684837832783268037 4340000565907093646862757)
                  ·
                    refine ⟨813750106107580058786767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4340000565907093646862757 813750106107580058786767)
                    ·
                      rfl

theorem cell22_2377159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_2377159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377159 prefixEnd_2377159 := by exact prefixLift 2377159
  have htrace : WordTrace (prefixWord ++ tailWord_2377159) baseStart_2377159 baseEnd_2377159 := by
    simpa [prefixWord, tailWord_2377159, baseEnd_2377159] using wordTrace_append hprefix tailTrace_2377159
  have hstable : (prefixWord ++ tailWord_2377159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377159).length < 2 ^ (prefixWord ++ tailWord_2377159).sum := by decide
  have hdescent : baseEnd_2377159 < baseStart_2377159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377197 : List Nat := [1, 5, 1, 3, 2, 2, 2, 2, 4]
def baseStart_2377197 : Nat := 118140960795 + 2377197 * 2 ^ 59
def prefixEnd_2377197 : Nat := 4983230072969 + 3 ^ 40 * 2377197 * 2
def baseEnd_2377197 : Nat := 271254371428053542112217

theorem tailTrace_2377197 : CollatzResearch.WordTrace tailWord_2377197 prefixEnd_2377197 271254371428053542112217 := by
  unfold tailWord_2377197
  simp only [CollatzResearch.WordTrace]
  refine ⟨86703497568828736769961845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57802331712552491179974563 86703497568828736769961845)
  ·
    refine ⟨8128452897077694072183923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86703497568828736769961845 8128452897077694072183923)
    ·
      refine ⟨12192679345616541108275885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8128452897077694072183923 12192679345616541108275885)
      ·
        refine ⟨4572254754606202915603457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12192679345616541108275885 4572254754606202915603457)
        ·
          refine ⟨3429191065954652186702593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4572254754606202915603457 3429191065954652186702593)
          ·
            refine ⟨2571893299465989140026945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3429191065954652186702593 2571893299465989140026945)
            ·
              refine ⟨1928919974599491855020209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2571893299465989140026945 1928919974599491855020209)
              ·
                refine ⟨1446689980949618891265157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1928919974599491855020209 1446689980949618891265157)
                ·
                  refine ⟨271254371428053542112217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1446689980949618891265157 271254371428053542112217)
                  ·
                    rfl

theorem cell22_2377197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_2377197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377197 prefixEnd_2377197 := by exact prefixLift 2377197
  have htrace : WordTrace (prefixWord ++ tailWord_2377197) baseStart_2377197 baseEnd_2377197 := by
    simpa [prefixWord, tailWord_2377197, baseEnd_2377197] using wordTrace_append hprefix tailTrace_2377197
  have hstable : (prefixWord ++ tailWord_2377197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377197).length < 2 ^ (prefixWord ++ tailWord_2377197).sum := by decide
  have hdescent : baseEnd_2377197 < baseStart_2377197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377223 : List Nat := [1, 1, 4, 3, 2, 2, 1, 2, 3, 3]
def baseStart_2377223 : Nat := 118140960795 + 2377223 * 2 ^ 59
def prefixEnd_2377223 : Nat := 4983230072969 + 3 ^ 40 * 2377223 * 2
def baseEnd_2377223 : Nat := 813772014615505225186571

theorem tailTrace_2377223 : CollatzResearch.WordTrace tailWord_2377223 prefixEnd_2377223 813772014615505225186571 := by
  unfold tailWord_2377223
  simp only [CollatzResearch.WordTrace]
  refine ⟨86704445866734543210408323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57802963911156362140272215 86704445866734543210408323)
  ·
    refine ⟨130056668800101814815612485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86704445866734543210408323 130056668800101814815612485)
    ·
      refine ⟨24385625400019090277927341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130056668800101814815612485 24385625400019090277927341)
      ·
        refine ⟨9144609525007158854222753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24385625400019090277927341 9144609525007158854222753)
        ·
          refine ⟨6858457143755369140667065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9144609525007158854222753 6858457143755369140667065)
          ·
            refine ⟨5143842857816526855500299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6858457143755369140667065 5143842857816526855500299)
            ·
              refine ⟨7715764286724790283250449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5143842857816526855500299 7715764286724790283250449)
              ·
                refine ⟨5786823215043592712437837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7715764286724790283250449 5786823215043592712437837)
                ·
                  refine ⟨2170058705641347267164189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5786823215043592712437837 2170058705641347267164189)
                  ·
                    refine ⟨813772014615505225186571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2170058705641347267164189 813772014615505225186571)
                    ·
                      rfl

theorem cell22_2377223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_2377223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377223 prefixEnd_2377223 := by exact prefixLift 2377223
  have htrace : WordTrace (prefixWord ++ tailWord_2377223) baseStart_2377223 baseEnd_2377223 := by
    simpa [prefixWord, tailWord_2377223, baseEnd_2377223] using wordTrace_append hprefix tailTrace_2377223
  have hstable : (prefixWord ++ tailWord_2377223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377223).length < 2 ^ (prefixWord ++ tailWord_2377223).sum := by decide
  have hdescent : baseEnd_2377223 < baseStart_2377223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377246 : List Nat := [4, 3, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_2377246 : Nat := 118140960795 + 2377246 * 2 ^ 59
def prefixEnd_2377246 : Nat := 4983230072969 + 3 ^ 40 * 2377246 * 2
def baseEnd_2377246 : Nat := 813779887985540831861501

theorem tailTrace_2377246 : CollatzResearch.WordTrace tailWord_2377246 prefixEnd_2377246 813779887985540831861501 := by
  unfold tailWord_2377246
  simp only [CollatzResearch.WordTrace]
  refine ⟨10838160593206402267311949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57803523163767478758997061 10838160593206402267311949)
  ·
    refine ⟨4064310222452400850241981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10838160593206402267311949 4064310222452400850241981)
    ·
      refine ⟨1524116333419650318840743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4064310222452400850241981 1524116333419650318840743)
      ·
        refine ⟨2286174500129475478261115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1524116333419650318840743 2286174500129475478261115)
        ·
          refine ⟨3429261750194213217391673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2286174500129475478261115 3429261750194213217391673)
          ·
            refine ⟨2571946312645659913043755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3429261750194213217391673 2571946312645659913043755)
            ·
              refine ⟨3857919468968489869565633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2571946312645659913043755 3857919468968489869565633)
              ·
                refine ⟨2893439601726367402174225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3857919468968489869565633 2893439601726367402174225)
                ·
                  refine ⟨2170079701294775551630669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2893439601726367402174225 2170079701294775551630669)
                  ·
                    refine ⟨813779887985540831861501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2170079701294775551630669 813779887985540831861501)
                    ·
                      rfl

theorem cell22_2377246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_2377246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377246 prefixEnd_2377246 := by exact prefixLift 2377246
  have htrace : WordTrace (prefixWord ++ tailWord_2377246) baseStart_2377246 baseEnd_2377246 := by
    simpa [prefixWord, tailWord_2377246, baseEnd_2377246] using wordTrace_append hprefix tailTrace_2377246
  have hstable : (prefixWord ++ tailWord_2377246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377246).length < 2 ^ (prefixWord ++ tailWord_2377246).sum := by decide
  have hdescent : baseEnd_2377246 < baseStart_2377246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377281 : List Nat := [1, 2, 5, 1, 1, 1, 1, 4, 6]
def baseStart_2377281 : Nat := 118140960795 + 2377281 * 2 ^ 59
def prefixEnd_2377281 : Nat := 4983230072969 + 3 ^ 40 * 2377281 * 2
def baseEnd_2377281 : Nat := 271263956400270802412131

theorem tailTrace_2377281 : CollatzResearch.WordTrace tailWord_2377281 prefixEnd_2377281 271263956400270802412131 := by
  unfold tailWord_2377281
  simp only [CollatzResearch.WordTrace]
  refine ⟨86706561300524419116019697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57804374200349612744013131 86706561300524419116019697)
  ·
    refine ⟨65029920975393314337014773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86706561300524419116019697 65029920975393314337014773)
    ·
      refine ⟨6096555091443123219095135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65029920975393314337014773 6096555091443123219095135)
      ·
        refine ⟨9144832637164684828642703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6096555091443123219095135 9144832637164684828642703)
        ·
          refine ⟨13717248955747027242964055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9144832637164684828642703 13717248955747027242964055)
          ·
            refine ⟨20575873433620540864446083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13717248955747027242964055 20575873433620540864446083)
            ·
              refine ⟨30863810150430811296669125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20575873433620540864446083 30863810150430811296669125)
              ·
                refine ⟨5786964403205777118125461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30863810150430811296669125 5786964403205777118125461)
                ·
                  refine ⟨271263956400270802412131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5786964403205777118125461 271263956400270802412131)
                  ·
                    rfl

theorem cell22_2377281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 6].length) (baseStart_2377281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377281 prefixEnd_2377281 := by exact prefixLift 2377281
  have htrace : WordTrace (prefixWord ++ tailWord_2377281) baseStart_2377281 baseEnd_2377281 := by
    simpa [prefixWord, tailWord_2377281, baseEnd_2377281] using wordTrace_append hprefix tailTrace_2377281
  have hstable : (prefixWord ++ tailWord_2377281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377281).length < 2 ^ (prefixWord ++ tailWord_2377281).sum := by decide
  have hdescent : baseEnd_2377281 < baseStart_2377281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377296 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 6, 3]
def baseStart_2377296 : Nat := 118140960795 + 2377296 * 2 ^ 59
def prefixEnd_2377296 : Nat := 4983230072969 + 3 ^ 40 * 2377296 * 2
def baseEnd_2377296 : Nat := 813797004007357368111347

theorem tailTrace_2377296 : CollatzResearch.WordTrace tailWord_2377296 prefixEnd_2377296 813797004007357368111347 := by
  unfold tailWord_2377296
  simp only [CollatzResearch.WordTrace]
  refine ⟨43353554197735038338907871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57804738930313384451877161 43353554197735038338907871)
  ·
    refine ⟨65030331296602557508361807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43353554197735038338907871 65030331296602557508361807)
    ·
      refine ⟨97545496944903836262542711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65030331296602557508361807 97545496944903836262542711)
      ·
        refine ⟨146318245417355754393814067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97545496944903836262542711 146318245417355754393814067)
        ·
          refine ⟨219477368126033631590721101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146318245417355754393814067 219477368126033631590721101)
          ·
            refine ⟨82304013047262611846520413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219477368126033631590721101 82304013047262611846520413)
            ·
              refine ⟨30864004892723479442445155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82304013047262611846520413 30864004892723479442445155)
              ·
                refine ⟨46296007339085219163667733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30864004892723479442445155 46296007339085219163667733)
                ·
                  refine ⟨2170125344019619648296925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46296007339085219163667733 2170125344019619648296925)
                  ·
                    refine ⟨813797004007357368111347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2170125344019619648296925 813797004007357368111347)
                    ·
                      rfl

theorem cell22_2377296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 6, 3].length) (baseStart_2377296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377296 prefixEnd_2377296 := by exact prefixLift 2377296
  have htrace : WordTrace (prefixWord ++ tailWord_2377296) baseStart_2377296 baseEnd_2377296 := by
    simpa [prefixWord, tailWord_2377296, baseEnd_2377296] using wordTrace_append hprefix tailTrace_2377296
  have hstable : (prefixWord ++ tailWord_2377296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377296).length < 2 ^ (prefixWord ++ tailWord_2377296).sum := by decide
  have hdescent : baseEnd_2377296 < baseStart_2377296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377313 : List Nat := [1, 2, 3, 1, 1, 3, 2, 4, 2, 3]
def baseStart_2377313 : Nat := 118140960795 + 2377313 * 2 ^ 59
def prefixEnd_2377313 : Nat := 4983230072969 + 3 ^ 40 * 2377313 * 2
def baseEnd_2377313 : Nat := 813802823454774990436295

theorem tailTrace_2377313 : CollatzResearch.WordTrace tailWord_2377313 prefixEnd_2377313 813802823454774990436295 := by
  unfold tailWord_2377313
  simp only [CollatzResearch.WordTrace]
  refine ⟨86707728436408488581184593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57805152290938992387456395 86707728436408488581184593)
  ·
    refine ⟨65030796327306366435888445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86707728436408488581184593 65030796327306366435888445)
    ·
      refine ⟨24386548622739887413458167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65030796327306366435888445 24386548622739887413458167)
      ·
        refine ⟨36579822934109831120187251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24386548622739887413458167 36579822934109831120187251)
        ·
          refine ⟨54869734401164746680280877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36579822934109831120187251 54869734401164746680280877)
          ·
            refine ⟨20576150400436780005105329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54869734401164746680280877 20576150400436780005105329)
            ·
              refine ⟨15432112800327585003828997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20576150400436780005105329 15432112800327585003828997)
              ·
                refine ⟨2893521150061422188217937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15432112800327585003828997 2893521150061422188217937)
                ·
                  refine ⟨2170140862546066641163453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2893521150061422188217937 2170140862546066641163453)
                  ·
                    refine ⟨813802823454774990436295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2170140862546066641163453 813802823454774990436295)
                    ·
                      rfl

theorem cell22_2377313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_2377313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377313 prefixEnd_2377313 := by exact prefixLift 2377313
  have htrace : WordTrace (prefixWord ++ tailWord_2377313) baseStart_2377313 baseEnd_2377313 := by
    simpa [prefixWord, tailWord_2377313, baseEnd_2377313] using wordTrace_append hprefix tailTrace_2377313
  have hstable : (prefixWord ++ tailWord_2377313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377313).length < 2 ^ (prefixWord ++ tailWord_2377313).sum := by decide
  have hdescent : baseEnd_2377313 < baseStart_2377313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377315 : List Nat := [1, 1, 1, 5, 1, 4, 3, 2, 4]
def baseStart_2377315 : Nat := 118140960795 + 2377315 * 2 ^ 59
def prefixEnd_2377315 : Nat := 4983230072969 + 3 ^ 40 * 2377315 * 2
def baseEnd_2377315 : Nat := 271267836031882550628763

theorem tailTrace_2377315 : CollatzResearch.WordTrace tailWord_2377315 prefixEnd_2377315 271267836031882550628763 := by
  unfold tailWord_2377315
  simp only [CollatzResearch.WordTrace]
  refine ⟨86707801382401242922757399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57805200921600828615171599 86707801382401242922757399)
  ·
    refine ⟨130061702073601864384136099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86707801382401242922757399 130061702073601864384136099)
    ·
      refine ⟨195092553110402796576204149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130061702073601864384136099 195092553110402796576204149)
      ·
        refine ⟨18289926854100262179019139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 195092553110402796576204149 18289926854100262179019139)
        ·
          refine ⟨27434890281150393268528709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18289926854100262179019139 27434890281150393268528709)
          ·
            refine ⟨5144041927715698737849133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27434890281150393268528709 5144041927715698737849133)
            ·
              refine ⟨1929015722893387026693425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5144041927715698737849133 1929015722893387026693425)
              ·
                refine ⟨1446761792170040270020069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1929015722893387026693425 1446761792170040270020069)
                ·
                  refine ⟨271267836031882550628763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1446761792170040270020069 271267836031882550628763)
                  ·
                    rfl

theorem cell22_2377315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 4].length) (baseStart_2377315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377315 prefixEnd_2377315 := by exact prefixLift 2377315
  have htrace : WordTrace (prefixWord ++ tailWord_2377315) baseStart_2377315 baseEnd_2377315 := by
    simpa [prefixWord, tailWord_2377315, baseEnd_2377315] using wordTrace_append hprefix tailTrace_2377315
  have hstable : (prefixWord ++ tailWord_2377315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377315).length < 2 ^ (prefixWord ++ tailWord_2377315).sum := by decide
  have hdescent : baseEnd_2377315 < baseStart_2377315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377330 : List Nat := [3, 2, 1, 2, 3, 2, 1, 3, 2, 3]
def baseStart_2377330 : Nat := 118140960795 + 2377330 * 2 ^ 59
def prefixEnd_2377330 : Nat := 4983230072969 + 3 ^ 40 * 2377330 * 2
def baseEnd_2377330 : Nat := 813808642902192612761243

theorem tailTrace_2377330 : CollatzResearch.WordTrace tailWord_2377330 prefixEnd_2377330 813808642902192612761243 := by
  unfold tailWord_2377330
  simp only [CollatzResearch.WordTrace]
  refine ⟨21677087119336725121138361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57805565651564600323035629 21677087119336725121138361)
  ·
    refine ⟨16257815339502543840853771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21677087119336725121138361 16257815339502543840853771)
    ·
      refine ⟨24386723009253815761280657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16257815339502543840853771 24386723009253815761280657)
      ·
        refine ⟨18290042256940361820960493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24386723009253815761280657 18290042256940361820960493)
        ·
          refine ⟨6858765846352635682860185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18290042256940361820960493 6858765846352635682860185)
          ·
            refine ⟨5144074384764476762145139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6858765846352635682860185 5144074384764476762145139)
            ·
              refine ⟨7716111577146715143217709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5144074384764476762145139 7716111577146715143217709)
              ·
                refine ⟨2893541841430018178706641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7716111577146715143217709 2893541841430018178706641)
                ·
                  refine ⟨2170156381072513634029981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2893541841430018178706641 2170156381072513634029981)
                  ·
                    refine ⟨813808642902192612761243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2170156381072513634029981 813808642902192612761243)
                    ·
                      rfl

theorem cell22_2377330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_2377330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377330 prefixEnd_2377330 := by exact prefixLift 2377330
  have htrace : WordTrace (prefixWord ++ tailWord_2377330) baseStart_2377330 baseEnd_2377330 := by
    simpa [prefixWord, tailWord_2377330, baseEnd_2377330] using wordTrace_append hprefix tailTrace_2377330
  have hstable : (prefixWord ++ tailWord_2377330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377330).length < 2 ^ (prefixWord ++ tailWord_2377330).sum := by decide
  have hdescent : baseEnd_2377330 < baseStart_2377330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377416 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 8]
def baseStart_2377416 : Nat := 118140960795 + 2377416 * 2 ^ 59
def prefixEnd_2377416 : Nat := 4983230072969 + 3 ^ 40 * 2377416 * 2
def baseEnd_2377416 : Nat := 271279360819905685036993

theorem tailTrace_2377416 : CollatzResearch.WordTrace tailWord_2377416 prefixEnd_2377416 271279360819905685036993 := by
  unfold tailWord_2377416
  simp only [CollatzResearch.WordTrace]
  refine ⟨43355742577517668586092051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57807656770023558114789401 43355742577517668586092051)
  ·
    refine ⟨65033613866276502879138077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43355742577517668586092051 65033613866276502879138077)
    ·
      refine ⟨24387605199853688579676779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65033613866276502879138077 24387605199853688579676779)
      ·
        refine ⟨36581407799780532869515169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24387605199853688579676779 36581407799780532869515169)
        ·
          refine ⟨27436055849835399652136377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36581407799780532869515169 27436055849835399652136377)
          ·
            refine ⟨20577041887376549739102283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27436055849835399652136377 20577041887376549739102283)
            ·
              refine ⟨30865562831064824608653425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20577041887376549739102283 30865562831064824608653425)
              ·
                refine ⟨23149172123298618456490069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30865562831064824608653425 23149172123298618456490069)
                ·
                  refine ⟨271279360819905685036993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23149172123298618456490069 271279360819905685036993)
                  ·
                    rfl

theorem cell22_2377416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 8].length) (baseStart_2377416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377416 prefixEnd_2377416 := by exact prefixLift 2377416
  have htrace : WordTrace (prefixWord ++ tailWord_2377416) baseStart_2377416 baseEnd_2377416 := by
    simpa [prefixWord, tailWord_2377416, baseEnd_2377416] using wordTrace_append hprefix tailTrace_2377416
  have hstable : (prefixWord ++ tailWord_2377416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377416).length < 2 ^ (prefixWord ++ tailWord_2377416).sum := by decide
  have hdescent : baseEnd_2377416 < baseStart_2377416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377433 : List Nat := [1, 2, 1, 2, 3, 4, 2, 1, 6]
def baseStart_2377433 : Nat := 118140960795 + 2377433 * 2 ^ 59
def prefixEnd_2377433 : Nat := 4983230072969 + 3 ^ 40 * 2377433 * 2
def baseEnd_2377433 : Nat := 271281300635711559145309

theorem tailTrace_2377433 : CollatzResearch.WordTrace tailWord_2377433 prefixEnd_2377433 271281300635711559145309 := by
  unfold tailWord_2377433
  simp only [CollatzResearch.WordTrace]
  refine ⟨86712105195973749075552953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57808070130649166050368635 86712105195973749075552953)
  ·
    refine ⟨65034078896980311806664715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86712105195973749075552953 65034078896980311806664715)
    ·
      refine ⟨97551118345470467709997073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65034078896980311806664715 97551118345470467709997073)
      ·
        refine ⟨73163338759102850782497805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97551118345470467709997073 73163338759102850782497805)
        ·
          refine ⟨27436252034663569043436677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73163338759102850782497805 27436252034663569043436677)
          ·
            refine ⟨5144297256499419195644377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27436252034663569043436677 5144297256499419195644377)
            ·
              refine ⟨3858222942374564396733283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5144297256499419195644377 3858222942374564396733283)
              ·
                refine ⟨5787334413561846595099925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3858222942374564396733283 5787334413561846595099925)
                ·
                  refine ⟨271281300635711559145309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5787334413561846595099925 271281300635711559145309)
                  ·
                    rfl

theorem cell22_2377433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 6].length) (baseStart_2377433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377433 prefixEnd_2377433 := by exact prefixLift 2377433
  have htrace : WordTrace (prefixWord ++ tailWord_2377433) baseStart_2377433 baseEnd_2377433 := by
    simpa [prefixWord, tailWord_2377433, baseEnd_2377433] using wordTrace_append hprefix tailTrace_2377433
  have hstable : (prefixWord ++ tailWord_2377433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377433).length < 2 ^ (prefixWord ++ tailWord_2377433).sum := by decide
  have hdescent : baseEnd_2377433 < baseStart_2377433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377542 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_2377542 : Nat := 118140960795 + 2377542 * 2 ^ 59
def prefixEnd_2377542 : Nat := 4983230072969 + 3 ^ 40 * 2377542 * 2
def baseEnd_2377542 : Nat := 813881214834694726460593

theorem tailTrace_2377542 : CollatzResearch.WordTrace tailWord_2377542 prefixEnd_2377542 813881214834694726460593 := by
  unfold tailWord_2377542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2709877523518089396602215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 57810720501719240460847253 2709877523518089396602215)
  ·
    refine ⟨4064816285277134094903323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2709877523518089396602215 4064816285277134094903323)
    ·
      refine ⟨6097224427915701142354985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4064816285277134094903323 6097224427915701142354985)
      ·
        refine ⟨4572918320936775856766239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6097224427915701142354985 4572918320936775856766239)
        ·
          refine ⟨6859377481405163785149359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4572918320936775856766239 6859377481405163785149359)
          ·
            refine ⟨10289066222107745677724039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6859377481405163785149359 10289066222107745677724039)
            ·
              refine ⟨15433599333161618516586059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10289066222107745677724039 15433599333161618516586059)
              ·
                refine ⟨23150398999742427774879089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15433599333161618516586059 23150398999742427774879089)
                ·
                  refine ⟨17362799249806820831159317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23150398999742427774879089 17362799249806820831159317)
                  ·
                    refine ⟨813881214834694726460593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17362799249806820831159317 813881214834694726460593)
                    ·
                      rfl

theorem cell22_2377542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_2377542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377542 prefixEnd_2377542 := by exact prefixLift 2377542
  have htrace : WordTrace (prefixWord ++ tailWord_2377542) baseStart_2377542 baseEnd_2377542 := by
    simpa [prefixWord, tailWord_2377542, baseEnd_2377542] using wordTrace_append hprefix tailTrace_2377542
  have hstable : (prefixWord ++ tailWord_2377542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377542).length < 2 ^ (prefixWord ++ tailWord_2377542).sum := by decide
  have hdescent : baseEnd_2377542 < baseStart_2377542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377544 : List Nat := [2, 1, 3, 1, 1, 4, 4, 2, 1, 3]
def baseStart_2377544 : Nat := 118140960795 + 2377544 * 2 ^ 59
def prefixEnd_2377544 : Nat := 4983230072969 + 3 ^ 40 * 2377544 * 2
def baseEnd_2377544 : Nat := 813881899475567387910587

theorem tailTrace_2377544 : CollatzResearch.WordTrace tailWord_2377544 prefixEnd_2377544 813881899475567387910587 := by
  unfold tailWord_2377544
  simp only [CollatzResearch.WordTrace]
  refine ⟨43358076849285807516421843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57810769132381076688562457 43358076849285807516421843)
  ·
    refine ⟨65037115273928711274632765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43358076849285807516421843 65037115273928711274632765)
    ·
      refine ⟨24388918227723266727987287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65037115273928711274632765 24388918227723266727987287)
      ·
        refine ⟨36583377341584900091980931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24388918227723266727987287 36583377341584900091980931)
        ·
          refine ⟨54875066012377350137971397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36583377341584900091980931 54875066012377350137971397)
          ·
            refine ⟨10289074877320753150869637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54875066012377350137971397 10289074877320753150869637)
            ·
              refine ⟨1929201539497641215788057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10289074877320753150869637 1929201539497641215788057)
              ·
                refine ⟨1446901154623230911841043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1929201539497641215788057 1446901154623230911841043)
                ·
                  refine ⟨2170351731934846367761565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1446901154623230911841043 2170351731934846367761565)
                  ·
                    refine ⟨813881899475567387910587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2170351731934846367761565 813881899475567387910587)
                    ·
                      rfl

theorem cell22_2377544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_2377544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377544 prefixEnd_2377544 := by exact prefixLift 2377544
  have htrace : WordTrace (prefixWord ++ tailWord_2377544) baseStart_2377544 baseEnd_2377544 := by
    simpa [prefixWord, tailWord_2377544, baseEnd_2377544] using wordTrace_append hprefix tailTrace_2377544
  have hstable : (prefixWord ++ tailWord_2377544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377544).length < 2 ^ (prefixWord ++ tailWord_2377544).sum := by decide
  have hdescent : baseEnd_2377544 < baseStart_2377544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377568 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 8]
def baseStart_2377568 : Nat := 118140960795 + 2377568 * 2 ^ 59
def prefixEnd_2377568 : Nat := 4983230072969 + 3 ^ 40 * 2377568 * 2
def baseEnd_2377568 : Nat := 271296705055346441770171

theorem tailTrace_2377568 : CollatzResearch.WordTrace tailWord_2377568 prefixEnd_2377568 271296705055346441770171 := by
  unfold tailWord_2377568
  simp only [CollatzResearch.WordTrace]
  refine ⟨43358514525242333565858679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57811352700323111421144905 43358514525242333565858679)
  ·
    refine ⟨65037771787863500348788019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43358514525242333565858679 65037771787863500348788019)
    ·
      refine ⟨97556657681795250523182029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65037771787863500348788019 97556657681795250523182029)
      ·
        refine ⟨36583746630673218946193261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97556657681795250523182029 36583746630673218946193261)
        ·
          refine ⟨13718904986502457104822473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36583746630673218946193261 13718904986502457104822473)
          ·
            refine ⟨10289178739876842828616855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13718904986502457104822473 10289178739876842828616855)
            ·
              refine ⟨15433768109815264242925283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10289178739876842828616855 15433768109815264242925283)
              ·
                refine ⟨23150652164722896364387925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15433768109815264242925283 23150652164722896364387925)
                ·
                  refine ⟨271296705055346441770171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23150652164722896364387925 271296705055346441770171)
                  ·
                    rfl

theorem cell22_2377568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 8].length) (baseStart_2377568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377568 prefixEnd_2377568 := by exact prefixLift 2377568
  have htrace : WordTrace (prefixWord ++ tailWord_2377568) baseStart_2377568 baseEnd_2377568 := by
    simpa [prefixWord, tailWord_2377568, baseEnd_2377568] using wordTrace_append hprefix tailTrace_2377568
  have hstable : (prefixWord ++ tailWord_2377568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377568).length < 2 ^ (prefixWord ++ tailWord_2377568).sum := by decide
  have hdescent : baseEnd_2377568 < baseStart_2377568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377600 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 4, 3]
def baseStart_2377600 : Nat := 118140960795 + 2377600 * 2 ^ 59
def prefixEnd_2377600 : Nat := 4983230072969 + 3 ^ 40 * 2377600 * 2
def baseEnd_2377600 : Nat := 813901069420001908510415

theorem tailTrace_2377600 : CollatzResearch.WordTrace tailWord_2377600 prefixEnd_2377600 813901069420001908510415 := by
  unfold tailWord_2377600
  simp only [CollatzResearch.WordTrace]
  refine ⟨43359098093184368298441127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57812130790912491064588169 43359098093184368298441127)
  ·
    refine ⟨65038647139776552447661691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43359098093184368298441127 65038647139776552447661691)
    ·
      refine ⟨97557970709664828671492537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65038647139776552447661691 97557970709664828671492537)
      ·
        refine ⟨73168478032248621503619403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97557970709664828671492537 73168478032248621503619403)
        ·
          refine ⟨109752717048372932255429105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73168478032248621503619403 109752717048372932255429105)
          ·
            refine ⟨82314537786279699191571829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109752717048372932255429105 82314537786279699191571829)
            ·
              refine ⟨7716987917463721799209859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82314537786279699191571829 7716987917463721799209859)
              ·
                refine ⟨11575481876195582698814789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7716987917463721799209859 11575481876195582698814789)
                ·
                  refine ⟨2170402851786671756027773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11575481876195582698814789 2170402851786671756027773)
                  ·
                    refine ⟨813901069420001908510415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2170402851786671756027773 813901069420001908510415)
                    ·
                      rfl

theorem cell22_2377600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 4, 3].length) (baseStart_2377600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377600 prefixEnd_2377600 := by exact prefixLift 2377600
  have htrace : WordTrace (prefixWord ++ tailWord_2377600) baseStart_2377600 baseEnd_2377600 := by
    simpa [prefixWord, tailWord_2377600, baseEnd_2377600] using wordTrace_append hprefix tailTrace_2377600
  have hstable : (prefixWord ++ tailWord_2377600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377600).length < 2 ^ (prefixWord ++ tailWord_2377600).sum := by decide
  have hdescent : baseEnd_2377600 < baseStart_2377600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377675 : List Nat := [1, 1, 1, 1, 3, 4, 3, 3, 5]
def baseStart_2377675 : Nat := 118140960795 + 2377675 * 2 ^ 59
def prefixEnd_2377675 : Nat := 4983230072969 + 3 ^ 40 * 2377675 * 2
def baseEnd_2377675 : Nat := 271308914484242237628395

theorem tailTrace_2377675 : CollatzResearch.WordTrace tailWord_2377675 prefixEnd_2377675 271308914484242237628395 := by
  unfold tailWord_2377675
  simp only [CollatzResearch.WordTrace]
  refine ⟨86720931661097024405862479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57813954440731349603908319 86720931661097024405862479)
  ·
    refine ⟨130081397491645536608793719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86720931661097024405862479 130081397491645536608793719)
    ·
      refine ⟨195122096237468304913190579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130081397491645536608793719 195122096237468304913190579)
      ·
        refine ⟨292683144356202457369785869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195122096237468304913190579 292683144356202457369785869)
        ·
          refine ⟨109756179133575921513669701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 292683144356202457369785869 109756179133575921513669701)
          ·
            refine ⟨20579283587545485283813069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109756179133575921513669701 20579283587545485283813069)
            ·
              refine ⟨7717231345329556981429901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20579283587545485283813069 7717231345329556981429901)
              ·
                refine ⟨2893961754498583868036213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7717231345329556981429901 2893961754498583868036213)
                ·
                  refine ⟨271308914484242237628395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2893961754498583868036213 271308914484242237628395)
                  ·
                    rfl

theorem cell22_2377675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 5].length) (baseStart_2377675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377675 prefixEnd_2377675 := by exact prefixLift 2377675
  have htrace : WordTrace (prefixWord ++ tailWord_2377675) baseStart_2377675 baseEnd_2377675 := by
    simpa [prefixWord, tailWord_2377675, baseEnd_2377675] using wordTrace_append hprefix tailTrace_2377675
  have hstable : (prefixWord ++ tailWord_2377675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377675).length < 2 ^ (prefixWord ++ tailWord_2377675).sum := by decide
  have hdescent : baseEnd_2377675 < baseStart_2377675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377713 : List Nat := [1, 2, 2, 2, 5, 2, 2, 2, 1, 3]
def baseStart_2377713 : Nat := 118140960795 + 2377713 * 2 ^ 59
def prefixEnd_2377713 : Nat := 4983230072969 + 3 ^ 40 * 2377713 * 2
def baseEnd_2377713 : Nat := 813939751629307280435069

theorem tailTrace_2377713 : CollatzResearch.WordTrace tailWord_2377713 prefixEnd_2377713 813939751629307280435069 := by
  unfold tailWord_2377713
  simp only [CollatzResearch.WordTrace]
  refine ⟨86722317634959356895745793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57814878423306237930497195 86722317634959356895745793)
  ·
    refine ⟨65041738226219517671809345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86722317634959356895745793 65041738226219517671809345)
    ·
      refine ⟨48781303669664638253857009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65041738226219517671809345 48781303669664638253857009)
      ·
        refine ⟨36585977752248478690392757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48781303669664638253857009 36585977752248478690392757)
        ·
          refine ⟨3429935414273294877224321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36585977752248478690392757 3429935414273294877224321)
          ·
            refine ⟨2572451560704971157918241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3429935414273294877224321 2572451560704971157918241)
            ·
              refine ⟨1929338670528728368438681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2572451560704971157918241 1929338670528728368438681)
              ·
                refine ⟨1447004002896546276329011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1929338670528728368438681 1447004002896546276329011)
                ·
                  refine ⟨2170506004344819414493517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1447004002896546276329011 2170506004344819414493517)
                  ·
                    refine ⟨813939751629307280435069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2170506004344819414493517 813939751629307280435069)
                    ·
                      rfl

theorem cell22_2377713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 1, 3].length) (baseStart_2377713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377713 prefixEnd_2377713 := by exact prefixLift 2377713
  have htrace : WordTrace (prefixWord ++ tailWord_2377713) baseStart_2377713 baseEnd_2377713 := by
    simpa [prefixWord, tailWord_2377713, baseEnd_2377713] using wordTrace_append hprefix tailTrace_2377713
  have hstable : (prefixWord ++ tailWord_2377713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377713).length < 2 ^ (prefixWord ++ tailWord_2377713).sum := by decide
  have hdescent : baseEnd_2377713 < baseStart_2377713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377752 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 4, 3]
def baseStart_2377752 : Nat := 118140960795 + 2377752 * 2 ^ 59
def prefixEnd_2377752 : Nat := 4983230072969 + 3 ^ 40 * 2377752 * 2
def baseEnd_2377752 : Nat := 813953102126324178709949

theorem tailTrace_2377752 : CollatzResearch.WordTrace tailWord_2377752 prefixEnd_2377752 813953102126324178709949 := by
  unfold tailWord_2377752
  simp only [CollatzResearch.WordTrace]
  refine ⟨43361870040909033278207755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57815826721212044370943673 43361870040909033278207755)
  ·
    refine ⟨65042805061363549917311633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43361870040909033278207755 65042805061363549917311633)
    ·
      refine ⟨48782103796022662437983725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65042805061363549917311633 48782103796022662437983725)
      ·
        refine ⟨18293288923508498414243897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48782103796022662437983725 18293288923508498414243897)
        ·
          refine ⟨13719966692631373810682923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18293288923508498414243897 13719966692631373810682923)
          ·
            refine ⟨20579950038947060716024385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13719966692631373810682923 20579950038947060716024385)
            ·
              refine ⟨15434962529210295537018289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20579950038947060716024385 15434962529210295537018289)
              ·
                refine ⟨11576221896907721652763717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15434962529210295537018289 11576221896907721652763717)
                ·
                  refine ⟨2170541605670197809893197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11576221896907721652763717 2170541605670197809893197)
                  ·
                    refine ⟨813953102126324178709949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2170541605670197809893197 813953102126324178709949)
                    ·
                      rfl

theorem cell22_2377752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 4, 3].length) (baseStart_2377752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377752 prefixEnd_2377752 := by exact prefixLift 2377752
  have htrace : WordTrace (prefixWord ++ tailWord_2377752) baseStart_2377752 baseEnd_2377752 := by
    simpa [prefixWord, tailWord_2377752, baseEnd_2377752] using wordTrace_append hprefix tailTrace_2377752
  have hstable : (prefixWord ++ tailWord_2377752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377752).length < 2 ^ (prefixWord ++ tailWord_2377752).sum := by decide
  have hdescent : baseEnd_2377752 < baseStart_2377752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377754 : List Nat := [3, 1, 1, 3, 1, 4, 2, 3, 4]
def baseStart_2377754 : Nat := 118140960795 + 2377754 * 2 ^ 59
def prefixEnd_2377754 : Nat := 4983230072969 + 3 ^ 40 * 2377754 * 2
def baseEnd_2377754 : Nat := 271317928922398946719981

theorem tailTrace_2377754 : CollatzResearch.WordTrace tailWord_2377754 prefixEnd_2377754 271317928922398946719981 := by
  unfold tailWord_2377754
  simp only [CollatzResearch.WordTrace]
  refine ⟨21680953256952705224497079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57815875351873880598658877 21680953256952705224497079)
  ·
    refine ⟨32521429885429057836745619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21680953256952705224497079 32521429885429057836745619)
    ·
      refine ⟨48782144828143586755118429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32521429885429057836745619 48782144828143586755118429)
      ·
        refine ⟨18293304310553845033169411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48782144828143586755118429 18293304310553845033169411)
        ·
          refine ⟨27439956465830767549754117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18293304310553845033169411 27439956465830767549754117)
          ·
            refine ⟨5144991837343268915578897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27439956465830767549754117 5144991837343268915578897)
            ·
              refine ⟨3858743878007451686684173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5144991837343268915578897 3858743878007451686684173)
              ·
                refine ⟨1447028954252794382506565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3858743878007451686684173 1447028954252794382506565)
                ·
                  refine ⟨271317928922398946719981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1447028954252794382506565 271317928922398946719981)
                  ·
                    rfl

theorem cell22_2377754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 4].length) (baseStart_2377754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377754 prefixEnd_2377754 := by exact prefixLift 2377754
  have htrace : WordTrace (prefixWord ++ tailWord_2377754) baseStart_2377754 baseEnd_2377754 := by
    simpa [prefixWord, tailWord_2377754, baseEnd_2377754] using wordTrace_append hprefix tailTrace_2377754
  have hstable : (prefixWord ++ tailWord_2377754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377754).length < 2 ^ (prefixWord ++ tailWord_2377754).sum := by decide
  have hdescent : baseEnd_2377754 < baseStart_2377754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377756 : List Nat := [2, 2, 3, 1, 3, 3, 2, 1, 1, 4]
def baseStart_2377756 : Nat := 118140960795 + 2377756 * 2 ^ 59
def prefixEnd_2377756 : Nat := 4983230072969 + 3 ^ 40 * 2377756 * 2
def baseEnd_2377756 : Nat := 813954471408069501609937

theorem tailTrace_2377756 : CollatzResearch.WordTrace tailWord_2377756 prefixEnd_2377756 813954471408069501609937 := by
  unfold tailWord_2377756
  simp only [CollatzResearch.WordTrace]
  refine ⟨43361942986901787619780561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57815923982535716826374081 43361942986901787619780561)
  ·
    refine ⟨32521457240176340714835421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43361942986901787619780561 32521457240176340714835421)
    ·
      refine ⟨12195546465066127768063283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32521457240176340714835421 12195546465066127768063283)
      ·
        refine ⟨18293319697599191652094925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12195546465066127768063283 18293319697599191652094925)
        ·
          refine ⟨6859994886599696869535597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18293319697599191652094925 6859994886599696869535597)
          ·
            refine ⟨2572498082474886326075849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6859994886599696869535597 2572498082474886326075849)
            ·
              refine ⟨1929373561856164744556887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2572498082474886326075849 1929373561856164744556887)
              ·
                refine ⟨2894060342784247116835331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1929373561856164744556887 2894060342784247116835331)
                ·
                  refine ⟨4341090514176370675252997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2894060342784247116835331 4341090514176370675252997)
                  ·
                    refine ⟨813954471408069501609937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4341090514176370675252997 813954471408069501609937)
                    ·
                      rfl

theorem cell22_2377756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_2377756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377756 prefixEnd_2377756 := by exact prefixLift 2377756
  have htrace : WordTrace (prefixWord ++ tailWord_2377756) baseStart_2377756 baseEnd_2377756 := by
    simpa [prefixWord, tailWord_2377756, baseEnd_2377756] using wordTrace_append hprefix tailTrace_2377756
  have hstable : (prefixWord ++ tailWord_2377756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377756).length < 2 ^ (prefixWord ++ tailWord_2377756).sum := by decide
  have hdescent : baseEnd_2377756 < baseStart_2377756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377765 : List Nat := [1, 3, 1, 2, 2, 4, 9]
def baseStart_2377765 : Nat := 118140960795 + 2377765 * 2 ^ 59
def prefixEnd_2377765 : Nat := 4983230072969 + 3 ^ 40 * 2377765 * 2
def baseEnd_2377765 : Nat := 30146576010814684375367

theorem tailTrace_2377765 : CollatzResearch.WordTrace tailWord_2377765 prefixEnd_2377765 30146576010814684375367 := by
  unfold tailWord_2377765
  simp only [CollatzResearch.WordTrace]
  refine ⟨86724214230770969776638749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57816142820513979851092499 86724214230770969776638749)
  ·
    refine ⟨32521580336539113666239531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86724214230770969776638749 32521580336539113666239531)
    ·
      refine ⟨48782370504808670499359297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32521580336539113666239531 48782370504808670499359297)
      ·
        refine ⟨36586777878606502874519473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48782370504808670499359297 36586777878606502874519473)
        ·
          refine ⟨27440083408954877155889605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36586777878606502874519473 27440083408954877155889605)
          ·
            refine ⟨5145015639179039466729301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27440083408954877155889605 5145015639179039466729301)
            ·
              refine ⟨30146576010814684375367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5145015639179039466729301 30146576010814684375367)
              ·
                rfl

theorem cell22_2377765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 9].length) (baseStart_2377765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377765 prefixEnd_2377765 := by exact prefixLift 2377765
  have htrace : WordTrace (prefixWord ++ tailWord_2377765) baseStart_2377765 baseEnd_2377765 := by
    simpa [prefixWord, tailWord_2377765, baseEnd_2377765] using wordTrace_append hprefix tailTrace_2377765
  have hstable : (prefixWord ++ tailWord_2377765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377765).length < 2 ^ (prefixWord ++ tailWord_2377765).sum := by decide
  have hdescent : baseEnd_2377765 < baseStart_2377765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377782 : List Nat := [5, 1, 2, 1, 1, 1, 2, 9]
def baseStart_2377782 : Nat := 118140960795 + 2377782 * 2 ^ 59
def prefixEnd_2377782 : Nat := 4983230072969 + 3 ^ 40 * 2377782 * 2
def baseEnd_2377782 : Nat := 90440374637712677828873

theorem tailTrace_2377782 : CollatzResearch.WordTrace tailWord_2377782 prefixEnd_2377782 90440374637712677828873 := by
  unfold tailWord_2377782
  simp only [CollatzResearch.WordTrace]
  refine ⟨5420302141981836355000475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57816556181139587786671733 5420302141981836355000475)
  ·
    refine ⟨8130453212972754532500713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5420302141981836355000475 8130453212972754532500713)
    ·
      refine ⟨6097839909729565899375535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8130453212972754532500713 6097839909729565899375535)
      ·
        refine ⟨9146759864594348849063303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6097839909729565899375535 9146759864594348849063303)
        ·
          refine ⟨13720139796891523273594955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9146759864594348849063303 13720139796891523273594955)
          ·
            refine ⟨20580209695337284910392433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13720139796891523273594955 20580209695337284910392433)
            ·
              refine ⟨15435157271502963682794325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20580209695337284910392433 15435157271502963682794325)
              ·
                refine ⟨90440374637712677828873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15435157271502963682794325 90440374637712677828873)
                ·
                  rfl

theorem cell22_2377782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_2377782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377782 prefixEnd_2377782 := by exact prefixLift 2377782
  have htrace : WordTrace (prefixWord ++ tailWord_2377782) baseStart_2377782 baseEnd_2377782 := by
    simpa [prefixWord, tailWord_2377782, baseEnd_2377782] using wordTrace_append hprefix tailTrace_2377782
  have hstable : (prefixWord ++ tailWord_2377782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377782).length < 2 ^ (prefixWord ++ tailWord_2377782).sum := by decide
  have hdescent : baseEnd_2377782 < baseStart_2377782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377882 : List Nat := [3, 1, 1, 5, 3, 1, 2, 2, 1, 3]
def baseStart_2377882 : Nat := 118140960795 + 2377882 * 2 ^ 59
def prefixEnd_2377882 : Nat := 4983230072969 + 3 ^ 40 * 2377882 * 2
def baseEnd_2377882 : Nat := 813997603783047172959551

theorem tailTrace_2377882 : CollatzResearch.WordTrace tailWord_2377882 prefixEnd_2377882 813997603783047172959551 := by
  unfold tailWord_2377882
  simp only [CollatzResearch.WordTrace]
  refine ⟨21682120392836774689661975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57818987714231399172431933 21682120392836774689661975)
  ·
    refine ⟨32523180589255162034492963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21682120392836774689661975 32523180589255162034492963)
    ·
      refine ⟨48784770883882743051739445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32523180589255162034492963 48784770883882743051739445)
      ·
        refine ⟨4573572270364007161100573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48784770883882743051739445 4573572270364007161100573)
        ·
          refine ⟨1715089601386502685412715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4573572270364007161100573 1715089601386502685412715)
          ·
            refine ⟨2572634402079754028119073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1715089601386502685412715 2572634402079754028119073)
            ·
              refine ⟨1929475801559815521089305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2572634402079754028119073 1929475801559815521089305)
              ·
                refine ⟨1447106851169861640816979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1929475801559815521089305 1447106851169861640816979)
                ·
                  refine ⟨2170660276754792461225469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1447106851169861640816979 2170660276754792461225469)
                  ·
                    refine ⟨813997603783047172959551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2170660276754792461225469 813997603783047172959551)
                    ·
                      rfl

theorem cell22_2377882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 1, 3].length) (baseStart_2377882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377882 prefixEnd_2377882 := by exact prefixLift 2377882
  have htrace : WordTrace (prefixWord ++ tailWord_2377882) baseStart_2377882 baseEnd_2377882 := by
    simpa [prefixWord, tailWord_2377882, baseEnd_2377882] using wordTrace_append hprefix tailTrace_2377882
  have hstable : (prefixWord ++ tailWord_2377882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377882).length < 2 ^ (prefixWord ++ tailWord_2377882).sum := by decide
  have hdescent : baseEnd_2377882 < baseStart_2377882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377938 : List Nat := [3, 2, 2, 2, 1, 4, 1, 2, 2, 3]
def baseStart_2377938 : Nat := 118140960795 + 2377938 * 2 ^ 59
def prefixEnd_2377938 : Nat := 4983230072969 + 3 ^ 40 * 2377938 * 2
def baseEnd_2377938 : Nat := 814016773727481693559379

theorem tailTrace_2377938 : CollatzResearch.WordTrace tailWord_2377938 prefixEnd_2377938 814016773727481693559379 := by
  unfold tailWord_2377938
  simp only [CollatzResearch.WordTrace]
  refine ⟨21682631014786055080671617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57820349372762813548457645 21682631014786055080671617)
  ·
    refine ⟨16261973261089541310503713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21682631014786055080671617 16261973261089541310503713)
    ·
      refine ⟨12196479945817155982877785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16261973261089541310503713 12196479945817155982877785)
      ·
        refine ⟨9147359959362866987158339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12196479945817155982877785 9147359959362866987158339)
        ·
          refine ⟨13721039939044300480737509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9147359959362866987158339 13721039939044300480737509)
          ·
            refine ⟨2572694988570806340138283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13721039939044300480737509 2572694988570806340138283)
            ·
              refine ⟨3859042482856209510207425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2572694988570806340138283 3859042482856209510207425)
              ·
                refine ⟨2894281862142157132655569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3859042482856209510207425 2894281862142157132655569)
                ·
                  refine ⟨2170711396606617849491677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2894281862142157132655569 2170711396606617849491677)
                  ·
                    refine ⟨814016773727481693559379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2170711396606617849491677 814016773727481693559379)
                    ·
                      rfl

theorem cell22_2377938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_2377938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377938 prefixEnd_2377938 := by exact prefixLift 2377938
  have htrace : WordTrace (prefixWord ++ tailWord_2377938) baseStart_2377938 baseEnd_2377938 := by
    simpa [prefixWord, tailWord_2377938, baseEnd_2377938] using wordTrace_append hprefix tailTrace_2377938
  have hstable : (prefixWord ++ tailWord_2377938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377938).length < 2 ^ (prefixWord ++ tailWord_2377938).sum := by decide
  have hdescent : baseEnd_2377938 < baseStart_2377938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377955 : List Nat := [1, 1, 1, 8, 1, 1, 3, 1, 2, 3]
def baseStart_2377955 : Nat := 118140960795 + 2377955 * 2 ^ 59
def prefixEnd_2377955 : Nat := 4983230072969 + 3 ^ 40 * 2377955 * 2
def baseEnd_2377955 : Nat := 814022593174899315884327

theorem tailTrace_2377955 : CollatzResearch.WordTrace tailWord_2377955 prefixEnd_2377955 814022593174899315884327 := by
  unfold tailWord_2377955
  simp only [CollatzResearch.WordTrace]
  refine ⟨86731144100082632226055319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57820762733388421484036879 86731144100082632226055319)
  ·
    refine ⟨130096716150123948339082979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86731144100082632226055319 130096716150123948339082979)
    ·
      refine ⟨195145074225185922508624469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130096716150123948339082979 195145074225185922508624469)
      ·
        refine ⟨2286856338576397529397943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 195145074225185922508624469 2286856338576397529397943)
        ·
          refine ⟨3430284507864596294096915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2286856338576397529397943 3430284507864596294096915)
          ·
            refine ⟨5145426761796894441145373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3430284507864596294096915 5145426761796894441145373)
            ·
              refine ⟨1929535035673835415429515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5145426761796894441145373 1929535035673835415429515)
              ·
                refine ⟨2894302553510753123144273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1929535035673835415429515 2894302553510753123144273)
                ·
                  refine ⟨2170726915133064842358205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2894302553510753123144273 2170726915133064842358205)
                  ·
                    refine ⟨814022593174899315884327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2170726915133064842358205 814022593174899315884327)
                    ·
                      rfl

theorem cell22_2377955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 2, 3].length) (baseStart_2377955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377955 prefixEnd_2377955 := by exact prefixLift 2377955
  have htrace : WordTrace (prefixWord ++ tailWord_2377955) baseStart_2377955 baseEnd_2377955 := by
    simpa [prefixWord, tailWord_2377955, baseEnd_2377955] using wordTrace_append hprefix tailTrace_2377955
  have hstable : (prefixWord ++ tailWord_2377955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377955).length < 2 ^ (prefixWord ++ tailWord_2377955).sum := by decide
  have hdescent : baseEnd_2377955 < baseStart_2377955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2377977 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 4, 5]
def baseStart_2377977 : Nat := 118140960795 + 2377977 * 2 ^ 59
def prefixEnd_2377977 : Nat := 4983230072969 + 3 ^ 40 * 2377977 * 2
def baseEnd_2377977 : Nat := 814030124224498591834259

theorem tailTrace_2377977 : CollatzResearch.WordTrace tailWord_2377977 prefixEnd_2377977 814030124224498591834259 := by
  unfold tailWord_2377977
  simp only [CollatzResearch.WordTrace]
  refine ⟨86731946506002929983356185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57821297670668619988904123 86731946506002929983356185)
  ·
    refine ⟨65048959879502197487517139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86731946506002929983356185 65048959879502197487517139)
    ·
      refine ⟨97573439819253296231275709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65048959879502197487517139 97573439819253296231275709)
      ·
        refine ⟨36590039932219986086728391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97573439819253296231275709 36590039932219986086728391)
        ·
          refine ⟨54885059898329979130092587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36590039932219986086728391 54885059898329979130092587)
          ·
            refine ⟨82327589847494968695138881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54885059898329979130092587 82327589847494968695138881)
            ·
              refine ⟨61745692385621226521354161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82327589847494968695138881 61745692385621226521354161)
              ·
                refine ⟨46309269289215919891015621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61745692385621226521354161 46309269289215919891015621)
                ·
                  refine ⟨8682987991727984979565429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46309269289215919891015621 8682987991727984979565429)
                  ·
                    refine ⟨814030124224498591834259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8682987991727984979565429 814030124224498591834259)
                    ·
                      rfl

theorem cell22_2377977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_2377977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2377977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2377977 prefixEnd_2377977 := by exact prefixLift 2377977
  have htrace : WordTrace (prefixWord ++ tailWord_2377977) baseStart_2377977 baseEnd_2377977 := by
    simpa [prefixWord, tailWord_2377977, baseEnd_2377977] using wordTrace_append hprefix tailTrace_2377977
  have hstable : (prefixWord ++ tailWord_2377977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2377977).length < 2 ^ (prefixWord ++ tailWord_2377977).sum := by decide
  have hdescent : baseEnd_2377977 < baseStart_2377977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2377977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378039 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 6, 3]
def baseStart_2378039 : Nat := 118140960795 + 2378039 * 2 ^ 59
def prefixEnd_2378039 : Nat := 4983230072969 + 3 ^ 40 * 2378039 * 2
def baseEnd_2378039 : Nat := 814051348091551096784069

theorem tailTrace_2378039 : CollatzResearch.WordTrace tailWord_2378039 prefixEnd_2378039 814051348091551096784069 := by
  unfold tailWord_2378039
  simp only [CollatzResearch.WordTrace]
  refine ⟨86734207831778314572113171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57822805221185543048075447 86734207831778314572113171)
  ·
    refine ⟨130101311747667471858169757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86734207831778314572113171 130101311747667471858169757)
    ·
      refine ⟨48787991905375301946813659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130101311747667471858169757 48787991905375301946813659)
      ·
        refine ⟨73181987858062952920220489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48787991905375301946813659 73181987858062952920220489)
        ·
          refine ⟨54886490893547214690165367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73181987858062952920220489 54886490893547214690165367)
          ·
            refine ⟨82329736340320822035248051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54886490893547214690165367 82329736340320822035248051)
            ·
              refine ⟨123494604510481233052872077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82329736340320822035248051 123494604510481233052872077)
              ·
                refine ⟨46310476691430462394827029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123494604510481233052872077 46310476691430462394827029)
                ·
                  refine ⟨2170803594910802924757517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46310476691430462394827029 2170803594910802924757517)
                  ·
                    refine ⟨814051348091551096784069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2170803594910802924757517 814051348091551096784069)
                    ·
                      rfl

theorem cell22_2378039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 3].length) (baseStart_2378039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378039 prefixEnd_2378039 := by exact prefixLift 2378039
  have htrace : WordTrace (prefixWord ++ tailWord_2378039) baseStart_2378039 baseEnd_2378039 := by
    simpa [prefixWord, tailWord_2378039, baseEnd_2378039] using wordTrace_append hprefix tailTrace_2378039
  have hstable : (prefixWord ++ tailWord_2378039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378039).length < 2 ^ (prefixWord ++ tailWord_2378039).sum := by decide
  have hdescent : baseEnd_2378039 < baseStart_2378039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378056 : List Nat := [2, 1, 3, 1, 1, 2, 3, 4, 2, 3]
def baseStart_2378056 : Nat := 118140960795 + 2378056 * 2 ^ 59
def prefixEnd_2378056 : Nat := 4983230072969 + 3 ^ 40 * 2378056 * 2
def baseEnd_2378056 : Nat := 814057167538968719109017

theorem tailTrace_2378056 : CollatzResearch.WordTrace tailWord_2378056 prefixEnd_2378056 814057167538968719109017 := by
  unfold tailWord_2378056
  simp only [CollatzResearch.WordTrace]
  refine ⟨43367413936358363237741011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57823218581811150983654681 43367413936358363237741011)
  ·
    refine ⟨65051120904537544856611517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43367413936358363237741011 65051120904537544856611517)
    ·
      refine ⟨24394170339201579321229319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65051120904537544856611517 24394170339201579321229319)
      ·
        refine ⟨36591255508802368981843979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24394170339201579321229319 36591255508802368981843979)
        ·
          refine ⟨54886883263203553472765969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36591255508802368981843979 54886883263203553472765969)
          ·
            refine ⟨41165162447402665104574477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54886883263203553472765969 41165162447402665104574477)
            ·
              refine ⟨15436935917775999414215429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41165162447402665104574477 15436935917775999414215429)
              ·
                refine ⟨2894425484582999890165393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15436935917775999414215429 2894425484582999890165393)
                ·
                  refine ⟨2170819113437249917624045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2894425484582999890165393 2170819113437249917624045)
                  ·
                    refine ⟨814057167538968719109017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2170819113437249917624045 814057167538968719109017)
                    ·
                      rfl

theorem cell22_2378056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_2378056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378056 prefixEnd_2378056 := by exact prefixLift 2378056
  have htrace : WordTrace (prefixWord ++ tailWord_2378056) baseStart_2378056 baseEnd_2378056 := by
    simpa [prefixWord, tailWord_2378056, baseEnd_2378056] using wordTrace_append hprefix tailTrace_2378056
  have hstable : (prefixWord ++ tailWord_2378056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378056).length < 2 ^ (prefixWord ++ tailWord_2378056).sum := by decide
  have hdescent : baseEnd_2378056 < baseStart_2378056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378088 : List Nat := [2, 1, 4, 2, 2, 3, 1, 1, 2, 4]
def baseStart_2378088 : Nat := 118140960795 + 2378088 * 2 ^ 59
def prefixEnd_2378088 : Nat := 4983230072969 + 3 ^ 40 * 2378088 * 2
def baseEnd_2378088 : Nat := 814068121792931302308919

theorem tailTrace_2378088 : CollatzResearch.WordTrace tailWord_2378088 prefixEnd_2378088 814068121792931302308919 := by
  unfold tailWord_2378088
  simp only [CollatzResearch.WordTrace]
  refine ⟨43367997504300397970323459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57823996672400530627097945 43367997504300397970323459)
  ·
    refine ⟨65051996256450596955485189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43367997504300397970323459 65051996256450596955485189)
    ·
      refine ⟨12197249298084486929153473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65051996256450596955485189 12197249298084486929153473)
      ·
        refine ⟨9147936973563365196865105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12197249298084486929153473 9147936973563365196865105)
        ·
          refine ⟨6860952730172523897648829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9147936973563365196865105 6860952730172523897648829)
          ·
            refine ⟨2572857273814696461618311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6860952730172523897648829 2572857273814696461618311)
            ·
              refine ⟨3859285910722044692427467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2572857273814696461618311 3859285910722044692427467)
              ·
                refine ⟨5788928866083067038641201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3859285910722044692427467 5788928866083067038641201)
                ·
                  refine ⟨4341696649562300278980901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5788928866083067038641201 4341696649562300278980901)
                  ·
                    refine ⟨814068121792931302308919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4341696649562300278980901 814068121792931302308919)
                    ·
                      rfl

theorem cell22_2378088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_2378088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378088 prefixEnd_2378088 := by exact prefixLift 2378088
  have htrace : WordTrace (prefixWord ++ tailWord_2378088) baseStart_2378088 baseEnd_2378088 := by
    simpa [prefixWord, tailWord_2378088, baseEnd_2378088] using wordTrace_append hprefix tailTrace_2378088
  have hstable : (prefixWord ++ tailWord_2378088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378088).length < 2 ^ (prefixWord ++ tailWord_2378088).sum := by decide
  have hdescent : baseEnd_2378088 < baseStart_2378088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378152 : List Nat := [2, 1, 6, 1, 1, 1, 3, 3, 1, 3]
def baseStart_2378152 : Nat := 118140960795 + 2378152 * 2 ^ 59
def prefixEnd_2378152 : Nat := 4983230072969 + 3 ^ 40 * 2378152 * 2
def baseEnd_2378152 : Nat := 814090030300856468708723

theorem tailTrace_2378152 : CollatzResearch.WordTrace tailWord_2378152 prefixEnd_2378152 814090030300856468708723 := by
  unfold tailWord_2378152
  simp only [CollatzResearch.WordTrace]
  refine ⟨43369164640184467435488355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57825552853579289913984473 43369164640184467435488355)
  ·
    refine ⟨65053746960276701153232533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43369164640184467435488355 65053746960276701153232533)
    ·
      refine ⟨3049394388762970366557775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65053746960276701153232533 3049394388762970366557775)
      ·
        refine ⟨4574091583144455549836663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3049394388762970366557775 4574091583144455549836663)
        ·
          refine ⟨6861137374716683324754995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4574091583144455549836663 6861137374716683324754995)
          ·
            refine ⟨10291706062075024987132493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6861137374716683324754995 10291706062075024987132493)
            ·
              refine ⟨3859389773278134370174685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10291706062075024987132493 3859389773278134370174685)
              ·
                refine ⟨1447271164979300388815507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3859389773278134370174685 1447271164979300388815507)
                ·
                  refine ⟨2170906747468950583223261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1447271164979300388815507 2170906747468950583223261)
                  ·
                    refine ⟨814090030300856468708723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2170906747468950583223261 814090030300856468708723)
                    ·
                      rfl

theorem cell22_2378152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_2378152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378152 prefixEnd_2378152 := by exact prefixLift 2378152
  have htrace : WordTrace (prefixWord ++ tailWord_2378152) baseStart_2378152 baseEnd_2378152 := by
    simpa [prefixWord, tailWord_2378152, baseEnd_2378152] using wordTrace_append hprefix tailTrace_2378152
  have hstable : (prefixWord ++ tailWord_2378152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378152).length < 2 ^ (prefixWord ++ tailWord_2378152).sum := by decide
  have hdescent : baseEnd_2378152 < baseStart_2378152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378221 : List Nat := [1, 5, 1, 3, 1, 11]
def baseStart_2378221 : Nat := 118140960795 + 2378221 * 2 ^ 59
def prefixEnd_2378221 : Nat := 4983230072969 + 3 ^ 40 * 2378221 * 2
def baseEnd_2378221 : Nat := 10050785807542756651031

theorem tailTrace_2378221 : CollatzResearch.WordTrace tailWord_2378221 prefixEnd_2378221 10050785807542756651031 := by
  unfold tailWord_2378221
  simp only [CollatzResearch.WordTrace]
  refine ⟨86740845917118959655238517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57827230611412639770159011 86740845917118959655238517)
  ·
    refine ⟨8131954304729902467678611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86740845917118959655238517 8131954304729902467678611)
    ·
      refine ⟨12197931457094853701517917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8131954304729902467678611 12197931457094853701517917)
      ·
        refine ⟨4574224296410570138069219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12197931457094853701517917 4574224296410570138069219)
        ·
          refine ⟨6861336444615855207103829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4574224296410570138069219 6861336444615855207103829)
          ·
            refine ⟨10050785807542756651031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6861336444615855207103829 10050785807542756651031)
            ·
              rfl

theorem cell22_2378221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 11].length) (baseStart_2378221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378221 prefixEnd_2378221 := by exact prefixLift 2378221
  have htrace : WordTrace (prefixWord ++ tailWord_2378221) baseStart_2378221 baseEnd_2378221 := by
    simpa [prefixWord, tailWord_2378221, baseEnd_2378221] using wordTrace_append hprefix tailTrace_2378221
  have hstable : (prefixWord ++ tailWord_2378221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378221).length < 2 ^ (prefixWord ++ tailWord_2378221).sum := by decide
  have hdescent : baseEnd_2378221 < baseStart_2378221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378300 : List Nat := [2, 2, 2, 2, 3, 2, 3, 1, 5]
def baseStart_2378300 : Nat := 118140960795 + 2378300 * 2 ^ 59
def prefixEnd_2378300 : Nat := 4983230072969 + 3 ^ 40 * 2378300 * 2
def baseEnd_2378300 : Nat := 271380231241811138669423

theorem tailTrace_2378300 : CollatzResearch.WordTrace tailWord_2378300 prefixEnd_2378300 271380231241811138669423 := by
  unfold tailWord_2378300
  simp only [CollatzResearch.WordTrace]
  refine ⟨43371863641916378073682177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57829151522555170764909569 43371863641916378073682177)
  ·
    refine ⟨32528897731437283555261633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43371863641916378073682177 32528897731437283555261633)
    ·
      refine ⟨24396673298577962666446225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32528897731437283555261633 24396673298577962666446225)
      ·
        refine ⟨18297504973933471999834669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24396673298577962666446225 18297504973933471999834669)
        ·
          refine ⟨6861564365225051999938001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18297504973933471999834669 6861564365225051999938001)
          ·
            refine ⟨5146173273918788999953501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6861564365225051999938001 5146173273918788999953501)
            ·
              refine ⟨1929814977719545874982563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5146173273918788999953501 1929814977719545874982563)
              ·
                refine ⟨2894722466579318812473845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1929814977719545874982563 2894722466579318812473845)
                ·
                  refine ⟨271380231241811138669423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2894722466579318812473845 271380231241811138669423)
                  ·
                    rfl

theorem cell22_2378300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 5].length) (baseStart_2378300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378300 prefixEnd_2378300 := by exact prefixLift 2378300
  have htrace : WordTrace (prefixWord ++ tailWord_2378300) baseStart_2378300 baseEnd_2378300 := by
    simpa [prefixWord, tailWord_2378300, baseEnd_2378300] using wordTrace_append hprefix tailTrace_2378300
  have hstable : (prefixWord ++ tailWord_2378300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378300).length < 2 ^ (prefixWord ++ tailWord_2378300).sum := by decide
  have hdescent : baseEnd_2378300 < baseStart_2378300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378371 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 2, 7]
def baseStart_2378371 : Nat := 118140960795 + 2378371 * 2 ^ 59
def prefixEnd_2378371 : Nat := 4983230072969 + 3 ^ 40 * 2378371 * 2
def baseEnd_2378371 : Nat := 814164998476412897483051

theorem tailTrace_2378371 : CollatzResearch.WordTrace tailWord_2378371 prefixEnd_2378371 814164998476412897483051 := by
  unfold tailWord_2378371
  simp only [CollatzResearch.WordTrace]
  refine ⟨86746316866575535273198967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57830877911050356848799311 86746316866575535273198967)
  ·
    refine ⟨130119475299863302909798451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86746316866575535273198967 130119475299863302909798451)
    ·
      refine ⟨195179212949794954364697677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130119475299863302909798451 195179212949794954364697677)
      ·
        refine ⟨73192204856173107886761629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195179212949794954364697677 73192204856173107886761629)
        ·
          refine ⟨27447076821064915457535611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73192204856173107886761629 27447076821064915457535611)
          ·
            refine ⟨41170615231597373186303417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27447076821064915457535611 41170615231597373186303417)
            ·
              refine ⟨30877961423698029889727563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41170615231597373186303417 30877961423698029889727563)
              ·
                refine ⟨46316942135547044834591345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30877961423698029889727563 46316942135547044834591345)
                ·
                  refine ⟨34737706601660283625943509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46316942135547044834591345 34737706601660283625943509)
                  ·
                    refine ⟨814164998476412897483051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34737706601660283625943509 814164998476412897483051)
                    ·
                      rfl

theorem cell22_2378371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 7].length) (baseStart_2378371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378371 prefixEnd_2378371 := by exact prefixLift 2378371
  have htrace : WordTrace (prefixWord ++ tailWord_2378371) baseStart_2378371 baseEnd_2378371 := by
    simpa [prefixWord, tailWord_2378371, baseEnd_2378371] using wordTrace_append hprefix tailTrace_2378371
  have hstable : (prefixWord ++ tailWord_2378371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378371).length < 2 ^ (prefixWord ++ tailWord_2378371).sum := by decide
  have hdescent : baseEnd_2378371 < baseStart_2378371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378394 : List Nat := [3, 1, 1, 6, 1, 1, 2, 2, 2, 3]
def baseStart_2378394 : Nat := 118140960795 + 2378394 * 2 ^ 59
def prefixEnd_2378394 : Nat := 4983230072969 + 3 ^ 40 * 2378394 * 2
def baseEnd_2378394 : Nat := 814172871846448504157981

theorem tailTrace_2378394 : CollatzResearch.WordTrace tailWord_2378394 prefixEnd_2378394 814172871846448504157981 := by
  unfold tailWord_2378394
  simp only [CollatzResearch.WordTrace]
  refine ⟨21686788936373052550321559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57831437163661473467524157 21686788936373052550321559)
  ·
    refine ⟨32530183404559578825482339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21686788936373052550321559 32530183404559578825482339)
    ·
      refine ⟨48795275106839368238223509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32530183404559578825482339 48795275106839368238223509)
      ·
        refine ⟨2287278520633095386166727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48795275106839368238223509 2287278520633095386166727)
        ·
          refine ⟨3430917780949643079250091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2287278520633095386166727 3430917780949643079250091)
          ·
            refine ⟨5146376671424464618875137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3430917780949643079250091 5146376671424464618875137)
            ·
              refine ⟨3859782503568348464156353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5146376671424464618875137 3859782503568348464156353)
              ·
                refine ⟨2894836877676261348117265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3859782503568348464156353 2894836877676261348117265)
                ·
                  refine ⟨2171127658257196011087949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2894836877676261348117265 2171127658257196011087949)
                  ·
                    refine ⟨814172871846448504157981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2171127658257196011087949 814172871846448504157981)
                    ·
                      rfl

theorem cell22_2378394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 2, 3].length) (baseStart_2378394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378394 prefixEnd_2378394 := by exact prefixLift 2378394
  have htrace : WordTrace (prefixWord ++ tailWord_2378394) baseStart_2378394 baseEnd_2378394 := by
    simpa [prefixWord, tailWord_2378394, baseEnd_2378394] using wordTrace_append hprefix tailTrace_2378394
  have hstable : (prefixWord ++ tailWord_2378394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378394).length < 2 ^ (prefixWord ++ tailWord_2378394).sum := by decide
  have hdescent : baseEnd_2378394 < baseStart_2378394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378407 : List Nat := [1, 1, 6, 3, 1, 2, 1, 7]
def baseStart_2378407 : Nat := 118140960795 + 2378407 * 2 ^ 59
def prefixEnd_2378407 : Nat := 4983230072969 + 3 ^ 40 * 2378407 * 2
def baseEnd_2378407 : Nat := 90464146890235644842549

theorem tailTrace_2378407 : CollatzResearch.WordTrace tailWord_2378407 prefixEnd_2378407 90464146890235644842549 := by
  unfold tailWord_2378407
  simp only [CollatzResearch.WordTrace]
  refine ⟨86747629894445113421509475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57831753262963408947672983 86747629894445113421509475)
  ·
    refine ⟨130121444841667670132264213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86747629894445113421509475 130121444841667670132264213)
    ·
      refine ⟨6099442726953172037449885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 130121444841667670132264213 6099442726953172037449885)
      ·
        refine ⟨2287291022607439514043707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6099442726953172037449885 2287291022607439514043707)
        ·
          refine ⟨3430936533911159271065561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2287291022607439514043707 3430936533911159271065561)
          ·
            refine ⟨2573202400433369453299171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3430936533911159271065561 2573202400433369453299171)
            ·
              refine ⟨3859803600650054179948757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2573202400433369453299171 3859803600650054179948757)
              ·
                refine ⟨90464146890235644842549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3859803600650054179948757 90464146890235644842549)
                ·
                  rfl

theorem cell22_2378407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 7].length) (baseStart_2378407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378407 prefixEnd_2378407 := by exact prefixLift 2378407
  have htrace : WordTrace (prefixWord ++ tailWord_2378407) baseStart_2378407 baseEnd_2378407 := by
    simpa [prefixWord, tailWord_2378407, baseEnd_2378407] using wordTrace_append hprefix tailTrace_2378407
  have hstable : (prefixWord ++ tailWord_2378407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378407).length < 2 ^ (prefixWord ++ tailWord_2378407).sum := by decide
  have hdescent : baseEnd_2378407 < baseStart_2378407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378463 : List Nat := [1, 1, 2, 3, 2, 3, 1, 3, 6]
def baseStart_2378463 : Nat := 118140960795 + 2378463 * 2 ^ 59
def prefixEnd_2378463 : Nat := 4983230072969 + 3 ^ 40 * 2378463 * 2
def baseEnd_2378463 : Nat := 271398830652185108060923

theorem tailTrace_2378463 : CollatzResearch.WordTrace tailWord_2378463 prefixEnd_2378463 271398830652185108060923 := by
  unfold tailWord_2378463
  simp only [CollatzResearch.WordTrace]
  refine ⟨86749672382242234985548043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57833114921494823323698695 86749672382242234985548043)
  ·
    refine ⟨130124508573363352478322065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86749672382242234985548043 130124508573363352478322065)
    ·
      refine ⟨97593381430022514358741549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130124508573363352478322065 97593381430022514358741549)
      ·
        refine ⟨36597518036258442884528081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97593381430022514358741549 36597518036258442884528081)
        ·
          refine ⟨27448138527193832163396061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36597518036258442884528081 27448138527193832163396061)
          ·
            refine ⟨10293051947697687061273523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27448138527193832163396061 10293051947697687061273523)
            ·
              refine ⟨15439577921546530591910285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10293051947697687061273523 15439577921546530591910285)
              ·
                refine ⟨5789841720579948971966357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15439577921546530591910285 5789841720579948971966357)
                ·
                  refine ⟨271398830652185108060923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5789841720579948971966357 271398830652185108060923)
                  ·
                    rfl

theorem cell22_2378463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 6].length) (baseStart_2378463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378463 prefixEnd_2378463 := by exact prefixLift 2378463
  have htrace : WordTrace (prefixWord ++ tailWord_2378463) baseStart_2378463 baseEnd_2378463 := by
    simpa [prefixWord, tailWord_2378463, baseEnd_2378463] using wordTrace_append hprefix tailTrace_2378463
  have hstable : (prefixWord ++ tailWord_2378463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378463).length < 2 ^ (prefixWord ++ tailWord_2378463).sum := by decide
  have hdescent : baseEnd_2378463 < baseStart_2378463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378482 : List Nat := [3, 2, 1, 3, 1, 3, 2, 2, 1, 4]
def baseStart_2378482 : Nat := 118140960795 + 2378482 * 2 ^ 59
def prefixEnd_2378482 : Nat := 4983230072969 + 3 ^ 40 * 2378482 * 2
def baseEnd_2378482 : Nat := 814202996044845607957711

theorem tailTrace_2378482 : CollatzResearch.WordTrace tailWord_2378482 prefixEnd_2378482 814202996044845607957711 := by
  unfold tailWord_2378482
  simp only [CollatzResearch.WordTrace]
  refine ⟨21687591342293350307622425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57833576912782267486993133 21687591342293350307622425)
  ·
    refine ⟨16265693506720012730716819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21687591342293350307622425 16265693506720012730716819)
    ·
      refine ⟨24398540260080019096075229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16265693506720012730716819 24398540260080019096075229)
      ·
        refine ⟨9149452597530007161028211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24398540260080019096075229 9149452597530007161028211)
        ·
          refine ⟨13724178896295010741542317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9149452597530007161028211 13724178896295010741542317)
          ·
            refine ⟨5146567086110629028078369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13724178896295010741542317 5146567086110629028078369)
            ·
              refine ⟨3859925314582971771058777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5146567086110629028078369 3859925314582971771058777)
              ·
                refine ⟨2894943985937228828294083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3859925314582971771058777 2894943985937228828294083)
                ·
                  refine ⟨4342415978905843242441125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2894943985937228828294083 4342415978905843242441125)
                  ·
                    refine ⟨814202996044845607957711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4342415978905843242441125 814202996044845607957711)
                    ·
                      rfl

theorem cell22_2378482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_2378482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378482 prefixEnd_2378482 := by exact prefixLift 2378482
  have htrace : WordTrace (prefixWord ++ tailWord_2378482) baseStart_2378482 baseEnd_2378482 := by
    simpa [prefixWord, tailWord_2378482, baseEnd_2378482] using wordTrace_append hprefix tailTrace_2378482
  have hstable : (prefixWord ++ tailWord_2378482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378482).length < 2 ^ (prefixWord ++ tailWord_2378482).sum := by decide
  have hdescent : baseEnd_2378482 < baseStart_2378482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378493 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_2378493 : Nat := 118140960795 + 2378493 * 2 ^ 59
def prefixEnd_2378493 : Nat := 4983230072969 + 3 ^ 40 * 2378493 * 2
def baseEnd_2378493 : Nat := 814206761569645245932677

theorem tailTrace_2378493 : CollatzResearch.WordTrace tailWord_2378493 prefixEnd_2378493 814206761569645245932677 := by
  unfold tailWord_2378493
  simp only [CollatzResearch.WordTrace]
  refine ⟨86750766572133550109140133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57833844381422366739426755 86750766572133550109140133)
  ·
    refine ⟨16265768732275040645463775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86750766572133550109140133 16265768732275040645463775)
    ·
      refine ⟨24398653098412560968195663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16265768732275040645463775 24398653098412560968195663)
      ·
        refine ⟨36597979647618841452293495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24398653098412560968195663 36597979647618841452293495)
        ·
          refine ⟨54896969471428262178440243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36597979647618841452293495 54896969471428262178440243)
          ·
            refine ⟨82345454207142393267660365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54896969471428262178440243 82345454207142393267660365)
            ·
              refine ⟨30879545327678397475372637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82345454207142393267660365 30879545327678397475372637)
              ·
                refine ⟨11579829497879399053264739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30879545327678397475372637 11579829497879399053264739)
                ·
                  refine ⟨17369744246819098579897109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11579829497879399053264739 17369744246819098579897109)
                  ·
                    refine ⟨814206761569645245932677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17369744246819098579897109 814206761569645245932677)
                    ·
                      rfl

theorem cell22_2378493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_2378493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378493 prefixEnd_2378493 := by exact prefixLift 2378493
  have htrace : WordTrace (prefixWord ++ tailWord_2378493) baseStart_2378493 baseEnd_2378493 := by
    simpa [prefixWord, tailWord_2378493, baseEnd_2378493] using wordTrace_append hprefix tailTrace_2378493
  have hstable : (prefixWord ++ tailWord_2378493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378493).length < 2 ^ (prefixWord ++ tailWord_2378493).sum := by decide
  have hdescent : baseEnd_2378493 < baseStart_2378493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378514 : List Nat := [3, 2, 4, 1, 2, 2, 1, 1, 6]
def baseStart_2378514 : Nat := 118140960795 + 2378514 * 2 ^ 59
def prefixEnd_2378514 : Nat := 4983230072969 + 3 ^ 40 * 2378514 * 2
def baseEnd_2378514 : Nat := 271404650099602730385871

theorem tailTrace_2378514 : CollatzResearch.WordTrace tailWord_2378514 prefixEnd_2378514 271404650099602730385871 := by
  unfold tailWord_2378514
  simp only [CollatzResearch.WordTrace]
  refine ⟨21687883126264367673913649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57834355003371647130436397 21687883126264367673913649)
  ·
    refine ⟨16265912344698275755435237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21687883126264367673913649 16265912344698275755435237)
    ·
      refine ⟨3049858564630926704144107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16265912344698275755435237 3049858564630926704144107)
      ·
        refine ⟨4574787846946390056216161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3049858564630926704144107 4574787846946390056216161)
        ·
          refine ⟨3431090885209792542162121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4574787846946390056216161 3431090885209792542162121)
          ·
            refine ⟨2573318163907344406621591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3431090885209792542162121 2573318163907344406621591)
            ·
              refine ⟨3859977245861016609932387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2573318163907344406621591 3859977245861016609932387)
              ·
                refine ⟨5789965868791524914898581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3859977245861016609932387 5789965868791524914898581)
                ·
                  refine ⟨271404650099602730385871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5789965868791524914898581 271404650099602730385871)
                  ·
                    rfl

theorem cell22_2378514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_2378514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378514 prefixEnd_2378514 := by exact prefixLift 2378514
  have htrace : WordTrace (prefixWord ++ tailWord_2378514) baseStart_2378514 baseEnd_2378514 := by
    simpa [prefixWord, tailWord_2378514, baseEnd_2378514] using wordTrace_append hprefix tailTrace_2378514
  have hstable : (prefixWord ++ tailWord_2378514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378514).length < 2 ^ (prefixWord ++ tailWord_2378514).sum := by decide
  have hdescent : baseEnd_2378514 < baseStart_2378514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378540 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 5, 3]
def baseStart_2378540 : Nat := 118140960795 + 2378540 * 2 ^ 59
def prefixEnd_2378540 : Nat := 4983230072969 + 3 ^ 40 * 2378540 * 2
def baseEnd_2378540 : Nat := 814222850630152790007533

theorem tailTrace_2378540 : CollatzResearch.WordTrace tailWord_2378540 prefixEnd_2378540 814222850630152790007533 := by
  unfold tailWord_2378540
  simp only [CollatzResearch.WordTrace]
  refine ⟨43376240401481638568050537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57834987201975518090734049 43376240401481638568050537)
  ·
    refine ⟨32532180301111228926037903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43376240401481638568050537 32532180301111228926037903)
    ·
      refine ⟨48798270451666843389056855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32532180301111228926037903 48798270451666843389056855)
      ·
        refine ⟨73197405677500265083585283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48798270451666843389056855 73197405677500265083585283)
        ·
          refine ⟨109796108516250397625377925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73197405677500265083585283 109796108516250397625377925)
          ·
            refine ⟨20586770346796949554758361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109796108516250397625377925 20586770346796949554758361)
            ·
              refine ⟨15440077760097712166068771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20586770346796949554758361 15440077760097712166068771)
              ·
                refine ⟨23160116640146568249103157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15440077760097712166068771 23160116640146568249103157)
                ·
                  refine ⟨2171260935013740773353421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23160116640146568249103157 2171260935013740773353421)
                  ·
                    refine ⟨814222850630152790007533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2171260935013740773353421 814222850630152790007533)
                    ·
                      rfl

theorem cell22_2378540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 3].length) (baseStart_2378540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378540 prefixEnd_2378540 := by exact prefixLift 2378540
  have htrace : WordTrace (prefixWord ++ tailWord_2378540) baseStart_2378540 baseEnd_2378540 := by
    simpa [prefixWord, tailWord_2378540, baseEnd_2378540] using wordTrace_append hprefix tailTrace_2378540
  have hstable : (prefixWord ++ tailWord_2378540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378540).length < 2 ^ (prefixWord ++ tailWord_2378540).sum := by decide
  have hdescent : baseEnd_2378540 < baseStart_2378540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378585 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 2, 5]
def baseStart_2378585 : Nat := 118140960795 + 2378585 * 2 ^ 59
def prefixEnd_2378585 : Nat := 4983230072969 + 3 ^ 40 * 2378585 * 2
def baseEnd_2378585 : Nat := 814238255049787672632395

theorem tailTrace_2378585 : CollatzResearch.WordTrace tailWord_2378585 prefixEnd_2378585 814238255049787672632395 := by
  unfold tailWord_2378585
  simp only [CollatzResearch.WordTrace]
  refine ⟨86754122087800249821489209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57836081391866833214326139 86754122087800249821489209)
  ·
    refine ⟨65065591565850187366116907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86754122087800249821489209 65065591565850187366116907)
    ·
      refine ⟨97598387348775281049175361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65065591565850187366116907 97598387348775281049175361)
      ·
        refine ⟨73198790511581460786881521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97598387348775281049175361 73198790511581460786881521)
        ·
          refine ⟨54899092883686095590161141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73198790511581460786881521 54899092883686095590161141)
          ·
            refine ⟨5146789957845571461577607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54899092883686095590161141 5146789957845571461577607)
            ·
              refine ⟨7720184936768357192366411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5146789957845571461577607 7720184936768357192366411)
              ·
                refine ⟨11580277405152535788549617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7720184936768357192366411 11580277405152535788549617)
                ·
                  refine ⟨8685208053864401841412213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11580277405152535788549617 8685208053864401841412213)
                  ·
                    refine ⟨814238255049787672632395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8685208053864401841412213 814238255049787672632395)
                    ·
                      rfl

theorem cell22_2378585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 5].length) (baseStart_2378585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378585 prefixEnd_2378585 := by exact prefixLift 2378585
  have htrace : WordTrace (prefixWord ++ tailWord_2378585) baseStart_2378585 baseEnd_2378585 := by
    simpa [prefixWord, tailWord_2378585, baseEnd_2378585] using wordTrace_append hprefix tailTrace_2378585
  have hstable : (prefixWord ++ tailWord_2378585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378585).length < 2 ^ (prefixWord ++ tailWord_2378585).sum := by decide
  have hdescent : baseEnd_2378585 < baseStart_2378585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378617 : List Nat := [1, 2, 1, 3, 2, 4, 1, 3, 1, 4]
def baseStart_2378617 : Nat := 118140960795 + 2378617 * 2 ^ 59
def prefixEnd_2378617 : Nat := 4983230072969 + 3 ^ 40 * 2378617 * 2
def baseEnd_2378617 : Nat := 814249209303750255832297

theorem tailTrace_2378617 : CollatzResearch.WordTrace tailWord_2378617 prefixEnd_2378617 814249209303750255832297 := by
  unfold tailWord_2378617
  simp only [CollatzResearch.WordTrace]
  refine ⟨86755289223684319286654105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57836859482456212857769403 86755289223684319286654105)
  ·
    refine ⟨65066466917763239464990579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86755289223684319286654105 65066466917763239464990579)
    ·
      refine ⟨97599700376644859197485869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65066466917763239464990579 97599700376644859197485869)
      ·
        refine ⟨36599887641241822199057201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97599700376644859197485869 36599887641241822199057201)
        ·
          refine ⟨27449915730931366649292901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36599887641241822199057201 27449915730931366649292901)
          ·
            refine ⟨5146859199549631246742419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27449915730931366649292901 5146859199549631246742419)
            ·
              refine ⟨7720288799324446870113629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5146859199549631246742419 7720288799324446870113629)
              ·
                refine ⟨2895108299746667576292611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7720288799324446870113629 2895108299746667576292611)
                ·
                  refine ⟨4342662449620001364438917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2895108299746667576292611 4342662449620001364438917)
                  ·
                    refine ⟨814249209303750255832297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4342662449620001364438917 814249209303750255832297)
                    ·
                      rfl

theorem cell22_2378617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 4].length) (baseStart_2378617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378617 prefixEnd_2378617 := by exact prefixLift 2378617
  have htrace : WordTrace (prefixWord ++ tailWord_2378617) baseStart_2378617 baseEnd_2378617 := by
    simpa [prefixWord, tailWord_2378617, baseEnd_2378617] using wordTrace_append hprefix tailTrace_2378617
  have hstable : (prefixWord ++ tailWord_2378617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378617).length < 2 ^ (prefixWord ++ tailWord_2378617).sum := by decide
  have hdescent : baseEnd_2378617 < baseStart_2378617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378632 : List Nat := [2, 1, 3, 3, 2, 2, 2, 1, 6]
def baseStart_2378632 : Nat := 118140960795 + 2378632 * 2 ^ 59
def prefixEnd_2378632 : Nat := 4983230072969 + 3 ^ 40 * 2378632 * 2
def baseEnd_2378632 : Nat := 271418114703431738902417

theorem tailTrace_2378632 : CollatzResearch.WordTrace tailWord_2378632 prefixEnd_2378632 271418114703431738902417 := by
  unfold tailWord_2378632
  simp only [CollatzResearch.WordTrace]
  refine ⟨43377918159314988424225075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57837224212419984565633433 43377918159314988424225075)
  ·
    refine ⟨65066877238972482636337613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43377918159314988424225075 65066877238972482636337613)
    ·
      refine ⟨24400078964614680988626605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65066877238972482636337613 24400078964614680988626605)
      ·
        refine ⟨9150029611730505370734977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24400078964614680988626605 9150029611730505370734977)
        ·
          refine ⟨6862522208797879028051233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9150029611730505370734977 6862522208797879028051233)
          ·
            refine ⟨5146891656598409271038425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6862522208797879028051233 5146891656598409271038425)
            ·
              refine ⟨3860168742448806953278819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5146891656598409271038425 3860168742448806953278819)
              ·
                refine ⟨5790253113673210429918229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3860168742448806953278819 5790253113673210429918229)
                ·
                  refine ⟨271418114703431738902417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5790253113673210429918229 271418114703431738902417)
                  ·
                    rfl

theorem cell22_2378632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 6].length) (baseStart_2378632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378632 prefixEnd_2378632 := by exact prefixLift 2378632
  have htrace : WordTrace (prefixWord ++ tailWord_2378632) baseStart_2378632 baseEnd_2378632 := by
    simpa [prefixWord, tailWord_2378632, baseEnd_2378632] using wordTrace_append hprefix tailTrace_2378632
  have hstable : (prefixWord ++ tailWord_2378632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378632).length < 2 ^ (prefixWord ++ tailWord_2378632).sum := by decide
  have hdescent : baseEnd_2378632 < baseStart_2378632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378645 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 1, 6]
def baseStart_2378645 : Nat := 118140960795 + 2378645 * 2 ^ 59
def prefixEnd_2378645 : Nat := 4983230072969 + 3 ^ 40 * 2378645 * 2
def baseEnd_2378645 : Nat := 814258794275967516132211

theorem tailTrace_2378645 : CollatzResearch.WordTrace tailWord_2378645 prefixEnd_2378645 814258794275967516132211 := by
  unfold tailWord_2378645
  simp only [CollatzResearch.WordTrace]
  refine ⟨86756310467582880068673389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57837540311721920045782259 86756310467582880068673389)
  ·
    refine ⟨32533616425343580025752521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86756310467582880068673389 32533616425343580025752521)
    ·
      refine ⟨24400212319007685019314391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32533616425343580025752521 24400212319007685019314391)
      ·
        refine ⟨36600318478511527528971587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24400212319007685019314391 36600318478511527528971587)
        ·
          refine ⟨54900477717767291293457381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36600318478511527528971587 54900477717767291293457381)
          ·
            refine ⟨10293839572081367117523259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54900477717767291293457381 10293839572081367117523259)
            ·
              refine ⟨15440759358122050676284889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10293839572081367117523259 15440759358122050676284889)
              ·
                refine ⟨11580569518591538007213667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15440759358122050676284889 11580569518591538007213667)
                ·
                  refine ⟨17370854277887307010820501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11580569518591538007213667 17370854277887307010820501)
                  ·
                    refine ⟨814258794275967516132211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17370854277887307010820501 814258794275967516132211)
                    ·
                      rfl

theorem cell22_2378645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_2378645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378645 prefixEnd_2378645 := by exact prefixLift 2378645
  have htrace : WordTrace (prefixWord ++ tailWord_2378645) baseStart_2378645 baseEnd_2378645 := by
    simpa [prefixWord, tailWord_2378645, baseEnd_2378645] using wordTrace_append hprefix tailTrace_2378645
  have hstable : (prefixWord ++ tailWord_2378645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378645).length < 2 ^ (prefixWord ++ tailWord_2378645).sum := by decide
  have hdescent : baseEnd_2378645 < baseStart_2378645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378660 : List Nat := [2, 3, 1, 2, 1, 2, 3, 8]
def baseStart_2378660 : Nat := 118140960795 + 2378660 * 2 ^ 59
def prefixEnd_2378660 : Nat := 4983230072969 + 3 ^ 40 * 2378660 * 2
def baseEnd_2378660 : Nat := 90473769898056941889685

theorem tailTrace_2378660 : CollatzResearch.WordTrace tailWord_2378660 prefixEnd_2378660 90473769898056941889685 := by
  unfold tailWord_2378660
  simp only [CollatzResearch.WordTrace]
  refine ⟨43378428781264268815234717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57837905041685691753646289 43378428781264268815234717)
  ·
    refine ⟨16266910792974100805713019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43378428781264268815234717 16266910792974100805713019)
    ·
      refine ⟨24400366189461151208569529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16266910792974100805713019 24400366189461151208569529)
      ·
        refine ⟨18300274642095863406427147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24400366189461151208569529 18300274642095863406427147)
        ·
          refine ⟨27450411963143795109640721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18300274642095863406427147 27450411963143795109640721)
          ·
            refine ⟨20587808972357846332230541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27450411963143795109640721 20587808972357846332230541)
            ·
              refine ⟨7720428364634192374586453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20587808972357846332230541 7720428364634192374586453)
              ·
                refine ⟨90473769898056941889685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7720428364634192374586453 90473769898056941889685)
                ·
                  rfl

theorem cell22_2378660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 8].length) (baseStart_2378660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378660 prefixEnd_2378660 := by exact prefixLift 2378660
  have htrace : WordTrace (prefixWord ++ tailWord_2378660) baseStart_2378660 baseEnd_2378660 := by
    simpa [prefixWord, tailWord_2378660, baseEnd_2378660] using wordTrace_append hprefix tailTrace_2378660
  have hstable : (prefixWord ++ tailWord_2378660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378660).length < 2 ^ (prefixWord ++ tailWord_2378660).sum := by decide
  have hdescent : baseEnd_2378660 < baseStart_2378660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378720 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 6, 5]
def baseStart_2378720 : Nat := 118140960795 + 2378720 * 2 ^ 59
def prefixEnd_2378720 : Nat := 4983230072969 + 3 ^ 40 * 2378720 * 2
def baseEnd_2378720 : Nat := 814284468308692320506981

theorem tailTrace_2378720 : CollatzResearch.WordTrace tailWord_2378720 prefixEnd_2378720 814284468308692320506981 := by
  unfold tailWord_2378720
  simp only [CollatzResearch.WordTrace]
  refine ⟨43379522971155583938826807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57839363961540778585102409 43379522971155583938826807)
  ·
    refine ⟨65069284456733375908240211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43379522971155583938826807 65069284456733375908240211)
    ·
      refine ⟨97603926685100063862360317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65069284456733375908240211 97603926685100063862360317)
      ·
        refine ⟨36601472506912523948385119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97603926685100063862360317 36601472506912523948385119)
        ·
          refine ⟨54902208760368785922577679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36601472506912523948385119 54902208760368785922577679)
          ·
            refine ⟨82353313140553178883866519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54902208760368785922577679 82353313140553178883866519)
            ·
              refine ⟨123529969710829768325799779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82353313140553178883866519 123529969710829768325799779)
              ·
                refine ⟨185294954566244652488699669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123529969710829768325799779 185294954566244652488699669)
                ·
                  refine ⟨8685700995292718085407797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 185294954566244652488699669 8685700995292718085407797)
                  ·
                    refine ⟨814284468308692320506981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8685700995292718085407797 814284468308692320506981)
                    ·
                      rfl

theorem cell22_2378720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_2378720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378720 prefixEnd_2378720 := by exact prefixLift 2378720
  have htrace : WordTrace (prefixWord ++ tailWord_2378720) baseStart_2378720 baseEnd_2378720 := by
    simpa [prefixWord, tailWord_2378720, baseEnd_2378720] using wordTrace_append hprefix tailTrace_2378720
  have hstable : (prefixWord ++ tailWord_2378720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378720).length < 2 ^ (prefixWord ++ tailWord_2378720).sum := by decide
  have hdescent : baseEnd_2378720 < baseStart_2378720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378786 : List Nat := [3, 3, 1, 1, 1, 3, 4, 1, 1, 4]
def baseStart_2378786 : Nat := 118140960795 + 2378786 * 2 ^ 59
def prefixEnd_2378786 : Nat := 4983230072969 + 3 ^ 40 * 2378786 * 2
def baseEnd_2378786 : Nat := 814307061457490148356779

theorem tailTrace_2378786 : CollatzResearch.WordTrace tailWord_2378786 prefixEnd_2378786 814307061457490148356779 := by
  unfold tailWord_2378786
  simp only [CollatzResearch.WordTrace]
  refine ⟨21690363290018015287389053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57840968773381374099704141 21690363290018015287389053)
  ·
    refine ⟨8133886233756755732770895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21690363290018015287389053 8133886233756755732770895)
    ·
      refine ⟨12200829350635133599156343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8133886233756755732770895 12200829350635133599156343)
      ·
        refine ⟨18301244025952700398734515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12200829350635133599156343 18301244025952700398734515)
        ·
          refine ⟨27451866038929050598101773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18301244025952700398734515 27451866038929050598101773)
          ·
            refine ⟨10294449764598393974288165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27451866038929050598101773 10294449764598393974288165)
            ·
              refine ⟨1930209330862198870179031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10294449764598393974288165 1930209330862198870179031)
              ·
                refine ⟨2895313996293298305268547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1930209330862198870179031 2895313996293298305268547)
                ·
                  refine ⟨4342970994439947457902821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2895313996293298305268547 4342970994439947457902821)
                  ·
                    refine ⟨814307061457490148356779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4342970994439947457902821 814307061457490148356779)
                    ·
                      rfl

theorem cell22_2378786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_2378786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378786 prefixEnd_2378786 := by exact prefixLift 2378786
  have htrace : WordTrace (prefixWord ++ tailWord_2378786) baseStart_2378786 baseEnd_2378786 := by
    simpa [prefixWord, tailWord_2378786, baseEnd_2378786] using wordTrace_append hprefix tailTrace_2378786
  have hstable : (prefixWord ++ tailWord_2378786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378786).length < 2 ^ (prefixWord ++ tailWord_2378786).sum := by decide
  have hdescent : baseEnd_2378786 < baseStart_2378786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378795 : List Nat := [1, 1, 1, 1, 2, 1, 15]
def baseStart_2378795 : Nat := 118140960795 + 2378795 * 2 ^ 59
def prefixEnd_2378795 : Nat := 4983230072969 + 3 ^ 40 * 2378795 * 2
def baseEnd_2378795 : Nat := 30159634901533967588213

theorem tailTrace_2378795 : CollatzResearch.WordTrace tailWord_2378795 prefixEnd_2378795 30159634901533967588213 := by
  unfold tailWord_2378795
  simp only [CollatzResearch.WordTrace]
  refine ⟨86761781417039455686633839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57841187611359637124422559 86761781417039455686633839)
  ·
    refine ⟨130142672125559183529950759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86761781417039455686633839 130142672125559183529950759)
    ·
      refine ⟨195214008188338775294926139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130142672125559183529950759 195214008188338775294926139)
      ·
        refine ⟨292821012282508162942389209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195214008188338775294926139 292821012282508162942389209)
        ·
          refine ⟨219615759211881122206791907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292821012282508162942389209 219615759211881122206791907)
          ·
            refine ⟨329423638817821683310187861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219615759211881122206791907 329423638817821683310187861)
            ·
              refine ⟨30159634901533967588213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 329423638817821683310187861 30159634901533967588213)
              ·
                rfl

theorem cell22_2378795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 15].length) (baseStart_2378795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378795 prefixEnd_2378795 := by exact prefixLift 2378795
  have htrace : WordTrace (prefixWord ++ tailWord_2378795) baseStart_2378795 baseEnd_2378795 := by
    simpa [prefixWord, tailWord_2378795, baseEnd_2378795] using wordTrace_append hprefix tailTrace_2378795
  have hstable : (prefixWord ++ tailWord_2378795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378795).length < 2 ^ (prefixWord ++ tailWord_2378795).sum := by decide
  have hdescent : baseEnd_2378795 < baseStart_2378795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378814 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_2378814 : Nat := 118140960795 + 2378814 * 2 ^ 59
def prefixEnd_2378814 : Nat := 4983230072969 + 3 ^ 40 * 2378814 * 2
def baseEnd_2378814 : Nat := 814316646429707408656693

theorem tailTrace_2378814 : CollatzResearch.WordTrace tailWord_2378814 prefixEnd_2378814 814316646429707408656693 := by
  unfold tailWord_2378814
  simp only [CollatzResearch.WordTrace]
  refine ⟨10845309300496327741446937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57841649602647081287716997 10845309300496327741446937)
  ·
    refine ⟨8133981975372245806085203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10845309300496327741446937 8133981975372245806085203)
    ·
      refine ⟨12200972963058368709127805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8133981975372245806085203 12200972963058368709127805)
      ·
        refine ⟨4575364861146888265922927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12200972963058368709127805 4575364861146888265922927)
        ·
          refine ⟨6863047291720332398884391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4575364861146888265922927 6863047291720332398884391)
          ·
            refine ⟨10294570937580498598326587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6863047291720332398884391 10294570937580498598326587)
            ·
              refine ⟨15441856406370747897489881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10294570937580498598326587 15441856406370747897489881)
              ·
                refine ⟨11581392304778060923117411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15441856406370747897489881 11581392304778060923117411)
                ·
                  refine ⟨17372088457167091384676117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11581392304778060923117411 17372088457167091384676117)
                  ·
                    refine ⟨814316646429707408656693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17372088457167091384676117 814316646429707408656693)
                    ·
                      rfl

theorem cell22_2378814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_2378814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378814 prefixEnd_2378814 := by exact prefixLift 2378814
  have htrace : WordTrace (prefixWord ++ tailWord_2378814) baseStart_2378814 baseEnd_2378814 := by
    simpa [prefixWord, tailWord_2378814, baseEnd_2378814] using wordTrace_append hprefix tailTrace_2378814
  have hstable : (prefixWord ++ tailWord_2378814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378814).length < 2 ^ (prefixWord ++ tailWord_2378814).sum := by decide
  have hdescent : baseEnd_2378814 < baseStart_2378814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378816 : List Nat := [2, 1, 1, 2, 2, 3, 5, 1, 2, 3]
def baseStart_2378816 : Nat := 118140960795 + 2378816 * 2 ^ 59
def prefixEnd_2378816 : Nat := 4983230072969 + 3 ^ 40 * 2378816 * 2
def baseEnd_2378816 : Nat := 814317331070580070106687

theorem tailTrace_2378816 : CollatzResearch.WordTrace tailWord_2378816 prefixEnd_2378816 814317331070580070106687 := by
  unfold tailWord_2378816
  simp only [CollatzResearch.WordTrace]
  refine ⟨43381273674981688136574151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57841698233308917515432201 43381273674981688136574151)
  ·
    refine ⟨65071910512472532204861227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43381273674981688136574151 65071910512472532204861227)
    ·
      refine ⟨97607865768708798307291841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65071910512472532204861227 97607865768708798307291841)
      ·
        refine ⟨73205899326531598730468881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97607865768708798307291841 73205899326531598730468881)
        ·
          refine ⟨54904424494898699047851661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73205899326531598730468881 54904424494898699047851661)
          ·
            refine ⟨20589159185587012142944373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54904424494898699047851661 20589159185587012142944373)
            ·
              refine ⟨1930233673648782388401035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20589159185587012142944373 1930233673648782388401035)
              ·
                refine ⟨2895350510473173582601553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1930233673648782388401035 2895350510473173582601553)
                ·
                  refine ⟨2171512882854880186951165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2895350510473173582601553 2171512882854880186951165)
                  ·
                    refine ⟨814317331070580070106687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2171512882854880186951165 814317331070580070106687)
                    ·
                      rfl

theorem cell22_2378816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 2, 3].length) (baseStart_2378816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378816 prefixEnd_2378816 := by exact prefixLift 2378816
  have htrace : WordTrace (prefixWord ++ tailWord_2378816) baseStart_2378816 baseEnd_2378816 := by
    simpa [prefixWord, tailWord_2378816, baseEnd_2378816] using wordTrace_append hprefix tailTrace_2378816
  have hstable : (prefixWord ++ tailWord_2378816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378816).length < 2 ^ (prefixWord ++ tailWord_2378816).sum := by decide
  have hdescent : baseEnd_2378816 < baseStart_2378816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378829 : List Nat := [1, 6, 1, 1, 1, 3, 1, 8]
def baseStart_2378829 : Nat := 118140960795 + 2378829 * 2 ^ 59
def prefixEnd_2378829 : Nat := 4983230072969 + 3 ^ 40 * 2378829 * 2
def baseEnd_2378829 : Nat := 90480197915139152170183

theorem tailTrace_2378829 : CollatzResearch.WordTrace tailWord_2378829 prefixEnd_2378829 90480197915139152170183 := by
  unfold tailWord_2378829
  simp only [CollatzResearch.WordTrace]
  refine ⟨86763021498916279493371541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57842014332610852995581027 86763021498916279493371541)
  ·
    refine ⟨4067016632761700601251791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86763021498916279493371541 4067016632761700601251791)
    ·
      refine ⟨6100524949142550901877687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4067016632761700601251791 6100524949142550901877687)
      ·
        refine ⟨9150787423713826352816531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6100524949142550901877687 9150787423713826352816531)
        ·
          refine ⟨13726181135570739529224797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9150787423713826352816531 13726181135570739529224797)
          ·
            refine ⟨5147317925839027323459299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13726181135570739529224797 5147317925839027323459299)
            ·
              refine ⟨7720976888758540985188949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5147317925839027323459299 7720976888758540985188949)
              ·
                refine ⟨90480197915139152170183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7720976888758540985188949 90480197915139152170183)
                ·
                  rfl

theorem cell22_2378829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 8].length) (baseStart_2378829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378829 prefixEnd_2378829 := by exact prefixLift 2378829
  have htrace : WordTrace (prefixWord ++ tailWord_2378829) baseStart_2378829 baseEnd_2378829 := by
    simpa [prefixWord, tailWord_2378829, baseEnd_2378829] using wordTrace_append hprefix tailTrace_2378829
  have hstable : (prefixWord ++ tailWord_2378829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378829).length < 2 ^ (prefixWord ++ tailWord_2378829).sum := by decide
  have hdescent : baseEnd_2378829 < baseStart_2378829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378846 : List Nat := [4, 4, 1, 1, 1, 1, 10]
def baseStart_2378846 : Nat := 118140960795 + 2378846 * 2 ^ 59
def prefixEnd_2378846 : Nat := 4983230072969 + 3 ^ 40 * 2378846 * 2
def baseEnd_2378846 : Nat := 30160281506802592290985

theorem tailTrace_2378846 : CollatzResearch.WordTrace tailWord_2378846 prefixEnd_2378846 30160281506802592290985 := by
  unfold tailWord_2378846
  simp only [CollatzResearch.WordTrace]
  refine ⟨10845455192481836424592549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57842427693236460931160261 10845455192481836424592549)
  ·
    refine ⟨2033522848590344329611103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10845455192481836424592549 2033522848590344329611103)
    ·
      refine ⟨3050284272885516494416655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2033522848590344329611103 3050284272885516494416655)
      ·
        refine ⟨4575426409328274741624983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3050284272885516494416655 4575426409328274741624983)
        ·
          refine ⟨6863139613992412112437475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4575426409328274741624983 6863139613992412112437475)
          ·
            refine ⟨10294709420988618168656213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6863139613992412112437475 10294709420988618168656213)
            ·
              refine ⟨30160281506802592290985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10294709420988618168656213 30160281506802592290985)
              ·
                rfl

theorem cell22_2378846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 10].length) (baseStart_2378846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378846 prefixEnd_2378846 := by exact prefixLift 2378846
  have htrace : WordTrace (prefixWord ++ tailWord_2378846) baseStart_2378846 baseEnd_2378846 := by
    simpa [prefixWord, tailWord_2378846, baseEnd_2378846] using wordTrace_append hprefix tailTrace_2378846
  have hstable : (prefixWord ++ tailWord_2378846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378846).length < 2 ^ (prefixWord ++ tailWord_2378846).sum := by decide
  have hdescent : baseEnd_2378846 < baseStart_2378846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378857 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 7]
def baseStart_2378857 : Nat := 118140960795 + 2378857 * 2 ^ 59
def prefixEnd_2378857 : Nat := 4983230072969 + 3 ^ 40 * 2378857 * 2
def baseEnd_2378857 : Nat := 271443788736156543277187

theorem tailTrace_2378857 : CollatzResearch.WordTrace tailWord_2378857 prefixEnd_2378857 271443788736156543277187 := by
  unfold tailWord_2378857
  simp only [CollatzResearch.WordTrace]
  refine ⟨86764042742814840275390825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57842695161876560183593883 86764042742814840275390825)
  ·
    refine ⟨65073032057111130206543119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86764042742814840275390825 65073032057111130206543119)
    ·
      refine ⟨97609548085666695309814679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65073032057111130206543119 97609548085666695309814679)
      ·
        refine ⟨146414322128500042964722019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97609548085666695309814679 146414322128500042964722019)
        ·
          refine ⟨219621483192750064447083029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146414322128500042964722019 219621483192750064447083029)
          ·
            refine ⟨10294757024660159270957017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 219621483192750064447083029 10294757024660159270957017)
            ·
              refine ⟨7721067768495119453217763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10294757024660159270957017 7721067768495119453217763)
              ·
                refine ⟨11581601652742679179826645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7721067768495119453217763 11581601652742679179826645)
                ·
                  refine ⟨271443788736156543277187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11581601652742679179826645 271443788736156543277187)
                  ·
                    rfl

theorem cell22_2378857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 7].length) (baseStart_2378857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378857 prefixEnd_2378857 := by exact prefixLift 2378857
  have htrace : WordTrace (prefixWord ++ tailWord_2378857) baseStart_2378857 baseEnd_2378857 := by
    simpa [prefixWord, tailWord_2378857, baseEnd_2378857] using wordTrace_append hprefix tailTrace_2378857
  have hstable : (prefixWord ++ tailWord_2378857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378857).length < 2 ^ (prefixWord ++ tailWord_2378857).sum := by decide
  have hdescent : baseEnd_2378857 < baseStart_2378857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378861 : List Nat := [1, 5, 1, 1, 2, 2, 3, 1, 3, 3]
def baseStart_2378861 : Nat := 118140960795 + 2378861 * 2 ^ 59
def prefixEnd_2378861 : Nat := 4983230072969 + 3 ^ 40 * 2378861 * 2
def baseEnd_2378861 : Nat := 814332735490214952731549

theorem tailTrace_2378861 : CollatzResearch.WordTrace tailWord_2378861 prefixEnd_2378861 814332735490214952731549 := by
  unfold tailWord_2378861
  simp only [CollatzResearch.WordTrace]
  refine ⟨86764188634800348958536437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57842792423200232639024291 86764188634800348958536437)
  ·
    refine ⟨8134142684512532714862791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86764188634800348958536437 8134142684512532714862791)
    ·
      refine ⟨12201214026768799072294187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8134142684512532714862791 12201214026768799072294187)
      ·
        refine ⟨18301821040153198608441281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12201214026768799072294187 18301821040153198608441281)
        ·
          refine ⟨13726365780114898956330961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18301821040153198608441281 13726365780114898956330961)
          ·
            refine ⟨10294774335086174217248221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13726365780114898956330961 10294774335086174217248221)
            ·
              refine ⟨3860540375657315331468083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10294774335086174217248221 3860540375657315331468083)
              ·
                refine ⟨5790810563485972997202125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3860540375657315331468083 5790810563485972997202125)
                ·
                  refine ⟨2171553961307239873950797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5790810563485972997202125 2171553961307239873950797)
                  ·
                    refine ⟨814332735490214952731549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2171553961307239873950797 814332735490214952731549)
                    ·
                      rfl

theorem cell22_2378861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_2378861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378861 prefixEnd_2378861 := by exact prefixLift 2378861
  have htrace : WordTrace (prefixWord ++ tailWord_2378861) baseStart_2378861 baseEnd_2378861 := by
    simpa [prefixWord, tailWord_2378861, baseEnd_2378861] using wordTrace_append hprefix tailTrace_2378861
  have hstable : (prefixWord ++ tailWord_2378861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378861).length < 2 ^ (prefixWord ++ tailWord_2378861).sum := by decide
  have hdescent : baseEnd_2378861 < baseStart_2378861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2378872 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 2, 5]
def baseStart_2378872 : Nat := 118140960795 + 2378872 * 2 ^ 59
def prefixEnd_2378872 : Nat := 4983230072969 + 3 ^ 40 * 2378872 * 2
def baseEnd_2378872 : Nat := 814336501015014590706515

theorem tailTrace_2378872 : CollatzResearch.WordTrace tailWord_2378872 prefixEnd_2378872 814336501015014590706515 := by
  unfold tailWord_2378872
  simp only [CollatzResearch.WordTrace]
  refine ⟨43382294918880248918593435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57843059891840331891457913 43382294918880248918593435)
  ·
    refine ⟨65073442378320373377890153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43382294918880248918593435 65073442378320373377890153)
    ·
      refine ⟨48805081783740280033417615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65073442378320373377890153 48805081783740280033417615)
      ·
        refine ⟨73207622675610420050126423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48805081783740280033417615 73207622675610420050126423)
        ·
          refine ⟨109811434013415630075189635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73207622675610420050126423 109811434013415630075189635)
          ·
            refine ⟨164717151020123445112784453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109811434013415630075189635 164717151020123445112784453)
            ·
              refine ⟨30884465816273145958647085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 164717151020123445112784453 30884465816273145958647085)
              ·
                refine ⟨11581674681102429734492657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30884465816273145958647085 11581674681102429734492657)
                ·
                  refine ⟨8686256010826822300869493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11581674681102429734492657 8686256010826822300869493)
                  ·
                    refine ⟨814336501015014590706515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8686256010826822300869493 814336501015014590706515)
                    ·
                      rfl

theorem cell22_2378872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_2378872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2378872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2378872 prefixEnd_2378872 := by exact prefixLift 2378872
  have htrace : WordTrace (prefixWord ++ tailWord_2378872) baseStart_2378872 baseEnd_2378872 := by
    simpa [prefixWord, tailWord_2378872, baseEnd_2378872] using wordTrace_append hprefix tailTrace_2378872
  have hstable : (prefixWord ++ tailWord_2378872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2378872).length < 2 ^ (prefixWord ++ tailWord_2378872).sum := by decide
  have hdescent : baseEnd_2378872 < baseStart_2378872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2378872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379009 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 7]
def baseStart_2379009 : Nat := 118140960795 + 2379009 * 2 ^ 59
def prefixEnd_2379009 : Nat := 4983230072969 + 3 ^ 40 * 2379009 * 2
def baseEnd_2379009 : Nat := 271461132971597300010365

theorem tailTrace_2379009 : CollatzResearch.WordTrace tailWord_2379009 prefixEnd_2379009 271461132971597300010365 := by
  unfold tailWord_2379009
  simp only [CollatzResearch.WordTrace]
  refine ⟨86769586638264170234924081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57846391092176113489949387 86769586638264170234924081)
  ·
    refine ⟨65077189978698127676193061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86769586638264170234924081 65077189978698127676193061)
    ·
      refine ⟨12201973121005898939286199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65077189978698127676193061 12201973121005898939286199)
      ·
        refine ⟨18302959681508848408929299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12201973121005898939286199 18302959681508848408929299)
        ·
          refine ⟨27454439522263272613393949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18302959681508848408929299 27454439522263272613393949)
          ·
            refine ⟨10295414820848727230022731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27454439522263272613393949 10295414820848727230022731)
            ·
              refine ⟨15443122231273090845034097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10295414820848727230022731 15443122231273090845034097)
              ·
                refine ⟨11582341673454818133775573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15443122231273090845034097 11582341673454818133775573)
                ·
                  refine ⟨271461132971597300010365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11582341673454818133775573 271461132971597300010365)
                  ·
                    rfl

theorem cell22_2379009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 7].length) (baseStart_2379009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379009 prefixEnd_2379009 := by exact prefixLift 2379009
  have htrace : WordTrace (prefixWord ++ tailWord_2379009) baseStart_2379009 baseEnd_2379009 := by
    simpa [prefixWord, tailWord_2379009, baseEnd_2379009] using wordTrace_append hprefix tailTrace_2379009
  have hstable : (prefixWord ++ tailWord_2379009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379009).length < 2 ^ (prefixWord ++ tailWord_2379009).sum := by decide
  have hdescent : baseEnd_2379009 < baseStart_2379009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379043 : List Nat := [1, 1, 1, 4, 2, 5, 2, 1, 5]
def baseStart_2379043 : Nat := 118140960795 + 2379043 * 2 ^ 59
def prefixEnd_2379043 : Nat := 4983230072969 + 3 ^ 40 * 2379043 * 2
def baseEnd_2379043 : Nat := 271465012603209048226997

theorem tailTrace_2379043 : CollatzResearch.WordTrace tailWord_2379043 prefixEnd_2379043 271465012603209048226997 := by
  unfold tailWord_2379043
  simp only [CollatzResearch.WordTrace]
  refine ⟨86770826720140994041661783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57847217813427329361107855 86770826720140994041661783)
  ·
    refine ⟨130156240080211491062492675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86770826720140994041661783 130156240080211491062492675)
    ·
      refine ⟨195234360120317236593739013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130156240080211491062492675 195234360120317236593739013)
      ·
        refine ⟨36606442522559481861326065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195234360120317236593739013 36606442522559481861326065)
        ·
          refine ⟨27454831891919611395994549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36606442522559481861326065 27454831891919611395994549)
          ·
            refine ⟨2573890489867463568374489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27454831891919611395994549 2573890489867463568374489)
            ·
              refine ⟨1930417867400597676280867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2573890489867463568374489 1930417867400597676280867)
              ·
                refine ⟨2895626801100896514421301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1930417867400597676280867 2895626801100896514421301)
                ·
                  refine ⟨271465012603209048226997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2895626801100896514421301 271465012603209048226997)
                  ·
                    rfl

theorem cell22_2379043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 5].length) (baseStart_2379043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379043 prefixEnd_2379043 := by exact prefixLift 2379043
  have htrace : WordTrace (prefixWord ++ tailWord_2379043) baseStart_2379043 baseEnd_2379043 := by
    simpa [prefixWord, tailWord_2379043, baseEnd_2379043] using wordTrace_append hprefix tailTrace_2379043
  have hstable : (prefixWord ++ tailWord_2379043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379043).length < 2 ^ (prefixWord ++ tailWord_2379043).sum := by decide
  have hdescent : baseEnd_2379043 < baseStart_2379043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379131 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 5, 3]
def baseStart_2379131 : Nat := 118140960795 + 2379131 * 2 ^ 59
def prefixEnd_2379131 : Nat := 4983230072969 + 3 ^ 40 * 2379131 * 2
def baseEnd_2379131 : Nat := 814425162008024248480721

theorem tailTrace_2379131 : CollatzResearch.WordTrace tailWord_2379131 prefixEnd_2379131 814425162008024248480721 := by
  unfold tailWord_2379131
  simp only [CollatzResearch.WordTrace]
  refine ⟨86774036343822185070865247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57849357562548123380576831 86774036343822185070865247)
  ·
    refine ⟨130161054515733277606297871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86774036343822185070865247 130161054515733277606297871)
    ·
      refine ⟨195241581773599916409446807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130161054515733277606297871 195241581773599916409446807)
      ·
        refine ⟨292862372660399874614170211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195241581773599916409446807 292862372660399874614170211)
        ·
          refine ⟨439293558990599811921255317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292862372660399874614170211 439293558990599811921255317)
          ·
            refine ⟨20591885577684366183808843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 439293558990599811921255317 20591885577684366183808843)
            ·
              refine ⟨30887828366526549275713265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20591885577684366183808843 30887828366526549275713265)
              ·
                refine ⟨23165871274894911956784949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30887828366526549275713265 23165871274894911956784949)
                ·
                  refine ⟨2171800432021397995948589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23165871274894911956784949 2171800432021397995948589)
                  ·
                    refine ⟨814425162008024248480721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2171800432021397995948589 814425162008024248480721)
                    ·
                      rfl

theorem cell22_2379131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 3].length) (baseStart_2379131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379131 prefixEnd_2379131 := by exact prefixLift 2379131
  have htrace : WordTrace (prefixWord ++ tailWord_2379131) baseStart_2379131 baseEnd_2379131 := by
    simpa [prefixWord, tailWord_2379131, baseEnd_2379131] using wordTrace_append hprefix tailTrace_2379131
  have hstable : (prefixWord ++ tailWord_2379131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379131).length < 2 ^ (prefixWord ++ tailWord_2379131).sum := by decide
  have hdescent : baseEnd_2379131 < baseStart_2379131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379137 : List Nat := [1, 2, 4, 3, 2, 2, 1, 2, 2, 3]
def baseStart_2379137 : Nat := 118140960795 + 2379137 * 2 ^ 59
def prefixEnd_2379137 : Nat := 4983230072969 + 3 ^ 40 * 2379137 * 2
def baseEnd_2379137 : Nat := 814427215930642232830703

theorem tailTrace_2379137 : CollatzResearch.WordTrace tailWord_2379137 prefixEnd_2379137 814427215930642232830703 := by
  unfold tailWord_2379137
  simp only [CollatzResearch.WordTrace]
  refine ⟨86774255181800448095583665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57849503454533632063722443 86774255181800448095583665)
  ·
    refine ⟨65080691386350336071687749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86774255181800448095583665 65080691386350336071687749)
    ·
      refine ⟨12202629634940688013441453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65080691386350336071687749 12202629634940688013441453)
      ·
        refine ⟨4575986113102758005040545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12202629634940688013441453 4575986113102758005040545)
        ·
          refine ⟨3431989584827068503780409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4575986113102758005040545 3431989584827068503780409)
          ·
            refine ⟨2573992188620301377835307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3431989584827068503780409 2573992188620301377835307)
            ·
              refine ⟨3860988282930452066752961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2573992188620301377835307 3860988282930452066752961)
              ·
                refine ⟨2895741212197839050064721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3860988282930452066752961 2895741212197839050064721)
                ·
                  refine ⟨2171805909148379287548541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2895741212197839050064721 2171805909148379287548541)
                  ·
                    refine ⟨814427215930642232830703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2171805909148379287548541 814427215930642232830703)
                    ·
                      rfl

theorem cell22_2379137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_2379137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379137 prefixEnd_2379137 := by exact prefixLift 2379137
  have htrace : WordTrace (prefixWord ++ tailWord_2379137) baseStart_2379137 baseEnd_2379137 := by
    simpa [prefixWord, tailWord_2379137, baseEnd_2379137] using wordTrace_append hprefix tailTrace_2379137
  have hstable : (prefixWord ++ tailWord_2379137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379137).length < 2 ^ (prefixWord ++ tailWord_2379137).sum := by decide
  have hdescent : baseEnd_2379137 < baseStart_2379137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379148 : List Nat := [2, 2, 1, 2, 1, 3, 4, 1, 3, 3]
def baseStart_2379148 : Nat := 118140960795 + 2379148 * 2 ^ 59
def prefixEnd_2379148 : Nat := 4983230072969 + 3 ^ 40 * 2379148 * 2
def baseEnd_2379148 : Nat := 814430981455441870805669

theorem tailTrace_2379148 : CollatzResearch.WordTrace tailWord_2379148 prefixEnd_2379148 814430981455441870805669 := by
  unfold tailWord_2379148
  simp only [CollatzResearch.WordTrace]
  refine ⟨43387328192380298487117049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57849770923173731316156065 43387328192380298487117049)
  ·
    refine ⟨32540496144285223865337787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43387328192380298487117049 32540496144285223865337787)
    ·
      refine ⟨48810744216427835798006681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32540496144285223865337787 48810744216427835798006681)
      ·
        refine ⟨36608058162320876848505011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48810744216427835798006681 36608058162320876848505011)
        ·
          refine ⟨54912087243481315272757517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36608058162320876848505011 54912087243481315272757517)
          ·
            refine ⟨20592032716305493227284069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54912087243481315272757517 20592032716305493227284069)
            ·
              refine ⟨3861006134307279980115763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20592032716305493227284069 3861006134307279980115763)
              ·
                refine ⟨5791509201460919970173645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3861006134307279980115763 5791509201460919970173645)
                ·
                  refine ⟨2171815950547844988815117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5791509201460919970173645 2171815950547844988815117)
                  ·
                    refine ⟨814430981455441870805669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2171815950547844988815117 814430981455441870805669)
                    ·
                      rfl

theorem cell22_2379148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 3, 3].length) (baseStart_2379148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379148 prefixEnd_2379148 := by exact prefixLift 2379148
  have htrace : WordTrace (prefixWord ++ tailWord_2379148) baseStart_2379148 baseEnd_2379148 := by
    simpa [prefixWord, tailWord_2379148, baseEnd_2379148] using wordTrace_append hprefix tailTrace_2379148
  have hstable : (prefixWord ++ tailWord_2379148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379148).length < 2 ^ (prefixWord ++ tailWord_2379148).sum := by decide
  have hdescent : baseEnd_2379148 < baseStart_2379148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379154 : List Nat := [3, 2, 3, 3, 1, 1, 3, 1, 2, 3]
def baseStart_2379154 : Nat := 118140960795 + 2379154 * 2 ^ 59
def prefixEnd_2379154 : Nat := 4983230072969 + 3 ^ 40 * 2379154 * 2
def baseEnd_2379154 : Nat := 814433035378059855155651

theorem tailTrace_2379154 : CollatzResearch.WordTrace tailWord_2379154 prefixEnd_2379154 814433035378059855155651 := by
  unfold tailWord_2379154
  simp only [CollatzResearch.WordTrace]
  refine ⟨21693718805684714999738129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57849916815159239999301677 21693718805684714999738129)
  ·
    refine ⟨16270289104263536249803597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21693718805684714999738129 16270289104263536249803597)
    ·
      refine ⟨6101358414098826093676349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16270289104263536249803597 6101358414098826093676349)
      ·
        refine ⟨2288009405287059785128631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6101358414098826093676349 2288009405287059785128631)
        ·
          refine ⟨3432014107930589677692947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2288009405287059785128631 3432014107930589677692947)
          ·
            refine ⟨5148021161895884516539421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3432014107930589677692947 5148021161895884516539421)
            ·
              refine ⟨1930507935710956693702283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5148021161895884516539421 1930507935710956693702283)
              ·
                refine ⟨2895761903566435040553425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1930507935710956693702283 2895761903566435040553425)
                ·
                  refine ⟨2171821427674826280415069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2895761903566435040553425 2171821427674826280415069)
                  ·
                    refine ⟨814433035378059855155651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2171821427674826280415069 814433035378059855155651)
                    ·
                      rfl

theorem cell22_2379154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_2379154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379154 prefixEnd_2379154 := by exact prefixLift 2379154
  have htrace : WordTrace (prefixWord ++ tailWord_2379154) baseStart_2379154 baseEnd_2379154 := by
    simpa [prefixWord, tailWord_2379154, baseEnd_2379154] using wordTrace_append hprefix tailTrace_2379154
  have hstable : (prefixWord ++ tailWord_2379154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379154).length < 2 ^ (prefixWord ++ tailWord_2379154).sum := by decide
  have hdescent : baseEnd_2379154 < baseStart_2379154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379225 : List Nat := [1, 2, 1, 2, 4, 4, 1, 2, 1, 4]
def baseStart_2379225 : Nat := 118140960795 + 2379225 * 2 ^ 59
def prefixEnd_2379225 : Nat := 4983230072969 + 3 ^ 40 * 2379225 * 2
def baseEnd_2379225 : Nat := 814457340129039336630433

theorem tailTrace_2379225 : CollatzResearch.WordTrace tailWord_2379225 prefixEnd_2379225 814457340129039336630433 := by
  unfold tailWord_2379225
  simp only [CollatzResearch.WordTrace]
  refine ⟨86777464805481639124787129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57851643203654426083191419 86777464805481639124787129)
  ·
    refine ⟨65083098604111229343590347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86777464805481639124787129 65083098604111229343590347)
    ·
      refine ⟨97624647906166844015385521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65083098604111229343590347 97624647906166844015385521)
      ·
        refine ⟨73218485929625133011539141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97624647906166844015385521 73218485929625133011539141)
        ·
          refine ⟨13728466111804712439663589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73218485929625133011539141 13728466111804712439663589)
          ·
            refine ⟨2574087395963383582436923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13728466111804712439663589 2574087395963383582436923)
            ·
              refine ⟨3861131093945075373655385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2574087395963383582436923 3861131093945075373655385)
              ·
                refine ⟨2895848320458806530241539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3861131093945075373655385 2895848320458806530241539)
                ·
                  refine ⟨4343772480688209795362309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2895848320458806530241539 4343772480688209795362309)
                  ·
                    refine ⟨814457340129039336630433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4343772480688209795362309 814457340129039336630433)
                    ·
                      rfl

theorem cell22_2379225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 4].length) (baseStart_2379225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379225 prefixEnd_2379225 := by exact prefixLift 2379225
  have htrace : WordTrace (prefixWord ++ tailWord_2379225) baseStart_2379225 baseEnd_2379225 := by
    simpa [prefixWord, tailWord_2379225, baseEnd_2379225] using wordTrace_append hprefix tailTrace_2379225
  have hstable : (prefixWord ++ tailWord_2379225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379225).length < 2 ^ (prefixWord ++ tailWord_2379225).sum := by decide
  have hdescent : baseEnd_2379225 < baseStart_2379225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379236 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_2379236 : Nat := 118140960795 + 2379236 * 2 ^ 59
def prefixEnd_2379236 : Nat := 4983230072969 + 3 ^ 40 * 2379236 * 2
def baseEnd_2379236 : Nat := 814461105653838974605399

theorem tailTrace_2379236 : CollatzResearch.WordTrace tailWord_2379236 prefixEnd_2379236 814461105653838974605399 := by
  unfold tailWord_2379236
  simp only [CollatzResearch.WordTrace]
  refine ⟨43388933004220894001718781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57851910672294525335625041 43388933004220894001718781)
  ·
    refine ⟨16270849876582835250644543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43388933004220894001718781 16270849876582835250644543)
    ·
      refine ⟨24406274814874252875966815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16270849876582835250644543 24406274814874252875966815)
      ·
        refine ⟨36609412222311379313950223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24406274814874252875966815 36609412222311379313950223)
        ·
          refine ⟨54914118333467068970925335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36609412222311379313950223 54914118333467068970925335)
          ·
            refine ⟨82371177500200603456388003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54914118333467068970925335 82371177500200603456388003)
            ·
              refine ⟨123556766250300905184582005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82371177500200603456388003 123556766250300905184582005)
              ·
                refine ⟨11583446835965709861054563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123556766250300905184582005 11583446835965709861054563)
                ·
                  refine ⟨17375170253948564791581845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11583446835965709861054563 17375170253948564791581845)
                  ·
                    refine ⟨814461105653838974605399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17375170253948564791581845 814461105653838974605399)
                    ·
                      rfl

theorem cell22_2379236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_2379236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379236 prefixEnd_2379236 := by exact prefixLift 2379236
  have htrace : WordTrace (prefixWord ++ tailWord_2379236) baseStart_2379236 baseEnd_2379236 := by
    simpa [prefixWord, tailWord_2379236, baseEnd_2379236] using wordTrace_append hprefix tailTrace_2379236
  have hstable : (prefixWord ++ tailWord_2379236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379236).length < 2 ^ (prefixWord ++ tailWord_2379236).sum := by decide
  have hdescent : baseEnd_2379236 < baseStart_2379236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379242 : List Nat := [3, 1, 3, 1, 4, 1, 3, 1, 1, 4]
def baseStart_2379242 : Nat := 118140960795 + 2379242 * 2 ^ 59
def prefixEnd_2379242 : Nat := 4983230072969 + 3 ^ 40 * 2379242 * 2
def baseEnd_2379242 : Nat := 814463159576456958955381

theorem tailTrace_2379242 : CollatzResearch.WordTrace tailWord_2379242 prefixEnd_2379242 814463159576456958955381 := by
  unfold tailWord_2379242
  simp only [CollatzResearch.WordTrace]
  refine ⟨21694521211605012757038995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57852056564280034018770653 21694521211605012757038995)
  ·
    refine ⟨32541781817407519135558493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21694521211605012757038995 32541781817407519135558493)
    ·
      refine ⟨12203168181527819675834435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32541781817407519135558493 12203168181527819675834435)
      ·
        refine ⟨18304752272291729513751653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12203168181527819675834435 18304752272291729513751653)
        ·
          refine ⟨3432141051054699283828435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18304752272291729513751653 3432141051054699283828435)
          ·
            refine ⟨5148211576582048925742653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3432141051054699283828435 5148211576582048925742653)
            ·
              refine ⟨1930579341218268347153495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5148211576582048925742653 1930579341218268347153495)
              ·
                refine ⟨2895869011827402520730243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1930579341218268347153495 2895869011827402520730243)
                ·
                  refine ⟨4343803517741103781095365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2895869011827402520730243 4343803517741103781095365)
                  ·
                    refine ⟨814463159576456958955381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4343803517741103781095365 814463159576456958955381)
                    ·
                      rfl

theorem cell22_2379242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_2379242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379242 prefixEnd_2379242 := by exact prefixLift 2379242
  have htrace : WordTrace (prefixWord ++ tailWord_2379242) baseStart_2379242 baseEnd_2379242 := by
    simpa [prefixWord, tailWord_2379242, baseEnd_2379242] using wordTrace_append hprefix tailTrace_2379242
  have hstable : (prefixWord ++ tailWord_2379242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379242).length < 2 ^ (prefixWord ++ tailWord_2379242).sum := by decide
  have hdescent : baseEnd_2379242 < baseStart_2379242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379281 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 2, 6]
def baseStart_2379281 : Nat := 118140960795 + 2379281 * 2 ^ 59
def prefixEnd_2379281 : Nat := 4983230072969 + 3 ^ 40 * 2379281 * 2
def baseEnd_2379281 : Nat := 814476510073473857230261

theorem tailTrace_2379281 : CollatzResearch.WordTrace tailWord_2379281 prefixEnd_2379281 814476510073473857230261 := by
  unfold tailWord_2379281
  simp only [CollatzResearch.WordTrace]
  refine ⟨86779507293278760688825697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57853004862185840459217131 86779507293278760688825697)
  ·
    refine ⟨65084630469959070516619273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86779507293278760688825697 65084630469959070516619273)
    ·
      refine ⟨48813472852469302887464455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65084630469959070516619273 48813472852469302887464455)
      ·
        refine ⟨73220209278703954331196683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48813472852469302887464455 73220209278703954331196683)
        ·
          refine ⟨109830313918055931496795025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73220209278703954331196683 109830313918055931496795025)
          ·
            refine ⟨82372735438541948622596269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109830313918055931496795025 82372735438541948622596269)
            ·
              refine ⟨30889775789453230733473601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82372735438541948622596269 30889775789453230733473601)
              ·
                refine ⟨23167331842089923050105201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30889775789453230733473601 23167331842089923050105201)
                ·
                  refine ⟨17375498881567442287578901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23167331842089923050105201 17375498881567442287578901)
                  ·
                    refine ⟨814476510073473857230261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17375498881567442287578901 814476510073473857230261)
                    ·
                      rfl

theorem cell22_2379281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_2379281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379281 prefixEnd_2379281 := by exact prefixLift 2379281
  have htrace : WordTrace (prefixWord ++ tailWord_2379281) baseStart_2379281 baseEnd_2379281 := by
    simpa [prefixWord, tailWord_2379281, baseEnd_2379281] using wordTrace_append hprefix tailTrace_2379281
  have hstable : (prefixWord ++ tailWord_2379281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379281).length < 2 ^ (prefixWord ++ tailWord_2379281).sum := by decide
  have hdescent : baseEnd_2379281 < baseStart_2379281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379283 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 5, 3]
def baseStart_2379283 : Nat := 118140960795 + 2379283 * 2 ^ 59
def prefixEnd_2379283 : Nat := 4983230072969 + 3 ^ 40 * 2379283 * 2
def baseEnd_2379283 : Nat := 814477194714346518680255

theorem tailTrace_2379283 : CollatzResearch.WordTrace tailWord_2379283 prefixEnd_2379283 814477194714346518680255 := by
  unfold tailWord_2379283
  simp only [CollatzResearch.WordTrace]
  refine ⟨86779580239271515030398503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57853053492847676686932335 86779580239271515030398503)
  ·
    refine ⟨130169370358907272545597755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86779580239271515030398503 130169370358907272545597755)
    ·
      refine ⟨195254055538360908818396633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130169370358907272545597755 195254055538360908818396633)
      ·
        refine ⟨146440541653770681613797475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195254055538360908818396633 146440541653770681613797475)
        ·
          refine ⟨219660812480656022420696213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146440541653770681613797475 219660812480656022420696213)
          ·
            refine ⟨10296600585030751050970135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 219660812480656022420696213 10296600585030751050970135)
            ·
              refine ⟨15444900877546126576455203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10296600585030751050970135 15444900877546126576455203)
              ·
                refine ⟨23167351316319189864682805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15444900877546126576455203 23167351316319189864682805)
                ·
                  refine ⟨2171939185904924049814013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23167351316319189864682805 2171939185904924049814013)
                  ·
                    refine ⟨814477194714346518680255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2171939185904924049814013 814477194714346518680255)
                    ·
                      rfl

theorem cell22_2379283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 3].length) (baseStart_2379283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379283 prefixEnd_2379283 := by exact prefixLift 2379283
  have htrace : WordTrace (prefixWord ++ tailWord_2379283) baseStart_2379283 baseEnd_2379283 := by
    simpa [prefixWord, tailWord_2379283, baseEnd_2379283] using wordTrace_append hprefix tailTrace_2379283
  have hstable : (prefixWord ++ tailWord_2379283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379283).length < 2 ^ (prefixWord ++ tailWord_2379283).sum := by decide
  have hdescent : baseEnd_2379283 < baseStart_2379283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379317 : List Nat := [1, 3, 3, 1, 1, 3, 2, 4, 1, 3]
def baseStart_2379317 : Nat := 118140960795 + 2379317 * 2 ^ 59
def prefixEnd_2379317 : Nat := 4983230072969 + 3 ^ 40 * 2379317 * 2
def baseEnd_2379317 : Nat := 814488833609181763330151

theorem tailTrace_2379317 : CollatzResearch.WordTrace tailWord_2379317 prefixEnd_2379317 814488833609181763330151 := by
  unfold tailWord_2379317
  simp only [CollatzResearch.WordTrace]
  refine ⟨86780820321148338837136205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57853880214098892558090803 86780820321148338837136205)
  ·
    refine ⟨32542807620430627063926077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86780820321148338837136205 32542807620430627063926077)
    ·
      refine ⟨12203552857661485148972279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32542807620430627063926077 12203552857661485148972279)
      ·
        refine ⟨18305329286492227723458419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12203552857661485148972279 18305329286492227723458419)
        ·
          refine ⟨27457993929738341585187629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18305329286492227723458419 27457993929738341585187629)
          ·
            refine ⟨10296747723651878094445361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27457993929738341585187629 10296747723651878094445361)
            ·
              refine ⟨7722560792738908570834021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10296747723651878094445361 7722560792738908570834021)
              ·
                refine ⟨1447980148638545357031379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7722560792738908570834021 1447980148638545357031379)
                ·
                  refine ⟨2171970222957818035547069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1447980148638545357031379 2171970222957818035547069)
                  ·
                    refine ⟨814488833609181763330151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2171970222957818035547069 814488833609181763330151)
                    ·
                      rfl

theorem cell22_2379317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_2379317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379317 prefixEnd_2379317 := by exact prefixLift 2379317
  have htrace : WordTrace (prefixWord ++ tailWord_2379317) baseStart_2379317 baseEnd_2379317 := by
    simpa [prefixWord, tailWord_2379317, baseEnd_2379317] using wordTrace_append hprefix tailTrace_2379317
  have hstable : (prefixWord ++ tailWord_2379317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379317).length < 2 ^ (prefixWord ++ tailWord_2379317).sum := by decide
  have hdescent : baseEnd_2379317 < baseStart_2379317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379388 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 6, 4]
def baseStart_2379388 : Nat := 118140960795 + 2379388 * 2 ^ 59
def prefixEnd_2379388 : Nat := 4983230072969 + 3 ^ 40 * 2379388 * 2
def baseEnd_2379388 : Nat := 814513138360161244804933

theorem tailTrace_2379388 : CollatzResearch.WordTrace tailWord_2379388 prefixEnd_2379388 814513138360161244804933 := by
  unfold tailWord_2379388
  simp only [CollatzResearch.WordTrace]
  refine ⟨43391704951945558981485409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57855606602594078641980545 43391704951945558981485409)
  ·
    refine ⟨32543778713959169236114057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43391704951945558981485409 32543778713959169236114057)
    ·
      refine ⟨24407834035469376927085543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32543778713959169236114057 24407834035469376927085543)
      ·
        refine ⟨36611751053204065390628315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24407834035469376927085543 36611751053204065390628315)
        ·
          refine ⟨54917626579806098085942473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36611751053204065390628315 54917626579806098085942473)
          ·
            refine ⟨41188219934854573564456855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54917626579806098085942473 41188219934854573564456855)
            ·
              refine ⟨61782329902281860346685283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41188219934854573564456855 61782329902281860346685283)
              ·
                refine ⟨92673494853422790520027925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61782329902281860346685283 92673494853422790520027925)
                ·
                  refine ⟨4344070071254193305626309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92673494853422790520027925 4344070071254193305626309)
                  ·
                    refine ⟨814513138360161244804933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4344070071254193305626309 814513138360161244804933)
                    ·
                      rfl

theorem cell22_2379388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_2379388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379388 prefixEnd_2379388 := by exact prefixLift 2379388
  have htrace : WordTrace (prefixWord ++ tailWord_2379388) baseStart_2379388 baseEnd_2379388 := by
    simpa [prefixWord, tailWord_2379388, baseEnd_2379388] using wordTrace_append hprefix tailTrace_2379388
  have hstable : (prefixWord ++ tailWord_2379388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379388).length < 2 ^ (prefixWord ++ tailWord_2379388).sum := by decide
  have hdescent : baseEnd_2379388 < baseStart_2379388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379420 : List Nat := [2, 2, 3, 2, 4, 9]
def baseStart_2379420 : Nat := 118140960795 + 2379420 * 2 ^ 59
def prefixEnd_2379420 : Nat := 4983230072969 + 3 ^ 40 * 2379420 * 2
def baseEnd_2379420 : Nat := 10055852995236096642035

theorem tailTrace_2379420 : CollatzResearch.WordTrace tailWord_2379420 prefixEnd_2379420 10055852995236096642035 := by
  unfold tailWord_2379420
  simp only [CollatzResearch.WordTrace]
  refine ⟨43392288519887593714067857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57856384693183458285423809 43392288519887593714067857)
  ·
    refine ⟨32544216389915695285550893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43392288519887593714067857 32544216389915695285550893)
    ·
      refine ⟨12204081146218385732081585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32544216389915695285550893 12204081146218385732081585)
      ·
        refine ⟨9153060859663789299061189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12204081146218385732081585 9153060859663789299061189)
        ·
          refine ⟨1716198911186960493573973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9153060859663789299061189 1716198911186960493573973)
          ·
            refine ⟨10055852995236096642035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1716198911186960493573973 10055852995236096642035)
            ·
              rfl

theorem cell22_2379420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 9].length) (baseStart_2379420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379420 prefixEnd_2379420 := by exact prefixLift 2379420
  have htrace : WordTrace (prefixWord ++ tailWord_2379420) baseStart_2379420 baseEnd_2379420 := by
    simpa [prefixWord, tailWord_2379420, baseEnd_2379420] using wordTrace_append hprefix tailTrace_2379420
  have hstable : (prefixWord ++ tailWord_2379420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379420).length < 2 ^ (prefixWord ++ tailWord_2379420).sum := by decide
  have hdescent : baseEnd_2379420 < baseStart_2379420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379422 : List Nat := [4, 3, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_2379422 : Nat := 118140960795 + 2379422 * 2 ^ 59
def prefixEnd_2379422 : Nat := 4983230072969 + 3 ^ 40 * 2379422 * 2
def baseEnd_2379422 : Nat := 814524777254996489454829

theorem tailTrace_2379422 : CollatzResearch.WordTrace tailWord_2379422 prefixEnd_2379422 814524777254996489454829 := by
  unfold tailWord_2379422
  simp only [CollatzResearch.WordTrace]
  refine ⟨10848081248220992721213565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57856433323845294513139013 10848081248220992721213565)
  ·
    refine ⟨4068030468082872270455087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10848081248220992721213565 4068030468082872270455087)
    ·
      refine ⟨6102045702124308405682631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4068030468082872270455087 6102045702124308405682631)
      ·
        refine ⟨9153068553186462608523947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6102045702124308405682631 9153068553186462608523947)
        ·
          refine ⟨13729602829779693912785921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9153068553186462608523947 13729602829779693912785921)
          ·
            refine ⟨10297202122334770434589441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13729602829779693912785921 10297202122334770434589441)
            ·
              refine ⟨7722901591751077825942081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10297202122334770434589441 7722901591751077825942081)
              ·
                refine ⟨5792176193813308369456561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7722901591751077825942081 5792176193813308369456561)
                ·
                  refine ⟨4344132145359981277092421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5792176193813308369456561 4344132145359981277092421)
                  ·
                    refine ⟨814524777254996489454829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4344132145359981277092421 814524777254996489454829)
                    ·
                      rfl

theorem cell22_2379422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_2379422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379422 prefixEnd_2379422 := by exact prefixLift 2379422
  have htrace : WordTrace (prefixWord ++ tailWord_2379422) baseStart_2379422 baseEnd_2379422 := by
    simpa [prefixWord, tailWord_2379422, baseEnd_2379422] using wordTrace_append hprefix tailTrace_2379422
  have hstable : (prefixWord ++ tailWord_2379422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379422).length < 2 ^ (prefixWord ++ tailWord_2379422).sum := by decide
  have hdescent : baseEnd_2379422 < baseStart_2379422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379452 : List Nat := [2, 2, 2, 3, 1, 3, 1, 2, 3, 3]
def baseStart_2379452 : Nat := 118140960795 + 2379452 * 2 ^ 59
def prefixEnd_2379452 : Nat := 4983230072969 + 3 ^ 40 * 2379452 * 2
def baseEnd_2379452 : Nat := 814535046868086411204737

theorem tailTrace_2379452 : CollatzResearch.WordTrace tailWord_2379452 prefixEnd_2379452 814535046868086411204737 := by
  unfold tailWord_2379452
  simp only [CollatzResearch.WordTrace]
  refine ⟨43392872087829628446650305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57857162783772837928867073 43392872087829628446650305)
  ·
    refine ⟨32544654065872221334987729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43392872087829628446650305 32544654065872221334987729)
    ·
      refine ⟨24408490549404166001240797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32544654065872221334987729 24408490549404166001240797)
      ·
        refine ⟨9153183956026562250465299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24408490549404166001240797 9153183956026562250465299)
        ·
          refine ⟨13729775934039843375697949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9153183956026562250465299 13729775934039843375697949)
          ·
            refine ⟨5148665975264941265886731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13729775934039843375697949 5148665975264941265886731)
            ·
              refine ⟨7722998962897411898830097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5148665975264941265886731 7722998962897411898830097)
              ·
                refine ⟨5792249222173058924122573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7722998962897411898830097 5792249222173058924122573)
                ·
                  refine ⟨2172093458314897096545965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5792249222173058924122573 2172093458314897096545965)
                  ·
                    refine ⟨814535046868086411204737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2172093458314897096545965 814535046868086411204737)
                    ·
                      rfl

theorem cell22_2379452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_2379452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379452 prefixEnd_2379452 := by exact prefixLift 2379452
  have htrace : WordTrace (prefixWord ++ tailWord_2379452) baseStart_2379452 baseEnd_2379452 := by
    simpa [prefixWord, tailWord_2379452, baseEnd_2379452] using wordTrace_append hprefix tailTrace_2379452
  have hstable : (prefixWord ++ tailWord_2379452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379452).length < 2 ^ (prefixWord ++ tailWord_2379452).sum := by decide
  have hdescent : baseEnd_2379452 < baseStart_2379452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379463 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 1, 7]
def baseStart_2379463 : Nat := 118140960795 + 2379463 * 2 ^ 59
def prefixEnd_2379463 : Nat := 4983230072969 + 3 ^ 40 * 2379463 * 2
def baseEnd_2379463 : Nat := 814538812392886049179703

theorem tailTrace_2379463 : CollatzResearch.WordTrace tailWord_2379463 prefixEnd_2379463 814538812392886049179703 := by
  unfold tailWord_2379463
  simp only [CollatzResearch.WordTrace]
  refine ⟨86786145378619405771951043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57857430252412937181300695 86786145378619405771951043)
  ·
    refine ⟨130179218067929108657926565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86786145378619405771951043 130179218067929108657926565)
    ·
      refine ⟨24408603387736707873361231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130179218067929108657926565 24408603387736707873361231)
      ·
        refine ⟨36612905081605061810041847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24408603387736707873361231 36612905081605061810041847)
        ·
          refine ⟨54919357622407592715062771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36612905081605061810041847 54919357622407592715062771)
          ·
            refine ⟨82379036433611389072594157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54919357622407592715062771 82379036433611389072594157)
            ·
              refine ⟨30892138662604270902222809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82379036433611389072594157 30892138662604270902222809)
              ·
                refine ⟨23169103996953203176667107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30892138662604270902222809 23169103996953203176667107)
                ·
                  refine ⟨34753655995429804765000661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23169103996953203176667107 34753655995429804765000661)
                  ·
                    refine ⟨814538812392886049179703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34753655995429804765000661 814538812392886049179703)
                    ·
                      rfl

theorem cell22_2379463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_2379463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379463 prefixEnd_2379463 := by exact prefixLift 2379463
  have htrace : WordTrace (prefixWord ++ tailWord_2379463) baseStart_2379463 baseEnd_2379463 := by
    simpa [prefixWord, tailWord_2379463, baseEnd_2379463] using wordTrace_append hprefix tailTrace_2379463
  have hstable : (prefixWord ++ tailWord_2379463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379463).length < 2 ^ (prefixWord ++ tailWord_2379463).sum := by decide
  have hdescent : baseEnd_2379463 < baseStart_2379463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379482 : List Nat := [3, 1, 1, 2, 2, 5, 1, 2, 5]
def baseStart_2379482 : Nat := 118140960795 + 2379482 * 2 ^ 59
def prefixEnd_2379482 : Nat := 4983230072969 + 3 ^ 40 * 2379482 * 2
def baseEnd_2379482 : Nat := 271515105493725444318215

theorem tailTrace_2379482 : CollatzResearch.WordTrace tailWord_2379482 prefixEnd_2379482 271515105493725444318215 := by
  unfold tailWord_2379482
  simp only [CollatzResearch.WordTrace]
  refine ⟨21696709591387643004223175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57857892243700381344595133 21696709591387643004223175)
  ·
    refine ⟨32545064387081464506334763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21696709591387643004223175 32545064387081464506334763)
    ·
      refine ⟨48817596580622196759502145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32545064387081464506334763 48817596580622196759502145)
      ·
        refine ⟨36613197435466647569626609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48817596580622196759502145 36613197435466647569626609)
        ·
          refine ⟨27459898076599985677219957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36613197435466647569626609 27459898076599985677219957)
          ·
            refine ⟨2574365444681248657239371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27459898076599985677219957 2574365444681248657239371)
            ·
              refine ⟨3861548167021872985859057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2574365444681248657239371 3861548167021872985859057)
              ·
                refine ⟨2896161125266404739394293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3861548167021872985859057 2896161125266404739394293)
                ·
                  refine ⟨271515105493725444318215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2896161125266404739394293 271515105493725444318215)
                  ·
                    rfl

theorem cell22_2379482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 5].length) (baseStart_2379482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379482 prefixEnd_2379482 := by exact prefixLift 2379482
  have htrace : WordTrace (prefixWord ++ tailWord_2379482) baseStart_2379482 baseEnd_2379482 := by
    simpa [prefixWord, tailWord_2379482, baseEnd_2379482] using wordTrace_append hprefix tailTrace_2379482
  have hstable : (prefixWord ++ tailWord_2379482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379482).length < 2 ^ (prefixWord ++ tailWord_2379482).sum := by decide
  have hdescent : baseEnd_2379482 < baseStart_2379482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379550 : List Nat := [4, 3, 2, 2, 2, 1, 2, 1, 5]
def baseStart_2379550 : Nat := 118140960795 + 2379550 * 2 ^ 59
def prefixEnd_2379550 : Nat := 4983230072969 + 3 ^ 40 * 2379550 * 2
def baseEnd_2379550 : Nat := 271522864756948940751479

theorem tailTrace_2379550 : CollatzResearch.WordTrace tailWord_2379550 prefixEnd_2379550 271522864756948940751479 := by
  unfold tailWord_2379550
  simp only [CollatzResearch.WordTrace]
  refine ⟨10848664816163027453796013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57859545686202813086912069 10848664816163027453796013)
  ·
    refine ⟨4068249306061135295173505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10848664816163027453796013 4068249306061135295173505)
    ·
      refine ⟨3051186979545851471380129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4068249306061135295173505 3051186979545851471380129)
      ·
        refine ⟨2288390234659388603535097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3051186979545851471380129 2288390234659388603535097)
        ·
          refine ⟨1716292675994541452651323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2288390234659388603535097 1716292675994541452651323)
          ·
            refine ⟨2574439013991812178976985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1716292675994541452651323 2574439013991812178976985)
            ·
              refine ⟨1930829260493859134232739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2574439013991812178976985 1930829260493859134232739)
              ·
                refine ⟨2896243890740788701349109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1930829260493859134232739 2896243890740788701349109)
                ·
                  refine ⟨271522864756948940751479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2896243890740788701349109 271522864756948940751479)
                  ·
                    rfl

theorem cell22_2379550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_2379550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379550 prefixEnd_2379550 := by exact prefixLift 2379550
  have htrace : WordTrace (prefixWord ++ tailWord_2379550) baseStart_2379550 baseEnd_2379550 := by
    simpa [prefixWord, tailWord_2379550, baseEnd_2379550] using wordTrace_append hprefix tailTrace_2379550
  have hstable : (prefixWord ++ tailWord_2379550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379550).length < 2 ^ (prefixWord ++ tailWord_2379550).sum := by decide
  have hdescent : baseEnd_2379550 < baseStart_2379550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379572 : List Nat := [2, 5, 1, 1, 2, 1, 2, 8]
def baseStart_2379572 : Nat := 118140960795 + 2379572 * 2 ^ 59
def prefixEnd_2379572 : Nat := 4983230072969 + 3 ^ 40 * 2379572 * 2
def baseEnd_2379572 : Nat := 90508458368938455356041

theorem tailTrace_2379572 : CollatzResearch.WordTrace tailWord_2379572 prefixEnd_2379572 90508458368938455356041 := by
  unfold tailWord_2379572
  simp only [CollatzResearch.WordTrace]
  refine ⟨43395060467612258693834485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57860080623483011591779313 43395060467612258693834485)
  ·
    refine ⟨4068286918838649252546983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43395060467612258693834485 4068286918838649252546983)
    ·
      refine ⟨6102430378257973878820475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4068286918838649252546983 6102430378257973878820475)
      ·
        refine ⟨9153645567386960818230713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6102430378257973878820475 9153645567386960818230713)
        ·
          refine ⟨6865234175540220613673035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9153645567386960818230713 6865234175540220613673035)
          ·
            refine ⟨10297851263310330920509553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6865234175540220613673035 10297851263310330920509553)
            ·
              refine ⟨7723388447482748190382165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10297851263310330920509553 7723388447482748190382165)
              ·
                refine ⟨90508458368938455356041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7723388447482748190382165 90508458368938455356041)
                ·
                  rfl

theorem cell22_2379572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 8].length) (baseStart_2379572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379572 prefixEnd_2379572 := by exact prefixLift 2379572
  have htrace : WordTrace (prefixWord ++ tailWord_2379572) baseStart_2379572 baseEnd_2379572 := by
    simpa [prefixWord, tailWord_2379572, baseEnd_2379572] using wordTrace_append hprefix tailTrace_2379572
  have hstable : (prefixWord ++ tailWord_2379572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379572).length < 2 ^ (prefixWord ++ tailWord_2379572).sum := by decide
  have hdescent : baseEnd_2379572 < baseStart_2379572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379574 : List Nat := [5, 1, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_2379574 : Nat := 118140960795 + 2379574 * 2 ^ 59
def prefixEnd_2379574 : Nat := 4983230072969 + 3 ^ 40 * 2379574 * 2
def baseEnd_2379574 : Nat := 814576809961318759654363

theorem tailTrace_2379574 : CollatzResearch.WordTrace tailWord_2379574 prefixEnd_2379574 814576809961318759654363 := by
  unfold tailWord_2379574
  simp only [CollatzResearch.WordTrace]
  refine ⟨5424387117576079483077611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57860129254144847819494517 5424387117576079483077611)
  ·
    refine ⟨8136580676364119224616417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5424387117576079483077611 8136580676364119224616417)
    ·
      refine ⟨6102435507273089418462313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8136580676364119224616417 6102435507273089418462313)
      ·
        refine ⟨4576826630454817063846735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6102435507273089418462313 4576826630454817063846735)
        ·
          refine ⟨6865239945682225595770103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4576826630454817063846735 6865239945682225595770103)
          ·
            refine ⟨10297859918523338393655155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6865239945682225595770103 10297859918523338393655155)
            ·
              refine ⟨15446789877785007590482733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10297859918523338393655155 15446789877785007590482733)
              ·
                refine ⟨5792546204169377846431025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15446789877785007590482733 5792546204169377846431025)
                ·
                  refine ⟨4344409653127033384823269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5792546204169377846431025 4344409653127033384823269)
                  ·
                    refine ⟨814576809961318759654363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4344409653127033384823269 814576809961318759654363)
                    ·
                      rfl

theorem cell22_2379574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_2379574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379574 prefixEnd_2379574 := by exact prefixLift 2379574
  have htrace : WordTrace (prefixWord ++ tailWord_2379574) baseStart_2379574 baseEnd_2379574 := by
    simpa [prefixWord, tailWord_2379574, baseEnd_2379574] using wordTrace_append hprefix tailTrace_2379574
  have hstable : (prefixWord ++ tailWord_2379574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379574).length < 2 ^ (prefixWord ++ tailWord_2379574).sum := by decide
  have hdescent : baseEnd_2379574 < baseStart_2379574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379615 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 1, 7]
def baseStart_2379615 : Nat := 118140960795 + 2379615 * 2 ^ 59
def prefixEnd_2379615 : Nat := 4983230072969 + 3 ^ 40 * 2379615 * 2
def baseEnd_2379615 : Nat := 814590845099208319379237

theorem tailTrace_2379615 : CollatzResearch.WordTrace tailWord_2379615 prefixEnd_2379615 814590845099208319379237 := by
  unfold tailWord_2379615
  simp only [CollatzResearch.WordTrace]
  refine ⟨86791689274068735731484299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57861126182712490487656199 86791689274068735731484299)
  ·
    refine ⟨130187533911103103597226449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86791689274068735731484299 130187533911103103597226449)
    ·
      refine ⟨97640650433327327697919837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130187533911103103597226449 97640650433327327697919837)
      ·
        refine ⟨36615243912497747886719939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97640650433327327697919837 36615243912497747886719939)
        ·
          refine ⟨54922865868746621830079909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36615243912497747886719939 54922865868746621830079909)
          ·
            refine ⟨10298037350389991593139983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54922865868746621830079909 10298037350389991593139983)
            ·
              refine ⟨15447056025584987389709975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10298037350389991593139983 15447056025584987389709975)
              ·
                refine ⟨23170584038377481084564963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15447056025584987389709975 23170584038377481084564963)
                ·
                  refine ⟨34755876057566221626847445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23170584038377481084564963 34755876057566221626847445)
                  ·
                    refine ⟨814590845099208319379237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34755876057566221626847445 814590845099208319379237)
                    ·
                      rfl

theorem cell22_2379615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_2379615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379615 prefixEnd_2379615 := by exact prefixLift 2379615
  have htrace : WordTrace (prefixWord ++ tailWord_2379615) baseStart_2379615 baseEnd_2379615 := by
    simpa [prefixWord, tailWord_2379615, baseEnd_2379615] using wordTrace_append hprefix tailTrace_2379615
  have hstable : (prefixWord ++ tailWord_2379615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379615).length < 2 ^ (prefixWord ++ tailWord_2379615).sum := by decide
  have hdescent : baseEnd_2379615 < baseStart_2379615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379645 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 10]
def baseStart_2379645 : Nat := 118140960795 + 2379645 * 2 ^ 59
def prefixEnd_2379645 : Nat := 4983230072969 + 3 ^ 40 * 2379645 * 2
def baseEnd_2379645 : Nat := 271533704904099413709715

theorem tailTrace_2379645 : CollatzResearch.WordTrace tailWord_2379645 prefixEnd_2379645 271533704904099413709715 := by
  unfold tailWord_2379645
  simp only [CollatzResearch.WordTrace]
  refine ⟨86792783463960050855076389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57861855642640033903384259 86792783463960050855076389)
  ·
    refine ⟨16273646899492509535326823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86792783463960050855076389 16273646899492509535326823)
    ·
      refine ⟨24410470349238764302990235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16273646899492509535326823 24410470349238764302990235)
      ·
        refine ⟨36615705523858146454485353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24410470349238764302990235 36615705523858146454485353)
        ·
          refine ⟨27461779142893609840864015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36615705523858146454485353 27461779142893609840864015)
          ·
            refine ⟨41192668714340414761296023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27461779142893609840864015 41192668714340414761296023)
            ·
              refine ⟨61789003071510622141944035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41192668714340414761296023 61789003071510622141944035)
              ·
                refine ⟨92683504607265933212916053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61789003071510622141944035 92683504607265933212916053)
                ·
                  refine ⟨271533704904099413709715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 92683504607265933212916053 271533704904099413709715)
                  ·
                    rfl

theorem cell22_2379645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_2379645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379645 prefixEnd_2379645 := by exact prefixLift 2379645
  have htrace : WordTrace (prefixWord ++ tailWord_2379645) baseStart_2379645 baseEnd_2379645 := by
    simpa [prefixWord, tailWord_2379645, baseEnd_2379645] using wordTrace_append hprefix tailTrace_2379645
  have hstable : (prefixWord ++ tailWord_2379645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379645).length < 2 ^ (prefixWord ++ tailWord_2379645).sum := by decide
  have hdescent : baseEnd_2379645 < baseStart_2379645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379681 : List Nat := [1, 2, 3, 4, 2, 1, 2, 2, 1, 4]
def baseStart_2379681 : Nat := 118140960795 + 2379681 * 2 ^ 59
def prefixEnd_2379681 : Nat := 4983230072969 + 3 ^ 40 * 2379681 * 2
def baseEnd_2379681 : Nat := 814613438248006147229035

theorem tailTrace_2379681 : CollatzResearch.WordTrace tailWord_2379681 prefixEnd_2379681 814613438248006147229035 := by
  unfold tailWord_2379681
  simp only [CollatzResearch.WordTrace]
  refine ⟨86794096491829629003386897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57862730994553086002257931 86794096491829629003386897)
  ·
    refine ⟨65095572368872221752540173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86794096491829629003386897 65095572368872221752540173)
    ·
      refine ⟨24410839638327083157202565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65095572368872221752540173 24410839638327083157202565)
      ·
        refine ⟨4577032432186328091975481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24410839638327083157202565 4577032432186328091975481)
        ·
          refine ⟨3432774324139746068981611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4577032432186328091975481 3432774324139746068981611)
          ·
            refine ⟨5149161486209619103472417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3432774324139746068981611 5149161486209619103472417)
            ·
              refine ⟨3861871114657214327604313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5149161486209619103472417 3861871114657214327604313)
              ·
                refine ⟨2896403335992910745703235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3861871114657214327604313 2896403335992910745703235)
                ·
                  refine ⟨4344605003989366118554853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2896403335992910745703235 4344605003989366118554853)
                  ·
                    refine ⟨814613438248006147229035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4344605003989366118554853 814613438248006147229035)
                    ·
                      rfl

theorem cell22_2379681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_2379681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379681 prefixEnd_2379681 := by exact prefixLift 2379681
  have htrace : WordTrace (prefixWord ++ tailWord_2379681) baseStart_2379681 baseEnd_2379681 := by
    simpa [prefixWord, tailWord_2379681, baseEnd_2379681] using wordTrace_append hprefix tailTrace_2379681
  have hstable : (prefixWord ++ tailWord_2379681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379681).length < 2 ^ (prefixWord ++ tailWord_2379681).sum := by decide
  have hdescent : baseEnd_2379681 < baseStart_2379681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379709 : List Nat := [1, 4, 1, 2, 3, 2, 1, 2, 2, 4]
def baseStart_2379709 : Nat := 118140960795 + 2379709 * 2 ^ 59
def prefixEnd_2379709 : Nat := 4983230072969 + 3 ^ 40 * 2379709 * 2
def baseEnd_2379709 : Nat := 814623023220223407528949

theorem tailTrace_2379709 : CollatzResearch.WordTrace tailWord_2379709 prefixEnd_2379709 814623023220223407528949 := by
  unfold tailWord_2379709
  simp only [CollatzResearch.WordTrace]
  refine ⟨86795117735728189785406181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57863411823818793190270787 86795117735728189785406181)
  ·
    refine ⟨16274084575449035584763659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86795117735728189785406181 16274084575449035584763659)
    ·
      refine ⟨24411126863173553377145489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16274084575449035584763659 24411126863173553377145489)
      ·
        refine ⟨18308345147380165032859117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24411126863173553377145489 18308345147380165032859117)
        ·
          refine ⟨6865629430267561887322169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18308345147380165032859117 6865629430267561887322169)
          ·
            refine ⟨5149222072700671415491627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6865629430267561887322169 5149222072700671415491627)
            ·
              refine ⟨7723833109051007123237441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5149222072700671415491627 7723833109051007123237441)
              ·
                refine ⟨5792874831788255342428081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7723833109051007123237441 5792874831788255342428081)
                ·
                  refine ⟨4344656123841191506821061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5792874831788255342428081 4344656123841191506821061)
                  ·
                    refine ⟨814623023220223407528949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4344656123841191506821061 814623023220223407528949)
                    ·
                      rfl

theorem cell22_2379709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_2379709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379709 prefixEnd_2379709 := by exact prefixLift 2379709
  have htrace : WordTrace (prefixWord ++ tailWord_2379709) baseStart_2379709 baseEnd_2379709 := by
    simpa [prefixWord, tailWord_2379709, baseEnd_2379709] using wordTrace_append hprefix tailTrace_2379709
  have hstable : (prefixWord ++ tailWord_2379709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379709).length < 2 ^ (prefixWord ++ tailWord_2379709).sum := by decide
  have hdescent : baseEnd_2379709 < baseStart_2379709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379769 : List Nat := [1, 2, 1, 3, 1, 5, 2, 2, 5]
def baseStart_2379769 : Nat := 118140960795 + 2379769 * 2 ^ 59
def prefixEnd_2379769 : Nat := 4983230072969 + 3 ^ 40 * 2379769 * 2
def baseEnd_2379769 : Nat := 271547854148801083676255

theorem tailTrace_2379769 : CollatzResearch.WordTrace tailWord_2379769 prefixEnd_2379769 271547854148801083676255 := by
  unfold tailWord_2379769
  simp only [CollatzResearch.WordTrace]
  refine ⟨86797306115510820032590361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57864870743673880021726907 86797306115510820032590361)
  ·
    refine ⟨65097979586633115024442771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86797306115510820032590361 65097979586633115024442771)
    ·
      refine ⟨97646969379949672536664157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65097979586633115024442771 97646969379949672536664157)
      ·
        refine ⟨36617613517481127201249059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97646969379949672536664157 36617613517481127201249059)
        ·
          refine ⟨54926420276221690801873589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36617613517481127201249059 54926420276221690801873589)
          ·
            refine ⟨5149351900895783512675649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54926420276221690801873589 5149351900895783512675649)
            ·
              refine ⟨3862013925671837634506737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5149351900895783512675649 3862013925671837634506737)
              ·
                refine ⟨2896510444253878225880053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3862013925671837634506737 2896510444253878225880053)
                ·
                  refine ⟨271547854148801083676255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2896510444253878225880053 271547854148801083676255)
                  ·
                    rfl

theorem cell22_2379769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 5].length) (baseStart_2379769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379769 prefixEnd_2379769 := by exact prefixLift 2379769
  have htrace : WordTrace (prefixWord ++ tailWord_2379769) baseStart_2379769 baseEnd_2379769 := by
    simpa [prefixWord, tailWord_2379769, baseEnd_2379769] using wordTrace_append hprefix tailTrace_2379769
  have hstable : (prefixWord ++ tailWord_2379769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379769).length < 2 ^ (prefixWord ++ tailWord_2379769).sum := by decide
  have hdescent : baseEnd_2379769 < baseStart_2379769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379773 : List Nat := [1, 4, 1, 1, 1, 2, 6, 2, 1, 3]
def baseStart_2379773 : Nat := 118140960795 + 2379773 * 2 ^ 59
def prefixEnd_2379773 : Nat := 4983230072969 + 3 ^ 40 * 2379773 * 2
def baseEnd_2379773 : Nat := 814644931728148573928753

theorem tailTrace_2379773 : CollatzResearch.WordTrace tailWord_2379773 prefixEnd_2379773 814644931728148573928753 := by
  unfold tailWord_2379773
  simp only [CollatzResearch.WordTrace]
  refine ⟨86797452007496328715735973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57864968004997552477157315 86797452007496328715735973)
  ·
    refine ⟨16274522251405561634200495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86797452007496328715735973 16274522251405561634200495)
    ·
      refine ⟨24411783377108342451300743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16274522251405561634200495 24411783377108342451300743)
      ·
        refine ⟨36617675065662513676951115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24411783377108342451300743 36617675065662513676951115)
        ·
          refine ⟨54926512598493770515426673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36617675065662513676951115 54926512598493770515426673)
          ·
            refine ⟨41194884448870327886570005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54926512598493770515426673 41194884448870327886570005)
            ·
              refine ⟨1931010208540796619682969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41194884448870327886570005 1931010208540796619682969)
              ·
                refine ⟨1448257656405597464762227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1931010208540796619682969 1448257656405597464762227)
                ·
                  refine ⟨2172386484608396197143341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1448257656405597464762227 2172386484608396197143341)
                  ·
                    refine ⟨814644931728148573928753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2172386484608396197143341 814644931728148573928753)
                    ·
                      rfl

theorem cell22_2379773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_2379773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379773 prefixEnd_2379773 := by exact prefixLift 2379773
  have htrace : WordTrace (prefixWord ++ tailWord_2379773) baseStart_2379773 baseEnd_2379773 := by
    simpa [prefixWord, tailWord_2379773, baseEnd_2379773] using wordTrace_append hprefix tailTrace_2379773
  have hstable : (prefixWord ++ tailWord_2379773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379773).length < 2 ^ (prefixWord ++ tailWord_2379773).sum := by decide
  have hdescent : baseEnd_2379773 < baseStart_2379773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379857 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 1, 9]
def baseStart_2379857 : Nat := 118140960795 + 2379857 * 2 ^ 59
def prefixEnd_2379857 : Nat := 4983230072969 + 3 ^ 40 * 2379857 * 2
def baseEnd_2379857 : Nat := 814673686644800354828495

theorem tailTrace_2379857 : CollatzResearch.WordTrace tailWord_2379857 prefixEnd_2379857 814673686644800354828495 := by
  unfold tailWord_2379857
  simp only [CollatzResearch.WordTrace]
  refine ⟨86800515739192011061793825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57867010492794674041195883 86800515739192011061793825)
  ·
    refine ⟨65100386804394008296345369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86800515739192011061793825 65100386804394008296345369)
    ·
      refine ⟨48825290103295506222259027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65100386804394008296345369 48825290103295506222259027)
      ·
        refine ⟨73237935154943259333388541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48825290103295506222259027 73237935154943259333388541)
        ·
          refine ⟨27464225683103722250020703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73237935154943259333388541 27464225683103722250020703)
          ·
            refine ⟨41196338524655583375031055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27464225683103722250020703 41196338524655583375031055)
            ·
              refine ⟨61794507786983375062546583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41196338524655583375031055 61794507786983375062546583)
              ·
                refine ⟨92691761680475062593819875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61794507786983375062546583 92691761680475062593819875)
                ·
                  refine ⟨139037642520712593890729813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92691761680475062593819875 139037642520712593890729813)
                  ·
                    refine ⟨814673686644800354828495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 139037642520712593890729813 814673686644800354828495)
                    ·
                      rfl

theorem cell22_2379857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_2379857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379857 prefixEnd_2379857 := by exact prefixLift 2379857
  have htrace : WordTrace (prefixWord ++ tailWord_2379857) baseStart_2379857 baseEnd_2379857 := by
    simpa [prefixWord, tailWord_2379857, baseEnd_2379857] using wordTrace_append hprefix tailTrace_2379857
  have hstable : (prefixWord ++ tailWord_2379857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379857).length < 2 ^ (prefixWord ++ tailWord_2379857).sum := by decide
  have hdescent : baseEnd_2379857 < baseStart_2379857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379938 : List Nat := [3, 3, 1, 3, 1, 2, 2, 2, 5]
def baseStart_2379938 : Nat := 118140960795 + 2379938 * 2 ^ 59
def prefixEnd_2379938 : Nat := 4983230072969 + 3 ^ 40 * 2379938 * 2
def baseEnd_2379938 : Nat := 271567138200047714517749

theorem tailTrace_2379938 : CollatzResearch.WordTrace tailWord_2379938 prefixEnd_2379938 271567138200047714517749 := by
  unfold tailWord_2379938
  simp only [CollatzResearch.WordTrace]
  refine ⟨21700867512974640473873117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57868980034599041263661645 21700867512974640473873117)
  ·
    refine ⟨8137825317365490177702419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21700867512974640473873117 8137825317365490177702419)
    ·
      refine ⟨12206737976048235266553629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8137825317365490177702419 12206737976048235266553629)
      ·
        refine ⟨4577526741018088224957611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12206737976048235266553629 4577526741018088224957611)
        ·
          refine ⟨6866290111527132337436417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4577526741018088224957611 6866290111527132337436417)
          ·
            refine ⟨5149717583645349253077313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6866290111527132337436417 5149717583645349253077313)
            ·
              refine ⟨3862288187734011939807985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5149717583645349253077313 3862288187734011939807985)
              ·
                refine ⟨2896716140800508954855989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3862288187734011939807985 2896716140800508954855989)
                ·
                  refine ⟨271567138200047714517749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2896716140800508954855989 271567138200047714517749)
                  ·
                    rfl

theorem cell22_2379938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_2379938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379938 prefixEnd_2379938 := by exact prefixLift 2379938
  have htrace : WordTrace (prefixWord ++ tailWord_2379938) baseStart_2379938 baseEnd_2379938 := by
    simpa [prefixWord, tailWord_2379938, baseEnd_2379938] using wordTrace_append hprefix tailTrace_2379938
  have hstable : (prefixWord ++ tailWord_2379938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379938).length < 2 ^ (prefixWord ++ tailWord_2379938).sum := by decide
  have hdescent : baseEnd_2379938 < baseStart_2379938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2379979 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 1, 6]
def baseStart_2379979 : Nat := 118140960795 + 2379979 * 2 ^ 59
def prefixEnd_2379979 : Nat := 4983230072969 + 3 ^ 40 * 2379979 * 2
def baseEnd_2379979 : Nat := 814715449738032703278121

theorem tailTrace_2379979 : CollatzResearch.WordTrace tailWord_2379979 prefixEnd_2379979 814715449738032703278121 := by
  unfold tailWord_2379979
  simp only [CollatzResearch.WordTrace]
  refine ⟨86804965444750025897734991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57869976963166683931823327 86804965444750025897734991)
  ·
    refine ⟨130207448167125038846602487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86804965444750025897734991 130207448167125038846602487)
    ·
      refine ⟨195311172250687558269903731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130207448167125038846602487 195311172250687558269903731)
      ·
        refine ⟨292966758376031337404855597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195311172250687558269903731 292966758376031337404855597)
        ·
          refine ⟨109862534391011751526820849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 292966758376031337404855597 109862534391011751526820849)
          ·
            refine ⟨82396900793258813645115637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109862534391011751526820849 82396900793258813645115637)
            ·
              refine ⟨7724709449368013779229591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82396900793258813645115637 7724709449368013779229591)
              ·
                refine ⟨11587064174052020668844387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7724709449368013779229591 11587064174052020668844387)
                ·
                  refine ⟨17380596261078031003266581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11587064174052020668844387 17380596261078031003266581)
                  ·
                    refine ⟨814715449738032703278121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17380596261078031003266581 814715449738032703278121)
                    ·
                      rfl

theorem cell22_2379979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 6].length) (baseStart_2379979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2379979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2379979 prefixEnd_2379979 := by exact prefixLift 2379979
  have htrace : WordTrace (prefixWord ++ tailWord_2379979) baseStart_2379979 baseEnd_2379979 := by
    simpa [prefixWord, tailWord_2379979, baseEnd_2379979] using wordTrace_append hprefix tailTrace_2379979
  have hstable : (prefixWord ++ tailWord_2379979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2379979).length < 2 ^ (prefixWord ++ tailWord_2379979).sum := by decide
  have hdescent : baseEnd_2379979 < baseStart_2379979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2379979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380015 : List Nat := [1, 1, 2, 1, 6, 2, 3, 1, 2, 3]
def baseStart_2380015 : Nat := 118140960795 + 2380015 * 2 ^ 59
def prefixEnd_2380015 : Nat := 4983230072969 + 3 ^ 40 * 2380015 * 2
def baseEnd_2380015 : Nat := 814727773273740609378011

theorem tailTrace_2380015 : CollatzResearch.WordTrace tailWord_2380015 prefixEnd_2380015 814727773273740609378011 := by
  unfold tailWord_2380015
  simp only [CollatzResearch.WordTrace]
  refine ⟨86806278472619604046045499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57870852315079736030696999 86806278472619604046045499)
  ·
    refine ⟨130209417708929406069068249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86806278472619604046045499 130209417708929406069068249)
    ·
      refine ⟨97657063281697054551801187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130209417708929406069068249 97657063281697054551801187)
      ·
        refine ⟨146485594922545581827701781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97657063281697054551801187 146485594922545581827701781)
        ·
          refine ⟨6866512261994324148173521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 146485594922545581827701781 6866512261994324148173521)
          ·
            refine ⟨5149884196495743111130141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6866512261994324148173521 5149884196495743111130141)
            ·
              refine ⟨1931206573685903666673803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5149884196495743111130141 1931206573685903666673803)
              ·
                refine ⟨2896809860528855500010705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1931206573685903666673803 2896809860528855500010705)
                ·
                  refine ⟨2172607395396641625008029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2896809860528855500010705 2172607395396641625008029)
                  ·
                    refine ⟨814727773273740609378011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2172607395396641625008029 814727773273740609378011)
                    ·
                      rfl

theorem cell22_2380015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 2, 3].length) (baseStart_2380015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380015 prefixEnd_2380015 := by exact prefixLift 2380015
  have htrace : WordTrace (prefixWord ++ tailWord_2380015) baseStart_2380015 baseEnd_2380015 := by
    simpa [prefixWord, tailWord_2380015, baseEnd_2380015] using wordTrace_append hprefix tailTrace_2380015
  have hstable : (prefixWord ++ tailWord_2380015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380015).length < 2 ^ (prefixWord ++ tailWord_2380015).sum := by decide
  have hdescent : baseEnd_2380015 < baseStart_2380015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380024 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 2, 6]
def baseStart_2380024 : Nat := 118140960795 + 2380024 * 2 ^ 59
def prefixEnd_2380024 : Nat := 4983230072969 + 3 ^ 40 * 2380024 * 2
def baseEnd_2380024 : Nat := 814730854157667585902983

theorem tailTrace_2380024 : CollatzResearch.WordTrace tailWord_2380024 prefixEnd_2380024 814730854157667585902983 := by
  unfold tailWord_2380024
  simp only [CollatzResearch.WordTrace]
  refine ⟨43403303364793499291561563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57871071153057999055415417 43403303364793499291561563)
  ·
    refine ⟨65104955047190248937342345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43403303364793499291561563 65104955047190248937342345)
    ·
      refine ⟨48828716285392686703006759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65104955047190248937342345 48828716285392686703006759)
      ·
        refine ⟨73243074428089030054510139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48828716285392686703006759 73243074428089030054510139)
        ·
          refine ⟨109864611642133545081765209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73243074428089030054510139 109864611642133545081765209)
          ·
            refine ⟨82398458731600158811323907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109864611642133545081765209 82398458731600158811323907)
            ·
              refine ⟨123597688097400238216985861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82398458731600158811323907 123597688097400238216985861)
              ·
                refine ⟨23174566518262544665684849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123597688097400238216985861 23174566518262544665684849)
                ·
                  refine ⟨17380924888696908499263637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23174566518262544665684849 17380924888696908499263637)
                  ·
                    refine ⟨814730854157667585902983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17380924888696908499263637 814730854157667585902983)
                    ·
                      rfl

theorem cell22_2380024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_2380024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380024 prefixEnd_2380024 := by exact prefixLift 2380024
  have htrace : WordTrace (prefixWord ++ tailWord_2380024) baseStart_2380024 baseEnd_2380024 := by
    simpa [prefixWord, tailWord_2380024, baseEnd_2380024] using wordTrace_append hprefix tailTrace_2380024
  have hstable : (prefixWord ++ tailWord_2380024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380024).length < 2 ^ (prefixWord ++ tailWord_2380024).sum := by decide
  have hdescent : baseEnd_2380024 < baseStart_2380024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380028 : List Nat := [2, 2, 2, 1, 4, 3, 2, 6]
def baseStart_2380028 : Nat := 118140960795 + 2380028 * 2 ^ 59
def prefixEnd_2380028 : Nat := 4983230072969 + 3 ^ 40 * 2380028 * 2
def baseEnd_2380028 : Nat := 90525802604379212089219

theorem tailTrace_2380028 : CollatzResearch.WordTrace tailWord_2380028 prefixEnd_2380028 90525802604379212089219 := by
  unfold tailWord_2380028
  simp only [CollatzResearch.WordTrace]
  refine ⟨43403376310786253633134369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57871168414381671510845825 43403376310786253633134369)
  ·
    refine ⟨32552532233089690224850777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43403376310786253633134369 32552532233089690224850777)
    ·
      refine ⟨24414399174817267668638083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32552532233089690224850777 24414399174817267668638083)
      ·
        refine ⟨36621598762225901502957125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24414399174817267668638083 36621598762225901502957125)
        ·
          refine ⟨6866549767917356531804461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36621598762225901502957125 6866549767917356531804461)
          ·
            refine ⟨2574956162969008699426673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6866549767917356531804461 2574956162969008699426673)
            ·
              refine ⟨1931217122226756524570005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2574956162969008699426673 1931217122226756524570005)
              ·
                refine ⟨90525802604379212089219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1931217122226756524570005 90525802604379212089219)
                ·
                  rfl

theorem cell22_2380028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 6].length) (baseStart_2380028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380028 prefixEnd_2380028 := by exact prefixLift 2380028
  have htrace : WordTrace (prefixWord ++ tailWord_2380028) baseStart_2380028 baseEnd_2380028 := by
    simpa [prefixWord, tailWord_2380028, baseEnd_2380028] using wordTrace_append hprefix tailTrace_2380028
  have hstable : (prefixWord ++ tailWord_2380028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380028).length < 2 ^ (prefixWord ++ tailWord_2380028).sum := by decide
  have hdescent : baseEnd_2380028 < baseStart_2380028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380056 : List Nat := [2, 1, 2, 3, 1, 2, 2, 4, 5]
def baseStart_2380056 : Nat := 118140960795 + 2380056 * 2 ^ 59
def prefixEnd_2380056 : Nat := 4983230072969 + 3 ^ 40 * 2380056 * 2
def baseEnd_2380056 : Nat := 271580602803876723034295

theorem tailTrace_2380056 : CollatzResearch.WordTrace tailWord_2380056 prefixEnd_2380056 271580602803876723034295 := by
  unfold tailWord_2380056
  simp only [CollatzResearch.WordTrace]
  refine ⟨43403886932735534024144011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57871849243647378698858681 43403886932735534024144011)
  ·
    refine ⟨65105830399103301036216017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43403886932735534024144011 65105830399103301036216017)
    ·
      refine ⟨48829372799327475777162013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65105830399103301036216017 48829372799327475777162013)
      ·
        refine ⟨18311014799747803416435755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48829372799327475777162013 18311014799747803416435755)
        ·
          refine ⟨27466522199621705124653633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18311014799747803416435755 27466522199621705124653633)
          ·
            refine ⟨20599891649716278843490225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27466522199621705124653633 20599891649716278843490225)
            ·
              refine ⟨15449918737287209132617669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20599891649716278843490225 15449918737287209132617669)
              ·
                refine ⟨2896859763241351712365813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15449918737287209132617669 2896859763241351712365813)
                ·
                  refine ⟨271580602803876723034295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2896859763241351712365813 271580602803876723034295)
                  ·
                    rfl

theorem cell22_2380056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 5].length) (baseStart_2380056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380056 prefixEnd_2380056 := by exact prefixLift 2380056
  have htrace : WordTrace (prefixWord ++ tailWord_2380056) baseStart_2380056 baseEnd_2380056 := by
    simpa [prefixWord, tailWord_2380056, baseEnd_2380056] using wordTrace_append hprefix tailTrace_2380056
  have hstable : (prefixWord ++ tailWord_2380056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380056).length < 2 ^ (prefixWord ++ tailWord_2380056).sum := by decide
  have hdescent : baseEnd_2380056 < baseStart_2380056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380131 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 1, 6]
def baseStart_2380131 : Nat := 118140960795 + 2380131 * 2 ^ 59
def prefixEnd_2380131 : Nat := 4983230072969 + 3 ^ 40 * 2380131 * 2
def baseEnd_2380131 : Nat := 814767482444354973477655

theorem tailTrace_2380131 : CollatzResearch.WordTrace tailWord_2380131 prefixEnd_2380131 814767482444354973477655 := by
  unfold tailWord_2380131
  simp only [CollatzResearch.WordTrace]
  refine ⟨86810509340199355857268247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57873672893466237238178831 86810509340199355857268247)
  ·
    refine ⟨130215764010299033785902371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86810509340199355857268247 130215764010299033785902371)
    ·
      refine ⟨195323646015448550678853557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130215764010299033785902371 195323646015448550678853557)
      ·
        refine ⟨18311591813948301626142521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 195323646015448550678853557 18311591813948301626142521)
        ·
          refine ⟨13733693860461226219606891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18311591813948301626142521 13733693860461226219606891)
          ·
            refine ⟨20600540790691839329410337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13733693860461226219606891 20600540790691839329410337)
            ·
              refine ⟨15450405593018879497057753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20600540790691839329410337 15450405593018879497057753)
              ·
                refine ⟨11587804194764159622793315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15450405593018879497057753 11587804194764159622793315)
                ·
                  refine ⟨17381706292146239434189973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11587804194764159622793315 17381706292146239434189973)
                  ·
                    refine ⟨814767482444354973477655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17381706292146239434189973 814767482444354973477655)
                    ·
                      rfl

theorem cell22_2380131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 6].length) (baseStart_2380131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380131 prefixEnd_2380131 := by exact prefixLift 2380131
  have htrace : WordTrace (prefixWord ++ tailWord_2380131) baseStart_2380131 baseEnd_2380131 := by
    simpa [prefixWord, tailWord_2380131, baseEnd_2380131] using wordTrace_append hprefix tailTrace_2380131
  have hstable : (prefixWord ++ tailWord_2380131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380131).length < 2 ^ (prefixWord ++ tailWord_2380131).sum := by decide
  have hdescent : baseEnd_2380131 < baseStart_2380131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380133 : List Nat := [1, 3, 1, 3, 1, 4, 2, 1, 1, 5]
def baseStart_2380133 : Nat := 118140960795 + 2380133 * 2 ^ 59
def prefixEnd_2380133 : Nat := 4983230072969 + 3 ^ 40 * 2380133 * 2
def baseEnd_2380133 : Nat := 814768167085227634927649

theorem tailTrace_2380133 : CollatzResearch.WordTrace tailWord_2380133 prefixEnd_2380133 814768167085227634927649 := by
  unfold tailWord_2380133
  simp only [CollatzResearch.WordTrace]
  refine ⟨86810582286192110198841053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57873721524128073465894035 86810582286192110198841053)
  ·
    refine ⟨32553968357322041324565395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86810582286192110198841053 32553968357322041324565395)
    ·
      refine ⟨48830952535983061986848093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32553968357322041324565395 48830952535983061986848093)
      ·
        refine ⟨18311607200993648245068035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48830952535983061986848093 18311607200993648245068035)
        ·
          refine ⟨27467410801490472367602053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18311607200993648245068035 27467410801490472367602053)
          ·
            refine ⟨5150139525279463568925385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27467410801490472367602053 5150139525279463568925385)
            ·
              refine ⟨3862604643959597676694039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5150139525279463568925385 3862604643959597676694039)
              ·
                refine ⟨5793906965939396515041059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3862604643959597676694039 5793906965939396515041059)
                ·
                  refine ⟨8690860448909094772561589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5793906965939396515041059 8690860448909094772561589)
                  ·
                    refine ⟨814768167085227634927649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8690860448909094772561589 814768167085227634927649)
                    ·
                      rfl

theorem cell22_2380133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_2380133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380133 prefixEnd_2380133 := by exact prefixLift 2380133
  have htrace : WordTrace (prefixWord ++ tailWord_2380133) baseStart_2380133 baseEnd_2380133 := by
    simpa [prefixWord, tailWord_2380133, baseEnd_2380133] using wordTrace_append hprefix tailTrace_2380133
  have hstable : (prefixWord ++ tailWord_2380133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380133).length < 2 ^ (prefixWord ++ tailWord_2380133).sum := by decide
  have hdescent : baseEnd_2380133 < baseStart_2380133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380238 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 3, 4]
def baseStart_2380238 : Nat := 118140960795 + 2380238 * 2 ^ 59
def prefixEnd_2380238 : Nat := 4983230072969 + 3 ^ 40 * 2380238 * 2
def baseEnd_2380238 : Nat := 814804110731042361052327

theorem tailTrace_2380238 : CollatzResearch.WordTrace tailWord_2380238 prefixEnd_2380238 814804110731042361052327 := by
  unfold tailWord_2380238
  simp only [CollatzResearch.WordTrace]
  refine ⟨10851801493851464141426671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57876274633874475420942245 10851801493851464141426671)
  ·
    refine ⟨16277702240777196212140007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10851801493851464141426671 16277702240777196212140007)
    ·
      refine ⟨24416553361165794318210011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16277702240777196212140007 24416553361165794318210011)
      ·
        refine ⟨36624830041748691477315017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24416553361165794318210011 36624830041748691477315017)
        ·
          refine ⟨27468622531311518607986263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36624830041748691477315017 27468622531311518607986263)
          ·
            refine ⟨41202933796967277911979395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27468622531311518607986263 41202933796967277911979395)
            ·
              refine ⟨61804400695450916867969093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41202933796967277911979395 61804400695450916867969093)
              ·
                refine ⟨11588325130397046912744205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61804400695450916867969093 11588325130397046912744205)
                ·
                  refine ⟨4345621923898892592279077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11588325130397046912744205 4345621923898892592279077)
                  ·
                    refine ⟨814804110731042361052327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4345621923898892592279077 814804110731042361052327)
                    ·
                      rfl

theorem cell22_2380238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_2380238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380238 prefixEnd_2380238 := by exact prefixLift 2380238
  have htrace : WordTrace (prefixWord ++ tailWord_2380238) baseStart_2380238 baseEnd_2380238 := by
    simpa [prefixWord, tailWord_2380238, baseEnd_2380238] using wordTrace_append hprefix tailTrace_2380238
  have hstable : (prefixWord ++ tailWord_2380238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380238).length < 2 ^ (prefixWord ++ tailWord_2380238).sum := by decide
  have hdescent : baseEnd_2380238 < baseStart_2380238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380242 : List Nat := [3, 2, 2, 4, 1, 1, 1, 3, 5]
def baseStart_2380242 : Nat := 118140960795 + 2380242 * 2 ^ 59
def prefixEnd_2380242 : Nat := 4983230072969 + 3 ^ 40 * 2380242 * 2
def baseEnd_2380242 : Nat := 271601826670929227984105

theorem tailTrace_2380242 : CollatzResearch.WordTrace tailWord_2380242 prefixEnd_2380242 271601826670929227984105 := by
  unfold tailWord_2380242
  simp only [CollatzResearch.WordTrace]
  refine ⟨21703639460699305453639745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57876371895198147876372653 21703639460699305453639745)
  ·
    refine ⟨16277729595524479090229809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21703639460699305453639745 16277729595524479090229809)
    ·
      refine ⟨12208297196643359317672357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16277729595524479090229809 12208297196643359317672357)
      ·
        refine ⟨2289055724370629872063567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12208297196643359317672357 2289055724370629872063567)
        ·
          refine ⟨3433583586555944808095351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2289055724370629872063567 3433583586555944808095351)
          ·
            refine ⟨5150375379833917212143027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3433583586555944808095351 5150375379833917212143027)
            ·
              refine ⟨7725563069750875818214541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5150375379833917212143027 7725563069750875818214541)
              ·
                refine ⟨2897086151156578431830453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7725563069750875818214541 2897086151156578431830453)
                ·
                  refine ⟨271601826670929227984105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2897086151156578431830453 271601826670929227984105)
                  ·
                    rfl

theorem cell22_2380242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_2380242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380242 prefixEnd_2380242 := by exact prefixLift 2380242
  have htrace : WordTrace (prefixWord ++ tailWord_2380242) baseStart_2380242 baseEnd_2380242 := by
    simpa [prefixWord, tailWord_2380242, baseEnd_2380242] using wordTrace_append hprefix tailTrace_2380242
  have hstable : (prefixWord ++ tailWord_2380242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380242).length < 2 ^ (prefixWord ++ tailWord_2380242).sum := by decide
  have hdescent : baseEnd_2380242 < baseStart_2380242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380253 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 8]
def baseStart_2380253 : Nat := 118140960795 + 2380253 * 2 ^ 59
def prefixEnd_2380253 : Nat := 4983230072969 + 3 ^ 40 * 2380253 * 2
def baseEnd_2380253 : Nat := 271603081845862440642427

theorem tailTrace_2380253 : CollatzResearch.WordTrace tailWord_2380253 prefixEnd_2380253 271603081845862440642427 := by
  unfold tailWord_2380253
  simp only [CollatzResearch.WordTrace]
  refine ⟨86814959045757370693209413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57876639363838247128806275 86814959045757370693209413)
  ·
    refine ⟨16277804821079507004976765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86814959045757370693209413 16277804821079507004976765)
    ·
      refine ⟨6104176807904815126866287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16277804821079507004976765 6104176807904815126866287)
      ·
        refine ⟨9156265211857222690299431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6104176807904815126866287 9156265211857222690299431)
        ·
          refine ⟨13734397817785834035449147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9156265211857222690299431 13734397817785834035449147)
          ·
            refine ⟨20601596726678751053173721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13734397817785834035449147 20601596726678751053173721)
            ·
              refine ⟨15451197545009063289880291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20601596726678751053173721 15451197545009063289880291)
              ·
                refine ⟨23176796317513594934820437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15451197545009063289880291 23176796317513594934820437)
                ·
                  refine ⟨271603081845862440642427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23176796317513594934820437 271603081845862440642427)
                  ·
                    rfl

theorem cell22_2380253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_2380253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380253 prefixEnd_2380253 := by exact prefixLift 2380253
  have htrace : WordTrace (prefixWord ++ tailWord_2380253) baseStart_2380253 baseEnd_2380253 := by
    simpa [prefixWord, tailWord_2380253, baseEnd_2380253] using wordTrace_append hprefix tailTrace_2380253
  have hstable : (prefixWord ++ tailWord_2380253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380253).length < 2 ^ (prefixWord ++ tailWord_2380253).sum := by decide
  have hdescent : baseEnd_2380253 < baseStart_2380253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
